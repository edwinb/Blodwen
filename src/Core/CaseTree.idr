module Core.CaseTree

import Core.TT

import Control.Monad.State
import Data.CSet
import Data.List

%default total

mutual
  public export
  data CaseTree : List Name -> Type where
       Case : Elem var vars -> (scTy : Term vars) -> 
              List (CaseAlt vars) -> CaseTree vars
       STerm : Term vars -> CaseTree vars
       Unmatched : (msg : String) -> CaseTree vars
       Impossible : CaseTree vars

  %name CaseTree sc

  public export
  data CaseAlt : List Name -> Type where
       ConCase : Name -> (tag : Int) -> (args : List Name) ->
                 CaseTree (args ++ vars) -> CaseAlt vars
       ConstCase : Constant -> CaseTree vars -> CaseAlt vars
       DefaultCase : CaseTree vars -> CaseAlt vars
  
  %name CaseAlt alt

public export
data CaseError = DifferingArgNumbers
               | DifferingTypes
               | MatchErased (vars ** (Env Term vars, Term vars))
               | UnknownType

export
getRefs : CaseTree vars_in -> List Name
getRefs sc = CSet.toList (getSet empty sc)
  where
    mutual
      getAltSet : SortedSet -> CaseAlt vars -> SortedSet
      getAltSet ns (ConCase n t args sc) = getSet (insert n ns) sc
      getAltSet ns (ConstCase i sc) = getSet ns sc
      getAltSet ns (DefaultCase sc) = getSet ns sc

      getAltSets : SortedSet -> List (CaseAlt vars) -> SortedSet
      getAltSets ns [] = ns
      getAltSets ns (a :: as) 
          = assert_total $ getAltSets (getAltSet ns a) as

      getSet : SortedSet -> CaseTree vars -> SortedSet
      getSet ns (Case x ty xs) = getAltSets ns xs
      getSet ns (STerm tm) = assert_total $ union ns (getRefs tm)
      getSet ns (Unmatched msg) = ns
      getSet ns Impossible = ns

mutual
  export
  Show (CaseTree vars) where
    show (Case {var} prf ty alts)
        = "case " ++ show var ++ " : " ++ show ty ++ " of { " ++
                showSep " | " (assert_total (map show alts)) ++ " }"
    show (STerm tm) = show tm
    show (Unmatched msg) = "Error: " ++ show msg
    show Impossible = "Impossible"

  export
  Show (CaseAlt vars) where
    show (ConCase n tag args sc)
        = show n ++ " " ++ showSep " " (map show args) ++ " => " ++
          show sc
    show (ConstCase c sc)
        = show c ++ " => " ++ show sc
    show (DefaultCase sc)
        = "_ => " ++ show sc

mutual
  insertCaseNames : (ns : List Name) -> CaseTree (outer ++ inner) ->
                    CaseTree (outer ++ (ns ++ inner))
  insertCaseNames {outer} {inner} ns (Case x ty xs) 
      = Case (insertElemNames {outer} {inner} ns x) 
             (insertNames {outer} ns ty)
             (assert_total (map (insertCaseAltNames {outer} {inner} ns) xs))
  insertCaseNames {outer} ns (STerm tm) = STerm (insertNames {outer} ns tm)
  insertCaseNames ns (Unmatched msg) = Unmatched msg
  insertCaseNames ns Impossible = Impossible

  insertCaseAltNames : (ns : List Name) -> CaseAlt (outer ++ inner) ->
                       CaseAlt (outer ++ (ns ++ inner))
  insertCaseAltNames {outer} {inner}  ns (ConCase x tag args sc) 
      = ConCase x tag args 
             (assert_total (rewrite appendAssociative args outer (ns ++ inner) in
                      (insertCaseNames {outer = args ++ outer} {inner} ns)
                  (rewrite sym (appendAssociative args outer inner) in 
                           sc)))
  insertCaseAltNames ns (ConstCase x sc) = ConstCase x (insertCaseNames ns sc)
  insertCaseAltNames ns (DefaultCase sc) = DefaultCase (insertCaseNames ns sc)

export
Weaken CaseTree where
  weakenNs ns t = insertCaseNames {outer = []} ns t 

mutual
  export
  embed : CaseTree args -> CaseTree (args ++ more)
  embed (Case x t xs) = Case (elemExtend x) (embed t) (assert_total (map embedAlt xs))
  embed (STerm tm) = STerm (embed tm)
  embed (Unmatched msg) = Unmatched msg
  embed Impossible = Impossible

  embedAlt : CaseAlt args -> CaseAlt (args ++ more)
  embedAlt {args} {more} (ConCase n tag ns sc) 
       = ConCase n tag ns 
                 (rewrite (appendAssociative ns args more) in
                          (embed sc))
  embedAlt (ConstCase x sc) = ConstCase x (embed sc)
  embedAlt (DefaultCase sc) = DefaultCase (embed sc)

public export
data Pat = PCon Name Int (List Pat)
         | PTCon Name Int (List Pat)
         | PConst Constant
         | PConstTy Constant
         | PVar Name
         | PAny

export
Show Pat where
  show (PCon n i args) = show n ++ " " ++ show i ++ " " ++ assert_total (show args)
  show (PTCon n i args) = "<TyCon>" ++ show n ++ " " ++ show i ++ " " ++ assert_total (show args)
  show (PConst c) = show c
  show (PConstTy c) = "<PrimTy>" ++ show c
  show (PVar n) = show n
  show PAny = "_"

export
argToPat : ClosedTerm -> Pat
argToPat tm with (unapply tm)
  argToPat (apply (Ref (DataCon tag _) cn) args) | ArgsList 
         = PCon cn tag (assert_total (map argToPat args))
  argToPat (apply (Ref (TyCon tag _) cn) args) | ArgsList 
         = PTCon cn tag (assert_total (map argToPat args))
  argToPat (apply (Ref Bound var) []) | ArgsList = PVar var
  argToPat (apply (Bind n (Pi _ _ aty) scty) []) | ArgsList
        = PTCon (UN "->") 0 (assert_total 
                               [argToPat aty, argToPat (subst Erased scty)])
  -- Only the ones we can match on become PConst
  argToPat (apply (PrimVal c) []) | ArgsList 
        = if constTag c == 0
             then PConst c
             else PTCon (UN (show c)) 0 []
  argToPat (apply TType []) | ArgsList = PTCon (UN "Type") 0 []
  argToPat (apply f args) | ArgsList = PAny
   
-- Convert a pattern back into a term so that we can refine types of patterns
export
mkTerm : (vars : List Name) -> Pat -> Term vars
mkTerm vars (PCon n t args) 
    = apply (Ref (DataCon t (length args)) n) 
            (assert_total (map (mkTerm vars) args))
mkTerm vars (PTCon n t args) 
    = apply (Ref (TyCon t (length args)) n) 
            (assert_total (map (mkTerm vars) args))
mkTerm vars (PConst c) = PrimVal c
mkTerm vars (PConstTy c) = PrimVal c
mkTerm vars (PVar n) 
    = case isVar n vars of
           Just prf => Local Nothing prf
           _ => Ref Bound n
mkTerm _ _ = Erased


