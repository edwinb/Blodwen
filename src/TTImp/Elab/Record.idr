module TTImp.Elab.Record

import TTImp.TTImp
import TTImp.Elab.Ambiguity
import TTImp.Elab.Delayed
import TTImp.Elab.Rewrite
import public TTImp.Elab.State
import TTImp.Reflect

import Core.AutoSearch
import Core.CaseTree
import Core.Context
import Core.Metadata
import Core.Normalise
import Core.Reflect
import Core.TT
import Core.Typecheck
import Core.Unify

import Data.List
import Data.List.Views

getRecordType : Env Term vars -> NF vars -> Maybe Name
getRecordType env (NTCon n _ _ _) = Just n
getRecordType env _ = Nothing

data Rec : Type -> Type where
     Field : String -> RawImp annot -> Rec annot -- field name on left, value on right
     Constr : Name -> List (String, Rec annot) -> Rec annot

toLHS : annot -> Rec annot -> RawImp annot
toLHS loc (Field n _) = IBindVar loc n
toLHS loc (Constr con args)
    = let args' = map (\a => toLHS loc (snd a)) args in
          apply (IVar loc con) args'

toRHS : annot -> Rec annot -> RawImp annot
toRHS loc (Field _ val) = val
toRHS loc (Constr con args)
    = let args' = map (\a => toRHS loc (snd a)) args in
          apply (IVar loc con) args'

findConName : Defs -> Name -> Maybe Name
findConName defs tyn
    = case lookupDefExact tyn (gamma defs) of
           Just (TCon _ _ _ _ [con]) => Just con
           _ => Nothing

findFields : Defs -> Name -> Maybe (List (String, Maybe Name))
findFields defs con
    = case lookupTyExact con (gamma defs) of
           Just t => Just (getExpNames (nf defs [] t))
           _ => Nothing
  where
    getExpNames : NF [] -> List (String, Maybe Name)
    getExpNames (NBind x (Pi _ p ty) sc)
        = let rest = getExpNames (sc (toClosure defaultOpts [] Erased)) in
              case p of
                   Explicit => (nameRoot x, getRecordType [] ty) :: rest
                   _ => rest
    getExpNames _ = []

genFieldName : {auto x : Ref Ctxt Defs} ->
               String -> Core annot String
genFieldName root
    = do defs <- get Ctxt
         put Ctxt (record { nextVar $= (+1) } defs)
         pure (root ++ show (nextVar defs))

-- There's probably a generic version of this in the prelude isn't
-- there?
replace : String -> Rec annot -> 
          List (String, Rec annot) -> List (String, Rec annot)
replace k v [] = []
replace k v ((k', v') :: vs)
    = if k == k' 
         then ((k, v) :: vs)
         else ((k', v') :: replace k v vs)

findPath : {auto c : Ref Ctxt Defs} ->
           annot -> List String -> List String -> Maybe Name -> 
           (String -> RawImp annot) ->
           Rec annot -> Core annot (Rec annot)
findPath loc [] full tyn val (Field lhs _) = pure (Field lhs (val lhs))
findPath loc [] full tyn val rec 
   = throw (IncompatibleFieldUpdate loc full)
findPath loc (p :: ps) full Nothing val (Field n v) 
   = throw (NotRecordField loc p Nothing)
findPath loc (p :: ps) full (Just tyn) val (Field n v) 
   = do defs <- get Ctxt
        let Just con = findConName defs tyn
                 | Nothing => throw (NotRecordType loc tyn)
        let Just fs = findFields defs con
                 | Nothing => throw (NotRecordType loc tyn)
        args <- mkArgs fs
        let rec' = Constr con args
        findPath loc (p :: ps) full (Just tyn) val rec'
  where
    mkArgs : List (String, Maybe Name) -> 
             Core annot (List (String, Rec annot))
    mkArgs [] = pure []
    mkArgs ((p, _) :: ps)
        = do fldn <- genFieldName p
             args' <- mkArgs ps
             pure ((p, Field fldn (IVar loc (UN fldn))) :: args')

findPath loc (p :: ps) full tyn val (Constr con args) 
   = do let Just prec = lookup p args
                 | Nothing => throw (NotRecordField loc p tyn)
        defs <- get Ctxt
        let Just fs = findFields defs con
                 | Nothing => pure (Constr con args)
        let Just mfty = lookup p fs
                 | Nothing => throw (NotRecordField loc p tyn)
        prec' <- findPath loc ps full mfty val prec
        pure (Constr con (replace p prec' args))

getSides : {auto c : Ref Ctxt Defs} ->
           annot -> IFieldUpdate annot -> Name -> RawImp annot -> Rec annot -> 
           Core annot (Rec annot)
getSides loc (ISetField path val) tyn orig rec 
   -- update 'rec' so that 'path' is accessible on the lhs and rhs,
   -- then set the path on the rhs to 'val'
   = findPath loc path path (Just tyn) (const val) rec
getSides loc (ISetFieldApp path val) tyn orig rec 
   = findPath loc path path (Just tyn) (\n => apply val [IVar loc (UN n)]) rec
 where
   get : List String -> RawImp annot -> RawImp annot
   get [] rec = rec
   get (p :: ps) rec = get ps (IApp loc (IVar loc (UN p)) rec)

getAllSides : {auto c : Ref Ctxt Defs} ->
              annot -> List (IFieldUpdate annot) -> Name -> 
              RawImp annot -> Rec annot -> 
              Core annot (Rec annot)
getAllSides loc [] tyn orig rec = pure rec
getAllSides loc (u :: upds) tyn orig rec 
    = getAllSides loc upds tyn orig !(getSides loc u tyn orig rec)

export
recUpdate : {auto c : Ref Ctxt Defs} -> 
            {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            {auto m : Ref Meta (Metadata annot)} ->
            RigCount -> Elaborator annot ->
            ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
            List (IFieldUpdate annot) -> 
            (rec : RawImp annot) -> (recty : Term vars) ->
            Core annot (RawImp annot)
recUpdate rigc process elabinfo loc env nest flds rec recty
      = do defs <- get Ctxt
           let Just rectyn = getRecordType env (nf defs env recty)
                    | Nothing => throw (RecordTypeNeeded loc env)
           fldn <- genFieldName "fld"
           sides <- getAllSides loc flds rectyn rec (Field fldn (IVar loc (UN fldn)))
           pure $ ICase loc rec (Implicit loc) [mkClause sides]
  where
    mkClause : Rec annot -> ImpClause annot
    mkClause rec = PatClause loc (toLHS loc rec) (toRHS loc rec)

