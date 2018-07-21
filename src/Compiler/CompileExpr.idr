module Compiler.CompileExpr

import Core.CaseTree
import Core.CompileExpr
import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect

%default covering

toCExp : Defs -> Name -> CaseTree vars -> CExp vars
toCExp defs n tree = CCrash "Not done yet"

-- Need this for ensuring that argument list matches up to operator arity for
-- builtins
data ArgList : Nat -> List Name -> Type where
     NoArgs : ArgList Z []
     ConsArg : (a : Name) -> ArgList k as -> ArgList (S k) (a :: as)

mkArgList : Int -> (n : Nat) -> (ns ** ArgList n ns)
mkArgList i Z = (_ ** NoArgs)
mkArgList i (S k) 
    = let (_ ** rec) = mkArgList (i + 1) k in
          (_ ** ConsArg (MN "arg" i) rec)

toCDef : {auto c : Ref Ctxt Defs} -> Name -> Def -> Core annot CDef
toCDef n None 
    = pure $ MkError $ CCrash ("Encountered undefined name " ++ show n)
toCDef n (PMDef _ args tree)
    = pure $ MkFun _ (toCExp !(get Ctxt) n tree) 
toCDef n (Builtin {arity} op)
    = let (ns ** args) = mkArgList 0 arity in
          pure $ MkFun _ (COp op (map toArgExp (getVars args)))
  where
    toArgExp : (x ** List.Elem x ns) -> CExp ns
    toArgExp (x ** p) = CLocal p

    weakenEl : (x ** List.Elem x ns) -> (x ** List.Elem x (a :: ns))
    weakenEl (x ** p) = (x ** There p)

    getVars : ArgList k ns -> Vect k (x ** List.Elem x ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = (a ** Here) :: map weakenEl (getVars rest)
toCDef n (DCon _ _ _)
    = throw (InternalError ("Can't compile constructors directly " ++ show n))
toCDef n (TCon _ _ _ _ _)
    = throw (InternalError ("Can't compile constructors directly " ++ show n))
-- We do want to be able to compile these, but also report an error at run time
-- (and, TODO: warn at compile time)
toCDef n (Hole _ _ _)
    = pure $ MkError $ CCrash ("Encountered unimplemented hole " ++ show n)
toCDef n (Guess _ _)
    = pure $ MkError $ CCrash ("Encountered constrained hole " ++ show n)
toCDef n (BySearch _ _)
    = pure $ MkError $ CCrash ("Encountered incomplete proof search " ++ show n)
toCDef n def 
    = pure $ MkError $ CCrash ("Encountered uncompilable name " ++ show (n, def))

export
compileDef : {auto c : Ref Ctxt Defs} -> Name -> Core annot ()
compileDef n
    = do defs <- get Ctxt
         case lookupDefExact n (gamma defs) of
              Just d => do ce <- toCDef n d
                           setCompiled n ce
              Nothing => throw (InternalError ("Trying to compile unknown name " ++ show n))
