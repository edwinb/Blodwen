module Core.TTI

import Core.CaseTree
import Core.Core
import Core.TT
import Utils.Binary

import Data.List

%default total

-- TTI instances for TT primitives

mutual
  export
	TTI GenName where
    toBuf b (Nested x y) 
        = do tag 0
             toBuf b x
             toBuf b y
    toBuf b (CaseBlock x y) 
        = do tag 1
             toBuf b x
             toBuf b y
    toBuf b (WithBlock x y) 
        = do tag 2
             toBuf b x
             toBuf b y

    fromBuf b 
        = case !getTag of
               0 => do x <- fromBuf b
                       y <- fromBuf b
                       pure (Nested x y)
               1 => do x <- fromBuf b
                       y <- fromBuf b
                       pure (CaseBlock x y)
               2 => do x <- fromBuf b
                       y <- fromBuf b
                       pure (WithBlock x y)
               _ => throw (TTIError (Corrupt "GenName"))

  export
	TTI Name where
    toBuf b (UN x) 
        = do tag 0
             toBuf b x
    toBuf b (MN x y) 
        = do tag 1
             toBuf b x
             toBuf b y
    toBuf b (NS xs x) 
        = do tag 2
             toBuf b xs
             toBuf b x
    toBuf b (HN x y) 
        = do tag 3
             toBuf b x
             toBuf b y
    toBuf b (PV x) 
        = do tag 4
             toBuf b x
    toBuf b (GN x) 
        = do tag 5
             toBuf b x

    fromBuf b 
        = assert_total $ case !getTag of
               0 => do x <- fromBuf b
                       pure (UN x)
               1 => do x <- fromBuf b
                       y <- fromBuf b
                       pure (MN x y)
               2 => do xs <- fromBuf b
                       x <- fromBuf b
                       pure (NS xs x)
               3 => do x <- fromBuf b
                       y <- fromBuf b
                       pure (HN x y)
               4 => do x <- fromBuf b
                       pure (PV x)
               5 => do x <- fromBuf b
                       pure (GN x)
               _ => throw (TTIError (Corrupt "Name"))

export
TTI NameType where
  toBuf b Bound = tag 0
  toBuf b Func = tag 1
  toBuf b (DataCon t arity) = do tag 2; toBuf b t; toBuf b arity
  toBuf b (TyCon t arity) = do tag 3; toBuf b t; toBuf b arity

  fromBuf b
      = case !getTag of
             0 => pure Bound
             1 => pure Func
             2 => do x <- fromBuf b; y <- fromBuf b; pure (DataCon x y)
             3 => do x <- fromBuf b; y <- fromBuf b; pure (TyCon x y)
             _ => corrupt "NameType"

export
TTI PiInfo where
  toBuf b Implicit = tag 0
  toBuf b Explicit = tag 1
  toBuf b AutoImplicit = tag 2

  fromBuf b
      = case !getTag of
             0 => pure Implicit
             1 => pure Explicit
             2 => pure AutoImplicit
             _ => corrupt "PiInfo"

export
TTI annot => TTI (Binder annot) where
  toBuf b (Lam x ty) = do tag 0; toBuf b x; toBuf b ty
  toBuf b (Let val ty) = do tag 1; toBuf b val; toBuf b ty
  toBuf b (Pi x ty) = do tag 2; toBuf b x; toBuf b ty
  toBuf b (PVar ty) = do tag 3; toBuf b ty
  toBuf b (PLet val ty) = do tag 4; toBuf b val; toBuf b ty
  toBuf b (PVTy ty) = do tag 5; toBuf b ty

  fromBuf b
      = case !getTag of
             0 => do x <- fromBuf b; y <- fromBuf b; pure (Lam x y)
             1 => do x <- fromBuf b; y <- fromBuf b; pure (Let x y)
             2 => do x <- fromBuf b; y <- fromBuf b; pure (Pi x y)
             3 => do x <- fromBuf b; pure (PVar x)
             4 => do x <- fromBuf b; y <- fromBuf b; pure (PLet x y)
             5 => do x <- fromBuf b; pure (PVTy x)
             _ => corrupt "Binder"

export
TTI Constant where
  toBuf b (I x) = do tag 0; toBuf b x
  toBuf b IntType = tag 1

  fromBuf b
      = case !getTag of
             0 => do x <- fromBuf b; pure (I x)
             1 => pure IntType
             _ => corrupt "Constant"

export
TTI (Term vars) where
  toBuf b (Local {x} h) = do tag 0; toBuf b x; toBuf b h
  toBuf b (Ref nt fn) = do tag 1; toBuf b nt; toBuf b fn
  toBuf b (Bind x bnd tm) 
      = do tag 2; toBuf b x
           assert_total (toBuf b bnd)
           toBuf b tm
  toBuf b (App tm x) = do tag 3; toBuf b tm; toBuf b x
  toBuf b (PrimVal x) = do tag 4; toBuf b x
  toBuf b Erased = tag 5
  toBuf b TType = tag 6

  fromBuf b -- total because it'll fail at the end of the buffer!
      = assert_total $ case !getTag of
           0 => do x <- fromBuf b; y <- fromBuf b; pure (Local {x} y)
           1 => do x <- fromBuf b; y <- fromBuf b
                   pure (Ref x y)
           2 => do x <- fromBuf b; y <- fromBuf b
                   z <- fromBuf b
                   pure (Bind x y z)
           3 => do x <- fromBuf b; y <- fromBuf b
                   pure (App x y)
           4 => do x <- fromBuf b
                   pure (PrimVal x)
           5 => pure Erased
           6 => pure TType
           _ => corrupt "Term"

mutual
  export
  TTI (CaseAlt vars) where
    toBuf b (ConCase x t args sc) 
        = do tag 0; toBuf b x; toBuf b t
             toBuf b args
             assert_total (toBuf b sc)
    toBuf b (ConstCase x sc)
        = do tag 1; toBuf b x; toBuf b sc
    toBuf b (DefaultCase sc)
        = do tag 2; toBuf b sc

    fromBuf b -- total because it'll fail at the end of the buffer!
        = assert_total $ case !getTag of
               0 => do w <- fromBuf b; x <- fromBuf b; 
                       y <- fromBuf b; z <- fromBuf b;
                       pure (ConCase w x y z)
               1 => do x <- fromBuf b; y <- fromBuf b;
                       pure (ConstCase x y)
               2 => do x <- fromBuf b
                       pure (DefaultCase x)
               _ => corrupt "CaseAlt"

  export
  TTI (CaseTree vars) where
    toBuf b (Case {var} x xs) 
        = do tag 0; toBuf b var; toBuf b x
             assert_total (toBuf b xs)
    toBuf b (STerm tm) 
        = do tag 1; toBuf b tm
    toBuf b (Unmatched msg) 
        = do tag 2; toBuf b msg
    toBuf b Impossible 
        = tag 3

    fromBuf b -- total because it'll fail at the end of the buffer!
        = assert_total $ case !getTag of
               0 => do var <- fromBuf b; x <- fromBuf b
                       y <- fromBuf b
                       pure (Case {var} x y)
               1 => do x <- fromBuf b
                       pure (STerm x)
               2 => do x <- fromBuf b
                       pure (Unmatched x)
               3 => pure Impossible
               _ => corrupt "CaseTree"
