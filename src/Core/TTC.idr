module Core.TTC

import Core.CaseTree
import Core.Core
import Core.TT
import Utils.Binary

import Data.List

%default total

-- TTC instances for TT primitives

mutual
  export
	TTC annot GenName where
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

    fromBuf s b 
        = case !getTag of
               0 => do x <- fromBuf s b
                       y <- fromBuf s b
                       pure (Nested x y)
               1 => do x <- fromBuf s b
                       y <- fromBuf s b
                       pure (CaseBlock x y)
               2 => do x <- fromBuf s b
                       y <- fromBuf s b
                       pure (WithBlock x y)
               _ => throw (TTCError (Corrupt "GenName"))

  export
	TTC annot Name where
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

    fromBuf s b 
        = assert_total $ case !getTag of
               0 => do x <- fromBuf s b
                       pure (UN x)
               1 => do x <- fromBuf s b
                       y <- fromBuf s b
                       pure (MN x y)
               2 => do xs <- fromBuf s b
                       x <- fromBuf s b
                       pure (NS xs x)
               3 => do x <- fromBuf s b
                       y <- fromBuf s b
                       pure (HN x y)
               4 => do x <- fromBuf s b
                       pure (PV x)
               5 => do x <- fromBuf s b
                       pure (GN x)
               _ => throw (TTCError (Corrupt "Name"))

export
TTC annot NameType where
  toBuf b Bound = tag 0
  toBuf b Func = tag 1
  toBuf b (DataCon t arity) = do tag 2; toBuf b t; toBuf b arity
  toBuf b (TyCon t arity) = do tag 3; toBuf b t; toBuf b arity

  fromBuf s b
      = case !getTag of
             0 => pure Bound
             1 => pure Func
             2 => do x <- fromBuf s b; y <- fromBuf s b; pure (DataCon x y)
             3 => do x <- fromBuf s b; y <- fromBuf s b; pure (TyCon x y)
             _ => corrupt "NameType"

export
TTC annot PiInfo where
  toBuf b Implicit = tag 0
  toBuf b Explicit = tag 1
  toBuf b AutoImplicit = tag 2

  fromBuf s b
      = case !getTag of
             0 => pure Implicit
             1 => pure Explicit
             2 => pure AutoImplicit
             _ => corrupt "PiInfo"

export
TTC annot RigCount where
  toBuf b Rig0 = tag 0
  toBuf b Rig1 = tag 1
  toBuf b RigW = tag 2

  fromBuf s b
      = case !getTag of
             0 => pure Rig0
             1 => pure Rig1
             2 => pure RigW
             _ => corrupt "RigCount"

export
TTC annot ty => TTC annot (Binder ty) where
  toBuf b (Lam c x ty) = do tag 0; toBuf b c; toBuf b x; toBuf b ty
  toBuf b (Let c val ty) = do tag 1; toBuf b c; toBuf b val; toBuf b ty
  toBuf b (Pi c x ty) = do tag 2; toBuf b c; toBuf b x; toBuf b ty
  toBuf b (PVar c ty) = do tag 3; toBuf b c; toBuf b ty
  toBuf b (PLet c val ty) = do tag 4; toBuf b c; toBuf b val; toBuf b ty
  toBuf b (PVTy c ty) = do tag 5; toBuf b c; toBuf b ty

  fromBuf s b
      = case !getTag of
             0 => do c <- fromBuf s b; x <- fromBuf s b; y <- fromBuf s b; pure (Lam c x y)
             1 => do c <- fromBuf s b; x <- fromBuf s b; y <- fromBuf s b; pure (Let c x y)
             2 => do c <- fromBuf s b; x <- fromBuf s b; y <- fromBuf s b; pure (Pi c x y)
             3 => do c <- fromBuf s b; x <- fromBuf s b; pure (PVar c x)
             4 => do c <- fromBuf s b; x <- fromBuf s b; y <- fromBuf s b; pure (PLet c x y)
             5 => do c <- fromBuf s b; x <- fromBuf s b; pure (PVTy c x)
             _ => corrupt "Binder"

export
TTC annot Constant where
  toBuf b (I x) = do tag 0; toBuf b x
  toBuf b (BI x) = do tag 1; toBuf b x
  toBuf b (Str x) = do tag 2; toBuf b x
  toBuf b (Ch x) = do tag 3; toBuf b x
  toBuf b (Db x) = do tag 4; toBuf b x
  
  toBuf b WorldVal = tag 5
  toBuf b IntType = tag 6
  toBuf b IntegerType = tag 7 
  toBuf b StringType = tag 8
  toBuf b CharType = tag 9
  toBuf b DoubleType = tag 10
  toBuf b WorldType = tag 11

  fromBuf s b
      = case !getTag of
             0 => do x <- fromBuf s b; pure (I x)
             1 => do x <- fromBuf s b; pure (BI x)
             2 => do x <- fromBuf s b; pure (Str x)
             3 => do x <- fromBuf s b; pure (Ch x)
             4 => do x <- fromBuf s b; pure (Db x)
             5 => pure WorldVal
             6 => pure IntType
             7 => pure IntegerType
             8 => pure StringType
             9 => pure CharType
             10 => pure DoubleType
             11 => pure WorldType
             _ => corrupt "Constant"

export
TTC annot (Term vars) where
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

  fromBuf s b -- total because it'll fail at the end of the buffer!
      = assert_total $ case !getTag of
           0 => do x <- fromBuf s b; y <- fromBuf s b; pure (Local {x} y)
           1 => do x <- fromBuf s b; y <- fromBuf s b
                   pure (Ref x y)
           2 => do x <- fromBuf s b; y <- fromBuf s b
                   z <- fromBuf s b
                   pure (Bind x y z)
           3 => do x <- fromBuf s b; y <- fromBuf s b
                   pure (App x y)
           4 => do x <- fromBuf s b
                   pure (PrimVal x)
           5 => pure Erased
           6 => pure TType
           _ => corrupt "Term"

export
TTC annot (Env Term vars) where
  toBuf b [] = pure ()
  toBuf b ((::) bnd env) 
      = do toBuf b bnd; toBuf b env

  -- Length has to correspond to length of 'vars'
  fromBuf s {vars = []} b = pure Nil
  fromBuf s {vars = x :: xs} b
      = do bnd <- fromBuf s b
           env <- fromBuf s b
           pure (bnd :: env)

mutual
  export
  TTC annot (CaseAlt vars) where
    toBuf b (ConCase x t args sc) 
        = do tag 0; toBuf b x; toBuf b t
             toBuf b args
             assert_total (toBuf b sc)
    toBuf b (ConstCase x sc)
        = do tag 1; toBuf b x; toBuf b sc
    toBuf b (DefaultCase sc)
        = do tag 2; toBuf b sc

    fromBuf s b -- total because it'll fail at the end of the buffer!
        = assert_total $ case !getTag of
               0 => do w <- fromBuf s b; x <- fromBuf s b; 
                       y <- fromBuf s b; z <- fromBuf s b;
                       pure (ConCase w x y z)
               1 => do x <- fromBuf s b; y <- fromBuf s b;
                       pure (ConstCase x y)
               2 => do x <- fromBuf s b
                       pure (DefaultCase x)
               _ => corrupt "CaseAlt"

  export
  TTC annot (CaseTree vars) where
    toBuf b (Case {var} x xs) 
        = do tag 0; toBuf b var; toBuf b x
             assert_total (toBuf b xs)
    toBuf b (STerm tm) 
        = do tag 1; toBuf b tm
    toBuf b (Unmatched msg) 
        = do tag 2; toBuf b msg
    toBuf b Impossible 
        = tag 3

    fromBuf s b -- total because it'll fail at the end of the buffer!
        = assert_total $ case !getTag of
               0 => do var <- fromBuf s b; x <- fromBuf s b
                       y <- fromBuf s b
                       pure (Case {var} x y)
               1 => do x <- fromBuf s b
                       pure (STerm x)
               2 => do x <- fromBuf s b
                       pure (Unmatched x)
               3 => pure Impossible
               _ => corrupt "CaseTree"

export
TTC annot Visibility where
  toBuf b Private = tag 0
  toBuf b Export = tag 1
  toBuf b Public = tag 2

  fromBuf s b 
      = case !getTag of
             0 => pure Private
             1 => pure Export
             2 => pure Public
             _ => corrupt "Visibility"

export
TTC annot PartialReason where
  toBuf b NotCovering = tag 0
  toBuf b NotStrictlyPositive = tag 1
  toBuf b (Calling xs) = do tag 2; toBuf b xs

  fromBuf s b 
      = case !getTag of
             0 => pure NotCovering
             1 => pure NotStrictlyPositive
             2 => do xs <- fromBuf s b
                     pure (Calling xs)
             _ => corrupt "PartialReason"

export
TTC annot Totality where
  toBuf b (Partial x) = do tag 0; toBuf b x
  toBuf b Unchecked = tag 1
  toBuf b Covering = tag 2
  toBuf b Total = tag 3

  fromBuf s b 
      = case !getTag of
             0 => do x <- fromBuf s b; pure (Partial x)
             1 => pure Unchecked
             2 => pure Covering
             3 => pure Total
             _ => corrupt "Totality"
