module Core.TTC

import Core.CaseTree
import Core.CompileExpr
import Core.Core
import Core.TT
import Utils.Binary

import Data.List
import Data.Vect

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
    toBuf b (PV x y) 
        = do tag 4
             toBuf b x
             toBuf b y
    toBuf b (DN x y) 
        = do tag 5
             toBuf b x
             toBuf b y
    toBuf b (GN x) 
        = do tag 6
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
                       y <- fromBuf s b
                       pure (PV x y)
               5 => do x <- fromBuf s b
                       y <- fromBuf s b
                       pure (DN x y)
               6 => do x <- fromBuf s b
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
  toBuf b (Rig1 x) = do tag 1; toBuf b x
  toBuf b RigW = tag 2

  fromBuf s b
      = case !getTag of
             0 => pure Rig0
             1 => do x <- fromBuf s b; pure (Rig1 x)
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
  toBuf b (Local {x} r h) = do tag 0; toBuf b x; toBuf b r; toBuf b h
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
           0 => do x <- fromBuf s b; r <- fromBuf s b;
                   y <- fromBuf s b; pure (Local {x} r y)
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
    toBuf b (Case {var} x ty xs) 
        = do tag 0; toBuf b var; toBuf b ty; toBuf b x
             assert_total (toBuf b xs)
    toBuf b (STerm tm) 
        = do tag 1; toBuf b tm
    toBuf b (Unmatched msg) 
        = do tag 2; toBuf b msg
    toBuf b Impossible 
        = tag 3

    fromBuf s b -- total because it'll fail at the end of the buffer!
        = assert_total $ case !getTag of
               0 => do var <- fromBuf s b
                       ty <- fromBuf s b
                       x <- fromBuf s b
                       y <- fromBuf s b
                       pure (Case {var} x ty y)
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
  toBuf b NotStrictlyPositive = tag 0
  toBuf b (BadCall xs) = do tag 1; toBuf b xs
  toBuf b (RecPath xs) = do tag 2; toBuf b xs

  fromBuf s b 
      = case !getTag of
             0 => pure NotStrictlyPositive
             1 => do xs <- fromBuf s b
                     pure (BadCall xs)
             2 => do xs <- fromBuf s b
                     pure (RecPath xs)
             _ => corrupt "PartialReason"

export
TTC annot Terminating where
  toBuf b Unchecked = tag 0
  toBuf b IsTerminating = tag 1
  toBuf b (NotTerminating p) = do tag 2; toBuf b p

  fromBuf s b
      = case !getTag of
             0 => pure Unchecked
             1 => pure IsTerminating
             2 => do p <- fromBuf s b
                     pure (NotTerminating p)
             _ => corrupt "Terminating"

export
TTC annot Covering where
  toBuf b IsCovering = tag 0
  toBuf b (MissingCases ms) 
      = do tag 1
           toBuf b ms
  toBuf b (NonCoveringCall ns) 
      = do tag 2
           toBuf b ns

  fromBuf s b 
      = case !getTag of
             0 => pure IsCovering
             1 => do ms <- fromBuf s b
                     pure (MissingCases ms)
             2 => do ns <- fromBuf s b
                     pure (NonCoveringCall ns)
             _ => corrupt "Covering"

export
TTC annot Totality where
  toBuf b (MkTotality term cov) = do toBuf b term; toBuf b cov

  fromBuf s b
      = do term <- fromBuf s b
           cov <- fromBuf s b
           pure (MkTotality term cov)

export
TTC annot (PrimFn n) where
  toBuf b (Add ty) = do tag 0; toBuf b ty
  toBuf b (Sub ty) = do tag 1; toBuf b ty
  toBuf b (Mul ty) = do tag 2; toBuf b ty
  toBuf b (Div ty) = do tag 3; toBuf b ty
  toBuf b (Mod ty) = do tag 4; toBuf b ty
  toBuf b (Neg ty) = do tag 5; toBuf b ty
  toBuf b (LT ty) = do tag 6; toBuf b ty
  toBuf b (LTE ty) = do tag 7; toBuf b ty
  toBuf b (EQ ty) = do tag 8; toBuf b ty
  toBuf b (GTE ty) = do tag 9; toBuf b ty
  toBuf b (GT ty) = do tag 10; toBuf b ty
  toBuf b StrLength = tag 11
  toBuf b StrHead = tag 12
  toBuf b StrTail = tag 13
  toBuf b StrIndex = tag 14
  toBuf b StrCons = tag 15
  toBuf b StrAppend = tag 16
  toBuf b StrReverse = tag 17
  toBuf b StrSubstr = tag 18
  toBuf b (Cast x y) = do tag 19; toBuf b x; toBuf b y
  toBuf b BelieveMe = tag 20

  fromBuf {n} s b
      = case n of
             S Z => fromBuf1 s b
             S (S Z) => fromBuf2 s b
             S (S (S Z)) => fromBuf3 s b
             _ => corrupt "PrimFn"
    where
      fromBuf1 : Ref Share (StringMap String) -> Ref Bin Binary ->
                 Core annot (PrimFn 1)
      fromBuf1 s b
          = case !getTag of
                 5 => do ty <- fromBuf s b; pure (Neg ty)
                 11 => pure StrLength
                 12 => pure StrHead
                 13 => pure StrTail
                 17 => pure StrReverse
                 19 => do x <- fromBuf s b; y <- fromBuf s b; pure (Cast x y)
                 _ => corrupt "PrimFn 1"

      fromBuf2 : Ref Share (StringMap String) -> Ref Bin Binary ->
                 Core annot (PrimFn 2)
      fromBuf2 s b
          = case !getTag of
                 0 => do ty <- fromBuf s b; pure (Add ty)
                 1 => do ty <- fromBuf s b; pure (Sub ty)
                 2 => do ty <- fromBuf s b; pure (Mul ty)
                 3 => do ty <- fromBuf s b; pure (Div ty)
                 4 => do ty <- fromBuf s b; pure (Mod ty)
                 6 => do ty <- fromBuf s b; pure (LT ty)
                 7 => do ty <- fromBuf s b; pure (LTE ty)
                 8 => do ty <- fromBuf s b; pure (EQ ty)
                 9 => do ty <- fromBuf s b; pure (GTE ty)
                 10 => do ty <- fromBuf s b; pure (GT ty)
                 14 => pure StrIndex
                 15 => pure StrCons
                 16 => pure StrAppend
                 _ => corrupt "PrimFn 2"
      
      fromBuf3 : Ref Share (StringMap String) -> Ref Bin Binary ->
                 Core annot (PrimFn 3)
      fromBuf3 s b
          = case !getTag of
                 18 => pure StrSubstr
                 20 => pure BelieveMe
                 _ => corrupt "PrimFn 3"
             
mutual
  export
  TTC annot (CExp vars) where
    toBuf b (CLocal {x} h) = do tag 0; toBuf b x; toBuf b h
    toBuf b (CRef n) = do tag 1; toBuf b n
    toBuf b (CLam x sc) = do tag 2; toBuf b x; toBuf b sc
    toBuf b (CLet x val sc) = do tag 3; toBuf b x; toBuf b val; toBuf b sc
    toBuf b (CApp f as) = assert_total $ do tag 4; toBuf b f; toBuf b as
    toBuf b (CCon t n as) = assert_total $ do tag 5; toBuf b t; toBuf b n; toBuf b as
    toBuf b (COp {arity} op as) = assert_total $ do tag 6; toBuf b arity; toBuf b op; toBuf b as
    toBuf b (CExtPrim f as) = assert_total $ do tag 7; toBuf b f; toBuf b as
    toBuf b (CForce x) = assert_total $ do tag 8; toBuf b x
    toBuf b (CDelay x) = assert_total $ do tag 9; toBuf b x
    toBuf b (CConCase sc alts def) = assert_total $ do tag 10; toBuf b sc; toBuf b alts; toBuf b def
    toBuf b (CConstCase sc alts def) = assert_total $ do tag 11; toBuf b sc; toBuf b alts; toBuf b def
    toBuf b (CPrimVal c) = do tag 12; toBuf b c
    toBuf b CErased = do tag 13
    toBuf b (CCrash msg) = do tag 14; toBuf b msg

    fromBuf s b
        = assert_total $ case !getTag of
               0 => do x <- fromBuf s b; h <- fromBuf s b
                       pure (CLocal {x} h)
               1 => do n <- fromBuf s b
                       pure (CRef n)
               2 => do x <- fromBuf s b; sc <- fromBuf s b
                       pure (CLam x sc)
               3 => do x <- fromBuf s b; val <- fromBuf s b; sc <- fromBuf s b
                       pure (CLet x val sc)
               4 => do f <- fromBuf s b; as <- fromBuf s b
                       pure (CApp f as)
               5 => do t <- fromBuf s b; n <- fromBuf s b; as <- fromBuf s b
                       pure (CCon t n as)
               6 => do arity <- fromBuf s b; op <- fromBuf s b; args <- fromBuf s b
                       pure (COp {arity} op args)
               7 => do p <- fromBuf s b; as <- fromBuf s b
                       pure (CExtPrim p as)
               8 => do x <- fromBuf s b
                       pure (CForce x)
               9 => do x <- fromBuf s b
                       pure (CDelay x)
               10 => do sc <- fromBuf s b; alts <- fromBuf s b; def <- fromBuf s b
                        pure (CConCase sc alts def)
               11 => do sc <- fromBuf s b; alts <- fromBuf s b; def <- fromBuf s b
                        pure (CConstCase sc alts def)
               12 => do c <- fromBuf s b
                        pure (CPrimVal c)
               13 => pure CErased
               14 => do msg <- fromBuf s b
                        pure (CCrash msg)
               _ => corrupt "CExp"

  export
  TTC annot (CConAlt vars) where
    toBuf b (MkConAlt n t as sc) = do toBuf b n; toBuf b t; toBuf b as; toBuf b sc

    fromBuf s b
        = do n <- fromBuf s b; t <- fromBuf s b
             as <- fromBuf s b; sc <- fromBuf s b
             pure (MkConAlt n t as sc)

  export
  TTC annot (CConstAlt vars) where
    toBuf b (MkConstAlt c sc) = do toBuf b c; toBuf b sc

    fromBuf s b
        = do c <- fromBuf s b; sc <- fromBuf s b
             pure (MkConstAlt c sc)

export
  TTC annot CDef where
    toBuf b (MkFun args cexpr) = do tag 0; toBuf b args; toBuf b cexpr
    toBuf b (MkCon t arity) = do tag 1; toBuf b t; toBuf b arity
    toBuf b (MkError cexpr) = do tag 2; toBuf b cexpr

    fromBuf s b 
        = case !getTag of
               0 => do args <- fromBuf s b; cexpr <- fromBuf s b
                       pure (MkFun args cexpr)
               1 => do t <- fromBuf s b; arity <- fromBuf s b
                       pure (MkCon t arity)
               2 => do cexpr <- fromBuf s b
                       pure (MkError cexpr)
               _ => corrupt "CDef"

