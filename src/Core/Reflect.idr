module Core.Reflect

import Core.Context
import Core.Normalise
import Core.TT

%default covering

public export
interface Reify a where
  reify : Defs -> NF vars -> Maybe a

public export
interface Reflect a where
  reflect : Defs -> Env Term vars -> a -> Maybe (Term vars)

export
getCon : Defs -> Name -> Maybe (Term vars)
getCon defs n
    = case lookupDefExact n (gamma defs) of
           Just (DCon t a _) => pure (Ref (DataCon t a) n)
           Just (TCon t a _ _ _ _) => pure (Ref (TyCon t a) n)
           Just _ => pure (Ref Func n)
           _ => Nothing

export
appCon : Defs -> Name -> List (Term vars) -> Maybe (Term vars)
appCon defs n args
    = do fn <- getCon defs n
         pure (apply fn args)

export
Reify () where
  reify defs _ = pure ()

export
Reflect () where
  reflect defs env _ = getCon defs (NS ["Prelude"] (UN "MkUnit"))

export
Reify String where
  reify defs (NPrimVal (Str str)) = pure str
  reify defs _ = Nothing

export
Reflect String where
  reflect defs env x = pure (PrimVal (Str x))

export
Reify Int where
  reify defs (NPrimVal (I i)) = pure i
  reify defs _ = Nothing

export
Reflect Int where
  reflect defs env x = pure (PrimVal (I x))

export
Reify Integer where
  reify defs (NPrimVal (BI i)) = pure i
  reify defs _ = Nothing

export
Reflect Integer where
  reflect defs env x = pure (PrimVal (BI x))

export
Reify Char where
  reify defs (NPrimVal (Ch i)) = pure i
  reify defs _ = Nothing

export
Reflect Char where
  reflect defs env x = pure (PrimVal (Ch x))

export
Reify Double where
  reify defs (NPrimVal (Db i)) = pure i
  reify defs _ = Nothing

export
Reflect Double where
  reflect defs env x = pure (PrimVal (Db x))

export
Reify Bool where
  reify defs (NDCon (NS _ (UN "True")) _ _ _) = pure True
  reify defs (NDCon (NS _ (UN "False")) _ _ _) = pure True
  reify defs _ = Nothing

export
Reflect Bool where
  reflect defs env True = getCon defs (NS ["Prelude"] (UN "True"))
  reflect defs env False = getCon defs (NS ["Prelude"] (UN "False"))

export
Reify a => Reify (List a) where
  reify defs (NDCon (NS _ (UN "Nil")) _ _ _)
      = pure []
  reify defs (NDCon (NS _ (UN "::")) _ _ [_, x, xs])
      = do x' <- reify defs (evalClosure defs x)
           xs' <- reify defs (evalClosure defs xs)
           pure (x' :: xs')
  reify defs _ = Nothing

export
Reflect a => Reflect (List a) where
  reflect defs env [] = getCon defs (NS ["Prelude"] (UN "Nil"))
  reflect defs env (x :: xs)
      = do x' <- reflect defs env x
           xs' <- reflect defs env xs
           appCon defs (NS ["Prelude"] (UN "::")) [x', xs']

export
(Reify a, Reify b) => Reify (a, b) where
  reify defs (NDCon (NS _ (UN "MkPair")) _ _ [_, _, x, y])
      = do x' <- reify defs (evalClosure defs x)
           y' <- reify defs (evalClosure defs y)
           pure (x', y')
  reify defs _ = Nothing

export
(Reflect a, Reflect b) => Reflect (a, b) where
  reflect defs env (x, y)
      = do x' <- reflect defs env x
           y' <- reflect defs env y
           appCon defs (NS ["Prelude"] (UN "MkPair")) [Erased, Erased, x', y']

export
Reify Name where
  reify defs (NDCon (NS ["Reflect"] (UN "UN")) _ _ [str])
      = do str' <- reify defs (evalClosure defs str)
           pure (UN str')
  reify defs (NDCon (NS ["Reflect"] (UN "MN")) _ _ [str, i])
      = do str' <- reify defs (evalClosure defs str)
           i' <- reify defs (evalClosure defs i)
           pure (MN str' i')
  reify defs (NDCon (NS ["Reflect"] (UN "NS")) _ _ [ns, n])
      = do ns' <- reify defs (evalClosure defs ns)
           n' <- reify defs (evalClosure defs n)
           pure (NS ns' n')
  reify defs _ = Nothing

export
Reflect Name where
  reflect defs env (UN x) 
      = do x' <- reflect defs env x
           appCon defs (NS ["Reflect"] (UN "UN")) [x']
  reflect defs env (MN x i) 
      = do x' <- reflect defs env x
           i' <- reflect defs env i
           appCon defs (NS ["Reflect"] (UN "MN")) [x', i']
  reflect defs env (NS ns n) 
      = do ns' <- reflect defs env ns
           n' <- reflect defs env n
           appCon defs (NS ["Reflect"] (UN "NS")) [ns', n']
  reflect defs env _ = Nothing

export
Reify Constant where
  reify defs (NDCon (NS ["Reflect"] (UN "I")) _ _ [x])
      = do x' <- reify defs (evalClosure defs x)
           pure (I x')
  reify defs (NDCon (NS ["Reflect"] (UN "BI")) _ _ [x])
      = do x' <- reify defs (evalClosure defs x)
           pure (BI x')
  reify defs (NDCon (NS ["Reflect"] (UN "Str")) _ _ [x])
      = do x' <- reify defs (evalClosure defs x)
           pure (Str x')
  reify defs (NDCon (NS ["Reflect"] (UN "Ch")) _ _ [x])
      = do x' <- reify defs (evalClosure defs x)
           pure (Ch x')
  reify defs (NDCon (NS ["Reflect"] (UN "Db")) _ _ [x])
      = do x' <- reify defs (evalClosure defs x)
           pure (Db x')
  reify defs (NDCon (NS ["Reflect"] (UN "WorldVal")) _ _ [])
      = pure WorldVal
  reify defs (NDCon (NS ["Reflect"] (UN "IntType")) _ _ [])
      = pure IntType
  reify defs (NDCon (NS ["Reflect"] (UN "IntegerType")) _ _ [])
      = pure IntegerType
  reify defs (NDCon (NS ["Reflect"] (UN "StringType")) _ _ [])
      = pure StringType
  reify defs (NDCon (NS ["Reflect"] (UN "CharType")) _ _ [])
      = pure CharType
  reify defs (NDCon (NS ["Reflect"] (UN "DoubleType")) _ _ [])
      = pure DoubleType
  reify defs (NDCon (NS ["Reflect"] (UN "WorldType")) _ _ [])
      = pure WorldType
  reify defs _ = Nothing

export
Reflect Constant where
  reflect defs env (I x)
      = do x' <- reflect defs env x
           appCon defs (NS ["Reflect"] (UN "I")) [x']
  reflect defs env (BI x)
      = do x' <- reflect defs env x
           appCon defs (NS ["Reflect"] (UN "BI")) [x']
  reflect defs env (Str x)
      = do x' <- reflect defs env x
           appCon defs (NS ["Reflect"] (UN "Str")) [x']
  reflect defs env (Ch x)
      = do x' <- reflect defs env x
           appCon defs (NS ["Reflect"] (UN "Ch")) [x']
  reflect defs env (Db x)
      = do x' <- reflect defs env x
           appCon defs (NS ["Reflect"] (UN "Db")) [x']
  reflect defs env WorldVal
      = getCon defs (NS ["Reflect"] (UN "WorldVal"))
  reflect defs env IntType
      = getCon defs (NS ["Reflect"] (UN "IntType"))
  reflect defs env IntegerType
      = getCon defs (NS ["Reflect"] (UN "IntegerType"))
  reflect defs env StringType
      = getCon defs (NS ["Reflect"] (UN "StringType"))
  reflect defs env CharType
      = getCon defs (NS ["Reflect"] (UN "CharType"))
  reflect defs env DoubleType
      = getCon defs (NS ["Reflect"] (UN "DoubleType"))
  reflect defs env WorldType
      = getCon defs (NS ["Reflect"] (UN "WorldType"))

export
Reify Visibility where
  reify defs (NDCon (NS ["Reflect"] (UN "Private")) _ _ [])
      = pure Private
  reify defs (NDCon (NS ["Reflect"] (UN "Export")) _ _ [])
      = pure Export
  reify defs (NDCon (NS ["Reflect"] (UN "Public")) _ _ [])
      = pure Public
  reify defs _ = Nothing

export
Reflect Visibility where
  reflect defs env Private = getCon defs (NS ["Reflect"] (UN "Private"))
  reflect defs env Export = getCon defs (NS ["Reflect"] (UN "Export"))
  reflect defs env Public = getCon defs (NS ["Reflect"] (UN "Public"))

