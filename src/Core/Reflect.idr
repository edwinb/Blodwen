module Core.Reflect

import Core.Context
import Core.Normalise
import Core.TT

%default covering

public export
interface Reflect a where
  reflect : Defs -> NF vars -> Maybe a

public export
interface Reify a where
  reify : Defs -> a -> Maybe ClosedTerm

export
getCon : Defs -> Name -> Maybe ClosedTerm
getCon defs n
    = case lookupDefExact n (gamma defs) of
           Just (DCon t a _) => pure (Ref (DataCon t a) n)
           Just (TCon t a _ _ _) => pure (Ref (TyCon t a) n)
           Just _ => pure (Ref Func n)
           _ => Nothing

export
appCon : Defs -> Name -> List ClosedTerm -> Maybe ClosedTerm
appCon defs n args
    = do fn <- getCon defs n
         pure (apply fn args)

export
Reflect () where
  reflect defs _ = pure ()

export
Reflect String where
  reflect defs (NPrimVal (Str str)) = pure str
  reflect defs _ = Nothing

export
Reify String where
  reify defs x = pure (PrimVal (Str x))

export
Reflect Int where
  reflect defs (NPrimVal (I i)) = pure i
  reflect defs _ = Nothing

export
Reify Int where
  reify defs x = pure (PrimVal (I x))

export
Reflect Integer where
  reflect defs (NPrimVal (BI i)) = pure i
  reflect defs _ = Nothing

export
Reify Integer where
  reify defs x = pure (PrimVal (BI x))

export
Reflect Char where
  reflect defs (NPrimVal (Ch i)) = pure i
  reflect defs _ = Nothing

export
Reify Char where
  reify defs x = pure (PrimVal (Ch x))

export
Reflect Double where
  reflect defs (NPrimVal (Db i)) = pure i
  reflect defs _ = Nothing

export
Reify Double where
  reify defs x = pure (PrimVal (Db x))

export
Reflect a => Reflect (List a) where
  reflect defs (NDCon (NS _ (UN "Nil")) _ _ _)
      = pure []
  reflect defs (NDCon (NS _ (UN "::")) _ _ [_, x, xs])
      = do x' <- reflect defs (evalClosure defs x)
           xs' <- reflect defs (evalClosure defs xs)
           pure (x' :: xs')
  reflect defs _ = Nothing

export
Reify a => Reify (List a) where
  reify defs [] = getCon defs (NS ["Stuff"] (UN "Nil"))
  reify defs (x :: xs)
      = do x' <- reify defs x
           xs' <- reify defs xs
           appCon defs (NS ["Stuff"] (UN "::")) [x', xs']

export
(Reflect a, Reflect b) => Reflect (a, b) where
  reflect defs (NDCon (NS _ (UN "MkPair")) _ _ [_, _, x, y])
      = do x' <- reflect defs (evalClosure defs x)
           y' <- reflect defs (evalClosure defs y)
           pure (x', y')
  reflect defs _ = Nothing

export
Reflect Name where
  reflect defs (NDCon (NS ["Reflect"] (UN "UN")) _ _ [str])
      = do str' <- reflect defs (evalClosure defs str)
           pure (UN str')
  reflect defs (NDCon (NS ["Reflect"] (UN "MN")) _ _ [str, i])
      = do str' <- reflect defs (evalClosure defs str)
           i' <- reflect defs (evalClosure defs i)
           pure (MN str' i')
  reflect defs (NDCon (NS ["Reflect"] (UN "NS")) _ _ [ns, n])
      = do ns' <- reflect defs (evalClosure defs ns)
           n' <- reflect defs (evalClosure defs n)
           pure (NS ns' n')
  reflect defs _ = Nothing

export
Reify Name where
  reify defs (UN x) 
      = do x' <- reify defs x
           appCon defs (NS ["Reflect"] (UN "UN")) [x']
  reify defs (MN x i) 
      = do x' <- reify defs x
           i' <- reify defs i
           appCon defs (NS ["Reflect"] (UN "MN")) [x', i']
  reify defs (NS ns n) 
      = do ns' <- reify defs ns
           n' <- reify defs n
           appCon defs (NS ["Reflect"] (UN "NS")) [ns', n']
  reify defs _ = Nothing

export
Reflect Constant where
  reflect defs (NDCon (NS ["Reflect"] (UN "I")) _ _ [x])
      = do x' <- reflect defs (evalClosure defs x)
           pure (I x')
  reflect defs (NDCon (NS ["Reflect"] (UN "BI")) _ _ [x])
      = do x' <- reflect defs (evalClosure defs x)
           pure (BI x')
  reflect defs (NDCon (NS ["Reflect"] (UN "Str")) _ _ [x])
      = do x' <- reflect defs (evalClosure defs x)
           pure (Str x')
  reflect defs (NDCon (NS ["Reflect"] (UN "Ch")) _ _ [x])
      = do x' <- reflect defs (evalClosure defs x)
           pure (Ch x')
  reflect defs (NDCon (NS ["Reflect"] (UN "Db")) _ _ [x])
      = do x' <- reflect defs (evalClosure defs x)
           pure (Db x')
  reflect defs (NDCon (NS ["Reflect"] (UN "IntType")) _ _ [])
      = pure IntType
  reflect defs (NDCon (NS ["Reflect"] (UN "IntegerType")) _ _ [])
      = pure IntegerType
  reflect defs (NDCon (NS ["Reflect"] (UN "StringType")) _ _ [])
      = pure StringType
  reflect defs (NDCon (NS ["Reflect"] (UN "CharType")) _ _ [])
      = pure CharType
  reflect defs (NDCon (NS ["Reflect"] (UN "DoubleType")) _ _ [])
      = pure DoubleType
  reflect defs _ = Nothing

export
Reify Constant where
  reify defs (I x)
      = do x' <- reify defs x
           appCon defs (NS ["Reflect"] (UN "I")) [x']
  reify defs (BI x)
      = do x' <- reify defs x
           appCon defs (NS ["Reflect"] (UN "BI")) [x']
  reify defs (Str x)
      = do x' <- reify defs x
           appCon defs (NS ["Reflect"] (UN "Str")) [x']
  reify defs (Ch x)
      = do x' <- reify defs x
           appCon defs (NS ["Reflect"] (UN "Ch")) [x']
  reify defs (Db x)
      = do x' <- reify defs x
           appCon defs (NS ["Reflect"] (UN "Db")) [x']
  reify defs IntType
      = getCon defs (NS ["Reflect"] (UN "IntType"))
  reify defs IntegerType
      = getCon defs (NS ["Reflect"] (UN "IntegerType"))
  reify defs StringType
      = getCon defs (NS ["Reflect"] (UN "StringType"))
  reify defs CharType
      = getCon defs (NS ["Reflect"] (UN "CharType"))
  reify defs DoubleType
      = getCon defs (NS ["Reflect"] (UN "DoubleType"))

export
Reflect Visibility where
  reflect defs (NDCon (NS ["Reflect"] (UN "Private")) _ _ [])
      = pure Private
  reflect defs (NDCon (NS ["Reflect"] (UN "Export")) _ _ [])
      = pure Export
  reflect defs (NDCon (NS ["Reflect"] (UN "Public")) _ _ [])
      = pure Public
  reflect defs _ = Nothing

export
Reify Visibility where
  reify defs Private = getCon defs (NS ["Reflect"] (UN "Private"))
  reify defs Export = getCon defs (NS ["Reflect"] (UN "Export"))
  reify defs Public = getCon defs (NS ["Reflect"] (UN "Public"))

