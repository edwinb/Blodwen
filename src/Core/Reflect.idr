module Core.Reflect

import Core.Context
import Core.Normalise
import Core.TT

public export
interface Reflect a where
  reflect : Defs -> NF vars -> Maybe a

public export
interface Reify a where
  reify : Defs -> a -> Maybe ClosedTerm

getCon : Name -> Defs -> Maybe ClosedTerm
getCon n defs
    = case lookupDefExact n (gamma defs) of
           Just (DCon t a _) => pure (Ref (DataCon t a) n)
           Just (TCon t a _ _ _) => pure (Ref (TyCon t a) n)
           Just _ => pure (Ref Func n)
           _ => Nothing

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
  reify defs [] = getCon (NS ["Stuff"] (UN "Nil")) defs
  reify defs (x :: xs)
      = do x' <- reify defs x
           xs' <- reify defs xs
           pure (App (App !(getCon (NS ["Stuff"] (UN "::")) defs) x') xs')

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
           pure (App !(getCon (NS ["Reflect"] (UN "UN")) defs) x')
  reify defs (MN x i) 
      = do x' <- reify defs x
           i' <- reify defs i
           pure (App (App !(getCon (NS ["Reflect"] (UN "MN")) defs) x') i')
  reify defs (NS ns n) 
      = do ns' <- reify defs ns
           n' <- reify defs n
           pure (App (App !(getCon (NS ["Reflect"] (UN "NS")) defs) ns') n')
  reify defs _ = Nothing

