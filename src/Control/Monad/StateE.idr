-- Like Control.ST, but much simpler in that it only handles non-dependent
-- states and non-dependent transitions, but slightly more flexible in that
-- it can throw and catch exceptions (and rethrow with different error
-- types).
module Control.Monad.StateE

import public Control.Catchable
import public Control.IOExcept

%default total

infix 5 :::

public export
data Resource : Type where
     (:::) : label -> Type -> Resource

public export
data StateInfo : Type where
     Nil : StateInfo
     (::) : Resource -> StateInfo -> StateInfo

public export
data Available : lbl -> StateInfo -> Type -> Type where
     Here : Available l ((l ::: ty) :: ss) ty
     There : Available l ss ty -> Available l (s :: ss) ty

namespace Vals
  public export
  data Vals : StateInfo -> Type where
       Nil : Vals []
       (::) : a -> Vals xs -> Vals ((ty ::: a) :: xs)

lookup : Available l ss ty -> Vals ss -> ty
lookup Here (x :: xs) = x
lookup (There p) (x :: xs) = lookup p xs

public export
updateTy : (ss : StateInfo) -> (p : Available l ss ty) -> Type -> StateInfo
updateTy ((l ::: ty) :: ss) Here newty = ((l ::: newty) :: ss)
updateTy (s :: ss) (There p) newty = s :: updateTy ss p newty

public export
updateM : (p : Available l ss ty) -> Vals ss -> ty' -> Vals (updateTy ss p ty')
updateM Here (x :: xs) new = new :: xs
updateM (There p) (x :: xs) new = x :: updateM p xs new

public export
update : (p : Available l ss ty) -> Vals ss -> ty -> Vals ss
update Here (x :: xs) new = new :: xs
update (There p) (x :: xs) new = x :: update p xs new

public export
drop : (ss : StateInfo) -> (prf : Available l ss ty) -> StateInfo
drop ((lbl ::: st) :: ss) Here = ss
drop (s :: ss) (There p) = s :: drop ss p

dropVal : (prf : Available l ss ty) -> Vals ss -> Vals (drop ss prf)
dropVal Here (x :: xs) = xs
dropVal (There p) (x :: xs) = x :: dropVal p xs

export
data StatesE : (statesIn : StateInfo) -> (statesOut : StateInfo) ->
               (err : Type) ->
               (m : Type -> Type) -> (a : Type) -> Type where
  STE : {m : Type -> Type} ->
        (Vals statesIn -> m (a, Vals statesOut)) -> 
        StatesE statesIn statesOut err m a

public export
SE : StateInfo -> Type -> (m : Type -> Type) -> Type -> Type
SE s ty m = StatesE s s ty m

bind : Monad m =>
       StatesE s1 s2 err m a ->
       (a -> StatesE s2 s3 err m b) ->
       StatesE s1 s3 err m b
bind (STE f) k 
    = STE (\vals => 
              do (v, vals') <- f vals
                 let STE kv = k v
                 kv vals')

namespace StateEBind
  export
  (>>=) : Monad m => StatesE s1 s2 err m a ->
										 (a -> StatesE s2 s3 err m b) ->
										 StatesE s1 s3 err m b
  (>>=) = bind

export
Functor f => Functor (StatesE s s err f) where
  map f (STE g) = STE (\vals => map (mapFst f) (g vals))
    where
      mapFst : (a -> x) -> (a, c) -> (x, c)
      mapFst fn (a, c) = (fn a, c)

export
Monad f => Applicative (StatesE s s err f) where
  pure x = STE (\vals => pure (x, vals))

  (STE f) <*> (STE a) 
      = STE (\vals =>
                 do (g, vals') <- f vals
                    (b, vals'') <- a vals'
                    pure (g b, vals''))

export
Monad m => Monad (StatesE s s err m) where
  (>>=) = bind

public export
data ElemStates : Resource -> StateInfo -> Type where
     HereStates : ElemStates a (a :: as)
     ThereStates : ElemStates a as -> ElemStates a (b :: as)

public export
Uninhabited (ElemStates x []) where
  uninhabited HereStates impossible
  uninhabited (ThereStates _) impossible

valElem : ElemStates x xs -> Vals xs -> Vals [x]
valElem HereStates (x :: xs) = [x]
valElem (ThereStates p) (x :: xs) = valElem p xs

public export %error_reduce
dropEl : (ys: _) -> ElemStates x ys -> StateInfo
dropEl (x :: as) HereStates = as
dropEl (x :: as) (ThereStates p) = x :: dropEl as p

dropDups : Vals xs -> (el : ElemStates x xs) -> Vals (dropEl xs el)
dropDups (y :: ys) HereStates = ys
dropDups (y :: ys) (ThereStates p) = y :: dropDups ys p

public export
data SubStates : StateInfo -> StateInfo -> Type where
     SubNil : SubStates [] []
     Skip : SubStates xs ys -> SubStates xs (y :: ys)
     InStates : (el : ElemStates x ys) -> SubStates xs (dropEl ys el) ->
                SubStates (x :: xs) ys

public export
updateWith : (new : StateInfo) -> (xs : StateInfo) ->
             SubStates ys xs -> StateInfo
-- At the end, add the ones which were updated by the subctxt
updateWith new [] SubNil = new
updateWith new [] (InStates el z) = absurd el
-- Don't add the ones which were consumed by the subctxt
updateWith [] (x :: xs) (InStates el p)
    = updateWith [] (dropEl _ el) p
-- A new item corresponding to an existing thing
updateWith (n :: ns) (x :: xs) (InStates el p)
    = n :: updateWith ns (dropEl _ el) p
updateWith new (x :: xs) (Skip p) = x :: updateWith new xs p

dropVals : Vals ys -> SubStates xs ys -> Vals xs
dropVals [] SubNil = []
dropVals [] (InStates idx rest) = absurd idx
dropVals (x :: xs) (InStates idx rest)
    = let [e] = valElem idx (x :: xs) in
          e :: dropVals (dropDups (x :: xs) idx) rest
dropVals (x :: xs) (Skip p) = dropVals xs p

rebuildVals : Vals new -> Vals old -> (prf : SubStates sub old) ->
              Vals (updateWith new old prf)
rebuildVals new [] SubNil = new
rebuildVals new [] (InStates el p) = absurd el
rebuildVals [] (x :: xs) (InStates el p)
    = rebuildVals [] (dropDups (x :: xs) el) p
rebuildVals (e :: es) (x :: xs) (InStates el p)
    = e :: rebuildVals es (dropDups (x :: xs) el) p
rebuildVals new (x :: xs) (Skip p) = x :: rebuildVals new xs p

export
call : Monad m =>
       StatesE sub new err m a ->
       {auto st_prf : SubStates sub old} ->
       StatesE old (updateWith new old st_prf) err m a
call (STE f) {st_prf}
    = STE (\vals =>
              do let vals' = dropVals vals st_prf
                 (res, vals'') <- f vals'
                 pure (res, rebuildVals vals'' vals st_prf))

export
implicit
imp_call : Monad m =>
       StatesE sub new err m a ->
       {auto st_prf : SubStates sub old} ->
       StatesE old (updateWith new old st_prf) err m a
imp_call = call

export
throw : Catchable m err => err -> StatesE s s err m b
throw e = STE (\vals => throw e)

export
catch : Catchable m err =>
        StatesE s s err m a -> (err -> StatesE s s err m a ) ->
        StatesE s s err m a
catch (STE prog) f 
    = STE (\vals => catch (prog vals) 
                          (\e => let STE resp = f e in resp vals))

export
get : Applicative m =>
      (l : lbl) -> {auto prf : Available l s ty} ->
      StatesE s s err m ty
get l {prf} = STE (\vals => pure (lookup prf vals, vals))

export
putM : Applicative m =>
      (l : lbl) -> (new : ty') -> {auto prf : Available l s ty} ->
      StatesE s (updateTy s prf ty') err m ()
putM l {prf} new = STE (\vals => pure ((), updateM prf vals new))

export
put : Applicative m =>
     (l : lbl) -> (new : ty) -> {auto prf : Available l s ty} ->
     StatesE s s err m ()
put l {prf} new = STE (\vals => pure ((), update prf vals new))

export
new : Applicative m =>
      (l : lbl) -> (val : ty) ->
      StatesE s ((l ::: ty) :: s) err m ()
new l val = STE (\vals => pure ((), val :: vals))

export
delete : Applicative m =>
         (l : lbl) -> {auto prf : Available l s ty} ->
         StatesE s (drop s prf) err m ()
delete l {prf} = STE (\vals => pure ((), dropVal prf vals))

export
lift : Monad m => m a -> StatesE s s err m a
lift prog 
    = STE (\vals => 
             do res <- prog
                pure (res, vals))

public export
interface ConsoleIO (m : Type -> Type) where
  putStr : String -> SE s err m ()
  getStr : SE s err m String

  putChar : Char -> SE s err m ()
  getChar : SE s err m Char

export 
ConsoleIO IO where
  putStr = lift . putStr
  getStr = lift getLine
  putChar = lift . putChar
  getChar = lift getChar

export 
ConsoleIO (IOExcept err) where
  putStr str = lift (ioe_lift (putStr str))
  getStr = lift (ioe_lift getLine)
  putChar c = lift (ioe_lift (putChar c))
  getChar = lift (ioe_lift getChar)

export
putStrLn : ConsoleIO m => String -> SE ss err m ()
putStrLn str = putStr (str ++ "\n")

export
print : (ConsoleIO m, Show a) => a -> SE ss err m ()
print a = putStr $ show a

export
printLn : (ConsoleIO m, Show a) => a -> SE ss err m ()
printLn a = putStrLn $ show a

export
runSTE : StatesE s s' err m a -> Vals s -> m (a, Vals s')
runSTE (STE prog) vals = prog vals

