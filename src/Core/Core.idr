module Core.Core

import Core.TT
import Core.CaseTree

import public Data.IORef
import public Control.Catchable

public export
data TTIErrorMsg
    = FormatOlder
    | FormatNewer
    | EndOfBuffer String
    | Corrupt String

-- All possible errors
-- 'annot' is an annotation provided by the thing which called the
-- function which had an error; it's intended to provide any useful information
-- a high level language might need, e.g. file/line number
public export
data Error annot
    = CantConvert annot (Env Term vars) (Term vars) (Term vars)
    | Cycle annot (Env Term vars) (Term vars) (Term vars)
    | WhenUnifying annot (Env Term vars) (Term vars) (Term vars) (Error annot)
    | ValidCase annot (Env Term vars) (Either (Term vars) (Error annot))
    | UndefinedName annot Name
    | AmbiguousName annot (List Name)
    | AmbiguousElab annot (List (Term vars))
    | AllFailed (List (Error annot))
    | InvalidImplicit annot Name (Term vars)
    | CantSolveGoal annot (Env Term vars) (Term vars)
    | NoDeclaration annot Name
    | AlreadyDefined annot Name
    | NotFunctionType annot (Term vars)
    | CaseCompile annot Name CaseError 
    | BadDotPattern annot (Term vars) (Term vars)
    | BadImplicit annot String
    | GenericMsg annot String
    | TTIError TTIErrorMsg
    | InternalError String

export
Show TTIErrorMsg where
  show FormatOlder = "TTI data is in an older format"
  show FormatNewer = "TTI data is in a newer format"
  show (EndOfBuffer when) = "End of buffer when reading " ++ when
  show (Corrupt ty) = "Corrupt TTI data for " ++ ty

-- Simplest possible display - higher level languages should unelaborate names
-- and display annotations appropriately
export
Show (Error annot) where
  show (CantConvert _ env x y) 
      = "Type mismatch: " ++ show x ++ " and " ++ show y
  show (Cycle _ env x y) 
      = "Occurs check failed: " ++ show x ++ " and " ++ show y
  show (WhenUnifying _ _ x y err)
      = "When unifying: " ++ show x ++ " and " ++ show y ++ "\n\t" ++ show err
  show (ValidCase _ _ prob)
      = case prob of
             Left tm => assert_total (show tm) ++ " is not a valid impossible pattern because it typechecks"
             Right err => "Not a valid impossible pattern:\n\t" ++ assert_total (show err)
  show (UndefinedName _ x) = "Undefined name " ++ show x
  show (AmbiguousName _ ns) = "Ambiguous name " ++ show ns
  show (AmbiguousElab _ ts) = "Ambiguous elaboration " ++ show ts
  show (AllFailed ts) = "No successful elaboration: " ++ assert_total (show ts)
  show (InvalidImplicit _ n tm) = show n ++ " is not a valid implicit argument in " ++ show tm
  show (CantSolveGoal _ env g) = "Can't solve goal " ++ assert_total (show g)
  show (NoDeclaration _ x) = "No type declaration for " ++ show x
  show (AlreadyDefined _ x) = show x ++ " is already defined"
  show (NotFunctionType _ tm) = "Not a function type: " ++ show tm
  show (CaseCompile _ n DifferingArgNumbers) 
      = "Patterns for " ++ show n ++ " have different numbers of arguments"
  show (BadDotPattern _ x y)
      = "Can't match on " ++ show x
  show (BadImplicit _ str) = str ++ " can't be bound here"
  show (GenericMsg _ str) = str
  show (TTIError str) = "File error: " ++ show str
  show (InternalError str) = "INTERNAL ERROR: " ++ str

export
error : Error annot -> Either (Error annot) a
error = Left

export
record Core annot t where
  constructor MkCore
  runCore : IO (Either (Error annot) t)

export
coreRun : Core annot a -> 
          (Error annot -> IO b) -> (a -> IO b) -> IO b
coreRun (MkCore act) err ok = either err ok !act

export
coreFail : Error annot -> Core annot a
coreFail e = MkCore $ pure (Left e)

-- This would be better if we restrict it to a limited set of IO operations
export
%inline
coreLift : IO a -> Core annot a
coreLift op = MkCore $ map Right op

{- Monad, Applicative, Traversable are specialised by hand for Core.
In theory, this shouldn't be necessary, but it turns out that Idris 1 doesn't
specialise interfaces under 'case' expressions, and this has a significant
impact on both compile time and run time. 

Of course it would be a good idea to fix this in Idris, but it's not an urgent
thing on the road to self hosting, and we can make sure this isn't a problem
in the next version (i.e., in this project...)! -}

-- Monad (specialised)
export %inline
(>>=) : Core annot a -> (a -> Core annot b) -> Core annot b
(>>=) (MkCore act) f 
    = MkCore $ act >>= 
         (\x => case x of
                     Left err => pure (Left err)
                     Right val => runCore (f val))

-- Applicative (specialised)
export %inline
pure : a -> Core annot a
pure x = MkCore (pure (pure x))

export
(<*>) : Core annot (a -> b) -> Core annot a -> Core annot b
(<*>) (MkCore f) (MkCore a) = MkCore [| f <*> a |]

export %inline
when : Bool -> Lazy (Core annot ()) -> Core annot ()
when True f = f
when False f = pure ()

export
Catchable (Core annot) (Error annot) where
  catch (MkCore prog) h 
      = MkCore (do p' <- prog
                   case p' of
                        Left e => let MkCore he = h e in he
                        Right val => pure (Right val))
  throw = coreFail

-- Traversable (specialised)
export
traverse : (a -> Core annot b) -> List a -> Core annot (List b)
traverse f [] = pure []
traverse f (x :: xs) = pure $ !(f x) :: !(traverse f xs)

export
data Ref : label -> Type -> Type where
	   MkRef : IORef a -> Ref x a

export
newRef : (x : label) -> t -> Core annot (Ref x t)
newRef x val 
    = do ref <- coreLift (newIORef val)
         pure (MkRef ref)

export %inline 
get : (x : label) -> {auto ref : Ref x a} -> Core annot a
get x {ref = MkRef io} = coreLift (readIORef io)

export %inline
put : (x : label) -> {auto ref : Ref x a} -> a -> Core annot ()
put x {ref = MkRef io} val = coreLift (writeIORef io val)


