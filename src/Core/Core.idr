module Core.Core

import Core.TT
import Core.CaseTree
import Parser.Support

import public Control.Catchable
import public Data.IORef

%default total

public export
data TTCErrorMsg
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
    = Fatal (Error annot) -- flag as unrecoverable (so don't postpone awaiting further info)
    | CantConvert annot (Env Term vars) (Term vars) (Term vars)
    | CantSolveEq annot (Env Term vars) (Term vars) (Term vars)
    | Cycle annot (Env Term vars) (Term vars) (Term vars)
    | WhenUnifying annot (Env Term vars) (Term vars) (Term vars) (Error annot)
    | ValidCase annot (Env Term vars) (Either (Term vars) (Error annot))
    | UndefinedName annot Name
    | InvisibleName annot Name
    | BadTypeConType annot Name 
    | BadDataConType annot Name Name
    | NotCovering annot Name Covering
    | NotTotal annot Name PartialReason
    | LinearUsed annot Nat Name
    | LinearMisuse annot Name RigCount RigCount
    | BorrowPartial annot (Env Term vars) (Term vars) (Term vars)
    | BorrowPartialType annot (Env Term vars) (Term vars)
    | AmbiguousName annot (List Name)
    | AmbiguousElab annot (Env Term vars) (List (Term vars))
    | AmbiguousSearch annot (Env Term vars) (List (Term vars))
    | AllFailed (List (Maybe Name, Error annot))
    | RecordTypeNeeded annot (Env Term vars)
    | NotRecordField annot String (Maybe Name)
    | NotRecordType annot Name
    | IncompatibleFieldUpdate annot (List String)
    | InvalidImplicit annot (Env Term vars) Name (Term vars)
    | CantSolveGoal annot (Term [])
    | DeterminingArg annot Name (Env Term vars) (Term vars)
    | UnsolvedHoles (List (annot, Name))
    | CantInferArgType annot (Env Term vars) Name Name (Term vars)
    | SolvedNamedHole annot (Env Term vars) Name (Term vars)
    | VisibilityError annot Visibility Name Visibility Name
    | NonLinearPattern annot Name
    | BadPattern annot Name
    | NoDeclaration annot Name
    | AlreadyDefined annot Name
    | NotFunctionType annot (Env Term vars) (Term vars)
    | RewriteNoChange annot (Env Term vars) (Term vars) (Term vars)
    | NotRewriteRule annot (Env Term vars) (Term vars)
    | CaseCompile annot Name CaseError 
    | BadDotPattern annot (Env Term vars) String (Term vars) (Term vars)
    | BadImplicit annot String
    | BadRunElab annot (Env Term vars) (Term vars)
    | GenericMsg annot String
    | TTCError TTCErrorMsg
    | FileErr String FileError
    | ParseFail annot ParseError
    | ModuleNotFound annot (List String)
    | CyclicImports (List (List String))
    | ForceNeeded
    | InternalError String

    | InType annot Name (Error annot)
    | InCon annot Name (Error annot)
    | InLHS annot Name (Error annot)
    | InRHS annot Name (Error annot)

export
Show TTCErrorMsg where
  show FormatOlder = "TTC data is in an older format"
  show FormatNewer = "TTC data is in a newer format"
  show (EndOfBuffer when) = "End of buffer when reading " ++ when
  show (Corrupt ty) = "Corrupt TTC data for " ++ ty

-- Simplest possible display - higher level languages should unelaborate names
-- and display annotations appropriately
export
Show annot => Show (Error annot) where
  show (Fatal err) = show err
  show (CantConvert fc env x y) 
      = show fc ++ ":Type mismatch: " ++ show x ++ " and " ++ show y
  show (CantSolveEq fc env x y) 
      = show fc ++ ":" ++ show x ++ " and " ++ show y ++ " are not equal"
  show (Cycle fc env x y) 
      = show fc ++ ":Occurs check failed: " ++ show x ++ " and " ++ show y
  show (WhenUnifying fc _ x y err)
      = show fc ++ ":When unifying: " ++ show x ++ " and " ++ show y ++ "\n\t" ++ show err
  show (ValidCase fc _ prob)
      = show fc ++ ":" ++ 
           case prob of
             Left tm => assert_total (show tm) ++ " is not a valid impossible pattern because it typechecks"
             Right err => "Not a valid impossible pattern:\n\t" ++ assert_total (show err)
  show (UndefinedName fc x) = show fc ++ ":Undefined name " ++ show x
  show (InvisibleName fc (NS ns x)) 
       = show fc ++ ":Name " ++ show x ++ " is inaccessible since " ++
         showSep "." (reverse ns) ++ " is not explicitly imported"
  show (InvisibleName fc x) = show fc ++ ":Name " ++ show x ++ " is inaccessible"
  show (BadTypeConType fc n) 
       = show fc ++ ":Return type of " ++ show n ++ " must be Type"
  show (BadDataConType fc n fam) 
       = show fc ++ ":Return type of " ++ show n ++ " must be in " ++ show fam
  show (NotCovering fc n cov)
       = show fc ++ ":" ++ show n ++ " is not covering:\n\t" ++
            case cov of
                 IsCovering => "Oh yes it is (Internal error!)"
                 MissingCases cs => "Missing cases:\n\t" ++
                                           showSep "\n\t" (map show cs)
                 NonCoveringCall ns => "Calls non covering function" 
                                           ++ (case ns of
                                                   [fn] => " " ++ show fn
                                                   _ => "s: " ++ showSep ", " (map show ns))

  show (NotTotal fc n r)
       = show fc ++ ":" ++ show n ++ " is not total"
  show (LinearUsed fc count n)
      = show fc ++ ":There are " ++ show count ++ " uses of linear name " ++ show n
  show (LinearMisuse fc n exp ctx)
      = show fc ++ ":Trying to use " ++ showRig exp ++ " name " ++ show n ++
                   " in " ++ showRel ctx ++ " context"
     where
       showRig : RigCount -> String
       showRig Rig0 = "irrelevant"
       showRig (Rig1 False) = "linear"
       showRig (Rig1 True) = "borrowed"
       showRig RigW = "unrestricted"

       showRel : RigCount -> String
       showRel Rig0 = "irrelevant"
       showRel (Rig1 False) = "relevant"
       showRel (Rig1 True) = "borrowed"
       showRel RigW = "non-linear"
  show (BorrowPartial fc env t arg)
      = show fc ++ ":" ++ show t ++ " borrows argument " ++ show arg ++ 
                   " so must be fully applied"
  show (BorrowPartialType fc env t)
      = show fc ++ ":" ++ show t ++ " borrows, so must return a concrete type"

  show (AmbiguousName fc ns) = show fc ++ ":Ambiguous name " ++ show ns
  show (AmbiguousElab fc env ts) = show fc ++ ":Ambiguous elaboration " ++ show ts
  show (AmbiguousSearch fc env ts) = show fc ++ ":Ambiguous search " ++ show ts
  show (AllFailed ts) = "No successful elaboration: " ++ assert_total (show ts)
  show (RecordTypeNeeded fc env)
      = show fc ++ ":Can't infer type of record to update"
  show (NotRecordField fc fld Nothing)
      = show fc ++ ":" ++ fld ++ " is not part of a record type"
  show (NotRecordField fc fld (Just ty)) 
      = show fc ++ ":Record type " ++ show ty ++ " has no field " ++ fld 
  show (NotRecordType fc ty)
      = show fc ++ ":" ++ show ty ++ " is not a record type"
  show (IncompatibleFieldUpdate fc flds) 
      = show fc ++ ":Field update " ++ showSep "->" flds ++ " not compatible with other updates" 
  show (InvalidImplicit fc env n tm) = show fc ++ ":" ++ show n ++ " is not a valid implicit argument in " ++ show tm 
  show (CantSolveGoal fc g) = show fc ++ ":Can't solve goal " ++ assert_total (show g)
  show (DeterminingArg fc n env g)
      = show fc ++ ":Can't solve goal " ++ assert_total (show g) ++ 
                " since argument " ++ show n ++ " can't be inferred"
  show (UnsolvedHoles hs) = "Unsolved holes " ++ show hs
  show (CantInferArgType fc env n h ty)
      = show fc ++ ":Can't infer type for " ++ show n ++
                   " (got " ++ show ty ++ " with hole " ++ show h ++ ")"
  show (SolvedNamedHole fc _ h _) = show fc ++ ":Named hole " ++ show h ++ " is solved by unification"
  show (VisibilityError fc vx x vy y)
      = show fc ++ ":" ++ show vx ++ " " ++ show x ++ " cannot refer to "
                       ++ show vy ++ " " ++ show y
  show (NonLinearPattern fc n) = show fc ++ ":Non linear pattern variable " ++ show n
  show (BadPattern fc n) = show fc ++ ":Pattern not allowed here: " ++ show n
  show (NoDeclaration fc x) = show fc ++ ":No type declaration for " ++ show x
  show (AlreadyDefined fc x) = show fc ++ ":" ++ show x ++ " is already defined"
  show (NotFunctionType fc env tm) = show fc ++ ":Not a function type: " ++ show tm
  show (RewriteNoChange fc env rule ty)
      = show fc ++ ":Rewriting by " ++ show rule ++ " did not change type " ++ show ty
  show (NotRewriteRule fc env rule)
      = show fc ++ ":" ++ show rule ++ " is not a rewrite rule type"
  show (CaseCompile fc n DifferingArgNumbers) 
      = show fc ++ ":Patterns for " ++ show n ++ " have different numbers of arguments"
  show (CaseCompile fc n DifferingTypes) 
      = show fc ++ ":Patterns for " ++ show n ++ " require matching on different types"
  show (CaseCompile fc n UnknownType) 
      = show fc ++ ":Can't infer type to match in " ++ show n
  show (CaseCompile fc n (MatchErased (_ ** (env, tm))))
      = show fc ++ ":Attempt to match on erased argument " ++ show tm ++ 
                   " in " ++ show n
  show (BadDotPattern fc env reason x y)
      = show fc ++ ":Can't match on " ++ show x ++ 
           (if reason /= "" then " (" ++ reason ++ ")" else "") ++
           " - it elaborates to " ++ show y
  show (BadImplicit fc str) = show fc ++ ":" ++ str ++ " can't be bound here"
  show (BadRunElab fc env script) = show fc ++ ":Bad elaborator script " ++ show script
  show (GenericMsg fc str) = show fc ++ ":" ++ str
  show (TTCError msg) = "Error in TTC file: " ++ show msg
  show (FileErr fname err) = "File error (" ++ fname ++ "): " ++ show err
  show (ParseFail fc err) = "Parse error (" ++ show err ++ ")"
  show (ModuleNotFound fc ns) 
      = show fc ++ ":" ++ showSep "." (reverse ns) ++ " not found"
  show (CyclicImports ns)
      = "Module imports form a cycle: " ++ showSep " -> " (map showMod ns)
    where
      showMod : List String -> String
      showMod ns = showSep "." (reverse ns)
  show ForceNeeded = "Internal error when resolving implicit laziness"
  show (InternalError str) = "INTERNAL ERROR: " ++ str

  show (InType fc n err)
       = show fc ++ ":When elaborating type of " ++ show n ++ ":\n" ++
         show err
  show (InCon fc n err)
       = show fc ++ ":When elaborating type of constructor " ++ show n ++ ":\n" ++
         show err
  show (InLHS fc n err)
       = show fc ++ ":When elaborating left hand side of " ++ show n ++ ":\n" ++
         show err
  show (InRHS fc n err)
       = show fc ++ ":When elaborating right hand side of " ++ show n ++ ":\n" ++
         show err

export
getAnnot : Error annot -> Maybe annot
getAnnot (Fatal err) = getAnnot err
getAnnot (CantConvert loc env tm y) = Just loc
getAnnot (CantSolveEq loc env tm y) = Just loc
getAnnot (Cycle loc env tm y) = Just loc
getAnnot (WhenUnifying loc env tm y z) = Just loc
getAnnot (ValidCase loc env y) = Just loc
getAnnot (UndefinedName loc y) = Just loc
getAnnot (InvisibleName loc y) = Just loc
getAnnot (BadTypeConType loc y) = Just loc
getAnnot (BadDataConType loc y z) = Just loc
getAnnot (NotCovering loc _ _) = Just loc
getAnnot (NotTotal loc _ _) = Just loc
getAnnot (LinearUsed loc k y) = Just loc
getAnnot (LinearMisuse loc y z w) = Just loc
getAnnot (BorrowPartial loc _ _ _) = Just loc
getAnnot (BorrowPartialType loc _ _) = Just loc
getAnnot (AmbiguousName loc xs) = Just loc
getAnnot (AmbiguousElab loc _ xs) = Just loc
getAnnot (AmbiguousSearch loc _ xs) = Just loc
getAnnot (AllFailed ((_, x) :: xs)) = getAnnot x
getAnnot (AllFailed []) = Nothing
getAnnot (RecordTypeNeeded loc _) = Just loc
getAnnot (NotRecordField loc _ _) = Just loc
getAnnot (NotRecordType loc _) = Just loc
getAnnot (IncompatibleFieldUpdate loc _) = Just loc
getAnnot (InvalidImplicit loc _ y tm) = Just loc
getAnnot (CantSolveGoal loc tm) = Just loc
getAnnot (DeterminingArg loc y env tm) = Just loc
getAnnot (UnsolvedHoles ((loc, _) :: xs)) = Just loc
getAnnot (UnsolvedHoles []) = Nothing
getAnnot (CantInferArgType loc _ y z tm) = Just loc
getAnnot (SolvedNamedHole loc _ _ y) = Just loc
getAnnot (VisibilityError loc y z w s) = Just loc
getAnnot (NonLinearPattern loc y) = Just loc
getAnnot (BadPattern loc y) = Just loc
getAnnot (NoDeclaration loc y) = Just loc
getAnnot (AlreadyDefined loc y) = Just loc
getAnnot (NotFunctionType loc _ tm) = Just loc
getAnnot (RewriteNoChange loc _ tm ty) = Just loc
getAnnot (NotRewriteRule loc _ ty) = Just loc
getAnnot (CaseCompile loc y z) = Just loc
getAnnot (BadDotPattern loc _ y tm z) = Just loc
getAnnot (BadImplicit loc y) = Just loc
getAnnot (BadRunElab loc _ tm) = Just loc
getAnnot (GenericMsg loc y) = Just loc
getAnnot (TTCError x) = Nothing
getAnnot (FileErr x y) = Nothing
getAnnot (ParseFail loc x) = Just loc
getAnnot (ModuleNotFound loc xs) = Just loc
getAnnot (CyclicImports xs) = Nothing
getAnnot ForceNeeded = Nothing
getAnnot (InternalError x) = Nothing
getAnnot (InType x y err) = getAnnot err
getAnnot (InCon x y err) = getAnnot err
getAnnot (InLHS x y err) = getAnnot err
getAnnot (InRHS x y err) = getAnnot err

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

export
wrapError : (Error annot -> Error annot) -> Core annot a -> Core annot a
wrapError fe (MkCore prog)
    = MkCore $ prog >>=
         (\x => case x of
                     Left err => pure (Left (fe err))
                     Right val => pure (Right val))

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
traverse' : (a -> Core annot b) -> List a -> List b -> Core annot (List b)
traverse' f [] acc = pure (reverse acc)
traverse' f (x :: xs) acc 
    = traverse' f xs (!(f x) :: acc) 

export
traverse : (a -> Core annot b) -> List a -> Core annot (List b)
traverse f xs = traverse' f xs []

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

export
cond : List (Lazy Bool, Lazy a) -> a -> a
cond [] def = def
cond ((x, y) :: xs) def = if x then y else cond xs def

