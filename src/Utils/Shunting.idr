module Utils.Shunting

import Core.Core

%default total

-- The shunting yard algorithm turns a list of tokens with operators into
-- a parse tree expressing the precedence and associativity correctly.
-- We assume that brackets, functions etc are dealt with in a higher level
-- parser, so we're only dealing with operators here.

-- Precedences/associativities
public export
data OpPrec 
          = AssocL Nat
          | AssocR Nat
          | NonAssoc Nat
          | Prefix Nat

-- Tokens are either operators or already parsed expressions in some 
-- higher level language
public export
data Tok annot a = Op annot String OpPrec
                 | Expr a

-- The result of shunting is a parse tree with the precedences made explicit
-- in the tree.
-- NOTE: I have been wondering if I can use types to express that the
-- subtrees use lower precedence operators, but my attempts so far have
-- ended up with more complicated types than the function 'higher', below,
-- which is the one that compares precedences. So I've just used simple
-- types instead and will rely on tests. It would be interesting to see if
-- there's a better way though!

public export
data Tree annot a = Inf annot String (Tree annot a) (Tree annot a)
                  | Pre annot String (Tree annot a)
                  | Leaf a

export
Show a => Show (Tree annot a) where
  show (Inf _ op l r) = "(" ++ op ++ " " ++ show l ++ " " ++ show r ++ ")"
  show (Pre _ op l) = "(" ++ op ++ " " ++ show l ++ ")"
  show (Leaf val) = show val

Show OpPrec where
  show (AssocL p) = "infixl " ++ show p
  show (AssocR p) = "infixr " ++ show p
  show (NonAssoc p) = "infix " ++ show p
  show (Prefix p) = "prefix " ++ show p

export
Show a => Show (Tok annot a) where
  show (Op _ op p) = op ++ " " ++ show p
  show (Expr val) = show val

-- Label for the output queue state
data Out : Type where

output : List (Tree annot a) -> Tok annot a -> 
         Core annot (List (Tree annot a))
output [] (Op _ _ _) = throw (InternalError "Invalid input to shunting")
output (x :: stk) (Op loc str (Prefix _)) = pure $ Pre loc str x :: stk
output (x :: y :: stk) (Op loc str _) = pure $ Inf loc str y x :: stk
output stk (Expr a) = pure $ Leaf a :: stk
output _ _ = throw (InternalError "Invalid input to shunting")

emit : {auto o : Ref Out (List (Tree annot a))} -> 
       Tok annot a -> Core annot ()
emit t
    = do out <- get Out
         put Out !(output out t)

getPrec : OpPrec -> Nat
getPrec (AssocL k) = k
getPrec (AssocR k) = k
getPrec (NonAssoc k) = k
getPrec (Prefix k) = k

isLAssoc : OpPrec -> Bool
isLAssoc (AssocL _) = True
isLAssoc _ = False

-- Return whether the first operator should be applied before the second,
-- assuming 
higher : annot -> String -> OpPrec -> String -> OpPrec -> Core annot Bool
higher loc opx op opy (Prefix p) = pure False
higher loc opx (NonAssoc x) opy oy
    = if x == getPrec oy
         then throw (GenericMsg loc ("Operator '" ++ opx ++ 
                                     "' is non-associative"))
         else pure (x > getPrec oy)
higher loc opx ox opy (NonAssoc y)
    = if getPrec ox == y
         then throw (GenericMsg loc ("Operator '" ++ opy ++ 
                                     "' is non-associative"))
         else pure (getPrec ox > y)
higher loc opl l opr r 
    = pure $ (getPrec l > getPrec r) ||
             ((getPrec l == getPrec r) && isLAssoc l)

processStack : {auto o : Ref Out (List (Tree annot a))} ->
               List (annot, String, OpPrec) -> String -> OpPrec ->
               Core annot (List (annot, String, OpPrec))
processStack [] op prec = pure []
processStack ((loc, opx, sprec) :: xs) opy prec 
    = if !(higher loc opx sprec opy prec)
         then do emit (Op loc opx sprec)
                 processStack xs opy prec
         else pure ((loc, opx, sprec) :: xs)

shunt : {auto o : Ref Out (List (Tree annot a))} ->
        (opstk : List (annot, String, OpPrec)) -> 
        List (Tok annot a) -> Core annot (Tree annot a)
shunt stk (Expr x :: rest)
    = do emit (Expr x)
         shunt stk rest
shunt stk (Op loc op prec :: rest) 
    = do stk' <- processStack stk op prec
         shunt ((loc, op, prec) :: stk') rest
shunt {annot} stk [] 
    = do traverse (\s => emit (Op (sloc s) (sop s) (sprec s))) stk
         [out] <- get Out
             | out => throw (InternalError "Invalid input to shunting")
         pure out
  where
    sloc : (annot, b, c) -> annot
    sloc (x, y, z) = x
    sop : (annot, b, c) -> b
    sop (x, y, z) = y
    sprec : (annot, b, c) -> c
    sprec (x, y, z) = z
 
export
parseOps : List (Tok annot a) -> Core annot (Tree annot a)
parseOps toks 
    = do o <- newRef {t = List (Tree annot a)} Out []
         shunt [] toks

-- Some things to help with testing, not exported

pl : Tok () Int
pl = Op () "+" (AssocL 8)

tm : Tok () Int
tm = Op () "*" (AssocL 9)

neg : Tok () Int
neg = Op () "-" (Prefix 10)

cons : Tok () Int
cons = Op () ":" (NonAssoc 9)

num : Int -> Tok () Int
num = Expr 

testParse : Show a => List (Tok () a) -> IO ()
testParse toks = coreRun (parseOps toks) (\err => printLn err) printLn
