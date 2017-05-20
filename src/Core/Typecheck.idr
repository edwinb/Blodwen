module Core.Typecheck

import Core.TT
import Core.Context
import Core.Evaluate

import Data.List

%default covering

-- All possible errors (not only typechecking errors)
public export
data Error = CantConvert (Env Term scope) (Value scope) (Value scope)
           | Msg String

export
error : Error -> Either Error a
error = Left

export
doConvert : Gamma -> Env Term outer -> 
          Value outer -> Value outer -> Either Error ()
doConvert gam env x y 
    = if convert gam env x y 
         then pure ()
         else error (CantConvert env x y)

-- Given a global context (Gamma) 
check : Gamma -> Env Term scope -> Raw -> Either Error (Term scope)
