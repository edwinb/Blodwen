module Core.Typecheck

import Core.TT
import Core.Context
import Core.Evaluate

%default total

data Error = ItWentWrong

-- Given a global context (Gamma) 
check : Gamma -> Env scope -> Raw -> Either Error (Term scope)
