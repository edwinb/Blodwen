module Core.CaseTree

import Core.TT
import Data.List

%default total

mutual
  public export
  data CaseTree : List Name -> Type where
       Case : Elem var scope -> List (CaseAlt scope) -> CaseTree scope
       STerm : Term scope -> CaseTree scope
       Unmatched : (msg : String) -> CaseTree scope
       Impossible : CaseTree scope

  %name CaseTree sc

  public export
  data CaseAlt : List Name -> Type where
       ConCase : Name -> (tag : Int) -> (args : List Name) ->
                 CaseTree (args ++ scope) -> CaseAlt scope
       ConstCase : Constant -> CaseTree scope -> CaseAlt scope
       DefaultCase : CaseTree scope -> CaseAlt scope
  
  %name CaseAlt alt

  export
  embed : CaseTree args -> CaseTree (args ++ more)
  embed (Case x xs) = Case (elemExtend x) (map embedAlt xs)
  embed (STerm tm) = STerm (embed tm)
  embed (Unmatched msg) = Unmatched msg
  embed Impossible = Impossible

  embedAlt : CaseAlt args -> CaseAlt (args ++ more)
  embedAlt {args} {more} (ConCase n tag ns sc) 
       = ConCase n tag ns 
                 (rewrite (appendAssociative ns args more) in
                          (embed sc))
  embedAlt (ConstCase x sc) = ConstCase x (embed sc)
  embedAlt (DefaultCase sc) = DefaultCase (embed sc)

  export
  testPlus : Name -> CaseTree [UN "x", UN "y"]
  testPlus plus
      = Case Here
            [ConCase (UN "Z") 0 []
              (STerm (Local {x = UN "y"} (There Here))),
             ConCase (UN "S") 1 [UN "k"]
              (STerm (App (Ref (DataCon 1 1) (UN "S")) 
              (App (App (Ref Func plus) 
                    (Local {x = UN "k"} Here)) 
                    (Local {x = UN "y"} (There (There Here))))))
            ]

