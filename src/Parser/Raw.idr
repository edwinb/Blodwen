module Parser.TT

import Core.TT

{- Parse raw TT as S-expressions

(foo a b c) -- application
(lam (x ty) scope)
(pi  (x ty) scope)
(pat (x ty) scope)
(let (x ty val) scope)

-}

