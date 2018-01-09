module Parser.REPL

import Core.TT
import Core.RawContext
import TTImp.TTImp
import Parser.RawImp

import public Parser.Support
import public Text.Parser
import Data.List.Views

%default covering

export
command : Rule (ImpREPL ())
command
    = do symbol ":"; exactIdent "t"
         tm <- expr init
         pure (Check tm)
  <|> do symbol ":"; exactIdent "s"
         n <- name
         pure (ProofSearch n)
  <|> do symbol ":"; exactIdent "di"
         n <- name
         pure (DebugInfo n)
  <|> do symbol ":"; exactIdent "q"
         pure Quit
  <|> do tm <- expr init
         pure (Eval tm)
