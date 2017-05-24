module Parser.Combinators

import public Parser.Grammar

%default total

export
some : Grammar tok True a -> 
       Grammar tok True (List a)
some p = do x <- p
            (do xs <- some p
                pure (x :: xs)) <|> pure [x]

export
many : Grammar tok True a -> 
       Grammar tok False (List a)
many p = some p
     <|> pure []

export
sepBy1 : Grammar tok True () -> Grammar tok True a -> 
         Grammar tok True (List a)
sepBy1 sep p = do x <- p
                  (do sep
                      xs <- sepBy1 sep p
                      pure (x :: xs)) <|> pure [x]

export
sepBy : Grammar tok True () -> Grammar tok True a -> 
        Grammar tok False (List a)
sepBy sep p = sepBy1 sep p <|> pure []

export
optional : Grammar tok True a -> (ifNothing : a) ->
           Grammar tok False a
optional p def = p <|> pure def

