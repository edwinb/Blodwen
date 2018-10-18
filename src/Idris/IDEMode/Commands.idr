module Idris.IDEMode.Commands

import Core.Core
import Core.Name

%default covering

public export
data SExp = SExpList (List SExp)
          | StringAtom String
          | BoolAtom Bool
          | IntegerAtom Integer
          | SymbolAtom String

public export
data IDECommand
     = Interpret String
     | LoadFile String (Maybe Integer)
     | TypeOf String (Maybe (Integer, Integer))
     | CaseSplit Integer Integer String
     | AddClause Integer String
     | ExprSearch Integer String (List String) Bool
    
readHints : List SExp -> Maybe (List String)
readHints [] = Just []
readHints (StringAtom s :: rest)
    = do rest' <- readHints rest
         pure (s :: rest')
readHints _ = Nothing

export
getIDECommand : SExp -> Maybe IDECommand
getIDECommand (SExpList [SymbolAtom "interpret", StringAtom cmd])
    = Just $ Interpret cmd
getIDECommand (SExpList [SymbolAtom "load-file", StringAtom fname])
    = Just $ LoadFile fname Nothing
getIDECommand (SExpList [SymbolAtom "load-file", StringAtom fname, IntegerAtom l])
    = Just $ LoadFile fname (Just l)
getIDECommand (SExpList [SymbolAtom "type-of", StringAtom n])
    = Just $ TypeOf n Nothing
getIDECommand (SExpList [SymbolAtom "type-of", StringAtom n,
                         IntegerAtom l, IntegerAtom c])
    = Just $ TypeOf n (Just (l, c))
getIDECommand (SExpList [SymbolAtom "case-split", IntegerAtom l, IntegerAtom c, 
                         StringAtom n])
    = Just $ CaseSplit l c n
getIDECommand (SExpList [SymbolAtom "case-split", IntegerAtom l, StringAtom n])
    = Just $ CaseSplit l 0 n
getIDECommand (SExpList [SymbolAtom "add-clause", IntegerAtom l, StringAtom n])
    = Just $ AddClause l n
getIDECommand (SExpList [SymbolAtom "proof-search", IntegerAtom l, StringAtom n])
    = Just $ ExprSearch l n [] False
getIDECommand (SExpList [SymbolAtom "proof-search", IntegerAtom l, StringAtom n, SExpList hs])
    = case readHints hs of
           Just hs' => Just $ ExprSearch l n hs' False
           _ => Nothing
getIDECommand (SExpList [SymbolAtom "proof-search", IntegerAtom l, StringAtom n, SExpList hs, SymbolAtom mode])
    = case readHints hs of
           Just hs' => Just $ ExprSearch l n hs' (getMode mode)
           _ => Nothing
  where
    getMode : String -> Bool
    getMode m = m == "all"
getIDECommand _ = Nothing

export
getMsg : SExp -> Maybe (IDECommand, Integer)
getMsg (SExpList [cmdexp, IntegerAtom num])
   = do cmd <- getIDECommand cmdexp
        pure (cmd, num)
getMsg _ = Nothing

escape : String -> String
escape = pack . concatMap escapeChar . unpack
  where
    escapeChar : Char -> List Char
    escapeChar '\\' = ['\\', '\\']
    escapeChar '"'  = ['\\', '\"']
    escapeChar c    = [c]

export
Show SExp where
  show (SExpList xs) = "(" ++ showSep " " (map show xs) ++ ")"
  show (StringAtom str) = "\"" ++ escape str ++ "\""
  show (BoolAtom b) = ":" ++ show b
  show (IntegerAtom i) = show i
  show (SymbolAtom s) = ":" ++ s

public export
interface SExpable a where
  toSExp : a -> SExp

export
SExpable SExp where
  toSExp = id

export
SExpable Bool where
  toSExp = BoolAtom

export
SExpable String where
  toSExp = StringAtom

export
SExpable Integer where
  toSExp = IntegerAtom

export
SExpable Int where
  toSExp = IntegerAtom . cast

export
SExpable Name where
  toSExp = SymbolAtom . show

export
(SExpable a, SExpable b) => SExpable (a, b) where
  toSExp (x, y) 
      = case toSExp y of
             SExpList xs => SExpList (toSExp x :: xs)
             y' => SExpList [toSExp x, y']

export
SExpable a => SExpable (List a) where
  toSExp xs
      = SExpList (map toSExp xs)

export
sym : String -> Name
sym = UN

export
version : Int -> Int -> SExp
version maj min = toSExp (SymbolAtom "protocol-version", maj, min)

hex : Int -> IO ()
hex num = foreign FFI_C "printf" (String -> Int -> IO ()) "%06x" num

export
send : SExpable a => a -> Core annot ()
send resp
    = do let r = show (toSExp resp) ++ "\n"
         coreLift $ hex (cast (length r))
         coreLift $ putStr r
         coreLift $ fflush stdout
