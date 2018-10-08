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

export
Show SExp where
  show (SExpList xs) = "(" ++ showSep " " (map show xs) ++ ")"
  show (StringAtom str) = show str
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
