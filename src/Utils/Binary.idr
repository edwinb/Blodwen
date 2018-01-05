module Utils.Binary

import Core.Core
import Data.Buffer
import Data.List

-- Serialising data as binary. Provides an interface TTI which allows
-- reading and writing to chunks of memory, "Binary", which can be written
-- to and read from files.

%default covering

-- A label for binary states
export 
data Bin : Type where

-- A component of the serialised data.
record Chunk where
  constructor MkChunk
  buf : Buffer
  loc : Int
  size : Int -- Capacity
  used : Int -- Amount used

newChunk : Buffer -> Chunk
newChunk b = MkChunk b 0 (size b) 0

avail : Chunk -> Int
avail c = size c - loc c

toRead : Chunk -> Int
toRead c = used c - loc c

appended : Int -> Chunk -> Chunk
appended i c = record { loc $= (+i),
                        used $= (+i) } c

incLoc : Int -> Chunk -> Chunk
incLoc i c = record { loc $= (+i) } c

-- Serialised data is stored as a list of chunks, in a zipper.
-- i.e. processed chunks, chunk we're working on, chunks to do
export
data Binary = MkBin (List Chunk) Chunk (List Chunk)

dumpBin : Binary -> IO ()
dumpBin (MkBin done chunk rest)
   = do printLn !(traverse bufferData (map buf done))
        printLn !(bufferData (buf chunk))
        printLn !(traverse bufferData (map buf rest))

nonEmptyRev : NonEmpty (xs ++ y :: ys)
nonEmptyRev {xs = []} = IsNonEmpty
nonEmptyRev {xs = (x :: xs)} = IsNonEmpty

reset : Binary -> Binary
reset (MkBin done cur rest) 
    = setBin (reverse done ++ cur :: rest) nonEmptyRev
  where
    setBin : (xs : List Chunk) -> (prf : NonEmpty xs) -> Binary
    setBin (chunk :: rest) IsNonEmpty 
        = MkBin [] (record { loc = 0 } chunk)
                   (map (record { loc = 0 }) rest)

req : List Chunk -> Int
req [] = 0
req (c :: cs)
    = used c + req cs

-- Take all the data from the chunks in a 'Binary' and copy them into one
-- single buffer, ready for writing to disk.
-- TODO: YAGNI? Delete if so...
toBuffer : Binary -> IO (Maybe Buffer)
toBuffer (MkBin done cur rest)
    = do let chunks = reverse done ++ cur :: rest
         Just b <- newBuffer (req chunks)
              | Nothing => pure Nothing
         copyToBuf 0 b chunks
         pure (Just b)
  where
    copyToBuf : (pos : Int) -> Buffer -> List Chunk -> IO ()
    copyToBuf pos b [] = pure ()
    copyToBuf pos b (c :: cs)
        = do copyData (buf c) 0 (used c) b pos
             copyToBuf (pos + used c) b cs

fromBuffer : Buffer -> IO Binary
fromBuffer buf
    = do len <- rawSize buf
         pure (MkBin [] (MkChunk buf 0 len len) []) -- assume all used

export
writeToFile : (fname : String) -> Binary -> IO (Either FileError ())
writeToFile fname (MkBin done cur rest)
    = do Right h <- openFile fname WriteTruncate
               | Left err => pure (Left err)
         let chunks = reverse done ++ cur :: rest
         writeChunks h chunks
         closeFile h
         pure (Right ())
  where
    writeChunks : File -> List Chunk -> IO ()
    writeChunks h [] = pure ()
    writeChunks h (c :: cs)
        = do writeBufferToFile h (resetBuffer (buf c)) (used c)
             writeChunks h cs

export
readFromFile : (fname : String) -> IO (Either FileError Binary)
readFromFile fname
    = do Right h <- openFile fname Read
               | Left err => pure (Left err)
         Right max <- fileSize h
               | Left err => pure (Left err)
         Just b <- newBuffer max
               | Nothing => pure (Left (GenericFileError 0)) --- um, not really
         b <- readBufferFromFile h b max
         pure (Right (MkBin [] (MkChunk b 0 max max) []))

public export
interface TTI a where -- TTI = TT intermediate code/interface file
  -- Add binary data representing the value to the given buffer
  toBuf : Ref Bin Binary -> a -> Core annot ()
  -- Return the data representing a thing of type 'a' from the given buffer.
  -- Throws if the data can't be parsed as an 'a'
  fromBuf : Ref Bin Binary -> Core annot a

-- Create a new list of chunks, initialised with one 64k chunk
export
initBinary : Core annot (Ref Bin Binary)
initBinary
    = do Just buf <- coreLift $ newBuffer 65536
             | Nothing => throw (InternalError "Buffer creation failed")
         newRef Bin (MkBin [] (newChunk buf) [])

export
corrupt : String -> Core annot a
corrupt ty = throw (TTIError (Corrupt ty))

-- Primitives; these are the only things that have to deal with growing
-- the buffer list

export
TTI Bits8 where
  toBuf b val 
    = do MkBin done chunk rest <- get Bin
         if avail chunk >= 1
            then
              do coreLift $ setByte (buf chunk) (loc chunk) val
                 put Bin (MkBin done (appended 1 chunk) rest)
            else 
              do Just newbuf <- coreLift $ newBuffer 65536
                    | Nothing => throw (InternalError "Buffer expansion failed")
                 coreLift $ setByte newbuf 0 val
                 put Bin (MkBin (chunk :: done)
                                (MkChunk newbuf 1 (size newbuf) 1)
                                rest)

  fromBuf b
    = do MkBin done chunk rest <- get Bin
         if toRead chunk >= 1
            then
              do val <- coreLift $ getByte (buf chunk) (loc chunk)
                 put Bin (MkBin done (incLoc 1 chunk) rest)
                 pure val
              else
                case rest of
                     [] => throw (TTIError (EndOfBuffer "Byte"))
                     (next :: rest) =>
                        do val <- coreLift $ getByte (buf next) 0
                           put Bin (MkBin (chunk :: done) (incLoc 1 next) rest)
                           pure val

export
tag : {auto b : Ref Bin Binary} -> Bits8 -> Core annot ()
tag {b} val = toBuf b val

export
getTag : {auto b : Ref Bin Binary} -> Core annot Bits8
getTag {b} = fromBuf b

export
TTI Int where
  toBuf b val
    = do MkBin done chunk rest <- get Bin
         if avail chunk >= 4
            then 
              do coreLift $ setInt (buf chunk) (loc chunk) val
                 put Bin (MkBin done (appended 4 chunk) rest)
            else 
              do Just newbuf <- coreLift $ newBuffer 65536
                    | Nothing => throw (InternalError "Buffer expansion failed")
                 coreLift $ setInt newbuf 0 val
                 put Bin (MkBin (chunk :: done)
                                (MkChunk newbuf 4 (size newbuf) 4)
                                rest)
  fromBuf b 
    = do MkBin done chunk rest <- get Bin
         if toRead chunk >= 4
            then
              do val <- coreLift $ getInt (buf chunk) (loc chunk)
                 put Bin (MkBin done (incLoc 4 chunk) rest)
                 pure val
              else
                case rest of
                     [] => throw (TTIError (EndOfBuffer "Int"))
                     (next :: rest) =>
                        do val <- coreLift $ getInt (buf next) 0
                           put Bin (MkBin (chunk :: done) (incLoc 4 next) rest)
                           pure val

export
TTI String where
  toBuf b val
      = do let req : Int = cast (length val)
           toBuf b req
           MkBin done chunk rest <- get Bin
           if avail chunk >= req
              then
                do coreLift $ setString (buf chunk) (loc chunk) val
                   put Bin (MkBin done (appended req chunk) rest)
              else 
                do Just newbuf <- coreLift $ newBuffer 65536
                      | Nothing => throw (InternalError "Buffer expansion failed")
                   coreLift $ setString newbuf 0 val
                   put Bin (MkBin (chunk :: done)
                                  (MkChunk newbuf req (size newbuf) req)
                                  rest)

  fromBuf b 
      = do len <- fromBuf {a = Int} b
           MkBin done chunk rest <- get Bin
           if toRead chunk >= len
              then
                do val <- coreLift $ getString (buf chunk) (loc chunk) len
                   put Bin (MkBin done (incLoc len chunk) rest)
                   pure val
              else 
                case rest of
                     [] => throw (TTIError (EndOfBuffer "String"))
                     (next :: rest) =>
                        do val <- coreLift $ getString (buf next) 0 len
                           put Bin (MkBin (chunk :: done)
                                          (incLoc len next) rest)
                           pure val

-- Some useful types from the prelude

export
TTI Bool where
  toBuf b False = tag 0
  toBuf b True = tag 1
  fromBuf b
      = case !getTag of
             0 => pure False
             1 => pure True
             _ => corrupt "Bool"

export
(TTI a, TTI b) => TTI (a, b) where
  toBuf b (x, y)
     = do toBuf b x
          toBuf b y
  fromBuf b
     = do x <- fromBuf b
          y <- fromBuf b
          pure (x, y)

export
TTI a => TTI (Maybe a) where
  toBuf b Nothing
     = tag 0
  toBuf b (Just val)
     = do tag 1
          toBuf b val

  fromBuf b
     = case !getTag of
            0 => pure Nothing
            1 => do val <- fromBuf b
                    pure (Just val)
            _ => corrupt "Maybe"

export
TTI a => TTI (List a) where
  toBuf b xs
      = do toBuf b (cast {to=Int} (length xs))
           traverse (toBuf b) xs
           pure ()
  fromBuf b 
      = do len <- fromBuf b {a = Int}
           readElems [] (cast len)
    where
      readElems : List a -> Nat -> Core annot (List a)
      readElems xs Z = pure (reverse xs)
      readElems xs (S k)
          = do val <- fromBuf b
               readElems (val :: xs) k

count : Elem x xs -> Int
count Here = 0
count (There p) = 1 + count p

-- Assumption is that it was type safe when we wrote it out, so believe_me
-- to rebuild proofs is fine.
-- We're just making up the implicit arguments - this is only fine at run
-- time because those arguments get erased!
mkPrf : Int -> Elem x xs
mkPrf i {x} {xs}
    = if i == 0 then believe_me (Here {x} {xs = x :: xs})
                else believe_me (There {y=x} (mkPrf {x} {xs} (i-1)))

export
TTI (Elem x xs) where
  toBuf b prf = toBuf b (count prf)
  fromBuf b
    = do val <- fromBuf b {a = Int}
         if val >= 0
            then pure (assert_total (mkPrf val))
            else corrupt "Elem"

toLimbs : Integer -> List Int
toLimbs x
    = if x == 0 
         then []
         else if x == -1 then [-1]
              else fromInteger (prim__andBigInt x 0xff) ::
                    toLimbs (prim__ashrBigInt x 8)

fromLimbs : List Int -> Integer
fromLimbs [] = 0
fromLimbs (x :: xs) = cast x + prim__shlBigInt (fromLimbs xs) 8

export
TTI Integer where
  toBuf b val
    = assert_total $ if val < 0
         then do toBuf b (the Bits8 0)
                 toBuf b (toLimbs (-val))
         else do toBuf b (the Bits8 1)
                 toBuf b (toLimbs val)
  fromBuf b 
    = do val <- fromBuf b {a = Bits8}
         case val of
              0 => do val <- fromBuf b
                      pure (-(fromLimbs val))
              1 => do val <- fromBuf b
                      pure (fromLimbs val)
              _ => corrupt "Integer"

export
TTI Nat where
  toBuf b val = toBuf b (cast {to=Integer} val)
  fromBuf b = do val <- fromBuf b
                 pure (fromInteger val)

{-
testMain : Core () ()
testMain
    = do buf <- initBinary
         toBuf buf (the Bits8 42)
         toBuf buf $ the Integer 12345678900000000000000000000000000000000
         toBuf buf $ the Integer (-12345678900000000000000000000000000000000)
         toBuf buf $ "AAAAAAAAAAAA"
         toBuf buf $ the Int 6
         toBuf buf $ "Sossidges!!!!"
         toBuf buf $ the Int 6
         toBuf buf $ ("abc", the Int 42, the Int 64)

         toBuf buf {a = Maybe String} Nothing
         toBuf buf $ Just "Foom"
         toBuf buf {a = List String} []
         toBuf buf $ ["Foo", "Bar", "Baz", "Quux"]

         bin <- get Bin
         put Bin (reset bin)
         bin <- get Bin

         val <- fromBuf buf
         coreLift $ printLn (the Bits8 val)
         val <- fromBuf buf
         coreLift $ printLn (the Integer val)
         val <- fromBuf buf
         coreLift $ printLn (the Integer val)
         val <- fromBuf buf
         coreLift $ printLn (the String val)
         val <- fromBuf buf
         coreLift $ printLn (the Int val)
         val <- fromBuf buf
         coreLift $ printLn (the String val)
         val <- fromBuf buf
         coreLift $ printLn (the Int val)

         (str, x, y) <- fromBuf {a = (String, Int, Int)} buf
         coreLift $ printLn (str, x, y)

         val <- fromBuf buf
         coreLift $ printLn (the (Maybe String) val)
         val <- fromBuf buf
         coreLift $ printLn (the (Maybe String) val)

         val <- fromBuf buf
         coreLift $ printLn (the (List String) val)
         val <- fromBuf buf
         coreLift $ printLn (the (List String) val)


main : IO ()
main = do coreRun testMain
              (\err => putStrLn (show err))
              (\res => putStrLn "OK!")
-}
