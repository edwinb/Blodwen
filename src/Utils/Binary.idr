module Utils.Binary

import Core.Core
import Data.Buffer

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
                     [] => throw (InternalError "End of buffer when reading Byte")
                     (next :: rest) =>
                        do val <- coreLift $ getByte (buf next) 0
                           put Bin (MkBin (chunk :: done) (incLoc 1 next) rest)
                           pure val

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
                     [] => throw (InternalError "End of buffer when reading Int")
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
                     [] => throw (InternalError "End of buffer when reading String")
                     (next :: rest) =>
                        do val <- coreLift $ getString (buf next) 0 len
                           put Bin (MkBin (chunk :: done)
                                          (incLoc len next) rest)
                           pure val

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
     = toBuf b (the Bits8 0)
  toBuf b (Just val)
     = do toBuf b (the Bits8 1)
          toBuf b val

  fromBuf b
     = do val <- fromBuf b {a = Bits8}
          case val of
               0 => pure Nothing
               1 => do val <- fromBuf b
                       pure (Just val)
               _ => throw (InternalError "Corrupted binary data for Maybe")

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

{-
testMain : Core () ()
testMain
    = do buf <- initBinary
         toBuf buf (the Bits8 42)
         toBuf buf $ the Int 1234567890
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
         coreLift $ printLn (the Int val)
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
