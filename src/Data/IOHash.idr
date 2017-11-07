module Data.IOHash

import Data.IOArray

-- A simple implementation of a mutable hash table

export
record IOHash key value where
  constructor MkTable
  eq : key -> key -> Bool
  hash : key -> Int
  numBuckets : Int
  buckets : IOArray (List (key, value))

export
new : (key -> key -> Bool) ->
      (key -> Int) -> Nat -> IO (IOHash key valInt)
new eq hash n
    = do arr <- newArray (cast n) []
         pure (MkTable eq hash (cast n) arr)

findPos : Int -> Int -> Int
findPos hash x = assert_total $ if x <=0 then 0 else abs (hash `mod` x)

export
insert : key -> value -> IOHash key value -> IO ()
insert k v table
    = do let arr = buckets table
         let pos = hash table k `findPos` numBuckets table
         row <- unsafeReadArray arr pos
         unsafeWriteArray arr pos ((k, v) :: row)

export
update : key -> value -> IOHash key value -> IO ()
update k v table
    = do let arr = buckets table
         let pos = hash table k `findPos` numBuckets table
         row <- unsafeReadArray arr pos
         unsafeWriteArray arr pos (updateVal (eq table) k v row)
  where
    updateVal : (key -> key -> Bool) -> key -> value ->
                List (key, value) -> List (key, value)
    updateVal eq k v [] = [(k, v)]
    updateVal eq k v ((k', v') :: rest)
        = if eq k k' then (k, v) :: rest
                     else ((k', v') :: updateVal eq k v rest)

export
delete : key -> IOHash key value -> IO ()
delete k table
    = do let arr = buckets table
         let pos = hash table k `findPos` numBuckets table
         row <- unsafeReadArray arr pos
         unsafeWriteArray arr pos (deleteVal (eq table) k row)
  where
    deleteVal : (key -> key -> Bool) -> key -> 
                List (key, value) -> List (key, value)
    deleteVal eq k [] = []
    deleteVal eq k ((k', v') :: rest)
        = if eq k k' then rest else ((k', v') :: deleteVal eq k rest)

export
lookup : key -> IOHash key value -> IO (Maybe value)
lookup k table
    = do let arr = buckets table
         let pos = hash table k `findPos` numBuckets table
         row <- unsafeReadArray arr pos
         pure (lookupBy (eq table) k row)
