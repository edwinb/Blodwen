module Data.CSet

import public Data.CMap

export
data SortedSet = SetWrapper (Data.CMap.SortedMap ())

export
empty : SortedSet 
empty = SetWrapper Data.CMap.empty

export
insert : Key -> SortedSet -> SortedSet
insert k (SetWrapper m) = SetWrapper (Data.CMap.insert k () m)

export
delete : Key -> SortedSet -> SortedSet
delete k (SetWrapper m) = SetWrapper (Data.CMap.delete k m)

export
contains : Key -> SortedSet -> Bool
contains k (SetWrapper m) = isJust (Data.CMap.lookup k m)

export
fromList : List Key -> SortedSet
fromList l = SetWrapper (Data.CMap.fromList (map (\i => (i, ())) l))

export
toList : SortedSet -> List Key
toList (SetWrapper m) = map (\(i, _) => i) (Data.CMap.toList m)

export
foldr : (Key -> acc -> acc) -> acc -> SortedSet -> acc
foldr f e xs = foldr f e (Data.CSet.toList xs)

||| Set union. Inserts all elements of x into y
export
union : (x, y : SortedSet) -> SortedSet
union x y = foldr insert x y

||| Set difference. Delete all elments in y from x
export
difference : (x, y : SortedSet) -> SortedSet
difference x y = foldr delete x y

||| Set symmetric difference. Uses the union of the differences.
export
symDifference : (x, y : SortedSet) -> SortedSet
symDifference x y = union (difference x y) (difference y x)

||| Set intersection. Implemented as the difference of the union and the symetric difference.
export
intersection : (x, y : SortedSet) -> SortedSet
intersection x y = difference x (difference x y)

export
Semigroup (SortedSet) where
  (<+>) = union

export
Monoid (SortedSet) where
  neutral = empty

export
keySet : SortedMap v -> SortedSet
keySet = SetWrapper . map (const ())
