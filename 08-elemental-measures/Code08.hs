{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}
{-@ LIQUID "--no-termination" @-}
module Code08 where

import Prelude  hiding (elem, reverse, filter)
import Data.Set hiding (insert, filter)

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

{-@ type True  = {v:Bool |     v} @-}
{-@ type False = {v:Bool | not v} @-}

{-@ prop_one_plus_one_eq_two :: _ -> True @-}
prop_one_plus_one_eq_two x   = (x == 1 + 1) `implies` (x == 2)

{-@ implies        :: p:Bool -> q:Bool -> Implies p q  @-}
implies False _    = True
implies _     True = True
implies _    _     = False

{-@ type Implies P Q = {v:_ | v <=> (P => Q)} @-}

{-@ prop_x_y_200 :: _ -> _ -> True @-}
prop_x_y_200 x y = (x < 100 && y < 100) `implies` (x + y < 200)

{-@ prop_intersection_comm :: _ -> _ -> True @-}
prop_intersection_comm x y
  = (x `intersection` y) == (y `intersection` x)

{-@ prop_union_assoc :: _ -> _ -> _ -> True @-}
prop_union_assoc x y z
  = (x `union` (y `union` z)) == (x `union` y) `union` z

{-@ prop_intersection_dist :: _ -> _ -> _ -> True @-}
prop_intersection_dist x y z
  =  x `intersection` (y `union` z)
     ==
     (x `intersection` y) `union` (x `intersection` z)

{-@ prop_cup_dif_bad :: _ -> _ -> True @-}
prop_cup_dif_bad x y
  = pre `implies` (x == ((x `union` y) `difference` y))
  where
    pre = x `intersection` y == empty

{-@ measure elts @-}
elts        :: (Ord a) => [a] -> Set a
elts []     = empty
elts (x:xs) = singleton x `union` elts xs

{-@ type ListS a S = {v:[a] | elts v = S} @-}
{-@ type ListEmp a = ListS a {Set_empty 0} @-}
{-@ type ListEq a X = ListS a {elts X}    @-}
{-@ type ListSub a X = {v:[a]| Set_sub (elts v) (elts X)} @-}
{-@ type ListUn a X Y = ListS a {Set_cup (elts X) (elts Y)} @-}
{-@ type ListUn1 a X Y = ListS a {Set_cup (Set_sng X) (elts Y)} @-}

{-@ append'       :: xs:_ -> ys:_ -> v:ListUn a xs ys @-}
append' []     ys = ys
append' (x:xs) ys = x : append' xs ys

{-@ reverse' :: xs:[a] -> v:ListEq a xs @-}
reverse' xs = revHelper [] xs

{-@ revHelper        :: xs:[a] -> ys:[a] -> v:ListUn a xs ys @-}
revHelper acc []     = acc
revHelper acc (x:xs) = revHelper (x:acc) xs

{-@ halve        :: n:Int -> xs:[a] -> {v:_ | elts xs = union (elts (fst v)) (elts (snd v))} @-}
halve            :: Int -> [a] -> ([a], [a])
halve 0 xs       = ([], xs)
halve n (x:y:zs) = (x:xs, y:ys) where (xs, ys) = halve (n-1) zs
halve _ xs       = ([], xs)

{-@ prop_halve_append  :: _ -> _ -> True @-}
prop_halve_append n xs = elts xs == elts xs'
  where
    xs'      =  append' ys zs
    (ys, zs) =  halve n xs

{-@ elem      :: (Eq a) => x:a -> xs:[a] -> {v:_ | v <=> member x (elts xs)} @-}
elem _ []     = False
elem x (y:ys) = x == y || elem x ys

{-@ test1 :: True @-}
test1      = elem 2 [1, 2, 3]

{-@ test2 :: False @-}
test2      = elem 2 [1, 3]

insert x []     = [x]
insert x (y:ys)
  | x <= y      = x : y : ys
  | otherwise   = y : insert x ys
{-@ insert :: x:a -> xs:[a] -> ListUn1 a x xs @-}

{-@ insertSort :: (Ord a) => xs:[a] -> ListEq a xs @-}
insertSort []     = []
insertSort (x:xs) = insert x (insertSort xs)

{-@ merge :: xs:[a] -> ys:[a] -> ListUn a xs ys @-}
merge [] ys          = ys
merge xs []          = xs
merge (x:xs) (y:ys)
  | x <= y           = x : merge xs (y:ys)
  | otherwise        = y : merge (x:xs) ys

{-@ prop_merge_app   :: _ -> _ -> True   @-}
prop_merge_app xs ys = elts zs == elts zs'
  where
    zs               = append' xs ys
    zs'              = merge   xs ys

{-@ mergeSort :: (Ord a) => xs:[a] -> ListEq a xs @-}
mergeSort :: (Ord a) => [a] -> [a]
mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
   (ys, zs)   = halve mid xs
   {-@ mid :: Btwn 1 sz @-}
   mid        = sz `div` 2
   sz         = length xs

{-@ measure unique @-}
unique        :: (Ord a) => [a] -> Bool
unique []     = True
unique (x:xs) = unique xs && not (member x (elts xs))

{-@ type UList a = {v:[a] | unique v }@-}

{-@ isUnique    :: UList Int @-}
isUnique :: [Int]
isUnique = [1, 2, 3]           -- accepted by LH

{-@ fail isNotUnique @-}
{-@ isNotUnique :: UList Int @-}
isNotUnique :: [Int]
isNotUnique = [1, 2, 3, 1]     -- rejected by LH

{-@ filter   :: (a -> Bool)
             -> xs:UList a
             -> {v:ListSub a xs | unique v}
  @-}
filter _ []   = []
filter f (x:xs)
  | f x       = x : xs'
  | otherwise = xs'
  where
    xs'       = filter f xs

{-@ filter' :: (a -> Bool)
            -> xs:[a]
            -> {v:ListSub a xs | unique xs ==> unique v }@-}
filter' _ []   = []
filter' f (x:xs)
  | f x       = x : xs'
  | otherwise = xs'
  where
    xs'       = filter' f xs

{-@ test3 :: UList _ @-}
test3     = filter' (> 2) [1,2,3,4]

{-@ test4 :: [_] @-}
test4     = filter' (> 3) [3,1,2,3]

{-@ reverse    :: xs:UList a -> {v:ListEq a xs | unique v}    @-}
reverse :: [a] -> [a]
reverse         = go []
  where
    {-@ go     :: acc:UList a -> xs:({v:UList a | Disj acc v}) -> {v:ListUn a acc xs | unique v} @-}
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs

{-@ nub              :: [a] -> UList a @-}
nub xs                = go [] xs
  where
    {-@ go :: UList a -> xs:[a] -> UList a @-}
    go :: (Eq a) => [a] -> [a] -> [a]
    go seen []        = seen
    go seen (x:xs)
      | x `isin` seen = go seen     xs
      | otherwise     = go (x:seen) xs

{-@ predicate In X Xs = member X (elts Xs) @-}
{-@ isin :: x:_ -> ys:_ -> {v:_ | v <=> In x ys} @-}
isin x (y:ys)
  | x == y    = True
  | otherwise = x `isin` ys
isin _ []     = False

{-@ append       :: xs:UList a -> ys:{v:UList a | Disj xs v} -> {v:ListUn a xs ys | unique v} @-}
append []     ys = ys
append (x:xs) ys = x : append xs ys

{-@ type Btwn I J = {v:_ | I <= v && v < J} @-}

{-@ range     :: i:Int -> j:Int -> UList (Btwn i j) @-}
range         :: Int -> Int -> [Int]
range i j
  | i < j     = cons i (range (i + 1) j)
  | otherwise = []
  where
    {-@ cons :: i:{v:Int | v < j} -> UList (Btwn {i+1} j) -> UList (Btwn i j) @-}
    cons :: Int -> [Int] -> [Int]
    cons i l = assert (lemma_notIn i j l) $ i : l

assert _ x = x

{-@ reflect lemma_notIn @-}
{-@ lemma_notIn :: i:Int
                -> j:{v:Int | i < j}
                -> xs:UList (Btwn {i+1} j)
                -> {v:Bool | not (In i xs)} @-}
lemma_notIn :: Int -> Int -> [Int] -> Bool
lemma_notIn _ _     [] = True
lemma_notIn i j (_:xs) = lemma_notIn i j xs

data Zipper a = Zipper {
    focus  :: a
  , left   :: [a]
  , right  :: [a]
  }

{-@ data Zipper a = Zipper {
      focus :: a
    , left  :: {v:UList a | not (member focus (elts v))}
    , right :: {v:UList a | not (member focus (elts v)) && Disj v left }
    } @-}

{-@ predicate Disj X Y = intersection (elts X) (elts Y) = empty        @-}

{-@ differentiate    :: UList a -> Maybe (Zipper a) @-}
differentiate []     = Nothing
differentiate (x:xs) = Just $ Zipper x [] xs

{-@ integrate            :: Zipper a -> UList a @-}
integrate (Zipper x l r) = reverse l `append` (x : r)

focusLeft                      :: Zipper a -> Zipper a
focusLeft (Zipper t (l:ls) rs) = Zipper l ls (t:rs)
focusLeft (Zipper t [] rs)     = Zipper x xs []
  where
    (x:xs)                     = reverse (t:rs)

focusRight    :: Zipper a -> Zipper a
focusRight    = reverseZipper . focusLeft . reverseZipper

reverseZipper :: Zipper a -> Zipper a
reverseZipper (Zipper t ls rs) = Zipper t rs ls

filterZipper :: (a -> Bool) -> Zipper a -> Maybe (Zipper a)
filterZipper p (Zipper f ls rs)
  = case filter p (f:rs) of
      f':rs' -> Just $ Zipper f' (filter p ls) rs'
      []     -> case filter p ls of
                  f':ls' -> Just $ Zipper f' ls' []
                  []     -> Nothing
