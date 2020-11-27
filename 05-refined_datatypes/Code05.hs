{-@ LIQUID "--no-termination" @-}
module Code05 where

import Prelude      hiding (abs, length, min)
import Data.Monoid
import Data.List    (foldl', foldr)
import Data.Vector  hiding (singleton, foldl', foldr, fromList, (++))
import Data.Maybe   (fromJust)

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

data Sparse a = SP { spDim   :: Int
                   , spElems :: [(Int, a)] }

{-@ data Sparse a = SP { spDim   :: Nat
                       , spElems :: [(Btwn 0 spDim, a)]} @-}

{-@ type Nat        = {v:Int | 0 <= v}            @-}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

okSP :: Sparse String
okSP = SP 5 [ (0, "cat")
            , (3, "dog") ]

{-@ fail badSP @-}
badSP :: Sparse String
badSP = SP 5 [ (0, "cat")
             , (6, "dog") ]

{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}

{-@ dotProd :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd :: Vector Int -> Sparse Int -> Int
dotProd x (SP _ y) = go 0 y
  where
    go sum ((i, v) : y') = go (sum + (x ! i) * v) y'
    go sum []            = sum

{-@ dotProd' :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd' :: Vector Int -> Sparse Int -> Int
dotProd' x (SP _ y) = foldl' body 0 y
  where
    body sum (i, v) = sum + (x ! i)  * v

{-@ fromList :: n:Nat -> [(Int, a)] -> Maybe (SparseN a n) @-}
fromList                 :: Int   -> [(Int, a)] -> Maybe (Sparse a)
fromList dim elts        = fmap (SP dim) (foldr go (Just []) elts)
  where
    go (i, v) acc
      | 0 < i && i < dim = fmap ((i, v) :) acc
      | otherwise        = Nothing

{-@ test1 :: SparseN String 3 @-}
test1     = fromJust $ fromList 3 [(0, "cat"), (2, "mouse")]


{-@ plus :: (Num a) => x:Sparse a -> y:SparseN a (spDim x) -> SparseN a (spDim x) @-}
plus     :: (Num a) => Sparse a -> Sparse a -> Sparse a
plus (SP dim x) (SP _ y) = SP dim (go 0)
  where
    go i
      | i < dim          = case find x i <> find y i of
                             Just (Sum v) -> (i, v) : go (i + 1)
                             Nothing      -> go (i + 1)
      | otherwise        = []

    find [] _            = Nothing
    find ((i, xi) : x) i'
      | i == i'          = Just (Sum xi)
      | otherwise        = find x i'

{-@ test2 :: SparseN Int 3 @-}
test2    :: Sparse Int
test2    = plus vec1 vec2
  where
    vec1 = SP 3 [(0, 12), (2, 9)]
    vec2 = SP 3 [(0, 8),  (1, 100)]

data IncList a =
    Emp
  | (:<) { hd :: a, tl :: IncList a }

infixr 9 :<

{-@ data IncList a =
        Emp
      | (:<) { hd :: a, tl :: IncList {v:a | hd <= v}}  @-}

okList  = 1 :< 2 :< 3 :< Emp      -- accepted by LH

{-@ fail badList @-}
badList = 2 :< 1 :< 3 :< Emp      -- rejected by LH

insertSort        :: (Ord a) => [a] -> IncList a
insertSort []     = Emp
insertSort (x:xs) = insert x (insertSort xs)

insert             :: (Ord a) => a -> IncList a -> IncList a
insert y Emp       = y :< Emp
insert y (x :< xs)
  | y <= x         = y :< x :< xs
  | otherwise      = x :< insert y xs

insertSort'     :: (Ord a) => [a] -> IncList a
insertSort' xs  = foldr f b xs
  where
     f          = insert
     b          = Emp

split          :: [a] -> ([a], [a])
split (x:y:zs) = (x:xs, y:ys)
  where
    (xs, ys)   = split zs
split xs       = (xs, [])

merge         :: (Ord a) => IncList a -> IncList a -> IncList a
merge xs  Emp = xs
merge Emp ys  = ys
merge (x :< xs) (y :< ys)
  | x <= y    = x :< merge xs (y :< ys)
  | otherwise = y :< merge (x :< xs) ys
merge _   _   = Emp

mergeSort :: (Ord a) => [a] -> IncList a
mergeSort []  = Emp
mergeSort [x] = x :< Emp
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
    (ys, zs)  = split xs

quickSort           :: (Ord a) => [a] -> IncList a
quickSort []        = Emp
quickSort (x:xs)    = append x lessers greaters
  where
    lessers         = quickSort [y | y <- xs, y < x ]
    greaters        = quickSort [z | z <- xs, z >= x]

{-@ append :: x:a -> IncList {y:a | y < x}
                  -> IncList {z:a | z >= x}
                  -> IncList a
  @-}
append z Emp       ys = z :< ys
append z (x :< xs) ys = x :< append z xs ys

data BST a = Leaf
           | Node { root  :: a
                  , left  :: BST a
                  , right :: BST a }

okBST :: BST Int
okBST =  Node 6
             (Node 2
                 (Node 1 Leaf Leaf)
                 (Node 4 Leaf Leaf))
             (Node 9
                 (Node 7 Leaf Leaf)
                 Leaf)

{-@ data BST a    = Leaf
                  | Node { root  :: a
                         , left  :: BSTL a root
                         , right :: BSTR a root } @-}

{-@ type BSTL a X = BST {v:a | v < X}             @-}
{-@ type BSTR a X = BST {v:a | X < v}             @-}

{-@ fail badBST @-}
badBST =  Node 66
             (Node 4
                 (Node 1 Leaf Leaf)
                 (Node 69 Leaf Leaf))  -- Out of order, rejected
             (Node 99
                 (Node 77 Leaf Leaf)
                 Leaf)

mem                 :: (Ord a) => a -> BST a -> Bool
mem _ Leaf          = False
mem k (Node k' l r)
  | k == k'         = True
  | k <  k'         = mem k l
  | otherwise       = mem k r

one   :: a -> BST a
one x = Node x Leaf Leaf

add                  :: (Ord a) => a -> BST a -> BST a
add k' Leaf          = one k'
add k' t@(Node k l r)
  | k' < k           = Node k (add k' l) r
  | k  < k'          = Node k l (add k' r)
  | otherwise        = t

data MinPair a = MP { mElt :: a, rest :: BST a }

{-@ data MinPair a = MP { mElt :: a, rest :: BSTR a mElt} @-}

{-@ measure nonLeaf @-}
{-@ nonLeaf :: BST a -> Bool @-}
nonLeaf :: BST a -> Bool
nonLeaf Leaf         = False
nonLeaf (Node _ _ _) = True

{-@ delMin :: (Ord a) => {t:BST a | nonLeaf t} -> MinPair a @-}
delMin                 :: (Ord a) => BST a -> MinPair a
delMin (Node k Leaf r) = MP k r
delMin (Node k l r)    = MP k' (Node k l' r)
  where
    MP k' l'           = delMin l
delMin Leaf            = die "Don't say I didn't warn ya!"

del                   :: (Ord a) => a -> BST a -> BST a
del k' (Node k l Leaf)
  | k' == k           = l
  | k' < k            = Node k (del k' l) Leaf
  | otherwise         = Node k l Leaf
del k' (Node k l r)
  | k' == k           = Node k'' l r''
  | k' < k            = Node k (del k' l) r
  | otherwise         = Node k l (del k' r)
  where
    MP k'' r''        = delMin r
del _  Leaf           = Leaf


bstSort   :: (Ord a) => [a] -> IncList a
bstSort   = toIncList . toBST

toBST     :: (Ord a) => [a] -> BST a
toBST     = foldr add Leaf

toIncList :: BST a -> IncList a
toIncList (Node x l r) = append x (toIncList l) (toIncList r)
toIncList Leaf         = Emp
