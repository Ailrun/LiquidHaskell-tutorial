{-@ LIQUID "--no-termination" @-}
module Code07 where

import Prelude   hiding (map, zipWith, zip, take, drop, reverse)
import Data.Maybe       (isJust, fromJust)

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

data Vector a = V { vDim  :: Int
                  , vElts :: [a]
                  }
              deriving (Eq)

data Matrix a = M { mRow  :: Int
                  , mCol  :: Int
                  , mElts :: Vector (Vector a)
                  }
              deriving (Eq)

{-@ ignore dotProd @-}
dotProd       :: (Num a) => Vector a -> Vector a -> a
dotProd vx vy = sum (prod xs ys)
  where
    prod      = zipWith (\x y -> x * y)
    xs        = vElts vx
    ys        = vElts vy

{-@ ignore matProd @-}
matProd       :: (Num a) => Matrix a -> Matrix a -> Matrix a
matProd (M rx _ xs) (M _ cy ys)
              = M rx cy elts
  where
    elts      = for xs (\xi ->
                  for ys (\yj ->
                    dotProd xi yj
                  )
                )

{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size        :: [a] -> Int
size []     = 0
size (_:rs) = 1 + size rs

{-@ measure notEmpty @-}
notEmpty       :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True

type List a = [a]
{-@ type ListN a N = {v:List a | size v = N} @-}
{-@ type ListX a X = ListN a {size X}        @-}

{-@ map      :: (a -> b) -> xs:List a -> ListX b xs @-}
map _ []     = []
map f (x:xs) = f x : map f xs

{-@ prop_map :: List a -> TRUE @-}
prop_map xs = size ys == size xs
  where
    ys      = map id xs

{-@ reverse       :: xs:List a -> ListX a xs @-}
reverse xs        = go [] xs
  where
    {-@ go :: xs:List a -> ys:List a -> ListN a {size xs + size ys} @-}
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs

{-@ zipWith :: (a -> b -> c) -> xs:List a
                             -> ListX b xs
                             -> ListX c xs
  @-}
zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
zipWith _ [] []         = []
zipWith _ _  _          = die "no other cases"

{-@ zip :: as:[a] -> bs:[b] -> {v:[(a,b)] | Tinier v as bs} @-}
zip (a:as) (b:bs) = (a, b) : zip as bs
zip [] _          = []
zip _  []         = []

{-@ predicate Tinier X Y Z = Min (size X) (size Y) (size Z) @-}
{-@ predicate Min X Y Z = (if Y < Z then X = Y else X = Z)  @-}

{-@ type ListXOrNull a X = {v:List a | size v = 0 || size X = 0 || size v = size X} @-}

{-@ zipOrNull :: xs:List a -> ys:ListXOrNull b xs -> {v:List (a, b) | Tinier v xs ys} @-}
zipOrNull       :: [a] -> [b] -> [(a, b)]
zipOrNull [] _  = []
zipOrNull _ []  = []
zipOrNull xs ys = zipWith (,) xs ys

{-@ test1 :: {v: _ | size v = 2} @-}
test1     = zipOrNull [0, 1] [True, False]

{-@ test2 :: {v: _ | size v = 0} @-}
test2     = zipOrNull [] [True, False]

{-@ test3 :: {v: _ | size v = 0} @-}
test3     = zipOrNull ["cat", "dog"] []

{-@ take'      :: n:Nat -> ListGE a n -> ListN a n @-}
take'          :: Int -> [a] -> [a]
take' 0 _      = []
take' n (x:xs) = x : take' (n-1) xs
take' _ _      = die "won't  happen"

{-@ type ListGE a N = {v:List a | N <= size v} @-}

{-@ drop :: n:Nat -> xs:ListGE a n -> ListN a {size xs - n} @-}
drop :: Int -> [a] -> [a]
drop 0 xs     = xs
drop n (_:xs) = drop (n-1) xs
drop _ _      = die "won't happen"

{-@ test4 :: ListN String 2 @-}
test4 = drop 1 ["cat", "dog", "mouse"]

{-@ take :: n:Nat -> xs:List a -> {v:List a | Min (size v) n (size xs)} @-}
take :: Int -> [a] -> [a]
take 0 _       = []
take _ []      = []
take n (x:xs)  = x : take (n-1) xs

{-@ test5 :: [ListN String 2] @-}
test5 = [ take 2  ["cat", "dog", "mouse"]
        , take 20 ["cow", "goat"]        ]

partition          :: (a -> Bool) -> [a] -> ([a], [a])
partition _ []     = ([], [])
partition f (x:xs)
  | f x            = (x:ys, zs)
  | otherwise      = (ys, x:zs)
  where
    (ys, zs)       = partition f xs
{-@ partition :: _ -> xs:_ -> {v:_ | Sum2 v (size xs)} @-}

{-@ predicate Sum2 X N = size (fst X) + size (snd X) = N @-}

-- >> quickSort [1,4,3,2]
-- [1,2,3,4]
{-@ quickSort    :: (Ord a) => xs:List a -> ListX a xs @-}
quickSort []     = []
quickSort (x:xs) = l' `append` [x] `append` r'
  where
    l'     = quickSort l
    r'     = quickSort r
    (l, r) = partition (< x) xs

{-@ append       :: xs:List a -> ys:List a -> {v:List a | size xs + size ys == size v} @-}
append [] ys     = ys
append (x:xs) ys = x : append xs ys

{-@ test10 :: ListN String 2 @-}
test10 = quickSort (drop 1 ["cat", "dog", "mouse"])

{-@ data Vector a = V { vDim  :: Nat
                      , vElts :: ListN a vDim }         
  @-}

okVec  = V 2 [10, 20]       -- accepted by LH
{-@ fail badVec @-}
badVec = V 2 [10, 20, 30]   -- rejected by LH

-- | Non Empty Vectors
{-@ type VectorNE a  = {v:Vector a | vDim v > 0} @-}

-- | Vectors of size N
{-@ type VectorN a N = {v:Vector a | vDim v = N} @-}

-- | Vectors of Size Equal to Another Vector X
{-@ type VectorX a X = VectorN a {vDim X}        @-}

{-@ vEmp :: VectorN a 0 @-}
vEmp = V 0 []

{-@ vCons :: a -> x:Vector a -> VectorN a {vDim x + 1} @-}
vCons x (V n xs) = V (n+1) (x:xs)

{-@ vHd :: VectorNE a -> a @-}
vHd (V _ (x:_))  = x
vHd _            = die "nope"

{-@ vTl          :: x:VectorNE a -> VectorN a {vDim x - 1} @-}
vTl (V n (_:xs)) = V (n-1) xs
vTl _            = die "nope"

{-@ for        :: x:Vector a -> (a -> b) -> VectorX b x @-}
for (V n xs) f = V n (map f xs)

{-@ vBin :: (a -> b -> c) -> x:Vector a
                          -> VectorX b x
                          -> VectorX c x
  @-}
vBin op (V n xs) (V _ ys) = V n (zipWith op xs ys)

{-@ dotProduct :: (Num a) => x:Vector a -> VectorX a x -> a @-}
dotProduct x y = sum $ vElts $ vBin (*) x y

{-@ vecFromList :: xs:List a -> VectorN a (size xs) @-}
vecFromList     :: [a] -> Vector a
vecFromList xs  = V (size xs) xs

test6  = dotProduct vx vy    -- should be accepted by LH
  where
    vx = vecFromList [1,2,3]
    vy = vecFromList [4,5,6]

{-@ flatten :: n:Nat
            -> m:Nat
            -> VectorN (VectorN a m) n
            -> VectorN a {m * n}
  @-}
flatten :: Int -> Int -> Vector (Vector a) -> Vector a
flatten _ _ (V _ []) = V 0 []
flatten n m (V _ ((V _ xs):vs)) = V (m * n) (xs `append` xss)
  where
    V _ xss = flatten (n - 1) m (V (n - 1) vs)

{-@ product   :: xs:Vector _
              -> ys:Vector _
              -> VectorN _ {vDim xs * vDim ys}
  @-}
product xs ys = flatten (vDim ys) (vDim xs) xys
  where
    xys       = for ys $ \y ->
                  for xs $ \x ->
                    x * y

{-@ data Matrix a =
      M { mRow  :: Pos
        , mCol  :: Pos
        , mElts :: VectorN (VectorN a mCol) mRow
        }
  @-}

{-@ type Pos = {v:Int | 0 < v} @-}

{-@ type MatrixN a R C   = {v:Matrix a | Dims v R C } @-}
{-@ predicate Dims M R C = mRow M = R && mCol M = C   @-}

{-@ ok23 :: MatrixN _ 2 3 @-}
ok23     = M 2 3 (V 2 [ V 3 [1, 2, 3]
                      , V 3 [4, 5, 6] ])

{-@ fail bad1 @-}
bad1 :: Matrix Int
bad1 = M 2 3 (V 2 [ V 3 [1, 2   ]
                  , V 3 [4, 5, 6]])

{-@ fail bad2 @-}
bad2 :: Matrix Int
bad2 = M 2 3 (V 2 [ V 2 [1, 2]
                  , V 2 [4, 5] ])

{-@ matFromList  :: xs:List (List _) -> Maybe ({v:MatrixN _ (size xs) (size (head xs)) | 0 < size xs && 0 < size (head xs) }) @-}
matFromList      :: [[a]] -> Maybe (Matrix a)
matFromList []   = Nothing
matFromList xss@(xs:_)
  | ok           = Just (M r c vs)
  | otherwise    = Nothing
  where
    r            = size xss
    c            = size xs
    ok           = 0 < r && 0 < c && isJust mayXss
    vs           = vecFromList (map vecFromList (fromJust mayXss))

    mayXss       = convert c xss

    {-@ convert :: c:Nat -> xs:List (List _) -> Maybe (ListX (ListN _ c) xs) @-}
    convert _ []        = Just []
    convert c (xs : xss)
      | size xs == c    = (xs :) <$> convert c xss
      | otherwise       = Nothing

{-@ mat23 :: Maybe (MatrixN Integer 2 2) @-}
mat23     = matFromList [ [1, 2]
                        , [3, 4] ]
