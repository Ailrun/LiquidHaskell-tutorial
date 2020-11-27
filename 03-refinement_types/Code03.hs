{-@ LIQUID "--no-termination" @-}
module Code03 where

import Prelude hiding (abs)

{-@ type Zero    = {v:Int | v == 0} @-}
{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ zero :: Zero @-}
zero  = 0 :: Int

{-@ one, two, three :: NonZero @-}
one   = 1 :: Int
two   = 2 :: Int
three = 3 :: Int

-- nonsense :: Int
-- nonsense = one'
--   where
--   {-@ one' :: Zero @-}
--   one' = 1

{-@ type Nat   = {v:Int | 0 <= v}        @-}
{-@ type Even  = {v:Int | v mod 2 == 0 } @-}
{-@ type Lt100 = {v:Int | v < 100}       @-}

{-@ zero' :: Nat @-}
zero'     = zero

{-@ zero'' :: Even @-}
zero''    = zero

{-@ zero''' :: Lt100 @-}
zero'''    = zero

{-@ die :: {v:String | false} -> a  @-}
die msg = error msg

cannotDie = if 1 + 1 == 3
              then die "horrible death"
              else ()

-- canDie = if 1 + 1 == 2
--            then die "horrible death"
--            else ()

-- divide'     :: Int -> Int -> Int
-- divide' n 0 = die "divide by zero"
-- divide' n d = n `div` d

{-@ divide :: Int -> NonZero -> Int @-}
divide :: Int -> Int -> Int
divide _ 0 = die "divide by zero"
divide n d = n `div` d

avg2 x y   = divide (x + y) 2
avg3 x y z = divide (x + y + z) 3

{-@ avg :: {v:[Int] | len v > 0} -> Int @-}
avg       :: [Int] -> Int
avg xs    = divide total n
  where
    total = sum xs
    n     = length xs

abs           :: Int -> Int
abs n
  | 0 < n     = n
  | otherwise = 0 - n

{-@ abs :: Int -> Nat @-}

calc = do putStrLn "Enter numerator"
          n <- readLn
          putStrLn "Enter denominator"
          d <- readLn
          putStrLn (result n d)
          calc

result n d
  | isPositive d = "Result = " ++ show (n `divide` d)
  | otherwise    = "Humph, please enter positive denominator!"

isPositive :: Int -> Bool
isPositive x = x > 0
{-@ isPositive :: x:Int -> {v:Bool | v <=> x > 0} @-}
-- -- Safe but not preferable type
-- {-@ isPositive :: x:Nat -> {v:Bool | v <=> x /= 0} @-}

{-@ lAssert  :: {v:Bool | v} -> a -> a @-}
lAssert True  x = x
lAssert False _ = die "yikes, assertion fails!"

yes = lAssert (1 + 1 == 2) ()
-- no  = lAssert (1 + 1 == 3) ()

truncate :: Int -> Int -> Int
truncate i max
  | i' <= max' = i
  | otherwise  = max' * (i `divide` i')
    where
      i'       = abs i
      max'     = abs max
