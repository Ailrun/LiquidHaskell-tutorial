{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--no-termination" @-}
module Code09 where

import Prelude hiding (replicate, take, length)

{-@ die :: {v:String | false} -> a @-}
die x = error x

data SList a = SL { size :: Int, elems :: [a] }

{-@ measure realSize @-}
realSize      :: [a] -> Int
realSize []     = 0
realSize (_:xs) = 1 + realSize xs

{-@ data SList a = SL {
      size  :: Nat
    , elems :: {v:[a] | realSize v = size}
    }
@-}

okList  = SL 1 ["cat"]    -- accepted

{-@ fail badList @-}
badList = SL 1 []         -- rejected

{-@ type SListN a N = {v:SList a | size v = N} @-}

{-@ nil :: SListN a 0 @-}
nil = SL 0 []

{-@ cons :: a -> xs:SList a -> SListN a {size xs + 1} @-}
cons x (SL n xs) = SL (n+1) (x:xs)

{-@ type SListNE a = {v:SList a | size v > 0} @-}

{-@ tl           :: xs:SListNE a -> SListN a {size xs - 1}  @-}
tl (SL n (_:xs)) = SL (n-1) xs
tl _             = die "empty SList"

{-@ hd           :: xs:SListNE a -> a @-}
hd (SL _ (x:_))  = x
hd _             = die "empty SList"

{-@ okList :: SListN String 1 @-}

okHd  = hd okList       -- accepted

{-@ fail badHd @-}
badHd = hd (tl okList)  -- rejected

{-@ data Queue a = Q {
      front :: SList a
    , back  :: SListLE a (size front)
    }
@-}
data Queue a = Q
  { front :: SList a
  , back  :: SList a
  }

{-@ type SListLE a N = {v:SList a | size v <= N} @-}

okQ  = Q okList nil  -- accepted, |front| > |back|

{-@ fail badQ @-}
badQ = Q nil okList  -- rejected, |front| < |back|

emp = Q nil nil

{-@ remove :: xs:QueueNE a -> (a, QueueN a {qSize xs - 1}) @-}
remove (Q f b)   = (hd f, makeq (tl f) b)

{-@ measure qSize @-}
qSize :: Queue a -> Int
qSize (Q f b) = size f + size b

-- | Queues of size `N`
{-@ type QueueN a N = {v:Queue a | qSize v = N } @-}

{-@ type QueueNE a = {v:Queue a | qSize v > 0 } @-}

okRemove  = remove example2Q   -- accept
{-@ fail badRemove @-}
badRemove = remove example0Q   -- reject

{-@ emp :: QueueN _ 0 @-}

{-@ example2Q :: QueueN _ 2 @-}
example2Q = Q (1 `cons` (2 `cons` nil)) nil

{-@ example0Q :: QueueN _ 0 @-}
example0Q = Q nil nil

{-@ insert :: a -> xs:Queue a -> QueueN a {qSize xs + 1} @-}
insert e (Q f b) = makeq f (e `cons` b)

{-@ replicate :: n:Nat -> a -> QueueN a n @-}
replicate :: Int -> a -> Queue a
replicate 0 _ = emp
replicate n x = insert x (replicate (n-1) x)

{-@ okReplicate :: QueueN _ 3 @-}
okReplicate = replicate 3 "Yeah!"  -- accept

{-@ fail badReplicate @-}
{-@ badReplicate :: QueueN _ 3 @-}
badReplicate = replicate 1 "No!"   -- reject

{-@ makeq :: f:SList a -> b:SListLE a {size f + 1} -> QueueN a {size f + size b} @-}
makeq f b
  | size b <= size f = Q f b
  | otherwise        = Q (rot f b nil) nil

{-@ rot :: f:SList a -> b:SListN a {size f + 1} -> acc:SList a -> SListN a {size f + size b + size acc} @-}
rot :: SList a -> SList a -> SList a -> SList a
rot f b acc
  | size f == 0 = hd b `cons` acc
  | otherwise   = hd f `cons` rot (tl f) (tl b) (hd b `cons` acc)

{-@ type QueueGE a N = {v:Queue a | qSize v >= N}@-}

{-@ take       :: n:Nat -> xs:QueueGE a n -> (QueueN a n, QueueN a {qSize xs - n}) @-}
take           :: Int -> Queue a -> (Queue a, Queue a)
take 0 q       = (emp          , q)
take n q       = (insert x out , q'')
  where
    (x  , q')  = remove q
    (out, q'') = take (n-1) q'

{-@ okTake :: (QueueN _ 2, QueueN _ 1) @-}
okTake   = take 2 exampleQ  -- accept

{-@ fail badTake @-}
badTake  = take 10 exampleQ -- reject

{-@ exampleQ :: QueueN _ 3 @-}
exampleQ = insert "nal" $ insert "bob" $ insert "alice" $ emp
