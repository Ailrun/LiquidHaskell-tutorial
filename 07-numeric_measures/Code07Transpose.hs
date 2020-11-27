{-@ LIQUID "--no-termination" @-}
-- | This does not work in the Code07 module somehow...
-- separate this to reduce the required computing resource
module Code07Transpose where

import Code07

{-@ matProduct :: (Num a) => x:Matrix a
                          -> y:{Matrix a | mCol x = mRow y}
                          -> MatrixN a (mRow x) (mCol y)
  @-}
matProduct (M rx _ xs) my@(M _ cy _)
                 = M rx cy elts
  where
    elts         = for xs (\xi ->
                     for ys' (\yj ->
                       dotProduct xi yj
                     )
                   )
    M _ _ ys'    = transpose my

-- >>> ok32 == transpose ok23
-- True
ok32 = M 3 2 (V 3 [ V 2 [1, 4]
                  , V 2 [2, 5]
                  , V 2 [3, 6] ])

{-@ transpose :: m:Matrix a -> MatrixN a (mCol m) (mRow m) @-}
transpose (M r c rows) = M c r $ txgo c r rows

{-@ txgo      :: c:Nat -> r:Nat
              -> VectorN (VectorN a c) r
              -> VectorN (VectorN a r) c
  @-}
txgo :: Int -> Int -> Vector (Vector a) -> Vector (Vector a)
txgo c r rows
  | 0 < c     = vCons (for rows vHd) (txgo (c - 1) r (for rows vTl))
  | otherwise = vEmp
