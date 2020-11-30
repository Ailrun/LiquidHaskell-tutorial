{-@ LIQUID "--no-termination" @-}
module Code10 where

import Data.Set hiding (elems)

{-@ die :: {v:_ | false} -> a @-}
die x   = error x

type Var  = String

data Expr = Const Int
          | Var   Var
          | Plus  Expr Expr
          | Let   Var  Expr Expr
          | Fun   Var  Expr
          | App   Expr Expr

{-@ measure val @-}
val             :: Expr -> Bool
val (Const _)   = True
val (Var _)     = False
val (Plus _ _)  = False
val (Let _ _ _) = False
val (Fun _ _)   = True
val (App _ _)   = False

{-@ type Val = {v:Expr | val v} @-}

{-@ plus                 :: Val -> Val -> Val @-}
plus (Const i) (Const j) = Const (i+j)
plus (Fun _ _) (Const _) = undefined
plus (Const _) (Fun _ _) = undefined
plus (Fun _ _) (Fun _ _) = undefined
plus _         _         = die "Bad call to plus"

{-@ type Env = Map Var Val @-}

{-@ eval :: g:Env -> ClosedExpr g -> Val @-}
eval :: Map Var Expr -> Expr -> Expr
eval _ i@(Const _)   = i
eval g (Var x)       = get x g
eval g (Plus e1 e2)  = plus (eval g e1) (eval g e2)
eval g (Let x e1 e2) = eval g' e2
  where
    g'               = set x v1 g
    v1               = eval g e1
eval _ i@(Fun _ _)   = i
eval g (App e1 e2)   =
  case eval g e1 of
    Fun x e
      | g' <- set x v2 g,
        free e `isSubsetOf` keys g' ->
        eval g' e
    _       -> undefined
  where
    v2 = eval g e2

{-@ measure free @-}
free               :: Expr -> Set Var
free (Const _)     = empty
free (Var x)       = singleton x
free (Plus e1 e2)  = xs1 `union` xs2
  where
    xs1            = free e1
    xs2            = free e2
free (Let x e1 e2) = fv1 `union` (fv2 `difference` xs)
  where
    fv1            = free e1
    fv2            = free e2
    xs             = singleton x
free (Fun x e)     = fv `difference` xs
  where
    fv             = free e
    xs             = singleton x
free (App e1 e2)   = fv1 `union` fv2
  where
    fv1            = free e1
    fv2            = free e2

{-@ type ClosedExpr G = {v:Expr | Set_sub (free v) (keys G)} @-}

{-@ topEval :: {v:Expr | Set_emp (free v)} -> Val @-}
topEval     = eval emp

{-@ evalAny   :: Env -> Expr -> Maybe Val @-}
evalAny g e
  | ok        = Just $ eval g e
  | otherwise = Nothing
  where
    ok        = free e `isSubsetOf` keys g

{-@ ignore tests @-}
tests   = [v1, v2]
  where
    v1  = topEval e1          -- Rejected by LH
    v2  = topEval e2          -- Accepted by LH
    e1  = Var x `Plus` c1
    e2  = Let x c10 e1
    x   = "x"
    c1  = Const 1
    c10 = Const 10

data Map k v = Node { key   :: k
                    , value :: v
                    , left  :: Map k v
                    , right :: Map k v }
             | Tip

{-@ data Map k v = Node { key   :: k
                        , value :: v
                        , left  :: Map {v:k | v < key} v
                        , right :: Map {v:k | key < v} v }
                 | Tip
  @-}

{-@ measure keys @-}
keys                :: (Ord k) => Map k v -> Set k
keys Tip            = empty
keys (Node k _ l r) = ks `union` kl `union` kr
  where
    kl              = keys l
    kr              = keys r
    ks              = singleton k

{-@ emp :: {m:Map k v | Set_emp (keys m)} @-}
emp     = Tip

{-@ set :: (Ord k) => k:k -> v -> m:Map k v
                   -> {n: Map k v | keys n = Set_cup (Set_sng k) (keys m)} @-}
set :: (Ord k) => k -> v -> Map k v -> Map k v
set k' v' (Node k v l r)
  | k' == k   = Node k v' l r
  | k' <  k   = Node k v (set k' v' l) r
  | otherwise = Node k v l (set k' v' r)
set k' v' Tip = Node k' v' Tip Tip

{-@ ignore get' @-}
{-@ get' :: (Ord k) => k:k -> m:{Map k v| Set_mem k (keys m)} -> v @-}
get' :: (Ord k) => k -> Map k v -> v
get' k' m@(Node k v l r)
  | k' == k   = v
  | k' <  k   = get' k' l
  | otherwise = get' k' r
get'  _ Tip   = die  "Lookup Never Fails"

{-@ lemma_notMem :: key:k
                 -> m:Map {k:k | k /= key} v
                 -> {v:Bool | not (Set_mem key (keys m))}
  @-}
lemma_notMem     :: k -> Map k v -> Bool
lemma_notMem _   Tip            = True
lemma_notMem key (Node _ _ l r) = lemma_notMem key l &&
                                  lemma_notMem key r

{-@ get :: (Ord k) => k:k -> m:{Map k v | Set_mem k (keys m)} -> v @-}
get :: (Ord k) => k -> Map k v -> v
get k' (Node k v l r)
  | k' == k   = v
  | k' <  k   = assert (lemma_notMem k' r) $
                  get k' l
  | otherwise = assert (lemma_notMem k' l) $
                  get k' r
get _ Tip     = die "Lookup failed? Impossible."

assert _ x = x

{-@ mem :: (Ord k) => k:k -> m:Map k v
                   -> {v:_ | v <=> Set_mem k (keys m)} @-}
mem :: (Ord k) => k -> Map k v -> Bool
mem k' (Node k _ l r)
  | k' == k   = True
  | k' <  k   = assert (lemma_notMem k' r) $ mem k' l
  | otherwise = assert (lemma_notMem k' l) $ mem k' r
mem _ Tip     = False

{-@ fresh :: xs:[Int] -> {v:Int | not (Elem v xs)} @-}
fresh :: [Int] -> Int
fresh xs = freshFrom xs xs 0
  where
    {-@ freshFrom    :: xs:[Int]
                     -> ys:[Int]
                     -> {v:Int | not (Set_mem v (Set_dif (elems xs) (elems ys)))}
                     -> {v:Int | not (Set_mem v (elems xs))}@-}
    freshFrom        :: [Int] -> [Int] -> Int -> Int
    freshFrom _ [] z = z
    freshFrom xs (y:ys) z
      | y == z       = freshFrom xs xs (z+1)
      | otherwise    = freshFrom xs ys z

{-@ predicate Elem X Ys  = Set_mem X (elems Ys) @-}
{-@ measure elems @-}
elems []     = empty
elems (x:xs) = (singleton x) `union` (elems xs)
