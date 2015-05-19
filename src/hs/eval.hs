{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module Eval  where

import Prelude hiding (lookup)
import qualified Data.Set as S

{-@ impossible :: {v: _ | false} -> a @-}
impossible = error

plus :: Expr -> Expr -> Expr

data Map k v = Emp
             | Bind k v (Map k v)
               deriving (Eq, Ord, Show)

{-@ empty :: {m:_ | noKeys m} @-}
empty :: Map k v
empty = Emp

member :: (Eq k) => k -> Map k v -> Bool
member k' (Bind k _ m)
  | k' == k   = True
  | otherwise = member k' m
member _  Emp = False

{-@ lookup    :: (Eq k) => k:k -> {m: _ | hasKey k m} -> v @-}
lookup    :: (Eq k) => k -> Map k v -> v
lookup k' (Bind k v m)
  | k' == k   = v
  | otherwise = lookup k' m
lookup _  Emp = impossible "lookup"

{-@ insert :: k:_ -> _ -> m:_ -> {v: _ | keys v = addKey k m } @-}
insert :: k -> v -> Map k v -> Map k v
insert = Bind

{-@ measure keys @-}
keys :: (Ord k) => Map k v -> S.Set k
keys Emp          = S.empty
keys (Bind k _ m) = addKey k m

{-@ inline addKey @-}
addKey :: (Ord k) => k -> Map k v -> S.Set k
addKey k kvs = S.singleton k `S.union` keys kvs

{-@ inline hasKey @-}
hasKey :: (Ord k) => k -> Map k v -> Bool
hasKey k m = S.member k (keys m)

{-@ inline noKeys @-}
noKeys :: (Ord k) => Map k v -> Bool
noKeys m = keys m == S.empty

--------------------------------------------------------
-- | Values
--------------------------------------------------------

type Var  = String

data Expr = Const Int
          | Var   Var
          | Plus  Expr Expr
          | Let   Var  Expr Expr

--------------------------------------------------------
-- | Values
--------------------------------------------------------

{-@ measure isVal @-}
isVal :: Expr -> Bool
isVal (Const _) = True
isVal _         = False

{-@ type Val = {v:Expr | isVal v} @-}

--------------------------------------------------------
-- | Operating on Values
--------------------------------------------------------

{-@ plus                 :: Val -> Val -> Val @-}
plus (Const i) (Const j) = Const (i+j)
plus _         _         = impossible "plus"

--------------------------------------------------------
-- | Environments / Stores
--------------------------------------------------------

{-@ type Env = Map Var Val @-}

{-@ eval :: g:Env -> ScopedExpr g -> Val @-}
eval _ i@(Const _)   = i
eval g (Var x)       = lookup x g
eval g (Plus e1 e2)  = plus  (eval g e1) (eval g e2)
eval g (Let x e1 e2) = eval g' e2
  where
    g'               = insert x v1 g
    v1               = eval g e1

{-@ type ScopedExpr G = {e: Expr | wellScoped G e} @-}

{-@ inline wellScoped @-}
wellScoped g e = free e `S.isSubsetOf` keys g

{-@ measure free @-}
free               :: Expr -> S.Set Var
free (Const _)     = S.empty
free (Var x)       = S.singleton x
free (Plus e1 e2)  = xs1 `S.union`  xs2
  where
    xs1            = free e1
    xs2            = free e2
free (Let x e1 e2) = xs1 `S.union` (xs2 `S.difference` xs)
  where
    xs1            = free e1
    xs2            = free e2
    xs             = S.singleton x



