{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module Eval  where

import Prelude hiding (lookup)
import qualified Data.Set as S

{-@ impossible :: {v: _ | false} -> a @-}
impossible = error

plus :: Expr -> Expr -> Expr

type Map k v = [(k, v)]

{-@ empty :: {m:_ | Set_emp (okeys m) }@-}
empty :: Map k v
empty = []

member :: (Eq k) => k -> Map k v -> Bool
member k' ((k,_) : kvs)
  | k' == k   = True
  | otherwise = member k' kvs
member _ []   = False

{-@ lookup    :: (Eq k) => k:k -> {m:Map k v | HasKey k m } -> v @-}
lookup    :: (Eq k) => k -> Map k v -> v
lookup k' ((k,v) : kvs)
  | k' == k   = v
  | otherwise = lookup k' kvs
lookup _   [] = impossible "lookup"

{-@ insert :: k:_ -> _ -> m:_ -> {mm: _ | okeys mm = Set_cup (Set_sng k) (okeys m) } @-}
insert :: k -> v -> Map k v -> Map k v
insert k v kvs = (k, v) : kvs

{- FIX measure keys @-}
-- FIX keys :: (Ord k) => Map k v -> S.Set k
-- FIX keys []       = S.empty
-- FIX keys (kv:kvs) = S.singleton (fst kv) `S.union` keys kvs

{- FIX inline hasKey @-}
-- FIX hasKey :: (Ord k) => k -> Map k v -> Bool
-- FIX hasKey k m = S.member k (okeys m)

-- FIX okeys  ===> keys
-- FIX HasKey ===> hasKey


{-@ predicate HasKey K M = Set_mem K (okeys M) @-}

{-@ measure okeys  :: [(a, b)] -> (S.Set a)
    okeys ([])     = (Set_empty 0)
    okeys (kv:kvs) = (Set_cup (Set_sng (fst kv)) (okeys kvs))
  @-}


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

{-@ eval :: g:Env -> ClosedExpr g -> Val @-}
eval _ i@(Const _)   = i
eval g (Var x)       = lookup x g
eval g (Plus e1 e2)  = plus  (eval g e1) (eval g e2)
eval g (Let x e1 e2) = eval g' e2
  where
    g'               = insert x v1 g
    v1               = eval g e1

{-@ type ClosedExpr G = {v:Expr | Set_sub (free v) (okeys G)} @-}

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



