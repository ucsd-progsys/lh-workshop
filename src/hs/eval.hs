{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

--------------------------------------------------------
-- | Boilerplate
--------------------------------------------------------

module Eval (Map, Expr (..), eval, evalTop, evalAny) where

import Prelude hiding (lookup)
import qualified Data.Set as S

{-@ impossible :: {v: _ | false} -> a @-}
impossible :: String -> a
impossible = error

type Env = Map Var Expr

plus :: Expr -> Expr -> Expr
evalTop :: Expr -> Expr
evalAny :: Map Var Expr -> Expr -> Maybe Expr


--------------------------------------------------------
-- | An Associative Map
--------------------------------------------------------

data Map k v = Emp
             | Bind k v (Map k v)
               deriving (Eq, Ord, Show)

--------------------------------------------------------
-- | Set of defined keys
--------------------------------------------------------

{-@ measure keys @-}
keys :: (Ord k) => Map k v -> S.Set k
keys Emp          = S.empty
keys (Bind k _ m) = add k m

--------------------------------------------------------
-- | Empty map without any keys
--------------------------------------------------------

{-@ empty :: {m:_ | noKeys m} @-}
empty :: Map k v
empty = Emp


{-@ inline noKeys @-}
noKeys :: (Ord k) => Map k v -> Bool
noKeys m = keys m == S.empty

--------------------------------------------------------
-- | Membership test (SKIP?)
--------------------------------------------------------

{-@ member :: (Eq k) => k:_ -> m:_ -> {v:Bool | Prop v <=> has k m} @-}
member :: (Eq k) => k -> Map k v -> Bool
member k' (Bind k _ m)
  | k' == k   = True
  | otherwise = member k' m
member _  Emp = False

--------------------------------------------------------
-- | Lookup binding
--------------------------------------------------------

{-@ lookup :: (Eq k) => k:_ -> {m: _ | has k m} -> v @-}
lookup    :: (Eq k) => k -> Map k v -> v
lookup k' (Bind k v m)
  | k' == k   = v
  | otherwise = lookup k' m
lookup _  Emp = impossible "lookup"

{-@ inline has @-}
has :: (Ord k) => k -> Map k v -> Bool
has k m = S.member k (keys m)

--------------------------------------------------------
-- | Insert binding
--------------------------------------------------------

{-@ insert :: k:_ -> _ -> m:_ -> {v: _ | keys v = add k m } @-}
insert :: k -> v -> Map k v -> Map k v
insert = Bind

{-@ inline add @-}
add :: (Ord k) => k -> Map k v -> S.Set k
add k kvs = S.singleton k `S.union` keys kvs

--------------------------------------------------------
-- | Expressions
--------------------------------------------------------

type Var  = String

data Expr = Val  Int
          | Var  Var
          | Plus Expr Expr
          | Let  Var  Expr Expr

--------------------------------------------------------
-- | Values
--------------------------------------------------------

{-@ measure isVal @-}
isVal :: Expr -> Bool
isVal (Val _) = True
isVal _       = False

{-@ type Val = {v:Expr | isVal v} @-}

--------------------------------------------------------
-- | Operating on Values
--------------------------------------------------------

{-@ plus :: Val -> Val -> Val @-}
plus (Val i) (Val j) = Val (i+j)
plus _         _     = impossible "plus"

--------------------------------------------------------
-- | Environments / Stores
--------------------------------------------------------

{-@ type Env = Map Var Val @-}

{-@ eval :: Env -> Expr -> Val @-}
eval _ i@(Val _)     = i
eval g (Var x)       = lookup x g
eval g (Plus e1 e2)  = plus (eval g e1) (eval g e2)
eval g (Let x e1 e2) = eval gx e2
  where
    gx               = insert x v1 g
    v1               = eval g e1


--------------------------------------------------------
-- | Free variables
--------------------------------------------------------

{-@ measure free @-}
free               :: Expr -> S.Set Var
free (Val _)       = S.empty
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

--------------------------------------------------------
-- | Well-scoped Expressions
--------------------------------------------------------

{-@ type ScopedExpr G = {e: Expr | wellScoped G e} @-}

{-@ inline wellScoped @-}
wellScoped :: Env -> Expr -> Bool
wellScoped g e = free e `S.isSubsetOf` keys g


--------------------------------------------------------
-- | Top-level Evaluation
--------------------------------------------------------

{-@ type ClosedExpr = {e: Expr | free e == S.empty} @-}

{-@ evalTop :: ClosedExpr -> Val @-}
evalTop = eval Emp


--------------------------------------------------------
-- | Checked Top-level Evaluation
--------------------------------------------------------

{-@ evalAny :: Env -> Expr -> Maybe Val @-}
evalAny g e
  | ok        = Just $ eval g e
  | otherwise = Nothing
  where
    ok        = wellScoped g e
