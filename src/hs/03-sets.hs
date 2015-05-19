{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}

module InsertSort where

import Prelude hiding (sum, length, map, filter, foldr, foldr1)
import qualified Data.Set as S

insert, insertE :: (Ord a) => a -> List a -> List a
sort, sortE     :: (Ord a) => [a] -> List a

{-@ measure length @-}
length :: List a -> Int
length Emp        = 0
length (_ ::: xs) = 1 + length xs

data List a = Emp
            | (:::) { hd :: a, tl :: List a }
            deriving (Eq, Ord, Show)

infixr 9 :::

-- | Lists of a given size N
{-@ type ListN a N = {v:List a | length v == N } @-}

-----------------------------------------------------------------------
-- | Size Preserving Insert Sort
-----------------------------------------------------------------------

{-@ sort :: (Ord a) => xs:[a] -> ListN a {len xs} @-}
sort []     = Emp
sort (x:xs) = insert x (sort xs)

{-@ insert :: (Ord a) => a -> xs:List a -> ListN a {1 + length xs} @-}
insert x Emp      = x ::: Emp
insert x (y:::ys)
  | x <= y        = x ::: y ::: ys
  | otherwise     = y ::: insert x ys

-----------------------------------------------------------------------
-- | Elements Preserving Insert Sort
-----------------------------------------------------------------------

{-@ measure elems @-}
elems :: (Ord a) => List a -> S.Set a
elems Emp      = S.empty
elems (x:::xs) = addElem x xs

{-@ inline addElem @-}
addElem :: (Ord a) => a -> List a -> S.Set a
addElem x xs = S.singleton x `S.union` elems xs

{-@ type ListE a S = {v:List a | elems v = S }@-}

{-@ sortE ::  xs:[a] -> ListE a {listElts xs}   @-}
sortE []     = Emp
sortE (x:xs) = insertE x (sortE xs)

{-@ insertE :: (Ord a) => x:a -> xs:List a -> ListE a {addElem x xs} @-}
insertE x Emp     = x ::: Emp
insertE x (y:::ys)
  | x <= y        = x ::: y ::: ys
  | otherwise     = y ::: insertE x ys

-----------------------------------------------------------------------
-- | A List Data Type
-----------------------------------------------------------------------

{-@ data List a = Emp
                | (:::) { hd :: a
                        , tl :: List {v:a | hd <= v} }
  @-}


okList :: List Int
okList = 1 ::: 2 ::: 3 ::: Emp

badList :: List Int
badList = 1 ::: 3 ::: 2 ::: Emp



