
 {#asdl}
=========

<div class="hidden">

\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}

module InsertSort where

import Prelude hiding (sum, length, map, filter, foldr, foldr1)
import qualified Data.Set as S -- hiding (elems, insert)

-- insert, insertE :: (Ord a) => a -> List a -> List a
-- sort, sortE     :: (Ord a) => [a] -> List a

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
\end{code}
</div>

Case Study: Insertion Sort
--------------------------

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


Case Study: Insertion Sort
==========================

Exercise: `insert`
------------------

**Q:** Lets fix the type of `insert` so `sort` checks?

\begin{code}
{-@ sort :: (Ord a) => xs:[a] -> ListN a {len xs} @-}
sort []     = Emp
sort (x:xs) = insert x (sort xs)

{-@ insert :: (Ord a) => a -> xs:List a -> List a @-}
insert x Emp      = x ::: Emp
insert x (y:::ys)
  | x <= y        = x ::: y ::: ys
  | otherwise     = y ::: insert x ys
\end{code}

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>




Permutation
-----------

<br>

Same *size* is all fine, how about *same *elements* in output?

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


SMT Solvers Reason About Sets
-----------------------------

<div class="fragment">

<br>

Hence, we can write `Set`-valued measures (over `Data.Set` API)

\begin{spec} <div/>
import qualified Data.Set as S
\end{spec}

</div>

Specifying List Elements
------------------------

<br>

\begin{code}
{-@ measure elems @-}
elems :: (Ord a) => List a -> S.Set a
elems Emp      = S.empty
elems (x:::xs) = addElem x xs

{-@ inline addElem @-}
addElem :: (Ord a) => a -> List a -> S.Set a
addElem x xs = S.singleton x `S.union` elems xs
\end{code}

<br>

<div class="fragment">
`inline` lets us use Haskell terms in refinements.
</div>



Multiple Measures
-----------------

Can support *many* measures for a type

Multiple Measures
=================

Example: List Elements
----------------------

Measure describing *set of elements* of a `List`

\begin{code}
{- measure elems @-}
\end{code}

<br>

<div class="fragment">
LiquidHaskell **strengthens** data constructors

\begin{spec}
data L a where
  N :: {v : List a | elems v = empty}
  C :: x:a -> xs:List a
    -> {v: List a | elems v = addElem x xs}
\end{spec}

</div>

Conjoining Refinements
----------------------

Data constructor refinements are **conjoined**

\begin{spec}
data List a where
  N :: {v:List a |  length v = 0
                 && elems  v = empty}
  C :: x:a
    -> xs:List a
    -> {v:List a |  length v = 1 + length xs
                 && elems v  = addElem x  xs }
\end{spec}


Recap
-----

<br>
<br>


1. Refinements: Types + Predicates
2. Subtyping: SMT Implication
3. **Datatypes:** Strengthened Constructors

<br>

<div class="fragment">Automatic Verification of Data Structures</div>

<br>
<br>

