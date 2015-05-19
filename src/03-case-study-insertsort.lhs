
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

insert, insertE :: (Ord a) => a -> List a -> List a
sort, sortE     :: (Ord a) => List a -> List a

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
==========================


Case Study: Insertion Sort
--------------------------

Recall the simplest sorting algorithm:

<br>

\begin{spec}
sort :: (Ord a) => List a -> List a
sort []           = Emp
sort (x:xs)       = insert x (sort xs)

insert :: (Ord a) => a -> List a -> List a
insert x Emp      = x ::: Emp
insert x (y:::ys)
  | x <= y        = x ::: y ::: ys
  | otherwise     = y ::: insert x ys
\end{spec}


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
--------------------------

<br>

**Goal:** specify & verify that output:

<br>

1. <div class="fragment">Is the same *size* as the input,</div>
2. <div class="fragment">Has the same *elements* as the input,</div>
3. <div class="fragment">Is in *increasing order**.</div>

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

 {#pr1}
=======


Property 1: Size
----------------

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



Property 1: Size
================


Exercise: `insert`
------------------

**Q:** Can you fix the type of `insert` so `sort` checks?

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



Property 2: Elements
====================


Permutation
-----------

<br>

Same *size* is all fine, how about *same elements* in output?

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

Hence, we can write *Set-valued* measures

<br>

Using the `Data.Set` API for convenience

<br>

\begin{spec} <div/>
import qualified Data.Set as S
\end{spec}

</div>


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
`inline` lets us reuse Haskell terms in refinements.
</div>

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

Exercise: Verifying Permutation
----------------------

<br>

Lets verify that `sortE` returns the same set of elements:

<br>

\begin{code}
{-@ type ListE a S = {v:List a | elems v = S }@-}

{-@ sortE :: (Ord a) => xs:List a -> ListE a {elems xs} @-}
sortE Emp         = Emp
sortE (x:::xs)    = insertE x (sortE xs)

{-@ insertE :: (Ord a) => x:a -> xs:List a -> List a @-}
insertE x Emp     = x ::: Emp
insertE x (y:::ys)
  | x <= y        = x ::: y ::: ys
  | otherwise     = y ::: insertE x ys
\end{code}

<br>

**Q:** What is the right type for `insertE`?

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


Property 3: Order
=================

Yes, but does it actually *sort* ?
----------------------------------

<br>

How to specify **ordered lists** ?


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



Specifying Ordered Lists
------------------------










Multiple Measures
=================

Different Measures for `List`
-----------------------------

We just wrote *two* measures for `List`

<br>

+ `length :: List a -> Nat`
+ `elems  :: List a -> Set a`
+ ...

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

Multiple Measures are Conjoined
-------------------------------

Data constructor refinements are **conjoined**

<br>

\begin{spec}
data List a where
  N :: {v:List a |  length v = 0
                 && elems  v = empty}
  C :: x:a
    -> xs:List a
    -> {v:List a |  length v = 1 + length xs
                 && elems v  = addElem x  xs }
\end{spec}

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

Measures vs. Indexed Types
--------------------------

<br>

Unlike [indexed types](http://dl.acm.org/citation.cfm?id=270793), measures ...

<br>

<div class="fragment">

+ **Decouple** properties from data type

+ **Reuse** same data type with different invariants

</div>

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



