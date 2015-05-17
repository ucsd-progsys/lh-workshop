
<div class="slideonly">

 {#measures}
============

Recap
-----

<br>
<br>

1. <div class="fragment">**Refinements:** Types + Predicates</div>
2. <div class="fragment">**Subtyping:** SMT Implication</div>

<br>
<br>

<div class="fragment">
So far: only specify properties of **base values** (e.g. `Int`) ...
</div>

<br>

<div class="fragment">
How to specify properties of **data types**?
</div>

</div>

<div class="hidden">

\begin{code}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--diff"           @-}

module DataTypes where

import Prelude hiding (sum, length, map, filter, foldr, foldr1)

-- map         :: (a -> b) -> List a -> List b
-- foldr1      :: (a -> a -> a) -> List a -> a
-- head        :: List a -> a
-- tail        :: List a -> List a
-- append      :: List a -> List a -> List a
-- filter      :: (a -> Bool) -> List a -> List a
-- impossible         :: String -> a
-- average     :: List Int -> Int
-- yearAverage :: Year Int -> Int
-- wtAverage   :: List (Int, Int) -> Int

infixr 9 :::

{-@ data List [length] a = Emp | (:::) {hd :: a, tl :: List a } @-}
{-@ invariant {v: List a | 0 <= length v} @-}


{-@ type Nat     = {v:Int | v >= 0} @-}
{-@ type Pos     = {v:Int | v >  0} @-}

{-@ impossible :: {v:_ | false} -> a @-}
impossible = error
\end{code}

</div>

<div class="slideonly">

 {#meas}
====================

Data Types
----------

</div>

Data Types
==========

Example: Lists
--------------

<br>

Lets define our own `List` data type:

<br>

\begin{code}
data List a = Emp | (:::) a (List a)
\end{code}


Specifying the Length of a List
-------------------------------

<br>

\begin{code}
{-@ measure length @-}
length :: List a -> Int
length Emp        = 0
length (_ ::: xs) = 1 + length xs
\end{code}

<br>

<div class="fragment">
**Measure**

Haskell function with *one equation per constructor*
</div>

Specifying the Length of a List
-------------------------------

<br>

\begin{spec}
{-@ measure length @-}
length :: List a -> Int
length Emp        = 0
length (_ ::: xs) = 1 + length xs
\end{spec}

<br>

**Measure**

*Strengthens* type of data constructor


Specifying the Length of a List
-------------------------------

<br>
**Measure**

*Strengthens* type of data constructor

<br>

\begin{spec} <div/>
data List a where
  Emp   :: {v: List a | length v = 0}
  (:::) :: x:a -> xs:List a
        -> {v:List a| length v = 1 + length t}
\end{spec}


 {#asdmeas}
===========

Using Measures
--------------

Using Measures
==============

Exercise: *Partial* Functions
-----------------------------


Fear `head` and `tail` no more!

<br>

<div class="fragment">
\begin{code}
head (x ::: _)  = x
head _          = impossible "head"

tail (_ ::: xs) = xs
tail _          = impossible "tail"
\end{code}

<br>

**Q:** Write types for `head` and `tail` that verify `impossible`.
</div>

 {#adasd}
=========

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

