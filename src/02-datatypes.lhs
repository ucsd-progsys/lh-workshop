
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
{-# LANGUAGE TupleSections    #-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--diff"           @-}

module DataTypes where

import Prelude hiding (replicate, (++), sum, init, length, map, filter, foldr, foldr1)

map         :: (a -> b) -> List a -> List b
foldr1      :: (a -> a -> a) -> List a -> a
head        :: List a -> a
tail        :: List a -> List a
init, init' :: (Int -> a) -> Int -> List a
-- append      :: List a -> List a -> List a
-- filter      :: (a -> Bool) -> List a -> List a
impossible         :: String -> a
average     :: List Int -> Int
-- wtAverage   :: List (Int, Int) -> Int

infixr 9 :::

{-@ data List [length] a = Emp | (:::) {hd :: a, tl :: List a } @-}
{-@ invariant {v: List a | 0 <= length v} @-}

{-@ type ListNE a = {v:List a | 0 < length v} @-}
{-@ type Nat      = {v:Int | v >= 0} @-}
{-@ type Pos      = {v:Int | v >  0} @-}

{-@ impossible :: {v:_ | false} -> a @-}
impossible = error

{-@ average :: ListNE Int -> Int @-}
average xs = total `div` n
  where
    total   = foldr1 (+) xs
    n       = length xs
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

<div class="fragment">
Lets define our own `List` data type:

<br>

\begin{code}
data List a = Emp | (:::) a (List a)
\end{code}
</div>


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

<div class="slideonly">

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

</div>


Specifying the Length of a List
-------------------------------

<br>

\begin{spec} <div/>
data List a where
  Emp   :: {v:List a | length v = 0}
  (:::) :: x:a -> xs:List a
        -> {v:List a | length v = 1 + length xs}
\end{spec}

<br>

**Measure**

*Strengthens* type of data constructor


<div class="slideonly">

 {#asdmeas}
===========

Using Measures
--------------

</div>

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

<div class="slideonly">

Naming Non-Empty Lists
----------------------

<br>

<div class="fragment">
A convenient *type alias*

<br>

\begin{spec} <div/>
{-@ type ListNE a = {v:List a| 0 < length v} @-}
\end{spec}

</div>


`head` and `tail` are Safe
--------------------------

When called with *non-empty* lists:

<br>

\begin{spec} <div/>
{-@ head :: ListNE a -> a @-}
head (x ::: _)  = x
head _          = impossible "head"

{-@ tail :: ListNE a -> List a @-}
tail (_ ::: xs) = xs
tail _          = impossible "tail"
\end{spec}

</div>



A Useful Partial Function `foldr1`
----------------------------------

*Fold* `f` over list initially using *first* element:

\begin{code}
{-@ foldr1 :: (a -> a -> a) -> ListNE a -> a @-}
foldr1 f (x ::: xs) = foldr f x xs
foldr1 _ _          = impossible "foldr1"

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _ acc Emp        = acc
foldr f acc (x ::: xs) = f x (foldr f acc xs)
\end{code}

</div>

Exercise: `average`
-------------------

<br>

\begin{code}
{-@ average' :: List Int -> Int @-}
average' xs = total `div` n
  where
    total   = foldr1 (+) xs
    n       = length xs
\end{code}

<br>

**Q:** What is a safe input type for `average`?


 {#flasd}
=========

Refining Data Types
-------------------

<br>
<br>

*Making illegal states unrepresentable*

Refining Data Types
===================

Example: Year is 12 Months
--------------------------

<br>

\begin{code}
data Year a = Year (List a)
\end{code}

<br>

<div class="fragment">
**Legal Values:** List of `12` elements

<br>

`"jan" ::: "feb" ::: ... ::: "dec" ::: Emp"`

</div>

Example: Year is 12 Months
--------------------------

**Refine Type to Legal Values**

<br>

\begin{code}
{-@ data Year a = Year (ListN a 12) @-}

-- | An alias for `List`s of size `N`
{-@ type ListN a N = {v:_ | length v == N} @-}
\end{code}
</div>

<br>

<div class="fragment">
*Make illegal states unrepresentable*

\begin{code}
badYear = Year (1 ::: Emp)
\end{code}
</div>

Exercise: `map`
---------------

\begin{code}
{-@ map :: (a -> b) -> xs:List a -> List b @-}
map _ Emp         = Emp
map f (x ::: xs)  = f x ::: map f xs
\end{code}

<br>

<div class="fragment">
**Q:** Can you fix `map` to verify `tempAverage` verifies?

<br>

\begin{code}
data Weather = W { temp :: Int, rain :: Int }

tempAverage :: Year Weather -> Int
tempAverage (Year ms) = average months
  where months        = map temp ms
\end{code}
</div>

Exercise: `init`
----------------

\begin{code}
{-@ init :: (Int -> a) -> Nat -> List a @-}
init _ 0 = Emp
init f n = f n ::: init f (n-1)
\end{code}

<br>

<div class="fragment">
**Q:** Can you fix the type of `init` so the below is safe?

<br>

\begin{code}
sanDiegoWeather :: Year Int
sanDiegoWeather = Year (init (const 72) 12)
\end{code}
</div>

Exercise: `init'`
------------------

\begin{code}
{-@ init' :: (Int -> a) -> n:Nat -> List a @-}
init' f n = go 0
  where
    go i | i < n     = f i ::: go (i+1)
         | otherwise = Emp
\end{code}

<br>

<div class="fragment">
**Q:** For bonus points, fix `init'` so the below is safe?

<br>

\begin{code}
sanDiegoWeather' :: Year Int
sanDiegoWeather' = Year (init' (const 72) 12)
\end{code}
</div>

Recap
-----

<br>
<br>

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. <div class="fragment">**Measures:** Specify Properties of data types</div>

<br>

<div class="fragment">
**Next: Case Studies**

+ [Sorting](03-case-study-insertsort.lhs.slides.html)
+ [Scoping](04-case-study-eval.lhs.slides.html)
+ [Buffering](05-case-study-bytestring.lhs.slides.html)
</div>


