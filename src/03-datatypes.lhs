<div class="hidden">

\begin{code}
{-# LANGUAGE TupleSections    #-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}
{- LIQUID "--totality"       @-} -- totality does not play well with record selectors
{-@ LIQUID "--diff"           @-}

module DataTypes where

import Prelude hiding (length, sum)
import qualified Data.Set as S -- hiding (elems, insert)


head       :: List a -> a
tail       :: List a -> List a
impossible :: String -> a
avg        :: List Int -> Int
insert     :: (Ord a) =>  a -> List a -> List a


sum :: List Int -> Int 
sum Emp = 0 
sum (x ::: xs) = x + sum xs
infixr 9 :::
infixr 9 :<:

{-@ data List [length] a = Emp | (:::) {hd :: a, tl :: List a } @-}
{-@ invariant {v: List a | 0 <= length v} @-}

{-@ type Nat      = {v:Int | v >= 0} @-}
{-@ type Pos      = {v:Int | v >  0} @-}

{-@ impossible :: {v:_ | false} -> a @-}
impossible = error

{-@ safeDiv :: Int -> {v:Int | v /= 0} -> Int   @-}
safeDiv :: Int -> Int -> Int 
safeDiv _ 0 = impossible "divide-by-zero"
safeDiv x n = x `div` n

\end{code}

</div>

<br>
<br>
<br>
<br>
<br>



Data Types
==========

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
<br>
<br>
<br>
<br>
<br>
<br>


Example: Lists
--------------

<br>

<div class="fragment">
Lets define our own `List` data type:

<br>

\begin{code}
data List a = Emp               -- Nil
            | (:::) a (List a)  -- Cons
\end{code}
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



Specifying the Length of a List
-------------------------------

<br>

<div class="fragment">
**Measure**

Haskell function with *a single equation per constructor*
</div>

<br>

\begin{code}
{-@ measure length @-}
length :: List a -> Int
length Emp        = 0
length (_ ::: xs) = 1 + length xs
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



Specifying the Length of a List
-------------------------------


<br>

**Measure**

*Strengthens* type of data constructor

<br>

<div class="fragment">

\begin{spec} <div/>
data List a where

  Emp   :: {v:List a | length v = 0}

  (:::) :: x:a -> xs:List a
        -> {v:List a | length v = 1 + length xs}
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


Using Measures
==============

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
<br>
<br>
<br>





Example: *Partial* Functions
-----------------------------

<br>

Fear `head` and `tail` no more!

<div class="fragment">
\begin{code}
{-@ head        :: List a -> a @-}
head (x ::: _)  = x
head _          = impossible "head"

{-@ tail        :: List a -> List a @-}
tail (_ ::: xs) = xs
tail _          = impossible "tail"
\end{code}

<br> <br>

**Q:** Write types for `head` and `tail` that verify `impossible`.
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

Naming Non-Empty Lists
----------------------

<br>

A convenient *type alias*

<br>

\begin{code}
{-@ type ListNE a = {v:List a| 0 < length v} @-}
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

<div class="slideonly">

`head` and `tail` are Safe
--------------------------

When called with *non-empty* lists:

<br>

\begin{spec}
{-@ head :: ListNE a -> a @-}
head (x ::: _)  = x
head _          = impossible "head"

{-@ tail :: ListNE a -> List a @-}
tail (_ ::: xs) = xs
tail _          = impossible "tail"
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

Back to `average`
---------------------------------

<br>

\begin{code}
{-@ avg    :: List Int -> Int @-}
avg xs     = safeDiv total n
  where
    total  = sum    xs
    n      = length xs         -- returns a Nat
\end{code}

<br> 
**Q:** Write type for `avg` that verifies safe division.



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


Multiple Measures
=================

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

Specifying A `List`s Elements
-----------------------------

<br>

\begin{code}
{-@ measure elems @-}
elems :: (Ord a) => List a -> S.Set a
elems Emp      = S.empty
elems (x:::xs) = addElem x xs

{-@ inline addElem @-}
addElem :: (Ord a) => a -> List a -> S.Set a
addElem x xs = S.union (S.singleton x) (elems xs)
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


Multiple Measures
-------------------------------

<br>

*Strengthens* type of data constructor

<br>

<div class="fragment">

\begin{spec} <div/>
data List a where

  Emp   :: {v:List a | length v == 0 
                     && elems v == S.empty}


  (:::) :: x:a -> xs:List a
        -> {v:List a | length v == 1 + length xs
                     && elems v == addElem v xs  }
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


Example : Inserting Elements
----------------------------

<br>
\begin{code}
{-@ insert :: x:a -> xs:List a 
           -> {v : List a | length v == length xs + 1
                          && elems v == addElem x xs  } @-}

insert x Emp = x ::: Emp
insert x (y ::: ys)
  | x <= y    = x ::: y ::: ys
  | otherwise = y ::: insert x ys 
\end{code}

<br>
<br>

Can we specify **sortedness**?

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




Refining Data Types
===================


<br>
<br>

&nbsp; &nbsp; *Make illegal states unrepresentable*

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



Example: Sorted Lists
----------------------

<br>

Lets **define** a type for ordered lists

<br>

\begin{code}
data OList a =
      OEmp
    | (:<:) { oHd :: a
            , oTl :: OList a }
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


Ordered Lists
-------------

<br>

Lets **refine** the type to enforce **order**

<br>

\begin{code}
{-@ data OList a =
      OEmp
    | (:<:) { oHd :: a
            , oTl :: OList {v:a | oHd <= v}} @-}
\end{code}

<br>

Head `oHd` is **smaller than every value** `v` in tail `oTl`



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


Ordered Lists
-------------

<br>

*Illegal values unrepresentable*

<br>

\begin{code}
okList :: OList Int
okList = 1 :<: 2 :<: 3 :<: OEmp

badList :: OList Int
badList = 1 :<: 3 :<: 2 :<: OEmp
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


Exercise: Insertion Sort
------------------------

<br>

**Q:** Oops. There's a problem! Can you fix it?

<br>

\begin{code}
{-@ sortO ::  xs:List a -> OList a @-}
sortO Emp      = OEmp
sortO (x:::xs) = insertO x (sortO xs)

{-@ insertO :: x:a -> xs:_  -> OList a @-}
insertO x (y :<: ys)
  | x <= y     = y :<: x :<: ys
  | otherwise  = y :<: insertO x ys
insertO x _    = x :<: OEmp
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
<br>




Refinements vs. Full Dependent Types
------------------------------------

<br>

+ *Limited* to **decidable logics** but ...

+ *Offer* massive amounts of **automation**

<br>

<div class="fragment">

Compare with `insertionSort` in:

+ [Haskell-Singletons](https://github.com/goldfirere/singletons/blob/master/tests/compile-and-dump/InsertionSort/InsertionSortImp.hs)
+ [Idris](https://github.com/davidfstr/idris-insertion-sort/tree/master)
+ [Coq](http://www.enseignement.polytechnique.fr/informatique/INF551/TD/TD5/aux/Insert_Sort.v)

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



Unfinished Business
-------------------
<br>

**Problem:** How to reason about `elems` and `lenght` of an `OList`?

<br>

**Solution:** Make `OList` an instance of `List` using Abstract Refinements!

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
<br>
<br>
<br>


Recap
-----

<br>
<br>

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. <div class="fragment">**Measures:** Specify Properties of Data</div>

<br>

<div class="fragment">
**Next:** [Abstract Refinements](04-abstract-refinements.html)
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
