<div class="hidden">

\begin{code}
{-# LANGUAGE TupleSections    #-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}
{-  LIQUID "--totality"       @-}
{-@ LIQUID "--diff"           @-}

module AbstractRefinements () where


import Prelude hiding (length)
import qualified Data.Set as S -- hiding (elems, insert)

isort  :: (Ord a) => List a -> List a 
insert :: (Ord a) => a -> List a -> List a 

infixr 9 ::: 


{-@ measure elems @-}
elems :: (Ord a) => List a -> S.Set a
elems Emp      = S.empty
elems (x:::xs) = addElem x xs

{-@ inline addElem @-}
addElem :: (Ord a) => a -> List a -> S.Set a
addElem x xs = S.union (S.singleton x) (elems xs)


{-@ measure length @-}
length :: List a -> Int
length Emp        = 0
length (_ ::: xs) = 1 + length xs

\end{code}

</div>

<br>
<br>
<br>
<br>
<br>



Abstract Refinements
====================

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


Key Idea
--------------
<br>

Abstract Your Property Away to make the specification Modular!

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


Monomorphic `max` Function
------------------------
<br>

Consinder a monomorphic max function: 
<br>

\begin{spec}
max     :: Int -> Int -> Int
max x y = if x >= y then x else y
\end{spec}

<br>

How can we refine the type of `max`?

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

Refining `max` type (I)
-----------------------

<br>

If `max` gets two `Odd` numbers: 
<br>

\begin{spec}
max     :: Odd -> Odd -> Odd
\end{spec}

<br>
Then it returns an `Odd` number:

\begin{spec}
maxOdd :: Odd
maxOdd = max 3 7
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
<br>
<br>
<br>
<br>


Refining `max` type (II)
------------------------

<br>

If `max` gets two `Even` numbers: 
<br>

\begin{spec}
max     :: Even -> Even -> Even
\end{spec}

<br>
Then it returns an `Even` number:

\begin{spec}
maxEven :: Even
maxEven = max 40 42
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
<br>
<br>
<br>
<br>


Refining `max` type (III)
-------------------------

<br>

If `max` gets two `Prime` numbers: 
<br>

\begin{spec}
max     :: Prime -> Prime -> Prime
\end{spec}

<br>
Then it returns a `Prime` number:

\begin{spec}
maxPrime :: Prime
maxPrime = max 7 13
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
<br>
<br>
<br>
<br>

Refining max type
------------------
<br>
So, what is the *primal* type of max? 
<br>

\begin{spec}
max     :: Odd   -> Odd   -> Odd
max     :: Even  -> Even  -> Even
max     :: Prime -> Prime -> Prime
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
<br>
<br>
<br>
<br>

Polymorphism via Parametric Invariants
---------------------------------------

<br>
`max` returns one of its two inputs `x` and `y`.

<br>

- **If** both inputs satisfy a property
- **Then** output must satisfy that property

<br>

This holds, **regardless of what that property was!**

<br>

- That is, we can **abstract over refinements**
- Or, **parameterize** a type over its refinements.


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



Parametric Invariants
----------------------

\begin{spec}
{-@ max :: forall <p :: Int -> Prop>. 
            Int<p> -> Int<p> -> Int<p> @-}
max     :: Int -> Int -> Int
max x y = if x <= y then y else x 
\end{spec}

Where
\begin{spec}
Int<p> is just an abbreviation for {v:Int | (p v)}
\end{spec}

This type states explicitly:

- For *any* property `p`, that is a property on `Int`,
- if `max` takes two inputs that satisfy `p`,
- then `max` returns an output that satisfies `p`.

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








Using Abstract Refinements
--------------------------

<br>

- *If* we call `max` with two arguments with the *same* concrete refinement,
- *Then* the `p` will be *automagically* instantiated with that concrete refinement,
- *The output* of the call will also enjoy the concrete refinement. 

\begin{spec}
{-@ type Odd = {v:Int | (v mod 2) = 1} @-}

{-@ maxOdd :: Odd @-}
maxOdd     = max 3 5
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
<br>
<br>
<br>
<br>


Key Idea
--------

<br>
<br>

*Abstract* The Property Away to make the specification *Modular*!


<br> 
<br>

Then, *instantiate* the property back to get your specification.


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

Ordered Lists
--------------


<br> 
<br>


Previously we saw how to refine the list data definition to get ordered lists: 

<br>

\begin{spec}
{-@ data OList a =
     OEmp
   | (:<:) { oHd :: a
           , oTl :: OList {v:a | oHd <= v}} @-}
\end{spec}

<br>

Just abstract the property away!

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


Abstract Refinements on Data Structures
----------------------------------------

<br>

\begin{code}
data List a 
  = Emp
   | (:::) { hd :: a 
           , tl :: List a }

{-@ data List a < p :: a -> a -> Prop >
  = Emp 
  | (:::) { hd :: a 
          , tl :: List < p > a< p hd > } @-}
\end{code}

<br>
<br>
Every element of the tail *recursively* satisfies `p` on the head!

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

Instantiation of Refinements
-----------------------------

Unrefined Lists 
\begin{code}
{-@ type TList a = List <{\x v -> true  }> a @-}
\end{code}
Increasing Lists 
\begin{code}
{-@ type OList a = List <{\x v -> x <= v}> a @-}
\end{code}
Decreasing Lists 
\begin{code}
{-@ type DList a = List <{\x v -> v <= x}> a @-}
\end{code}
Unique Lists 
\begin{code}
{-@ type UList a = List <{\x v -> x /= v}> a @-}
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
<br>
<br>


Using Abstract Refinements
---------------------------

Use increasing lists 

\begin{code}
{-@ type OList a = List <{\x v -> x <= v}> a @-}
\end{code}

to specify insertion sort, as before!

\begin{code}
{-@ isort ::  xs:List a -> OList a  @-}
isort Emp      = Emp
isort (x:::xs) = insert x (isort xs)

{-@ insert :: x:a -> xs:OList a 
           -> {v : OList a | length v == length xs + 1
                           && elems v == addElem x xs  } @-}
insert x (y ::: ys)
  | x <= y     = x ::: y ::: ys
  | otherwise  = y ::: insert x ys
insert x _     = x ::: Emp
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
<br>
<br>


Haskell's list
-----------------

<br>

Haskell build-in list comes parameterized for you! 

<br>
You can just instantiate the abstract refinement! 

<br>

\begin{code}
{-@ type IList a =  [a]<{\x v -> (v >= x)}>  @-}
\end{code}


<br>
And prove recursive list properties!
<br>
<br>
<br>
<br>
<br>
<br>


\begin{code}
{-@ sort :: (Ord a) => [a] -> IList a  @-}
sort :: (Ord a) => [a] -> [a]
sort = mergeAll . sequences
  where
    sequences (a:b:xs)
      | a `compare` b == GT = descending b [a]  xs
      | otherwise           = ascending  b (a:) xs 
    sequences [x] = [[x]]
    sequences []  = [[]]
    {- descending :: x:a -> IList {v:a | x < v} -> [a] -> [IList a] @-}
    descending a as (b:bs)
      | a `compare` b == GT = descending b (a:as) bs
    descending a as bs      = (a:as): sequences bs
    {- ascending :: x:a -> (IList {v:a|v>=x} -> IList a) -> [a] -> [IList a] @-}
    ascending a as (b:bs)
      | a `compare` b /= GT = ascending b (\ys -> as (a:ys)) bs 
    ascending a as bs       = as [a]: sequences bs
    mergeAll [x] = x
    mergeAll xs  = mergeAll (mergePairs xs)
    mergePairs (a:b:xs) = merge1 a b: mergePairs xs
    mergePairs [x]      = [x]
    mergePairs []       = []
\end{code}

<div class="hidden">
    {-@ descending :: x:a -> IList {v:a | x < v} -> [a] -> [IList a] @-}
    {-@ ascending :: x:a -> (IList {v:a|v>=x} -> IList a) -> [a] -> [IList a] @-}

\begin{code}
merge1 (a:as) (b:bs)
 | a `compare` b == GT  = b:merge1 (a:as) bs
 | otherwise            = a:merge1 as (b:bs)
merge1 [] bs            = bs 
merge1 as []            = as  
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
<br>
<br>
<br>

Recap
-----

<br>
<br>

1. **Refinements:** Types + Predicates
2. **Subtyping:** SMT Implication
3. **Measures:** Specify Properties of Data
4. <div class="fragment">**Abstract Refinements:** Decouple properties from code</div>

<br>

<div class="fragment">
**Next:**[Bounded Refinements](05-bounded-refinements.html)
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
<br>
<br>
<br>
