<div class="hidden">

\begin{code}
{-# LANGUAGE TupleSections    #-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--totality"      @-}
{-@ LIQUID "--diff"           @-}

module Termination where

import Prelude hiding (map, repeat)

fib :: Int -> Int
map :: (a -> b) -> [a] -> [b]

isOdd, isEven :: Int -> Bool 
ack :: Int -> Int -> Int 
range :: Int -> Int -> [Int]

\end{code}

</div>

<br>
<br>
<br>
<br>
<br>



Termination Checking
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


Why termination Checking?
-------------------------

<br>
<br>

LiquidHaskell checks _by default_ that all your functions terminate!

Why?

- It is the _expected_ case!
- For soundness: [Refinement Types for Haskell](http://goto.ucsd.edu/~nvazou/refinement_types_for_haskell.pdf)

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

Example: Termination of `fib`
-----------------------------

<br>
<br>
\begin{code}
{-@ fib :: i:Int -> Int  @-}
fib i | i == 0    = 0 
      | i == 1    = 1 
      | otherwise = fib (i-1) + fib (i-2)
\end{code}

<br>
<br>
**Q:** Why is there an error?
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


Proving Termination I
----------------------
<br>
Liquid Haskell checks a _well founded_ metric decreases at each recursive call. 


<br>
<br>
_Well founded_ metrics:

 - the first integer argument.
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



User specified Termination Metrics
-----------------------------------

The first integer is not always decreasing!

\begin{code}
{-@ range :: lo:Int -> hi:Int -> [Int] / [0] @-} 
range lo hi
 | lo < hi = lo : range (lo+1) hi
 | otherwise = []
\end{code}
<br>
<br>

**Q:** Replace `0` with the decreasing metric!

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

Proving Termination 
----------------------

Liquid Haskell checks a _well founded_ metric decreases at each recursive call. 


<br>
<br>
_Well founded_ metrics:

 - user specified metrics, or
 - the first integer argument.
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


Lexicographic Termination
-----------------------------------

Why does [Ackermann Function](https://en.wikipedia.org/wiki/Ackermann_function) terminate?


\begin{code}
{-@ ack :: m:Int -> n:Int -> Int / [0, 0] @-} 
ack m n
  | m == 0 = n + 1
  | n == 0 = ack (m-1) 1
  | otherwise = ack (m-1) (ack m (n-1))
\end{code}
<br>
<br>

**Q:** Replace `0` with the decreasing _metrics_!

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


How about data types?
-----------------------------------

Map ADTs to integers using measures!

\begin{code}
{-@ map :: (a -> b) -> xs:[a] -> [b] / [len xs]  @-}
map _ []     = []
map f (x:xs) = f x : map f xs 
\end{code}

<br>
<br>

But Liquid Haskell knows that!

<br>
It will use `len` as the default metric to check `x:[a]` decreasing.

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

User specified metrics on ADTs
-----------------------------------

<br>

\begin{code}
{-@ merge :: xs:[a] -> ys:[a] -> [a] / [0] @-}
merge xs []   = xs
merge [] ys   = ys
merge (x:xs) (y:ys) 
  | x < y     = x:(merge xs (y:ys))
  | otherwise = y:(merge ys (x:xs))
\end{code}

<br>
<br>

Does `merge` terminate?

<br>

Liquid Haskell cannot know that!

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


Mutual Recursive Functions
-----------------------------------

Same idea generalizes to mutual recursion. 

\begin{code}
{-@ isEven :: n:Nat -> Bool / [n, 0] @-}
{-@ isOdd  :: m:Nat -> Bool / [m, 0] @-}

isEven 0 = True
isEven n = isOdd (n-1)

isOdd m = not $ isEven m
\end{code}
<br>
<br>

Can you find the correct metric?

<br>

Liquid Haskell does not even attempt to guess it...

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

Diverging Functions 
-----------------------------------

<br>
`lazy` annotation deactivates termination checking.

<br>
\begin{code}
{-@ lazy repeat @-}

repeat x = x:repeat x 
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
<br>



Proving Termination 
----------------------

For non `Lazy` specified functions,

Liquid Haskell checks a _well founded_ metric decreases at each recursive call. 


<br>
<br>
_Well founded_ metrics:

 - user specified _lexocographic_ metrics,
 - the first integer or "sized" argument.
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
4. <div class="fragment">**Termination:**</div> Use Logic to Prove Termination 

<br>
What properties can be expressed in the logic? 
<br> 

 - Linear Arithmetic, Booleans, Uninterpreted Functions, ... (SMT logic)
 
 - Terminating Haskell functions.

<br>

<div class="fragment">

**Next:** [Refinement Reflection](05-refinement-reflection.html)

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
<br>
