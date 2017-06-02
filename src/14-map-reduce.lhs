<div class="hidden">

\begin{code}
{-# LANGUAGE TupleSections    #-}
{-@ LIQUID "--no-warnings"    @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--higherorder"    @-}
{-@ LIQUID "--totality"       @-}
{-@ LIQUID "--exactdc"        @-}

module MapReduce where

import Prelude hiding (mconcat, map, split, take, drop, sum, (++))
import Language.Haskell.Liquid.ProofCombinators 

map :: (a -> b) -> List a -> List b
sumEq :: Int -> List Int -> Proof 

sumRightId :: List Int -> Proof 
sumDistr :: List Int -> List Int -> Proof 

mRTheorem :: Int -> (List a -> b) -> (b -> b -> b) 
          -> (List a -> Proof) 
          -> (List a -> List a -> Proof) 
          -> List a -> Proof 

appendTakeDrop :: Int -> List a -> Proof 

llen :: List a -> Int 
{-@ infix ++ @-}
(++) :: List a -> List a -> List a 
drop :: Int -> List a -> List a 
take :: Int -> List a -> List a 
\end{code}

</div>

<br>
<br>
<br>
<br>
<br>



Case Study: MapReduce   
=======================
<br>
<br>
<br>

[MapReduce](https://en.wikipedia.org/wiki/MapReduce)

  - Chunk Input, 
  - Map Operation (in parallel), and 
  - Reduce the results.

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


Implementation 
---------------

\begin{code}
{-@ reflect mapReduce @-}
mapReduce :: Int -> (List a -> b) -> (b -> b -> b) -> List a -> b 
mapReduce n f op is = reduce op (f N) (map f (chunk n is))

{-@ reflect reduce @-}
reduce :: (a -> a -> a) -> a -> List a -> a 
reduce op b N        = b 
reduce op b (C x xs) = op x (reduce op b xs) 

{-@ reflect map @-}
{-@ map :: (a -> b) -> xs:List a -> {v:List b | llen v == llen xs } @-}
map _  N       = N
map f (C x xs) = f x `C` map f xs 

{-@ reflect chunk @-}
chunk :: Int -> List a -> List (List a)
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
<br>
<br>
<br>

Use Case: Summing List 
----------------------

\begin{code}
{-@ reflect sum @-}
sum  :: List Int -> Int 
sum N        = 0 
sum (C x xs) = x `plus` sum xs

{-@ reflect plus @-}
plus :: Int -> Int -> Int 
plus x y = x + y 

{-@ reflect psum @-}
psum :: Int -> List Int -> Int 
psum n is = mapReduce n sum plus is 
\end{code}

**Question:** Is `psum` equivalent to `sum`?
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


Proving Code Equivalence 
-------------------------

\begin{code}
{-@ sumEq :: n:Int -> is:List Int -> { sum is == psum n is } @-}
sumEq n is 
  =   psum n is 
  ==. mapReduce n sum plus is 
  ==. sum is 
      ? mRTheorem n sum plus sumRightId sumDistr is 
  *** QED 

{-@ sumDistr   :: xs:List Int -> ys:List Int -> 
      {sum (xs ++ ys) == plus (sum xs) (sum ys)} @-}

{-@ sumRightId :: xs:List Int -> 
      {plus (sum xs) (sum N) == sum xs} @-}
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
<br>
<br>
<br>

Sum relevant Proofs 
-------------------

- Right Identity 

\begin{code}
sumRightId xs 
  =  plus (sum xs) (sum N) ==. sum xs + 0 ==. sum xs *** QED 
\end{code}

- Distribution 

\begin{code}
sumDistr N ys 
  =   sum (N ++ ys)
  ==. sum ys
  ==. plus 0       (sum ys)
  ==. plus (sum N) (sum ys)
  *** QED 
sumDistr (C x xs) ys  
  =   sum ((C x xs) ++ ys)
  ==. sum (C x (xs ++ ys))
  ==. x `plus` (sum (xs ++ ys))
      ? sumDistr xs ys
  ==. x `plus` (plus (sum xs) (sum ys))
  ==. x + (sum xs + sum ys)
  ==. ((x + sum xs) + sum ys)
  ==. ((x `plus` sum xs) `plus` sum ys)
  ==. sum (C x xs) `plus` sum ys
  *** QED 
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
<br>
<br>
<br>


Map Reduce Equivalence
-----------------------

\begin{code}
{-@ mRTheorem :: n:Int -> f:(List a -> b) -> op:(b -> b -> b)
     -> rightId:(xs:List a -> {op (f xs) (f N) == f xs } ) 
     -> distrib:(xs:List a -> ys:List a 
                           -> {f (xs ++ ys) == op (f xs) (f ys)} )
     -> is:List a 
     -> { mapReduce n f op is == f is }
     / [llen is]
  @-}
mRTheorem n f op rightId _ N 
  =   mapReduce n f op N 
  ==. reduce op (f N) (map f (chunk n N))
  ==. reduce op (f N) (map f (C N N))
  ==. reduce op (f N) (f N `C` map f N )
  ==. reduce op (f N) (f N `C` N)
  ==. op (f N) (reduce op (f N) N)
  ==. op (f N) (f N)
       ? rightId N
  ==. f N 
  *** QED 

mRTheorem n f op rightId _ is@(C _ _)
  | n <= 1 || llen is <= n 
  =   mapReduce n f op is 
  ==. reduce op (f N) (map f (chunk n is))
  ==. reduce op (f N) (map f (C is N))
  ==. reduce op (f N) (f is `C` map f N)
  ==. reduce op (f N) (f is `C` N)
  ==. op (f is) (reduce op (f N) N)
  ==. op (f is) (f N)
  ==. f is  
       ? rightId is
  *** QED 

mRTheorem n f op rightId distrib is 
  =   mapReduce n f op is 
  ==. reduce op (f N) (map f (chunk n is)) 
  ==. reduce op (f N) (map f (C (take n is) (chunk n (drop n is)))) 
  ==. reduce op (f N) (C (f (take n is)) (map f (chunk n (drop n is)))) 
  ==. op (f (take n is)) (reduce op (f N) (map f (chunk n (drop n is))))  
  ==. op (f (take n is)) (mapReduce n f op (drop n is)) 
  ==. op (f (take n is)) (f (drop n is)) 
      ? mRTheorem n f op rightId distrib (drop n is)
  ==. f ((take n is) ++ (drop n is))
      ? distrib (take n is) (drop n is)
  ==. f is 
      ? appendTakeDrop n is 
  *** QED  
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
<br>
<br>
<br>

Append of Take and Drop
-----------------------

\begin{code}
{-@ appendTakeDrop :: i:Nat -> xs:{List a | i <= llen xs} ->
     {xs == (take i xs) ++ (drop i xs) }  @-}

appendTakeDrop i N 
  =    (take i N) ++  (drop i N)
  ==.  N ++ N 
  ==. N 
  *** QED 
appendTakeDrop i (C x xs)
  | i == 0 
  =    (take 0 (C x xs)) ++ (drop 0 (C x xs))
  ==.  N  ++ (C x xs)
  ==. C x xs 
  *** QED 
  | otherwise
  =    (take i (C x xs))  ++ (drop i (C x xs))
  ==.  (C x (take (i-1) xs))  ++ (drop (i-1) xs)
  ==. C x ( (take (i-1) xs) ++ (drop (i-1) xs))
  ==. C x xs ? appendTakeDrop (i-1) xs 
  *** QED 
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
<br>
<br>
<br>

List Definition 
---------------

Built-in Lists are not supported for now.

(So does imports...)

\begin{code}
{-@ data List [llen] a = N | C {lhead :: a, ltail :: List a} @-}
data List a = N | C a (List a)

{-@ measure llen @-}
{-@ llen :: List a -> Nat @-}
llen N        = 0 
llen (C _ xs) = 1 + llen xs
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
<br>
<br>
<br>

List Manipulation
------------------

\begin{code}
{-@ chunk :: i:Int -> xs:List a 
    -> {v:List (List a) | if (i <= 1 || llen xs <= i) then (llen v == 1) else (llen v < llen xs) } 
  / [llen xs] @-}
chunk i xs 
  | i <= 1 
  = C xs N 
  | llen xs <= i 
  = C xs N 
  | otherwise
  = C (take i xs) (chunk i (drop i xs))

{-@ reflect drop @-}
{-@ drop :: i:Nat -> xs:{List a | i <= llen xs } -> {v:List a | llen v == llen xs - i } @-}
drop i N = N 
drop i (C x xs)
  | i == 0 
  = C x xs  
  | otherwise 
  = drop (i-1) xs 

{-@ reflect take @-}
{-@ take :: i:Nat -> xs:{List a | i <= llen xs } -> {v:List a | llen v == i} @-} 
take i N = N 
take i (C x xs)
  | i == 0 
  = N  
  | otherwise 
  = C x (take (i-1) xs)


{-@ reflect ++  @-}
N ++        ys = ys  
(C x xs) ++ ys = x `C` (xs ++ ys)
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
<br>
<br>


Recap
-----

<br>
<br>

-  **Refinement Reflection:** Allow Haskell functions in Logic
-  <div class="fragment">**Case Study:**</div> Prove Program Equivalence 

<br>
<br>

Prove crucial properties **for** Haskell **in** Haskell!

<br>

where Haskell = a general purspose programming language.
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

Thank You!
----------

<br>

`cabal install liquidhaskell`

<br>

[https://github.com/ucsd-progsys/liquidhaskell](https://github.com/ucsd-progsys/liquidhaskell)

<br>

[`http://www.refinement-types.org`](http://www.refinement-types.org)

<br>

[online demo @ http://goto.ucsd.edu/liquidhaskell](http://goto.ucsd.edu/liquidhaskell)

<br>
<br>
<br>
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
2. **Automation:** SMT Implication
3. **Measures:** Specify Properties of Data
4. **Termination:** Semantic Termination Checking
5. **Reflection:** Allow Haskell functions in Logic! 
6. <div class="fragment">**Case Study:**</div> Prove Program Equivalence

<br>

**Next:** [Information Flow](08-security.html): Refinement Types for Security Policies

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
