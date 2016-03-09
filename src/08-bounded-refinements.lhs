<div class="hidden">
\begin{code}
module BoundedRefinements () where

import Prelude hiding ((++), (.))
import Language.Haskell.Liquid.Prelude
{-@ type IList a = [a]<{\hd tl -> hd <= tl}> @-}

append :: Ord a => a -> [a] -> [a] -> [a]
qsort1 :: Ord a => [a] -> [a]
incr   :: Int -> Int 
incr2  :: Int -> Int 

chain :: (b -> c -> Bool) -> (a -> b -> Bool) -> (a -> c -> Bool) -> a -> b -> c -> Bool
recProp :: (a -> Bool) -> (a -> Bool) -> (a -> a -> Bool) -> a -> a -> Bool
\end{code}

</div>

<br>
<br>
<br>
<br>
<br>

Bounded Refinement Types
========================
<br>
<br>

*Relating* Abstract Refinements

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

Verification of QuickSort (I)
------------------------------

\begin{code}
{-@ qsort1 :: xs:[a] -> IList a  @-}
qsort1 []     = []
qsort1 (x:xs) = append1 listLess (x:listGEq)   
  where
    listLess  = qsort1 [y | y <- xs, y <  x]  
           -- :: IList {y:a | y <  x}
    listGEq   = qsort1 [z | z <- xs, z >= x]  
           -- :: IList {y:a | y <  x}
\end{code}

<br>

\begin{code}
append1 :: [a] -> [a] -> [a]
append1 []     ys = ys
append1 (x:xs) ys = x:append1 xs ys 
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


Ghost Variables
---------------

<br>
<br>
<br>

**Good:** Bring info in scope for verification!
<br> 
<br>

**Bad:** Modification of run-time code.
<br>

<br>
**Ugly:** Pollute the code. 

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


Verification of `append`
-------------------------

\begin{code}
{-@ append :: x:a 
           -> IList {hd:a | hd < x} 
           -> IList {tl:a | x <= tl} 
           -> IList a                  @-}
append _ []     ws = ws 
append x (y:ys) ws = y:append x ys ws 
\end{code}

<br>
Verification requirement:

\begin{spec}
hdProp  = \hd -> hd < x      -- property of head elements
tlProp  = \tl -> x <= tl     -- property of tail elements
----------------------------------------------------------
recProp = \hd tl -> hd <= tl -- recursive (sorted) list 
\end{spec}

<br>
<br>

Abstracting over Properties:

\begin{spec}
forall hd tl. hdProp hd => tlProp tl => recProp hd tl 
\end{spec}


<br>
<br>
*Note:* Abstract requirement is independent of `x`!



<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

Bounds on Abstract Refinements
-------------------------------

Turn Requirement:
<br>

\begin{spec}
forall hd tl. hdProp hd => tlProp tl => recProp hd tl 
\end{spec}

<br>
Into a *Bound*: Haskell function that relates abstract refinements
<br>

\begin{code}
{-@ bound recProp @-}
recProp hdProp tlProp recProp 
  = \hd tl -> hdProp hd ==> tlProp tl ==> recProp hd tl 
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






Bound Abstraction
-----------------
<br>

\begin{code}
{-@ (++) :: forall < hdprop :: a -> Prop
                   , tlprop :: a -> Prop
                   , p :: a -> a -> Prop>.
        (RecProp a hdprop tlprop p) => 
        [a< hdprop >]< p > -> [a< tlprop >]< p > -> [a]< p > @-}
(++) []      ys = ys
(++) (x:xs) ys = x:(xs ++ ys)
\end{code}

<br>
Bound `RecProp` combines 

 - the recursive property `p`
 - the property of each head `hdprop`
 - the property of tail elements `tlprop`

<br>

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>



Bound Instantiations
---------------------

\begin{code}
{-@ qsort :: xs:[a] -> IList a  @-}
qsort []     = []
qsort (x:xs) = listLess ++ (x:listGEq)           
          -- :: IList a == [a]<{\hd tl -> hd <= tl}>
  where
    listLess = qsort [y | y <- xs, y < x ]   
          -- :: IList {y:a | y <  x}
    listGEq  = qsort [z | z <- xs, z >= x]   
	      -- :: IList {z:a | x <= z}
\end{code}

<br>
<br>
Abstract Refinement Instantiation:
\begin{spec}
recProp = \hd tl -> hd <= tl -- recursive (sort) property
hdProp  = \hd -> hd < x      -- property of head elements
tlProp  = \tl -> x <= tl     -- property of tail elements
\end{spec}


<br> 
<br>

Bound Instantiation:

\begin{spec}
recProp 
  = \hd tl -> hd < x  ==> x <= tl ==>  hd <= tl 
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
<br> 
<br>
<br> 
<br>


Verification of `compose`
-------------------------


<br>
You should know compose:

<br>
\begin{code}
(.) f g x = f (g x)   
\end{code}

<br>
<br>



What type of compose can verify the following?
<br>

\begin{code}
{-@ incr2 :: n:Int -> {v:Int| v = n + 2} @-}
incr2     =  incr . incr 

{-@ incr  :: n:Int -> {v:Int| v = n + 1} @-}
incr x    = x + 1
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
<br>

Specification of Compose
-------------------------

<br>

\begin{code}
{-@
(.) :: forall < p :: b -> c -> Prop, q :: a -> b -> Prop, r :: a -> c -> Prop>. 
       (Chain b c a p q r) => 
       (y:b -> c< p y >)
    -> (z:a -> b< q z >)
    ->  x:a -> c< r x >
@-}    
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
<br>

Specification of Compose
-------------------------

<br> 

Relate refinements of input functions:

<br> 

\begin{code}
{-@ bound chain @-}
chain p q r = \ x y z -> q x y ==> p y z ==> r x z
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
<br>

Call compose
-------------------------

Discharge compose bound at call site:

\begin{spec}
{-@ incr2 :: n:Int -> {v:Int| v = n + 2} @-}
incr2     =  incr . incr 

{-@ incr  :: n:Int -> {v:Int| v = n + 1} @-}
incr x    = x + 1
\end{spec}


<br>
<br>

Abstract Refinement Instantiation:
\begin{spec}
p, q := \n v -> v = n + 1
   r := \n v -> v = n + 2
\end{spec}

<br> 
<br>

Bound Instantiation:
\begin{spec}
Chain = 
 \ x y z -> y = x + 1 ==> z = y + 1 ==> z = x + 2
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
4. **Abstract Refinements:** Decouple properties from code
5. **Bounded Refinements:** Relating Abstract Refinements


<br> 
<br>
<br> 
<br>
<br> 
<br>
<br> 
<br>
<br> 
<br>
<br> 
<br>
<br> 
<br>
<br> 
<br>
<br> 
<br>
<br> 
<br>