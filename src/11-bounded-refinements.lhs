<div class="hidden">
\begin{code}
module BoundedRefinements () where

import Prelude hiding ((++), (.))
import Language.Haskell.Liquid.Prelude
{-@ type IList a = [a]<{\hd tl -> hd <= tl}> @-}

append :: Ord a => a -> [a] -> [a] -> [a]
qsort1 :: Ord a => [a] -> [a]

-- chain :: (b -> c -> Bool) -> (a -> b -> Bool) -> (a -> c -> Bool) -> a -> b -> c -> Bool
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
{-  bound recProp @-}
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
{-@ (++) :: forall < hdprop :: a -> Bool
                   , tlprop :: a -> Bool
                   , p :: a -> a -> Bool>.
        {hd :: a < hdprop >|- a< tlprop > <: a < p hd >} 
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
