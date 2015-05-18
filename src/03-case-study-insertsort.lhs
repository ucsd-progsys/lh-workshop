
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

