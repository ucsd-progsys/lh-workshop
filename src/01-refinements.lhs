
 {#simplerefinements}
=======================

Simple Refinement Types
-----------------------

<div class="hidden">

\begin{code}
{-@ LIQUID "--no-termination" @-}
module SimpleRefinements where
-- import Language.Haskell.Liquid.Prelude
import Prelude hiding (abs, max)

-- boring haskell type sigs
nats, poss :: [Int]
zero       :: Int
zero'      :: Int
safeDiv    :: Int -> Int -> Int
abs        :: Int -> Int
\end{code}

</div>

Simple Refinement Types
=======================


Types + Predicates
------------------

<br>

\begin{spec}<div/>
b := Int
   | Bool
   | ...         -- base types
   | a, b, c     -- type variables
\end{spec}


</div>


Types + Predicates
------------------

<br>

\begin{spec}<div/>
b := Int
   | Bool
   | ...         -- base types
   | a, b, c     -- type variables

t := {x:b | p}   -- refined base
   | x:t -> t    -- refined function
\end{spec}

</div>


Types + Predicates
------------------

<br>

\begin{spec}<div/>
b := Int
   | Bool
   | ...         -- base types
   | a, b, c     -- type variables

t := {x:b | p}   -- refined base
   | x:t -> t    -- refined function

p := ...         -- predicate in decidable logic
\end{spec}





Predicates
----------

<br>

\begin{spec} <div/>
p := e           -- atom
   | e1 == e2    -- equality
   | e1 <  e2    -- ordering
   | (p && p)    -- and
   | (p || p)    -- or
   | (not p)     -- negation
\end{spec}

<br>

Expressions
-----------

<br>

\begin{spec} <div/>
e := x, y, z,...    -- variable
   | 0, 1, 2,...    -- constant
   | (e + e)        -- addition
   | (e - e)        -- subtraction
   | (c * e)        -- linear multiplication
   | (f e1 ... en)  -- uninterpreted function
\end{spec}

<br>

<div class="fragment">

**Refinement Logic: QF-UFLIA**

Quant.-Free. Uninterpreted Functions and Linear Arithmetic

</div>

Example: Integers equal to `0`
------------------------------

<br>

\begin{code}
{-@ type Zero = {v:Int | v = 0} @-}

{-@ zero :: Zero @-}
zero     =  0
\end{code}

<br>


<div class="fragment">
Refinement types via special comments `{-@ ... @-}`
</div>


Example: Natural Numbers
------------------------

<br>

\begin{code}
{-@ type Nat = {v:Int | 0 <= v} @-}

{-@ nats :: [Nat]               @-}
nats     =  [0, 1, 2, 3]
\end{code}

<br>

Exercise: Positive Integers
---------------------------

<br>

\begin{code}
{-@ type Pos = {v:Int | 0 <= v} @-}

{-@ poss :: [Pos]               @-}
poss     =  [0, 1, 2, 3]
\end{code}

<br>

<div class="fragment">
**Q:** First, can you fix `Pos` so `poss` is **rejected**?
</div>

<br>

<div class="fragment">
**Q:** Second, can you modify `poss` so it is **accepted**?
</div>

Type Checking
=============

A Term Can Have Many Types
--------------------------

<br>

<div class="fragment">
What *is* the type of `0` ?

<br>

\begin{spec}
{-@ zero  :: Zero @-}
zero      = 0

{-@ zero' :: Nat  @-}
zero'     = zero
\end{spec}

</div>

Predicate Subtyping [[PVS]](http://pvs.csl.sri.com/papers/subtypes98/tse98.pdf)
-------------------

<br>

$$\boxed{\Gamma \vdash t_1 \preceq t_2}$$

<div class="fragment">

<br>

Where **environment** $\Gamma$ is a sequence of binders

<br>

$$\Gamma \defeq \overline{\bindx{x_i}{P_i}}$$

</div>

Predicate Subtyping [[PVS]](http://pvs.csl.sri.com/papers/subtypes98/tse98.pdf)
------------------------

<br>

$$\boxed{\Gamma \vdash t_1 \preceq t_2}$$


<br>

$$
\begin{array}{rll}
{\mathbf{If\ VC\ is\ Valid}}   & \bigwedge_i P_i \Rightarrow  Q  \Rightarrow R & (\mbox{By SMT}) \\
                &  & \\
{\mathbf{Then}} & \overline{\bindx{x_i}{P_i}} \vdash \reft{v}{b}{Q} \subty \reft{v}{b}{R} & \\
\end{array}
$$


Example: Natural Numbers
------------------------

<br>

\begin{spec} <div/>
        type Nat = {v:Int | 0 <= v}
\end{spec}

<br>

<div class="fragment">

$$
\begin{array}{rcrccll}
\mathbf{VC\ is\ Valid:} & \True     & \Rightarrow &  v = 0   & \Rightarrow &  0 \leq v & \mbox{(by SMT)} \\
%                &           &             &          &             &           \\
\mathbf{So:}      & \emptyset & \vdash      & \Zero  & \subty      & \Nat   &   \\
\end{array}
$$
</div>

<br>

<div class="fragment">

Hence, we can type:

\begin{code}
{-@ zero' :: Nat @-}
zero'     =  zero   -- zero :: Zero <: Nat
\end{code}
</div>


[SMT](http://en.wikipedia.org/wiki/Satisfiability_modulo_theories) Automates Subtyping
------------------------

<br>

Eliminates *boring* proofs ...

<br>

... makes verification *practical*.



Contracts: Function Types
=========================

 {#as}
------

Pre-Conditions
--------------


<br>

\begin{code}
{-@ die :: {v:_ | false} -> a @-}
die msg = error msg
\end{code}

<br>

<div class="fragment">
No value satisfies `false` $\Rightarrow$ **no valid inputs** for `die`
</div>

<br>

<div class="fragment">
Program type-checks $\Rightarrow$ `die` **never called at run-time**
</div>


Exercise: Pre-Conditions
------------------------

Let's write a *safe* division function

<br>

\begin{code}
{-@ safeDiv :: Int -> Int -> Int   @-}
safeDiv _ 0 = die "divide-by-zero"
safeDiv x n = x `div` n
\end{code}

<br>

<div class="fragment">
Yikes, an error!

<br>

**Q:** Can you **fix the type** of `safeDiv` to banish the error?
</div>


Precondition: `safeDiv`
-----------------------

Specify pre-condition as **input type**

\begin{spec} <div/>
{-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
\end{spec}

<br>

Precondition is checked at **call-site**

\begin{code}
{-@ bad :: Nat -> Int @-}
bad n   = 10 `safeDiv` n
\end{code}

<br>

<div class="fragment">
**Rejected As**

$$(0 \leq n) \Rightarrow (v = n) \not \Rightarrow (v \not = 0)$$

</div>

Precondition: `safeDiv`
-----------------------

Specify pre-condition as **input type**

\begin{spec} <div/>
{-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
\end{spec}

<br>

Precondition is checked at **call-site**

\begin{code}
{-@ ok  :: Nat -> Int @-}
ok n    = 10 `safeDiv` (n+1)
\end{code}

<br>

<div class="fragment">
**Verifies As**

$$(0 \leq n) \Rightarrow (v = n+1) \Rightarrow (v \not = 0)$$
</div>

HEREHEREHERE

Post-Conditions
---------------

**Ensures** output is a `Nat` greater than input `x`.

\begin{code}
abs x | 0 <= x    = x
      | otherwise = 0 - x
\end{code}

<br>

<div class="fragment">
Specify post-condition as **output type**

\begin{code}
{-@ abs :: x:Int -> {v:Nat | x <= v} @-}
\end{code}
</div>

<br>

<div class="fragment">
**Dependent Function Types**

Outputs *refer to* inputs
</div>

Postcondition: `abs`
--------------------

Specify post-condition as **output type**

\begin{spec} <div/>
{-@ abs :: x:Int -> {v:Nat | x <= v} @-}
abs x | 0 <= x    = x
      | otherwise = 0 - x
\end{spec}

<br>

Postcondition is checked at **return-site**

<br>

Postcondition: `abs`
--------------------

Specify post-condition as **output type**

\begin{spec} <div/>
{-@ abs :: x:Int -> {v:Nat | x <= v} @-}
abs x | 0 <= x    = x
      | otherwise = 0 - x
\end{spec}

<br>

**Verified As**

<br>

$$\begin{array}{rll}
\bindx{x}{\Int},\bindx{\_}{0 \leq x}      & \vdash \reftx{v}{v = x}     & \subty \reftx{v}{0 \leq v \wedge x \leq v} \\
\bindx{x}{\Int},\bindx{\_}{0 \not \leq x} & \vdash \reftx{v}{v = 0 - x} & \subty \reftx{v}{0 \leq v \wedge x \leq v} \\
\end{array}$$

Postcondition: `abs`
--------------------

Specify post-condition as **output type**

\begin{spec} <div/>
{-@ abs :: x:Int -> {v:Nat | x <= v} @-}
abs x | 0 <= x    = x
      | otherwise = 0 - x
\end{spec}

<br>

**Verified As**

<br>

$$\begin{array}{rll}
(0 \leq x)      & \Rightarrow (v = x)     & \Rightarrow (0 \leq v \wedge x \leq v) \\
(0 \not \leq x) & \Rightarrow (v = 0 - x) & \Rightarrow (0 \leq v \wedge x \leq v) \\
\end{array}$$


Recipe Scales Up
----------------

<br>

<div class="fragment">
Define type *checker* and get *inference* for free [[PLDI 08]](http://goto.ucsd.edu/~rjhala/papers/liquid_types.pdf)
</div>

<br>

<div class="fragment">
Scales to Collections, HOFs, Polymorphism ...
</div>

<br>

<div class="fragment">
[DEMO](../hs/001_Refinements.hs)

<br>

[[continue...]](02_Measures.lhs.slides.html)

</div>
