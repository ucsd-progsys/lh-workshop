
<div class="slideonly">

 {#simplerefinements}
=======================

Simple Refinement Types
-----------------------

</div>

<div class="hidden">

\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--diff"           @-}
{-@ LIQUID "--short-names"    @-}

module SimpleRefinements where
import Prelude hiding (abs, max)

nats, poss  :: [Int]
zero        :: Int
zero'       :: Int
safeDiv     :: Int -> Int -> Int
size, size' :: [a] -> Int
\end{code}

</div>


<div class="slideonly">

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

**Q:** Can you fix `Pos` so `poss` is **rejected**?

<br>

<div class="fragment">
**Q:** Now, can you modify `poss` so it is **accepted**?
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

Eliminates **boring** proofs ...

<br>

<div class="fragment">
... makes verification **practical**.
</div>



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

Precond. Checked at Call-Site
-----------------------------

<br>

\begin{code}
avg2 x y   = safeDiv (x + y) 2
\end{code}

<br>

<div class="slideonly">
<div class="fragment">
**Precondition**

\begin{spec} <div/>
{-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
\end{spec}
</div>
</div>

<br>

<div class="slideonly">
<div class="fragment">
**Verifies As**

$\bindx{x}{\Int}, \bindx{y}{\Int} \vdash \reftx{v}{v = 2} \subty \reftx{v}{v \not = 0}$
</div>
</div>

Precond. Checked at Call-Site
-----------------------------

<br>

\begin{code}
avg2 x y   = safeDiv (x + y) 2
\end{code}

<br>

<div class="slideonly">
**Precondition**

\begin{spec} <div/>
{-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
\end{spec}
</div>

<br>

<div class="slideonly">
**Verifies As**

$$(v = 2) \Rightarrow (v \not = 0)$$
</div>

Exercise: Check That Data
-------------------------

\begin{code}
calc :: IO ()
calc = do
  putStrLn "Enter numerator"
  n <- readLn
  putStrLn "Enter denominator"
  d <- readLn
  putStrLn $ "Result = " ++ show (div n d)
  calc
\end{code}

<br>

**Q:** Can you fix `calc` so it typechecks?


Precond. Checked at Call-Site
-----------------------------

<br>

\begin{code}
avg        :: [Int] -> Int
avg xs     = div total n
  where
    total  = sum    xs
    n      = length xs
\end{code}

<br>

<div class="slideonly">
<div class="fragment">
**Rejected** as `n` can be *any* `Int`

$$(v = n) \not \Rightarrow (v \not = 0)$$

</div>
</div>

`size` returns positive values
------------------------------

<br>

\begin{code}
size [_]    = 1
size (_:xs) = 1 +  size xs
-- size _   = die "We'll cross this bridge ..."
\end{code}

<br>

<div class="fragment">
Specify **post-condition** as **output type**

<br>

\begin{code}
{-@ size :: [a] -> Pos @-}
\end{code}
</div>


Postconds Checked at Return
---------------------------

<br>

\begin{spec} <div/>
{-@ size    :: [a] -> Pos @-}
size []     = 1                        -- (1)
size (_:xs) = 1 + n  where n = size xs -- (2)
\end{spec}

<br>

<div class="fragment">
**Verified As**

<br>

$$\begin{array}{rll}
\True   & \Rightarrow (v = 1)     & \Rightarrow (0 < v) & \qquad \mbox{at (1)} \\
(0 < n) & \Rightarrow (v = 1 + n) & \Rightarrow (0 < v) & \qquad \mbox{at (2)} \\
\end{array}$$
</div>

Verifying `avg`
---------------

<br>

\begin{code}
avg' xs    = safeDiv total n
  where
    total  = sum  xs
    n      = size xs
\end{code}

<br>

<div class="slideonly">
<div class="fragment">
**Verifies As**

$$(0 < n) \Rightarrow (v = n) \Rightarrow (v \not = 0)$$
</div>
</div>

Recap
=====

 {#recap-01}
------------


<div class="fragment">
**Refinement Types**

Types + Predicates
</div>

<br>

<div class="fragment">
**Specify Properties**

Via Refined Input- and Output- Types
</div>

<br>

<div class="fragment">
**Verify Properties**

Via SMT based Predicate Subtyping
</div>


  {#exit-01}
------------

How to prevent calling `size` with **empty lists**?

<br>

\begin{code}
{-@ size'    :: [a] -> Pos @-}
size' [_]    = 1
size' (_:xs) = 1 + size' xs
size' _      = die "Lets cross this bridge."
\end{code}

<br>

<div class="fragment">
[[continue...]](02-measures.html)
<br>


