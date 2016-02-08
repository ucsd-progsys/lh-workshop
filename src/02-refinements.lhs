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
four        :: Int
safeDiv     :: Int -> Int -> Int
\end{code}

</div>

<br>
<br>
<br>
<br>
<br>


Simple Refinement Types
=======================


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

Simple Refinement Types
------------------

<br>

Refinement Types = *Types* + *Predicates*


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

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


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

Example: Natural Numbers
------------------------

<br>

\begin{code}
{-@ type Nat = {v:Int | 0 <= v} @-}

{-@ nats :: [Nat]               @-}
nats     =  [0, 1, 2, 3]
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

Exercise: Positive Integers
---------------------------

<br>

\begin{code}
{-@ type Pos = {v:Int | 0 <= v} @-}

{-@ poss :: [Pos]               @-}
poss     =  [0, 1, 2, 3]
\end{code}

<br>

**Q:** First, can you fix `Pos` so `poss` is **rejected**?

<br>

<div class="fragment">
**Q:** Next, can you modify `poss` so it is **accepted**?
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

Refinement Type Checking
========================


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>






A Term Can Have *Many* Types
----------------------------



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


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

Predicate Subtyping [[NUPRL, PVS]](http://pvs.csl.sri.com/papers/subtypes98/tse98.pdf)
----------------------------------

<br>

In **environment** $\Gamma$ the type $t_1$ is a **subtype** of the type $t_2$

<br>

$$\boxed{\Gamma \vdash t_1 \preceq t_2}$$

<div class="fragment">

<br>

**Environment** $\Gamma$ is a sequence of binders

<br>

$$\Gamma \doteq \overline{\bindx{x_i}{P_i}}$$

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


Predicate Subtyping [[NUPRL, PVS]](http://pvs.csl.sri.com/papers/subtypes98/tse98.pdf)
--------------------

<br>

$$\boxed{\Gamma \vdash t_1 \preceq t_2}$$


<br>

$$
\begin{array}{rll}
{\mathbf{If\ VC\ is\ Valid}}   & \bigwedge_i P_i \Rightarrow  Q  \Rightarrow R & (\mbox{By SMT}) \\
                &  & \\
{\mathbf{Then}} & \overline{\bindx{x_i}{P_i}} \vdash \reft{v}{b}{Q} \preceq \reft{v}{b}{R} & \\
\end{array}
$$


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


Example: Natural Numbers
------------------------

<br>

<div class="fragment">

$$
\begin{array}{rcrccll}
\mathbf{VC\ is\ Valid:} & \True     & \Rightarrow &  v = 0   & \Rightarrow &  0 \leq v & \mbox{(by SMT)} \\
                        &           &             &          &             &           &        \\
\mathbf{So:}            & \emptyset & \vdash      & \Zero    & \preceq     & \Nat      &   \\
\end{array}
$$
</div>

<br>

<div class="fragment">

And so, we can type:

\begin{code}
{-@ zero' :: Nat @-}
zero'     =  zero   -- zero :: Zero <: Nat
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



Example: Natural Numbers
------------------------

<br>

<div class="fragment">

$$
\begin{array}{rcrccll}
\mathbf{VC\ is\ Valid:} & x = 3 & \Rightarrow &  v = x + 1 & \Rightarrow &  0 \leq v & \mbox{(by SMT)} \\
                        &       &             &            &             &               \\
\mathbf{So:}            & x = 3 & \vdash      & \{v:Int\ |\ v = x + 1\}      & \preceq     & \Nat      &   \\
\end{array}
$$
</div>

<br>

<div class="fragment">

And so, we can type:

\begin{code}
{-@ four :: Nat @-}
four  = x + 1          -- x = 3 |- {v = x + 1} <: Nat
  where
    x = 3
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





[SMT](http://en.wikipedia.org/wiki/Satisfiability_modulo_theories) Automates Subtyping
------------------------

<br>

**Eliminates boring proofs** ... makes verification practical.

<br>


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


Contracts: Function Types
=========================

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>




Pre-Conditions
--------------


<br>

\begin{code}
{-@ impossible :: {v:_ | false} -> a @-}
impossible msg = error msg
\end{code}

<br>

<div class="fragment">
No value satisfies `false` $\Rightarrow$ **no valid inputs** for `impossible`
</div>

<br>

<div class="fragment">
Program type-checks $\Rightarrow$ `impossible` **never called at run-time**
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

Exercise: Pre-Conditions
------------------------

<br>

Let's write a **safe division** function

<br>

\begin{code}
{-@ type NonZero = {v:Int | v /= 0} @-}

{-@ safeDiv :: Int -> Int -> Int   @-}
safeDiv _ 0 = impossible "divide-by-zero"
safeDiv x n = x `div` n
\end{code}

<br>

<div class="fragment">
**Q:** Yikes! Can you **fix the type** of `safeDiv` to banish the error?
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


Precondition Checked at Call-Site
---------------------------------

<br>

\begin{code}
avg2 x y   = safeDiv (x + y) 2
\end{code}

<div class="fragment">
**Precondition**

\begin{spec} <div/>
{-@ safeDiv :: n:Int -> d:NonZero -> Int @-}
\end{spec}
</div>

<br>

**Verifies As**

$$\inferrule{}{(v = 2) \Rightarrow (v \not = 0)}
            {\bindx{x}{\Int}, \bindx{y}{\Int} \vdash \reftx{v}{v = 2} \preceq \reftx{v}{v \not = 0}}
$$


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

Precondition Checked at Call-Site
---------------------------------

<br>

\begin{code}
avg        :: [Int] -> Int
avg xs     = safeDiv total n
  where
    total  = sum    xs
    n      = length xs         -- returns a Nat
\end{code}

<br>

<div class="fragment">
**Rejected** as `n` can be *any* `Nat`

$$0 \leq n \Rightarrow (v = n) \not \Rightarrow (v \not = 0)$$


<br>
<br>

_How_ to talk about list length in logic?

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

Recap
-----

<br>

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


<br>
<br>
<br>
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

How to describe  **non empty lists**?

<br>

\begin{spec}
{-@ length    :: {v:[a]| length v > 0 } -> Pos @-}
\end{spec}

<br>

<div class="fragment">
Next: How to **describe properties of** structures [[continue...]](03-datatypes.html)
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
