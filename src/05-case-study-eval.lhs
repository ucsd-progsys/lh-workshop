
<div class="hidden">
\begin{code}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module Eval (Map, Expr (..), plus, eval, topEval, safeEval) where

import Prelude hiding (lookup)
import qualified Data.Set as S

{-@ impossible :: {v: _ | false} -> a @-}
impossible :: String -> a
impossible = error

type Env = Map Var Expr

plus :: Expr -> Expr -> Expr
topEval :: Expr -> Expr
safeEval :: Map Var Expr -> Expr -> Maybe Expr

--------------------------------------------------------
-- | Membership test (SKIP?)
--------------------------------------------------------

{-@ member :: (Eq k) => k:_ -> m:_ -> {v:Bool | Prop v <=> has k m} @-}
member :: (Eq k) => k -> Map k v -> Bool
member k' (Bind k _ m)
  | k' == k   = True
  | otherwise = member k' m
member _  Emp = False

\end{code}
</div>

<br>
<br>
<br>
<br>
<br>

Case Study: Associative Maps & Evaluation
=========================================

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

Associative Maps
----------------

<br>

We've all been bitten by these!

\begin{spec}
ghci> :m +Data.Map
ghci> let m = fromList [ ("haskell"   , "lazy")
                       , ("javascript", "eager")]

ghci> m ! "haskell"
"lazy"

ghci> m ! "python"
"*** Exception: key is not in the map
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




Associative Maps & Evaluation
-----------------------------

<br>

Next, lets see how to use:

<br>

+ Sets to create safe **associative maps**

+ Measures to create **well-scoped evaluators**

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


Associative Maps
================


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


A Simple Associative Map
------------------------

<br>

Lets start with the type definition:

<br>

\begin{code}
data Map k v = Emp
             | Bind k v (Map k v)
               deriving (Eq, Ord, Show)
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


Lets Banish Missing Key Exceptions!
-----------------------------------

<br>

**1. Refine the Type with defined `keys`**

\begin{spec}
keys   :: Map k v -> Set k
type MapK k v Ks = {m:Map k v | keys m = Ks}
\end{spec}

**2. Refine the API to track `keys`**

\begin{spec}
empty  :: MapK k v emp
insert :: k:k -> v -> m:Map k v -> MapK k v {add k m}
lookup :: k:k -> {m: Map | has k m} -> v
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




Specifying the Set of `keys`
----------------------------

<br>

Via a measure similar to `elems` of a `List`:

<br>

\begin{code}
{-@ measure keys @-}
keys :: (Ord k) => Map k v -> S.Set k
keys Emp          = S.empty
keys (Bind k _ m) = add k m
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


The Empty `Map`
---------------

<br>

The `empty` map has **no keys**

<br>

\begin{code}
{-@ empty :: {m:Map k v | noKeys m} @-}
empty :: Map k v
empty = Emp

{-@ inline noKeys @-}
noKeys :: (Ord k) => Map k v -> Bool
noKeys m = keys m == S.empty
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


Inserting a New Key-Value Binding
---------------------------------

<br>

Adds the key to those of the old `Map`

<br>

\begin{code}
{-@ insert :: k:_ -> _ -> m:_ -> {v: _ | keys v = add k m } @-}
insert :: k -> v -> Map k v -> Map k v
insert k v m = Bind k v m

{-@ inline add @-}
add :: (Ord k) => k -> Map k v -> S.Set k
add k kvs = S.union (S.singleton k) (keys kvs)
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


Exercise: Looking Up a Key's Value
----------------------------------

<br>

**Q:** Urgh! How can we *prevent the impossible* from happening?

<br>

\begin{code}
{-@ lookup :: (Eq k) => k:k -> {m:Map k v | has k m} -> v @-}
lookup k' (Bind k v m)
  | k' == k   = v
  | otherwise = lookup k' m
lookup _  Emp = impossible "lookup"

{-@ inline has @-}
has :: (Ord k) => k -> Map k v -> Bool
has k m = True    -- EXERCISE fix using,
                  --   keys     :: Map k v -> Set k
                  --   S.member :: k -> S.Set k -> Bool
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

Key Not Found Begone!
---------------------

<br>

Errors caught at compile time!

<br>

\begin{code}
test      = [ lookup hs langs   -- Ok
            , lookup py langs   -- Err
            ]
  where
    langs = Bind hs "lazy"  $
            Bind js "eager" $
            Emp
    hs    = "haskell"
    js    = "javascript"
    py    = "python"
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


Well-Scoped Evaluators
======================


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>



Expressions
-----------

<br>

Lets define a small language of `Expr`

<br>

\begin{code}
data Var  = V String deriving (Eq, Ord, Show)

data Expr = Val  Int
          | Var  Var
          | Plus Expr Expr
          | Let  Var  Expr Expr
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


Values
------

<br>

We can define values as a **refinement** of `Expr`

<br>

\begin{code}
{-@ type Val = {v:Expr | isVal v} @-}

{-@ measure isVal @-}
isVal :: Expr -> Bool
isVal (Val _) = True
isVal _       = False
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



Exercise: Operating on Values
-----------------------------

<br>

**Q:** What's a suitable signature for `plus`?

<br>

\begin{code}
plus (Val i) (Val j) = Val (i+j)
plus _         _     = impossible "plus"
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

Environments
------------

<br>

An `Env`ironment maps `Var`iables to `Val`ues

<br>

\begin{code}
{-@ type Env = Map Var Val @-}
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



Evaluate Using Environments
---------------------------

<br>

We can now `eval` an `Expr` as:

<br>

\begin{code}
{-@ eval :: Env -> Expr -> Val @-}
eval _ i@(Val _)     = i
eval g (Var x)       = lookup x g
eval g (Plus e1 e2)  = plus (eval g e1) (eval g e2)
eval g (Let x e1 e2) = eval gx e2
  where
    gx               = insert x v1 g
    v1               = eval g e1
\end{code}

<br>

**Yikes! `lookup` is rejected!** How to ensure that `x::Var` is in `g::Env`?

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>




Free vs Bound Variables
-----------------------

<br>

For example in `let x = 10 in x + y`

+ `y` occurs **free**,  *i.e.* defined *outside*,
+ `x` occurs **bound**, *i.e.* defined *inside* (as `10`).

<br>

`eval` looks-up `Env` for values of [free variables](http://en.wikipedia.org/wiki/Free_variables_and_bound_variables)


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>




Free Variables
--------------

<br>
Specify `free` variables as a `measure`
<br>

\begin{code}
{-@ measure free @-}
free               :: Expr -> S.Set Var
free (Val _)       = S.empty
free (Var x)       = S.singleton x
free (Plus e1 e2)  = S.union xs1 xs2
  where xs1        = free e1
        xs2        = free e2
free (Let x e1 e2) = S.union xs1 (S.difference xs2 xs)
  where xs1        = free e1
        xs2        = free e2
        xs         = S.singleton x
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

Free Variables: Example
-----------------------

<br>

<div class="fragment">

\begin{spec} <div/>
ghci> let e1 = Let (V "x") (Val 10)
                 (Plus (Var (V "x")) (Var (V "y")))

ghci> free e1
      S.Set (V "y")
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


Well-scoped Expressions
-----------------------

<br>

`e` is **well-scoped** in an env `G` if **free** variables of `e` are **defined in** `G`:

<br>

\begin{code}
{-@ type ScopedExpr G = {e: Expr | wellScoped G e} @-}

{-@ inline wellScoped @-}
wellScoped :: Env -> Expr -> Bool
wellScoped g e = S.isSubsetOf (free e) (keys g)
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


Exercise: Well-Scoped `eval`
----------------------------

<br>

**Q:** Can you go back and fix the type of `eval` so it is safe?

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

Exercise: Top-level Evaluation
------------------------------

<br>

A **closed** `Expr` can be evaluated in an **empty** environment.

\begin{code}
{-@ type ClosedExpr = {e: Expr | closed e} @-}

{-@ topEval :: ClosedExpr -> Val @-}
topEval =  eval Emp
\end{code}

**Q:** Fix the definition of `closed` so `topEval` is safe?

\begin{code}
{-@ inline closed @-}
closed :: Expr -> Bool
closed e = True -- EXERCISE
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

Exercise: Checked Top-level Evaluation
--------------------------------------

<br>

`safeEval` should work with **any** `Expr` and `Env`

<br>

**Q:** What is the right check `ok` such that `safeEval` verifies?

<br>

\begin{code}
{-@ safeEval :: Env -> Expr -> Maybe Val @-}
safeEval g e
  | ok        = Just $ eval g e
  | otherwise = Nothing
  where
    ok        = True -- EXERCISE
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



Wrap Up: Associative Maps & Evaluation
--------------------------------------

<br>
<br>

1. **Missing key** errors are everywhere (and annoying!)

2. **Use sets** to refine associative map API

3. **Use measures** to create well-scoped evaluators

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


Continue
--------

<br>

<div class="fragment">
**Next: Case Studies**

+ [Insertion Sort](04-case-study-insertsort.html)
+ [Well Scoped Evaluator](05-case-study-eval.html)
+ [Low-level Memory](06-case-study-bytestring.html)
</div>

<br>

[[Continue]](06-case-study-bytestring.html)

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

<div class="hidden">

CHEAT SHEET :)

topEval

topEval:
  closed e = free e == S.empty

safeEval:
  ok       = wellScoped g e

</div>
