Well-Typed Programs Can Go Wrong
================================

 {#asd}
-------


<div class="hidden">

\begin{code}
main = putStrLn "Easter Egg: to force Makefile"
\end{code}

</div>



Division By Zero
----------------


<div class="fragment">
\begin{spec}
λ> let average xs = sum xs `div` length xs

λ> average [100, 202, 300]
2
\end{spec}
</div>

<br>

<div class="fragment">
\begin{spec}
λ> average []
*** Exception: divide by zero
\end{spec}


</div>

Missing Keys
------------

<div class="fragment">
\begin{spec}
λ> :m +Data.Map
λ> let m = fromList [ ("haskell", "lazy")
                    , ("pyret"  , "eager")]

λ> m ! "haskell"
"lazy"
\end{spec}
</div>

<br>

<div class="fragment">
\begin{spec}
λ> m ! "racket"
"*** Exception: key is not in the map
\end{spec}
</div>

Segmentation Faults
-------------------

<div class="fragment">
\begin{spec}
λ> :m +Data.Vector
λ> let v = fromList ["haskell", "pyret"]
λ> unsafeIndex v 0
"haskell"
\end{spec}
</div>

<div class="fragment">
<br>
\begin{spec}
λ> V.unsafeIndex v 3

'ghci' terminated by signal SIGSEGV ...
\end{spec}
</div>


"HeartBleeds"
-------------


\begin{spec}
λ> :m + Data.Text Data.Text.Unsafe
λ> let t = pack "LambdaConf"
λ> takeWord16 5 t
"Lambda"
\end{spec}

<br>

<div class="fragment">
Memory overflows **leaking secrets**...

<br>

\begin{spec}
λ> takeWord16 20 t
"LambdaConf\1912\3148\SOH\NUL\15928\2486\SOH\NUL"
\end{spec}
</div>

Goal
----

Extend Type System

<br>

+ To prevent *wider class* of errors

+ To enforce *program specific* properties


Algorithmic Verification
========================

Tension
-------

<img src="img/tension0.png" height=300px>

Automation vs. Expressiveness

Tension
-------

<img src="img/tension1.png" height=300px>

Extremes: Hindley-Milner vs. CoC

Tension
-------

<img src="img/tension2.png" height=300px>

Trading off Automation for Expressiveness

Tension
-------

<img src="img/tension3.png" height=300px>

**Goal:** Find a sweet spot?

Refinement Types
----------------

<br>
<br>

[[continue]](01_SimpleRefinements.lhs.slides.html)
