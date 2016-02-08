<br>
<br>
<br>
<br>

<h1 style="border-bottom:none">LiquidHaskell: Liquid Types for Haskell</b>

<h4 style="border-bottom:none"><i>Niki Vazou (University of California, San Diego)</i></h4>

<br>
<br>

<br>
<br>

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


Well-Typed Programs *Can* Go Wrong
==================================


<div class="hidden">

\begin{code}
main = putStrLn "Easter Egg: to force Makefile"
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



Division By Zero
----------------


<div class="fragment">
\begin{spec}
λ> let average xs = sum xs `div` length xs

λ> average [100, 202, 300]
200
\end{spec}
</div>

<br>

<div class="fragment">
\begin{spec}
λ> average []
*** Exception: divide by zero
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



Partial Functions
------------

<div class="fragment">
\begin{spec}
λ> head "compose"
'c'
\end{spec}
</div>

<br>

<div class="fragment">
\begin{spec}
λ> head []
*** Exception: Prelude.head: empty list
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



Fuctional Correctness
---------------------

<div class="fragment">
\begin{spec}
λ> sort [42, 5, 3, 1]
[5, 3]
\end{spec}
</div>

<div class="fragment">
<br>
\begin{spec}
λ> (incr . incr) 40
0
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



Goal: Extend Type System
------------------------

<br>

<br>

+ To prevent **wider class** of errors

+ To enforce **program specific** properties

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>







Plan
----

<br>

1. [**Refinements Types**](02-refinements.html)
2. [**Data Types**](03-datatypes.html)
3. [**Abstract Refinements**](04-abstract-refinements.html)
4. [**Bounded Refinements**](05-bounded-refinements.html)


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


Evaluation
----------

<br>

+ Diverse Code Bases

+ 10KLoc / 56 Modules

+ Memory Safety, Termination, Functional Correctness

<br>

<div class="fragment">
**Inference is Crucial**
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

Evaluation
----------


<img src="img/code-spec-indiv.png" height=250px>


+ **Specifications:** 1 / 10 LOC  (*ok*)

+ **Compile Time:**  1s / 10 LOC  (*not ok!*)

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


<div class="hidden">

Evaluation
----------


**Library**                     **LOC**     **Specs**      **Time**
---------------------------   ---------   -----------    ----------
`XMonad.StackSet`                   256            74          27s
`Data.List`                         814            46          26s
`Data.Set.Splay`                    149            27          27s
`Data.Vector.Algorithms`           1219            76          89s
`HsColour`                         1047            19         196s
`Data.Map.Base`                    1396           125         174s
`Data.Text`                        3128           305         499s
`Data.Bytestring`                  3505           307         294s
**Total**                     **11512**       **977**    **1336s**
---------------------------   ---------   -----------    ----------

</div>





Conclusion
----------

<br>

**Refinement Types:** Automated Dependent Typing via SMT

<br>

<div class="fragment">

-------------------       ------------------------------------------------
**Properties:**           Predicates  *+ Types*
**Proofs:**               SMT Solvers *+ Subtyping*
**Inference:**            Abstract Interpretation *+ Hindley-Milner*
-------------------       ------------------------------------------------

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




Thank You!
----------

<br>
<br>

`cabal install liquidhaskell`
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
