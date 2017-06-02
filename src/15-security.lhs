<div class="hidden">

\begin{code}
{-# LANGUAGE TupleSections       #-}
{-@ LIQUID "--no-warnings"       @-}
{-@ LIQUID "--short-names"       @-}
{- LIQUID "--diff"              @-}
{-@ LIQUID "--no-pattern-inline" @-}

module Security where

import Prelude hiding (print)
import Tagged 

\end{code}

</div>

<br>
<br>
<br>
<br>
<br>



Information Flow Security
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


LIFTY* (Liquid Information Flow TYpes) 
--------------------------------------------------

<br>

Use Liquid Types to encode (and repair) information flow.

<br>

Policy Agnostic Programming 

  - Programmer only cares about functionality. 
  - Policies are encoded as liquid types. 
  - Vefirier automatically insert checks to enforce policies. 

<br>
<br>

*Type-Driven Repair for Information Flow Security by Polikarpova et. al.
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

Example: Conference Managment System
----------------------

<br> 
\begin{code}
showPaper :: PaperId -> IO ()
showPaper pid = print getCurrentUser $ do 
   title     <- getTitle pid
   authors   <- getAuthors pid 
   return (title ++ ":_" ++ show authors) 
\end{code}

<br>
**Blind Review Policy:** Only Chair can see Authors.
<br>
**Policy Violation:** Look at the type error!
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


Policies as Refinement Types
----------------------

<br> 
**Blind Review Policy:** Only Chair can see Authors.
<br>

\begin{spec}
getAuthors :: PaperId -> Tagged <{\u -> u == Chair}> [User]
\end{spec}

<br>
<br>
where the `Tagged` monad is policy parametric
<br>
<br>
\begin{spec}
data Tagged <p :: User -> Bool> a
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


Policy Propagation: The Tagged Monad
-------------------------------------

<br>
\begin{spec}
(>>=)  :: forall <p :: User -> Bool>. 
          Tagged <p> a
       -> (a -> Tagged <p> b)
       -> Tagged <p> b

return :: forall <p :: User -> Bool>. 
          a -> Tagged <p> a 

print  :: forall <p :: User -> Bool>. 
          viewer:Tagged <p> (User<p>) 
       -> msg:Tagged <p> String 
       -> IO ()
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

The Chair can see more...
-------------------------
<br>

\begin{spec}
{-@ whenUserIsChair :: forall <p :: User -> Bool>.  
     Tagged <{\v -> v == Chair}>[a] 
  -> Tagged <p> [a] 
   @-}
whenUserIsChair t = do 
  u <- getCurrentUser 
  if u == Chair then t else return []
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

Program Repair
--------------
<br>

Using the `whenUserIsChair` conditional

<br>

\begin{code}
showPaperFixed :: PaperId -> IO ()
showPaperFixed pid = print getCurrentUser $ do 
   title     <- getTitle pid
   authors   <- {- whenUserIsChair $ -} getAuthors pid 
   return (title ++ ":_" ++ show authors) 
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


More complex policies
-------------------

<br>
<br>

- Viewer should have same privilages as the user (bug in HotCRP).

- Only print paper status after notification date (bug in EDAS).
 

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
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
4. **Termination:** Semantic Termination Checking
5. **Reflection:** Allow Haskell functions in Logic 
6. **Case Study:** Prove Program Equivalence
7. <div class="fragment"> **Information Flow Security Policies** </div>

<br>
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

