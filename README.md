README
======

This repository has the materials for a 2-hour workshop on
[Programming with Refinement Types](http://www.refinement-types.org)
which is also a tutorial introduction to [LiquidHaskell](https://github.com/ucsd-progsys/liquidhaskell).

TODO
----

- remove nasty "fix@#$@#$" gibberish in error messages
- remove GHC.Types.Int ~~~~> Int     in error messages
- build VM image with emacs 
- build image with spacemacs
- post _site   on refinement-types.org
- post _slides on refinement-types.org


Build
-----

To build rust-style html (in dist/_site)

     $ make html

To build reveal.js slides (in dist/_slides)

     $ make slides

Contents
--------

+ 00-motivation.lhs

+ 01-refinements.lhs
    + div, pos, etc.

+ 02-datatypes.lhs
    - foldr1, map  (BOS14/001_Refinements.hs)

+ 03-case-study-sorting.lhs
    - insert-sort (n), insert-sort (elts), insert-sort (ord)
    
+ 04-case-study-evaluator.lhs (BOOK)

- 05-case-study-bytestring.lhs (BOS14)


02-measures
-----------

+ DEF  type    list
+ DEF  measure length
+ EX   head/tail 
+ SHOW alias ListNE
+ SHOW append
+ SHOW filter
+ SHOW foldr1
+ EX   average
+ EX   rainAverage / map

HEREHEREHEREHEREHERE

-- SETS

+ SHOW insert/sort
+ SHOW elems
+ SHOW insert/sort' (compare)

Comparison with DT
------------------

[HS+DT proof](https://github.com/jstolarek/dep-typed-wbl-heaps-hs/blob/master/src/TwoPassMerge/CombinedProofs.hs#L68)

[HS](https://github.com/jstolarek/dep-typed-wbl-heaps-hs/blob/master/src/TwoPassMerge/NoProofs.hs#L96)

[HS+Liquid](https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/WBL.hs#L129)


https://github.com/davidfstr/idris-insertion-sort/tree/master
