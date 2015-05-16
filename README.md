README
======

This repository has the materials for a 2-hour workshop on
[Programming with Refinement Types](http://www.refinement-types.org)
which is also a tutorial introduction to [LiquidHaskell](https://github.com/ucsd-progsys/liquidhaskell).

Build
-----

To build rust-style html (in dist/_site)

     $ make html

To build reveal.js slides (in dist/_slides)

     $ make slides

Contents
--------

+ 00-motivation.lhs

- 01-logic.lhs

- 02-refinements.lhs (div, foldr1, map, pos etc. --> CSV, weights, zipWith)
    (BOS/hs)
- 03-eval.lhs
    (BOOK)
- 04-bst.lhs
    (BOOK)
- 05-bytestring.lhs
    (from BOS14)


Comparison with DT
------------------

[HS+DT proof](https://github.com/jstolarek/dep-typed-wbl-heaps-hs/blob/master/src/TwoPassMerge/CombinedProofs.hs#L68)

[HS](https://github.com/jstolarek/dep-typed-wbl-heaps-hs/blob/master/src/TwoPassMerge/NoProofs.hs#L96)

[HS+Liquid](https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/WBL.hs#L129)

