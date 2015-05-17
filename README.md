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

+ 01-refinements.lhs
    + div, pos, etc.
    - foldr1, map  (BOS14/001_Refinements.hs)
    - CSV, weights, zipWith

- 02-eval.lhs (BOOK)

- 03-bst.lhs  (BOOK)

- 04-bytestring.lhs (BOS14)


Comparison with DT
------------------

[HS+DT proof](https://github.com/jstolarek/dep-typed-wbl-heaps-hs/blob/master/src/TwoPassMerge/CombinedProofs.hs#L68)

[HS](https://github.com/jstolarek/dep-typed-wbl-heaps-hs/blob/master/src/TwoPassMerge/NoProofs.hs#L96)

[HS+Liquid](https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/WBL.hs#L129)

