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

+ 02-measures.lhs
    - foldr1, map  (BOS14/001_Refinements.hs)

+ 03-sort.lhs
    - insert-sort (n), insert-sort (elts), insert-sort (ord)
    
+ 04-eval.lhs (BOOK)

- 05-bytestring.lhs (BOS14)


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
+ SHOW wtAverage

-- SETS

+ SHOW insert/sort
+ SHOW elems
+ SHOW insert/sort' (compare)

{-@ average   :: ListNE Nat -> Nat @-}
average xs    = tot `divide` n
  where
    total     = foldr1 (+) xs
    n         = length xs


data Month = Jan | Feb | Mar | April | May  -- | ...
type AnnualRain = {v: [(Month, Nat)] | length v == 12 }

rainAverage :: AnnualRain -> Nat
rainAverage = average . map snd

map f []     = []
map f (x:xs) = f x : map f xs


{-@ wtAverage :: {v: List (Pos, Pos) | size v > 0} -> Int @-}
wtAverage wxs = total `divide` weights
  where
    total     = sum $ map (\(w, x) -> w * x) wxs
    weights   = sum $ map (\(w, _) -> w    ) wxs
    sum       = foldr1 plus -- (+)
    plus      = (+)


Comparison with DT
------------------

[HS+DT proof](https://github.com/jstolarek/dep-typed-wbl-heaps-hs/blob/master/src/TwoPassMerge/CombinedProofs.hs#L68)

[HS](https://github.com/jstolarek/dep-typed-wbl-heaps-hs/blob/master/src/TwoPassMerge/NoProofs.hs#L96)

[HS+Liquid](https://github.com/ucsd-progsys/liquidhaskell/blob/master/tests/pos/WBL.hs#L129)


https://github.com/davidfstr/idris-insertion-sort/tree/master
