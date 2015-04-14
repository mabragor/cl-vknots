cl-vknots
=========

Assorted collection of tools to calculate (cabled) HOMFLY polynomials for (virtual) knots
and links, from the Khovanov hypercube formalism.

This code is based on  work with A.Morozov and An.Morozov. The arXiv paper explaining
the underlying ideas will follow, when it's ready.

Note: some of the functionality (and most importantly, the tests) are implemented through
interface with Wolfram Mathematica and Mathematica package KnotTheory, which can be
downloaded from www.katlas.org.

Calculate HOMFLY polynomial for the twisted unknot.
```lisp
(homfly-serial-toolchian '((1 1) (2 1)))
```

or, the same with query to Katlas of what is braid representation for twisted unknot,
and subsequent conversion to Seifert form (the form in the example above)
```lisp
(homfly-serial-toolchain (planar->seifert (braid->planar (get-braid-rep1 (wm-torus-knot 1 2)))))
"-(q^(-1 + N)*(q*q[-1 + N] - q[N])*q[N])"			 
```

Currently all answers for knots in Rolfsen table up to 10 crossings, that program can calculate,
coincide with Katlas answers, modulo substitution q -> 1/q (the unit tests, in particular, include this check).


Basic ideas, embedded in the algorithm
--------------------------------------

  * dimensions at the vertices of secondary quantum hypercube are encoded in dessins d'enfant,
    or fat graphs
  * there is a set of recursion relations on these fat graphs, which allows in most cases
    to reduce them to numbers.
  * these relations are:
    * non-topologically-invariant analogs of Reidemeister moves
    * flip-covariance
  * the usual "change of starting vertex" for summation when considering non-Seifert knot
    can be reformulated as assignment of q-charge to vertices of the hypercube.


TODO
----

  A couple of things needs to be done for the instrument to be more useable

  * add unit-tests for virtual knots
  * add search over flips of the horde-diagrams, to tackle difficult cases
  * express HOMFLY in a-z variables.
  * add pre-calculation of horde-diagrams and memoization of results