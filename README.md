cl-vknots
=========

Convenient tools to calculate (cabled) HOMFLY polynomials for knots
and links, usual and virtual, from the Khovanov hypercube formalism.

This branch specifically attempts to calculate everything without flips.
Just to see, how far we can go without them.

This code is based on  work with A.Morozov and An.Morozov. The arXiv paper explaining
the underlying ideas can be found at http://arxiv.org/abs/1506.07516

Note: some of the functionality (and most importantly, the tests) are implemented through
interface with Wolfram Mathematica and Mathematica package KnotTheory, which can be
downloaded from www.katlas.org. KnotTheory is to be placed under src/ subdirectory of this project.
The incorrect setup here may lead to hangs of the machine. You've been warned!)

Main interface
--------------

Main function is DWIM-HOMFLY, which (tries) to automatically determine,
what you enter (planar diagram of a knot, description of fat graph, or a horde diagram)
and act calculate HOMFLY for it

```lisp
;;; calculate HOMFLY for trefoil
(dwim-homfly "Knot[3,1]") ;; specify input by number in Rolfsen table
(dwim-homfly "TorusKnot[3,2]") ;; or explicitly as torus knot
(dwin-homfly "TorusKnot[2,3]")
```

```lisp
;;; calculate HOMFLY for eight diagram (twisted unknot)
(dwim-homfly '((b 1 2 1 2))) ;; input in form of planar diagram
(dwim-homfly '((1 1) (2 1))) ;; input in form of dessin d'enfant
```

```lisp
;;; calculate HOMFLY for virtual Hopf link
(dwim-homfly '((1 2))) ;; input as horde diagram in form of edge numbers
(dwim-homfly '(1 -1)) ;; input as horde diagram in form of edge lengths
```


The rest of this readme describes more esoteric functionality, in case
this simple one is not working properly or is insufficient for your needs.

Simple cabled answers
---------------------

DWIM-HOMFLY has :CABLE parameter, which lets you calculate link-free cabled
version of HOMFLY

```lisp
(dwim-homfly "Knot[3,1]" :cable 2) ;; two strand cabled HOMFLY for trefoil
```

However, since cabling is defined only before going to dessins (i.e. not for dessins and hordes),
when asked to calculate cabled HOMFLY for dessin, DWIM-HOMFLY just calculates fundamental (non-cabled)
version.

The peculiarities
-----------------

Calculate HOMFLY polynomial for the twisted unknot.
```lisp
(homfly-serial-toolchian '((1 1) (2 1)))
```

Same can be done more conveniently, by querying Katlas for braid representation for twisted unknot
(call to GET-BRAID-REP1), then constructing planar diagram from braid (call to BRAID->PLANAR)
and then constructing fat-graph form from planar diagram (call to PLANAR->SEIFERT).
This fat graph form is exactly as in example above, so we feed it to HOMFLY-SERIAL-TOOLCHAIN.
```lisp
(homfly-serial-toolchain (planar->seifert (braid->planar (get-braid-rep1 (wm-torus-knot 1 2)))))
"-(q^(-1 + N)*(q*q[-1 + N] - q[N])*q[N])"			 
```

For historical reasons, there are two HOMFLY-calculating functions, HOMFLY-SERIAL-TOOLCHAIN and
HOMFLY-ACTUAL-SERIAL-TOOLCHAIN, which internally differ only in convention about q-weights
of hypercube vertices (not to be confused with q-dimensions of vertices, which are the same).
Outputs of these functions coincide upto change q -> 1/q


Currently, program can calculate fundamental HOMFLY polynomials for all knots in Rolfsen table,
and the check that this is the case is included in program's test-suite.
To run it, do.
```lisp
(ql:quickload 'cl-vknots-tests)
(in-package cl-vknots-tests)
(explain! (run 'rolfsen-actual-homflies))
```

To calculate HOMFLY polynomial for individual knot (say, trefoil) from Rolfsen table, do
```lisp
(homfly-actual-serial-toolchain (planar->seifert (braid->planar (get-braid-rep1 "Knot[3,1]"))))
```


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



Planar diagram format
---------------------

By no means is the algorithm limited to calculation of HOMFLY only for braids.
It is just that braid representation is easy to fetch from Katlas. But you can
always type arbitrary (possibly, virtual) planar diagram yourself.
For example, for virtual trefoil (2.1-knot in terminology of www.math.toronto.edu/~drorbn/Students/GreenJ/
planar diagram description is
```lisp
'((w 1 2 3 4)
  (n 3 4 5 6)
  (w 5 6 1 2))
```
The format is almost self-explanatory. We have a list of three vertices, two of them are "white"
(letter W at the beginning of the sublist) and one is "sterile", or "neutral" (letter N at the beginning
of the sublist). Further, we have 6 edges, connecting those vertices with each other, and
remaining parts of the sublists describe, which edge connects, in order, to bottom left, bottom right, top left
and top right corners of the given vertex. Corners are determined from the picture such that strands go
from bottom left to top right and from bottom right to top left.

More examples of manually typed planar diagrams can be found in src/planar-diagrams.lisp


Cabling
-------

There are two functions to do cabling of a planar diagram
  * CABLE -- does the very naive cabling
  * LINK-FREE-CABLE -- cables with insertion of toric braid, which compensates pairwise
  linking numbers of strands in the cable.

For example, 2-cabled link-free answer for HOMFLY for virtual trefoil can be calculated
like this
```lisp
(homfly-actual-serial-toolchain (planar->seifert (link-free-cable *2.1-knot*)))
```
Of course, variable *2.1-knot*, containing planar diagram of a virtual trefoil,
should be defined beforehand (it is defined in src/planar-diagrams.lisp)


TODO
----

  A couple of things needs to be done for the instrument to be more useable

  * do DWIM-HOMFLY function, which just does calculate HOMFLY for anything,
    without the need to remember all these chains of function calls (!)
  * add unit-tests for virtual knots
  * (done) add search over flips of the horde-diagrams, to tackle difficult cases
  * add fetching of Morse-link representation of the knot from Katlas
  * express HOMFLY in a-z variables.
  * add pre-calculation of horde-diagrams and memoization of results
  * write checks in Mathematica scripts, so that they don't hang and don't loop infinitely