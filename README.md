# curry-agda

This repository contains [Agda](http://wiki.portal.chalmers.se/agda)
libraries and examples to prove properties of operations defined in
[Curry](http://curry-language.org/).

The ideas behind these libraries and proofs are discussed in
[this paper](http://www-ps.informatik.uni-kiel.de/~mh/papers/WFLP16_Agda.html).

The Agda proofs require the
[Iowa Agda Library](https://svn.divms.uiowa.edu/repos/clc/projects/agda/ial).

The recent Curry distributions
[PAKCS](http://www.informatik.uni-kiel.de/~pakcs/)
and
[KiCS2](http://www-ps.informatik.uni-kiel.de/kics2/)
contain automatic translator from Curry into the format of these proofs.

Contents:

 * `nondet`: This directory contains the libraries
   (`nondet.agda` and `nondet-thms.agda`) and proofs for the
   _set of values_ representation of non-determinism in Agda.
 * `choices`: This directory contains the proofs for the
   _planned choices_ representation of non-determinism in Agda.
