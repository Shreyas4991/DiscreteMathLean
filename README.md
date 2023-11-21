# Discrete Math in Lean

The idea here is to build a library of mathematical results useful for Theoretical Computer Scientists. This means most of the results will be concerned with discrete and finite structures, even when more general results exist, perhaps even in Mathlib. The library should eventually act as a complement to Lean's main math library [Mathlib](https://github.com/leanprover-community/mathlib4), but give priority to styles and methods that work better for theoretical computer scientists. This could mean the following:

* We focus on finite and discrete versions of theorems and results in combinatorics, probability etc. If a simple proof  works but only for finite structures, then we prefer that to instantiating a more general lemma from mathlib.
  
* Where it is sensible to do so, we should not hesitate to use tactics and lemmas from mathlib. If a theorem is a trivial instantiation of a more abstract version in mathlib, it might be reasonable to use this theorem, as long as the corresponding proof specific to finite/discrete structures doesn't exist or is more tedious.

* To emphasise again: We wantonly ignore infinite cardinality structures, unless they are useful to us. An example of an infinite structure that is useful to us is ordinal arithmetic which finds its uses in Buchi automaton. In such cases, if Mathlib has an implementation that is comprehensible to computer scientists, we should try to stick to that version.

* It should be perfectly okay to restate the same results in different abstractions and prove them within those abstractions. Equivalences can be established further down the line. For example, a result on graphs could exist in both spectral and combinatorial forms. If a probability lemma has a combinatorial version, it should be perfectly fine for both these versions to exist.