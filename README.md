# Sic

Metatheory and compilers for the Sic programming language.
Its design is decided by the RFCs of [`sic-lang/rfcs`](https://github.com/sic-lang/rfcs).

## Metatheory

The metatheory, in `theory/`, formalizes in Lean the type system of [RFC 36](https://github.com/sic-lang/rfcs/pull/36), still under review; no compiler exists yet.

The core follows the graded type theory of the [formalization of Abel, Danielsson and Eriksson](https://github.com/graded-type-theory/graded-type-theory/tree/1f720ee636cb16aec130cc1ddc1c32acea8809d0) (ADE), from which it differs by its three modes, its grades, which count the uses at run time and in total, and its levels, which are not terms, and the proofs follow most of its metatheory, from the logical relation to the properties of the usage.
Of the [formalization of the logical relation by Pujet](https://github.com/loic-p/logrel-mltt/tree/ef332527cb2203216ffe9d59b82e98ff13b2db3d), the proofs follow the encoding of the logical relation as a predicate indexed by its interpretation, which needs no induction-recursion, absent from Lean.
The comments `-- ADE:` and `-- Pujet:` on the declarations name their counterparts in these formalizations, at the commits `1f720ee6` of ADE and `ef332527` of Pujet.

## License

Licensed under the [Apache License, Version 2.0](LICENSES/Apache-2.0.txt) with [LLVM Exceptions](LICENSES/LLVM-exception.txt) (`Apache-2.0 WITH LLVM-exception`).
