# Sic

Metatheory and compilers for the Sic programming language.
Its design is decided by the RFCs of [`sic-lang/rfcs`](https://github.com/sic-lang/rfcs).

## Status

The metatheory, in [`theory/`](theory), formalizes in Lean the core of [RFC 24](https://github.com/sic-lang/rfcs/pull/24), still under review: so far its universes, with level variables, and its functions.
No compiler exists yet.

The [documentation of the metatheory](https://sic-lang.github.io/sic/) presents each module, and reads in this order:

1. [the terms](https://sic-lang.github.io/sic/Sic/Core/Syntax.html), with their [levels](https://sic-lang.github.io/sic/Sic/Core/Level.html) and their [grades](https://sic-lang.github.io/sic/Sic/Grade.html);
2. [the typing](https://sic-lang.github.io/sic/Sic/Core/Typing.html) and [the usage](https://sic-lang.github.io/sic/Sic/Core/Usage.html), the judgments of RFC 24, with the [modes](https://sic-lang.github.io/sic/Sic/Mode.html) and the [grade vectors](https://sic-lang.github.io/sic/Sic/GradeVector.html) of the usage;
3. [the reduction](https://sic-lang.github.io/sic/Sic/Core/Reduction.html), which the proofs use to compare terms;
4. [the logical relation](https://sic-lang.github.io/sic/Sic/Core/Reducibility/LogicalRelation.html), from which [the fundamental lemma](https://sic-lang.github.io/sic/Sic/Core/Reducibility/Fundamental.html) proves [the normalization](https://sic-lang.github.io/sic/Sic/Core/Normalization.html);
5. its consequences: [the injectivity of the types](https://sic-lang.github.io/sic/Sic/Core/Injectivity.html), [the canonicity](https://sic-lang.github.io/sic/Sic/Core/Canonicity.html) and [the consistency](https://sic-lang.github.io/sic/Sic/Core/Consistency.html).

The checks of `SicTest/` show that the definitions mean what the RFCs say, on examples such as [the Church numerals](https://sic-lang.github.io/sic/SicTest/ChurchNumerals/Typing.html).

The comments `-- ADE:` and `-- Pujet:` on the declarations name their counterparts in the [formalization of Abel, Danielsson and Eriksson](https://github.com/graded-type-theory/graded-type-theory/tree/1f720ee636cb16aec130cc1ddc1c32acea8809d0), at its commit `1f720ee6`, and in the [formalization of the logical relation by Pujet](https://github.com/loic-p/logrel-mltt/tree/ef332527cb2203216ffe9d59b82e98ff13b2db3d), at its commit `ef332527`.

## License

Licensed under the [Apache License, Version 2.0](LICENSES/Apache-2.0.txt) with [LLVM Exceptions](LICENSES/LLVM-exception.txt) (`Apache-2.0 WITH LLVM-exception`).
