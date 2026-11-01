# Sic

Metatheory and compilers for the Sic programming language.
Its design is decided by the RFCs of [`sic-lang/rfcs`](https://github.com/sic-lang/rfcs).

## Status

The metatheory, in [`theory/`](theory), formalizes in Lean the core of [RFC 24](https://github.com/sic-lang/rfcs/pull/24), still under review, and the [documentation of the metatheory](https://sic-lang.github.io/sic/) presents each of its modules.
No compiler exists yet.

### Elements of the Core

Each element of RFC 24, named as the RFC writes it, links to its definition in Lean, or is not modeled yet.

| Section of RFC 24 | Element | Definition |
| --- | --- | --- |
| Grading | Multiplicities | [`Multiplicity`](https://sic-lang.github.io/sic/Sic/Multiplicity.html#Sic.Multiplicity) |
| | Grades | [`Grade`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade) |
| | Modes | [`Mode`](https://sic-lang.github.io/sic/Sic/Mode.html#Sic.Mode) |
| Judgments | `⊢ Γ` | [`WfCon`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfCon) |
| | `Γ ⊢ A` | [`IsType`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.IsType) |
| | `Γ ⊢ A ≡ B` | [`TypeEq`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.TypeEq) |
| | `Γ ⊢ t : A` | [`HasType`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasType) |
| | `Γ ⊢ t ≡ u : A` | [`TermEq`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.TermEq) |
| | `γ ▶_m t` | [`Usage`](https://sic-lang.github.io/sic/Sic/Core/Usage.html#Sic.Core.Usage) |
| Universes | Levels | [`Level`](https://sic-lang.github.io/sic/Sic/Core/Level.html#Sic.Core.Level) |
| | `U_l` | [`Term.univ`](https://sic-lang.github.io/sic/Sic/Core/Syntax.html#Sic.Core.Term.univ) |
| Strict Propositions | `Ω_l` | Not yet |
| Functions | `Π^q_p (x : A). B` | [`Term.pi`](https://sic-lang.github.io/sic/Sic/Core/Syntax.html#Sic.Core.Term.pi) |
| | `λ_p (x : A). t` | [`Term.lam`](https://sic-lang.github.io/sic/Sic/Core/Syntax.html#Sic.Core.Term.lam) |
| | `t ∘_p a` | [`Term.app`](https://sic-lang.github.io/sic/Sic/Core/Syntax.html#Sic.Core.Term.app) |
| Records | `Σ^◇_κ{f₁ :^q₁_p₁ A₁, …, fₙ :^qₙ_pₙ Aₙ}` | Not yet |
| | `R{t₁, …, tₙ}` | Not yet |
| | `match_r t as z return C with R{x₁, …, xₙ} ⇒ u` | Not yet |
| | `π_{R, i} t` | Not yet |
| Erasure | `t•` | Not yet |

### Properties

The formalization proves the admissible properties that RFC 24 lists, followed by the properties expected of a type system.

| Property | Status |
| --- | --- |
| Context conversion | Proved: [`HasType.conv_con`](https://sic-lang.github.io/sic/Sic/Core/ContextConversion.html#Sic.Core.HasType.conv_con) |
| Level instantiation | Proved: [`HasType.substLevels`](https://sic-lang.github.io/sic/Sic/Core/LevelInstantiation.html#Sic.Core.HasType.substLevels) |
| Presuppositions | Proved: [`HasType.wfType`](https://sic-lang.github.io/sic/Sic/Core/WellFormed.html#Sic.Core.HasType.wfType) |
| Subject reduction | Proved: [`HasType.termRed`](https://sic-lang.github.io/sic/Sic/Core/SubjectReduction.html#Sic.Core.HasType.termRed) |
| Substitution | Proved: [`HasType.subst`](https://sic-lang.github.io/sic/Sic/Core/TypedSubstitution.html#Sic.Core.HasType.subst), and for the usage [`Usage.subst`](https://sic-lang.github.io/sic/Sic/Core/UsageSubstitution.html#Sic.Core.Usage.subst) |
| Types in sorts | Proved: [`IsType.sort`](https://sic-lang.github.io/sic/Sic/Core/WellFormed.html#Sic.Core.IsType.sort) |
| Usage preservation | Proved: [`Usage.termRed`](https://sic-lang.github.io/sic/Sic/Core/UsageReduction.html#Sic.Core.Usage.termRed) |
| Weakening | Proved: [`HasType.wk`](https://sic-lang.github.io/sic/Sic/Core/TypedSubstitution.html#Sic.Core.HasType.wk), and for the usage [`Usage.wk`](https://sic-lang.github.io/sic/Sic/Core/UsageWeakening.html#Sic.Core.Usage.wk) |
| Normalization to weak head normal forms | Proved: [`HasType.whnf`](https://sic-lang.github.io/sic/Sic/Core/Normalization.html#Sic.Core.HasType.whnf) |
| Injectivity of the types of functions | Proved: [`TypeEq.pi_inj`](https://sic-lang.github.io/sic/Sic/Core/Injectivity.html#Sic.Core.TypeEq.pi_inj) |
| Canonicity | Proved: [`HasType.canonical_pi`](https://sic-lang.github.io/sic/Sic/Core/Canonicity.html#Sic.Core.HasType.canonical_pi) and [`HasType.canonical_univ`](https://sic-lang.github.io/sic/Sic/Core/Canonicity.html#Sic.Core.HasType.canonical_univ) |
| Consistency | Proved: [`not_hasType_forall`](https://sic-lang.github.io/sic/Sic/Core/Consistency.html#Sic.Core.not_hasType_forall) |
| Decidability of the usage | Proved: [`Usage.decidable`](https://sic-lang.github.io/sic/Sic/Core/UsageInference.html#Sic.Core.Usage.decidable) |
| Decidability of the typing | Not yet |
| Soundness of the erasure | Not yet |

### Meaning of the Definitions

The checks of `SicTest/` demonstrate that the definitions have the meaning that the RFCs specify, on examples such as [the Church numerals](https://sic-lang.github.io/sic/SicTest/ChurchNumerals/Typing.html), and the following ones check the meaning of the definitions themselves.

| Definition | Meaning | Checks |
| --- | --- | --- |
| Multiplicities | The sum, the product and the meet give the best multiplicity for the numbers of uses that they combine, and the order is the inclusion of these numbers | [`add_best`](https://sic-lang.github.io/sic/SicTest/Multiplicity.html#SicTest.Multiplicity.add_best), [`mul_best`](https://sic-lang.github.io/sic/SicTest/Multiplicity.html#SicTest.Multiplicity.mul_best), [`min_best`](https://sic-lang.github.io/sic/SicTest/Multiplicity.html#SicTest.Multiplicity.min_best), [`le_iff`](https://sic-lang.github.io/sic/SicTest/Multiplicity.html#SicTest.Multiplicity.le_iff) |
| Grades | The same, at run time and in total | [`add_best`](https://sic-lang.github.io/sic/SicTest/Grade.html#SicTest.Grade.add_best), [`mul_best`](https://sic-lang.github.io/sic/SicTest/Grade.html#SicTest.Grade.mul_best), [`min_best`](https://sic-lang.github.io/sic/SicTest/Grade.html#SicTest.Grade.min_best), [`le_iff`](https://sic-lang.github.io/sic/SicTest/Grade.html#SicTest.Grade.le_iff) |
| Modes | A use counts in each mode as RFC 24 says | [`counts_zeroZero`](https://sic-lang.github.io/sic/SicTest/Mode.html#SicTest.Mode.counts_zeroZero), [`counts_zeroOne`](https://sic-lang.github.io/sic/SicTest/Mode.html#SicTest.Mode.counts_zeroOne), [`counts_oneOne`](https://sic-lang.github.io/sic/SicTest/Mode.html#SicTest.Mode.counts_oneOne) |
| Levels | Without variables, two levels are equal when they have the same value | [`equiv_iff_eval`](https://sic-lang.github.io/sic/SicTest/Meaning/Level.html#SicTest.Meaning.Level.equiv_iff_eval) |
| Weakenings | They are exactly the strictly increasing maps of the variables | [`strictMono_iff_wk`](https://sic-lang.github.io/sic/SicTest/Meaning/Substitution.html#SicTest.Meaning.Substitution.strictMono_iff_wk) |
| Weakening of the grade vectors | A moved variable keeps its grade, and an added variable gets `𝟘` | [`wk_var`](https://sic-lang.github.io/sic/SicTest/Meaning/UsageWeakening.html#SicTest.Meaning.UsageWeakening.wk_var), [`wk_added`](https://sic-lang.github.io/sic/SicTest/Meaning/UsageWeakening.html#SicTest.Meaning.UsageWeakening.wk_added) |
| Substitution of the grade vectors | `γ <* Ψ` is the sum of the vectors `γ x • Ψ x` | [`subst_apply`](https://sic-lang.github.io/sic/SicTest/GradeMatrix.html#SicTest.GradeMatrix.subst_apply) |
| Usage | The multiplicities `0`, `1` and `ω` allow no use, exactly one, and any number | [`usage_zero`](https://sic-lang.github.io/sic/SicTest/Rfc24/Usage.html#SicTest.Rfc24.Usage.usage_zero), [`usage_one`](https://sic-lang.github.io/sic/SicTest/Rfc24/Usage.html#SicTest.Rfc24.Usage.usage_one), [`usage_omega`](https://sic-lang.github.io/sic/SicTest/Rfc24/Usage.html#SicTest.Rfc24.Usage.usage_omega) |

### Formalizations Followed

The core follows the graded type theory of the [formalization of Abel, Danielsson and Eriksson](https://github.com/graded-type-theory/graded-type-theory/tree/1f720ee636cb16aec130cc1ddc1c32acea8809d0) (ADE), from which it differs by its three modes, its grades, which count the uses at run time and in total, and its levels, which are not terms, and the proofs follow most of its metatheory, from the logical relation to the properties of the usage.
Of the [formalization of the logical relation by Pujet](https://github.com/loic-p/logrel-mltt/tree/ef332527cb2203216ffe9d59b82e98ff13b2db3d), the proofs follow the encoding of the logical relation as a predicate indexed by its interpretation, which needs no induction-recursion, absent from Lean.
The comments `-- ADE:` and `-- Pujet:` on the declarations name their counterparts in these formalizations, at the commits `1f720ee6` of ADE and `ef332527` of Pujet.

## License

Licensed under the [Apache License, Version 2.0](LICENSES/Apache-2.0.txt) with [LLVM Exceptions](LICENSES/LLVM-exception.txt) (`Apache-2.0 WITH LLVM-exception`).
