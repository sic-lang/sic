# Sic

Metatheory and compilers for the Sic programming language.
Its design is decided by the RFCs of [`sic-lang/rfcs`](https://github.com/sic-lang/rfcs).

## Status

The metatheory, in [`theory/`](theory), formalizes in Lean the core of Sic, as the following RFCs, still under review, specify it, and the [documentation of the metatheory](https://sic-lang.github.io/sic/) presents each of its modules.
The formalization of the previous version of the core, [RFC 24](https://github.com/sic-lang/rfcs/pull/24) before its rewrite, is being rebuilt on these RFCs, and the checks of the Lean library are those of that version where a row links to them.
No compiler exists yet.

Each row names a rule, a formula or a definition as the RFC writes it, linking to its section, and links to its formalization in Lean, or is not formalized yet.

### [RFC 33](https://github.com/sic-lang/rfcs/pull/33): Grades

#### [Proposal](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#proposal)

| Name | Status |
| --- | --- |
| [Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#multiplicities) | Defined: [`Sic.Multiplicity`](https://sic-lang.github.io/sic/Sic/Multiplicity.html#Sic.Multiplicity), with its sum, product, meet and order |
| [Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#grades) | Defined: [`Sic.Grade`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade), with its sum, product, meet and order |
| [Modes](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modes) | Defined: [`Sic.Mode`](https://sic-lang.github.io/sic/Sic/Mode.html#Sic.Mode) |

#### [Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#grades)

| Name | Status |
| --- | --- |
| [$`(\mathsf{run}_p)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#grades) | Defined: [`run`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.run) |

#### [Meaning](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning)

| Name | Status |
| --- | --- |
| [$`(\mathsf{uses}_u)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Formalized: [`Allows`](https://sic-lang.github.io/sic/SicTest/Multiplicity.html#SicTest.Multiplicity.Allows) |
| [$`(\mathsf{best}_u)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Formalized: [`IsBest`](https://sic-lang.github.io/sic/SicTest/Multiplicity.html#SicTest.Multiplicity.IsBest) |
| [$`(+_u)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Proved: [`add_best`](https://sic-lang.github.io/sic/SicTest/Multiplicity.html#SicTest.Multiplicity.add_best) |
| [$`(\cdot_u)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Proved: [`mul_best`](https://sic-lang.github.io/sic/SicTest/Multiplicity.html#SicTest.Multiplicity.mul_best) |
| [$`(\wedge_u)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Proved: [`min_best`](https://sic-lang.github.io/sic/SicTest/Multiplicity.html#SicTest.Multiplicity.min_best) |
| [$`(\le_u)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Proved: [`le_iff`](https://sic-lang.github.io/sic/SicTest/Multiplicity.html#SicTest.Multiplicity.le_iff) |
| [$`(\mathsf{uses}_p)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Formalized: [`Allows`](https://sic-lang.github.io/sic/SicTest/Grade.html#SicTest.Grade.Allows) |
| [$`(\mathsf{best}_p)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Formalized: [`IsBest`](https://sic-lang.github.io/sic/SicTest/Grade.html#SicTest.Grade.IsBest) |
| [$`(+_p)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Proved: [`add_best`](https://sic-lang.github.io/sic/SicTest/Grade.html#SicTest.Grade.add_best) |
| [$`(\cdot_p)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Proved: [`mul_best`](https://sic-lang.github.io/sic/SicTest/Grade.html#SicTest.Grade.mul_best) |
| [$`(\wedge_p)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Proved: [`min_best`](https://sic-lang.github.io/sic/SicTest/Grade.html#SicTest.Grade.min_best) |
| [$`(\le_p)`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Proved: [`le_iff`](https://sic-lang.github.io/sic/SicTest/Grade.html#SicTest.Grade.le_iff) |
| [$`(\mathsf{sound}_{\mathsf{run}})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Not yet |

#### [Properties](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#properties)

| Name | Status |
| --- | --- |
| [$`(\cdot_{+})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | Proved: [`mul_add`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.mul_add), [`add_mul`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.add_mul) |
| [$`(\cdot_{\wedge})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | Proved: [`mul_min`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.mul_min), [`min_mul`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.min_mul) |
| [$`(+_{\le})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | Proved: [`add_le_add`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.add_le_add) |
| [$`(\wedge_{\le})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | Proved: [`le_min`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.le_min), [`min_le_left`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.min_le_left), [`min_le_right`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.min_le_right) |
| [$`(\mathbb{0}_{p})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | Proved: [`zero_ne_one`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.zero_ne_one), [`add_eq_zero`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.add_eq_zero), [`min_eq_zero`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.min_eq_zero), [`mul_eq_zero`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.mul_eq_zero) |
| [$`(\bigwedge_{p})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#greatest-lower-bounds) | Not yet |
| [$`(\bigwedge_{+})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#greatest-lower-bounds) | Not yet |
| [$`(\bigwedge_{\cdot})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#greatest-lower-bounds) | Not yet |
| [$`(\mathsf{run}_{\mathsf{op}})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#projection) | Not yet |
| [$`(\mathsf{run}_{\le})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#projection) | Not yet |
| [$`(\mathsf{run}_{m})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#projection) | Not yet |
| [$`(\mathsf{run}_{\odot})`$](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#projection) | Not yet |

### [RFC 24](https://github.com/sic-lang/rfcs/pull/24): Graded Dependent Core

#### [Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#levels)

| Name | Status |
| --- | --- |
| [$`(\rho_0)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | Not yet |
| [$`(\rho_+)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | Not yet |
| [$`(\rho_\sqcup)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | Not yet |
| [$`(=_l)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | Not yet |
| [$`(\le_l)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | Not yet |

#### [Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#judgments)

| Name | Status |
| --- | --- |
| [$`(\mathsf{ctx}_\varepsilon)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#contexts) | Not yet |
| [$`(\mathsf{ctx}_x)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#contexts) | Not yet |
| [$`(\mathsf{sig}_\varnothing)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | Not yet |
| [$`(\mathsf{sig}_{\mathcal{D}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | Not yet |
| [$`(\mathsf{sig}_{≔})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | Not yet |
| [$`(\mathsf{sig}_c)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | Not yet |
| [$`(\sqcup_s)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#declarations) | Not yet |
| [$`(\mathsf{ctx}_X)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| [$`(\mathsf{var}_X)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| [$`(\mathsf{tel}_\varepsilon)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| [$`(\mathsf{tel}_{,})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| [$`(\mathsf{tel}_{\equiv\varepsilon})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| [$`(\mathsf{tel}_{\equiv,})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| [$`(\mathsf{var}_{X\equiv})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| [$`(\mathsf{var}_{X\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| [$`(\mathsf{tel}_{\kappa\varepsilon})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#telescopes) | Not yet |
| [$`(\mathsf{tel}_{\kappa,})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#telescopes) | Not yet |
| [$`(\mathsf{arg}_\varepsilon)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| [$`(\mathsf{arg}_x)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| [$`(\mathsf{arg}_X)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| [$`(\mathsf{arg}_{\equiv\varepsilon})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| [$`(\mathsf{arg}_{\equiv x})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| [$`(\mathsf{arg}_{\equiv X})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| [$`(D)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| [$`(D_\equiv)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| [$`(\mathsf{def})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | Not yet |
| [$`(c)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | Not yet |
| [$`(c_{\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | Not yet |
| [$`(\delta)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | Not yet |
| [$`(\mathsf{const})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#constants) | Not yet |
| [$`(\mathsf{var})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#variables) | Not yet |
| [$`(\mathsf{var}_{\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#variables) | Not yet |
| [$`(\mathsf{refl}_{\mathsf{type}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| [$`(\mathsf{sym}_{\mathsf{type}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| [$`(\mathsf{trans}_{\mathsf{type}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| [$`(\mathsf{refl})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| [$`(\mathsf{sym})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| [$`(\mathsf{trans})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| [$`(\mathsf{conv})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#type-conversion) | Not yet |
| [$`(\mathsf{conv}_\equiv)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#type-conversion) | Not yet |
| [$`(\mathsf{sub})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#usage) | Not yet |

#### [Universes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#universes)

| Name | Status |
| --- | --- |
| [$`(U)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-universes) | Not yet |
| [$`(U_\equiv)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-universes) | Not yet |
| [$`(U_{\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-universes) | Not yet |
| [$`(U_{\mathsf{type}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-universes-as-types) | Not yet |
| [$`(U_{\mathsf{type}\equiv})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-universes-as-types) | Not yet |

#### [Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#strict-propositions)

| Name | Status |
| --- | --- |
| [$`(\Omega)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-propositions) | Not yet |
| [$`(\Omega_\equiv)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-propositions) | Not yet |
| [$`(\Omega_{\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-propositions) | Not yet |
| [$`(\Omega_{\mathsf{type}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-propositions-as-types) | Not yet |
| [$`(\Omega_{\mathsf{type}\equiv})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-propositions-as-types) | Not yet |
| [$`(\mathsf{irr})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#proof-irrelevance) | Not yet |

#### [Meaning](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning)

| Name | Status |
| --- | --- |
| [$`(\vDash_{\mathsf{type}\equiv})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`(\vDash_{\mathsf{type}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`(\vDash_\equiv)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`(\vDash)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`(\mathsf{eq}_\varepsilon)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`(\mathsf{eq}_x)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`(\mathsf{eq}_X)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`({\vDash}\Gamma_{\mathsf{type}\equiv})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`({\vDash}\Gamma_{\mathsf{type}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`({\vDash}\Gamma_\equiv)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`({\vDash}\Gamma)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`({\vDash}\mathsf{tel}_{\kappa\varepsilon})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`({\vDash}\mathsf{tel}_{\kappa,})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`({\vDash}\mathsf{ctx}_\varepsilon)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`({\vDash}\mathsf{ctx}_x)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`({\vDash}\mathsf{ctx}_X)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| [$`(\vDash_\rho)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-levels) | Not yet |
| [$`({\vDash}\mathsf{sig}_\varnothing)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | Not yet |
| [$`({\vDash}\mathsf{sig}_{\mathcal{D}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | Not yet |
| [$`({\vDash}\mathsf{sig}_{≔})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | Not yet |
| [$`({\vDash}\mathsf{sig}_c)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | Not yet |
| [$`(\mathsf{eq}_U)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-universes) | Not yet |
| [$`(\mathsf{eq}_{\mathsf{true}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | Not yet |
| [$`(\mathsf{eq}_{\mathsf{false}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | Not yet |
| [$`(\vDash_{\equiv\Omega})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | Not yet |
| [$`(\mathsf{eq}_\Omega)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | Not yet |
| [$`(\mathsf{exact}_\Omega)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | Not yet |
| [$`(\mathsf{sound}_{\mathsf{sig}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |
| [$`(\mathsf{sound}_{\mathsf{ctx}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |
| [$`(\mathsf{sound}_{\mathsf{type}})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |
| [$`(\mathsf{sound}_{\mathsf{type}\equiv})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |
| [$`(\mathsf{sound})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |
| [$`(\mathsf{sound}_\equiv)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |

#### [Properties](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#properties)

| Name | Status |
| --- | --- |
| [$`(\mathsf{subject})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#preservation) | Not yet |
| [$`(\mathsf{usage}_\beta)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#preservation) | Not yet |
| [$`(\mathsf{normal})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#normalization-and-decidability) | Not yet |
| [$`(\mathsf{decidable}_\equiv)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#normalization-and-decidability) | Not yet |
| [$`(\mathsf{decidable}_\vdash)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#normalization-and-decidability) | Not yet |
| [$`(\mathsf{hyp}_\iota)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#consistency-and-canonicity) | Not yet |
| [$`(\mathsf{consistent})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#consistency-and-canonicity) | Not yet |
| [$`(\mathsf{canonical})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#consistency-and-canonicity) | Not yet |
| [$`(\mathsf{hyp}_\bullet)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#erasure-properties) | Not yet |
| [$`(\mathsf{sound}_\bullet)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#erasure-properties) | Not yet |
| [$`(\mathsf{absent}_\bullet)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#erasure-properties) | Not yet |
| [$`(\mathsf{absent}_\circ)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#erasure-properties) | Not yet |
| [$`(\bullet_\circ)`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#erasure-properties) | Not yet |
| [$`(\mathsf{project})`$](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#projection-lemma) | Not yet |

### [RFC 34](https://github.com/sic-lang/rfcs/pull/34): Data and Codata Types

#### [Declarations](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#declarations)

| Name | Status |
| --- | --- |
| [$`(\mathsf{data})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#formation) | Not yet |
| [$`(\mathsf{codata})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#formation) | Not yet |
| [$`(\langle \Theta \rangle_\varepsilon)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#prelude) | Not yet |
| [$`(\langle \Theta \rangle_{,})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#prelude) | Not yet |
| [$`(\langle \bar t \rangle_\varepsilon)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#prelude) | Not yet |
| [$`(\langle \bar t \rangle_{,})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#prelude) | Not yet |
| [$`(\mathsf{lift}_D)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| [$`(\mathsf{lift}_{D'})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| [$`(\mathsf{lift}^{+})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| [$`(\mathsf{lift}^{-})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| [$`(\mathsf{map}_D)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| [$`(\mathsf{map}_{D'})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| [$`(\mathsf{map}^{+})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| [$`(\mathsf{map}^{-})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| [$`(\Pi_D)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| [$`(\Pi_{D'})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| [$`(\Pi_X)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |

#### [Data Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#data-types)

| Name | Status |
| --- | --- |
| [$`(\zeta^{+})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#usage-of-data-types) | Not yet |
| [$`(D^{+}_{\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#usage-of-data-types) | Not yet |
| [$`(D^{+}_{\mathsf{i}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#constructors) | Not yet |
| [$`(D^{+}_{\mathsf{i}\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#constructors) | Not yet |
| [$`(D^{+}_{\mathsf{rec}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#recursor) | Not yet |
| [$`(D^{+}_{\mathsf{rec}\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#recursor) | Not yet |
| [$`(D^{+}_{\mathsf{rec}\beta})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#recursor) | Not yet |
| [$`(D^{+}_\eta)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#extensionality-of-data) | Not yet |

#### [Codata Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#codata-types)

| Name | Status |
| --- | --- |
| [$`(\zeta^{-})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#usage-of-codata-types) | Not yet |
| [$`(D^{-}_\pi)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#destructors) | Not yet |
| [$`(D^{-}_{\pi\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#destructors) | Not yet |
| [$`(\oplus_D)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#corecursor) | Not yet |
| [$`(\oplus_{D'})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#corecursor) | Not yet |
| [$`(D^{-}_{\mathsf{i}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#corecursor) | Not yet |
| [$`(D^{-}_{\mathsf{i}\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#corecursor) | Not yet |
| [$`(D^{-}_{\pi\beta})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#corecursor) | Not yet |
| [$`(D^{-}_\eta)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#extensionality-of-codata) | Not yet |

#### [Meaning](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning)

| Name | Status |
| --- | --- |
| [$`({\vDash}_{\mathsf{data}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-declarations) | Not yet |
| [$`({\vDash}_{\mathsf{codata}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-declarations) | Not yet |
| [$`({\vDash}\mathsf{dtor}_{\kappa\varepsilon})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-declarations) | Not yet |
| [$`({\vDash}\mathsf{dtor}_{\kappa,})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-declarations) | Not yet |
| [$`(\mathsf{eq}_{\mathsf{con}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-data-types) | Not yet |
| [$`(\mathsf{true}_{\mathsf{data}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-data-types) | Not yet |
| [$`(\mathsf{eq}_\mu)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-data-types) | Not yet |
| [$`(\mathsf{eq}_{\mathsf{data}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-data-types) | Not yet |
| [$`(\mathsf{eq}_{\mathsf{corec}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-codata-types) | Not yet |
| [$`(\mathsf{true}_{\mathsf{codata}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-codata-types) | Not yet |
| [$`(\mathsf{eq}_\nu)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-codata-types) | Not yet |
| [$`(\mathsf{eq}_{\mathsf{codata}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-codata-types) | Not yet |
| [$`(\mathsf{incomplete}_{\mathsf{typ}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| [$`(\mathsf{undecidable}_\vDash)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| [$`(\mathsf{incomplete}^{+}_{D\equiv})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| [$`(\mathsf{incomplete}^{-}_{D\equiv})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| [$`(\mathsf{valid}^{+}_\eta)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| [$`(\mathsf{valid}^{-}_\eta)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| [$`(\mathsf{incomplete}^{+}_\eta)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| [$`(\mathsf{incomplete}^{-}_\eta)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |

#### [Properties](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#properties)

| Name | Status |
| --- | --- |
| [$`(\mathsf{sound}_{\mathsf{data}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#obligations-of-the-contract) | Not yet |
| [$`(\mathsf{sound}_{\mathsf{codata}})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#obligations-of-the-contract) | Not yet |
| [$`(\mathsf{usage}^{\pm}_\beta)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#obligations-of-the-contract) | Not yet |
| [$`(\mathsf{project}^{\pm})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#obligations-of-the-contract) | Not yet |
| [$`(\mathsf{rec}_{\bigwedge})`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#usage-of-recursion) | Not yet |
| [$`(\top)`$](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#absorbing-types) | Not yet |

### [RFC 35](https://github.com/sic-lang/rfcs/pull/35): Observational Equality

#### [Equality](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality)

| Name | Status |
| --- | --- |
| [$`(\sim)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#formation-of-equalities) | Not yet |
| [$`(\sim_{\mathsf{irr}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#formation-of-equalities) | Not yet |
| [$`(\sim_{\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#formation-of-equalities) | Not yet |
| [$`(\mathsf{refl})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#reflexivity) | Not yet |
| [$`(\mathsf{refl}_{\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#reflexivity) | Not yet |
| [$`(\mathsf{transp})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#transport) | Not yet |
| [$`(\mathsf{transp}_{\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#transport) | Not yet |
| [$`(\mathsf{ap}_\sim)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#transport) | Not yet |
| [$`(\mathsf{cast})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast) | Not yet |
| [$`(\mathsf{cast}_{\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast) | Not yet |
| [$`(\mathsf{cast}_{\mathsf{refl}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast) | Not yet |

#### [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types)

| Name | Status |
| --- | --- |
| [$`(\sim_U)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| [$`(\sim_\Omega)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| [$`(\sim_{\mathsf{prop}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| [$`(\sim_{\ne})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| [$`(\sim^{+}_D)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| [$`(\sim^{-}_D)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| [$`(\sim_{D\ne})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| [$`(\sim_{\mathsf{tel}\varepsilon})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| [$`(\sim_{\mathsf{tel},})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| [$`(\sim_{\mathsf{dtor}\varepsilon})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| [$`(\sim_{\mathsf{dtor},})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |

#### [Equality of Terms](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-terms)

| Name | Status |
| --- | --- |
| [$`(\sim^{+})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-data) | Not yet |
| [$`(\sim^{+}_{\ne})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-data) | Not yet |
| [$`(\sim_{\mathsf{fields}\varepsilon})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-data) | Not yet |
| [$`(\sim_{\mathsf{fields},})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-data) | Not yet |
| [$`(\sim^{-}_{\mathsf{decl}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-codata) | Not yet |
| [$`(\sim^{-})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-codata) | Not yet |
| [$`(\mathsf{cast}_{\mathsf{tel}\varepsilon})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-and-cast-of-the-telescopes) | Not yet |
| [$`(\mathsf{cast}_{\mathsf{tel},})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-and-cast-of-the-telescopes) | Not yet |

#### [Cast of Terms](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast-of-terms)

| Name | Status |
| --- | --- |
| [$`(\mathsf{cast}^{+})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast-of-data) | Not yet |
| [$`(\mathsf{cast}^{-})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast-of-codata) | Not yet |

#### [Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#quotients)

| Name | Status |
| --- | --- |
| [$`(\mathsf{quotient})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#formation-of-quotients) | Not yet |
| [$`(D^{/}_{\mathsf{i}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| [$`(D^{/}_{\mathsf{i}\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| [$`(D^{/}_{\mathsf{rec}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| [$`(D^{/}_{\mathsf{rec}\mathsf{m}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| [$`(D^{/}_{\mathsf{rec}\beta})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| [$`(\sim^{/})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| [$`(\sim^{/}_{D})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| [$`(\mathsf{cast}^{/})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |

#### [Meaning](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning)

| Name | Status |
| --- | --- |
| [$`(\mathsf{true}_\sim)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-equality) | Not yet |
| [$`(\mathsf{true}_{\sim\mathsf{type}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-equality) | Not yet |
| [$`(\mathsf{valid}_{\mathsf{cast}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-cast) | Not yet |
| [$`({\vDash}_{\mathsf{quotient}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-quotients) | Not yet |
| [$`(\mathsf{eq}^{/})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-quotients) | Not yet |
| [$`(\mathsf{eq}_{\mathsf{quotient}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-quotients) | Not yet |

#### [Properties](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties)

| Name | Status |
| --- | --- |
| [$`(\mathsf{sym}_\sim)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| [$`(\mathsf{trans}_\sim)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| [$`(J_\sim)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| [$`(J_{\sim\beta})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| [$`(\mathsf{sound}_\sim)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| [$`(\mathsf{usage}_{\mathsf{cast}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| [$`(\mathsf{decidable}_{\mathsf{cast}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| [$`(\mathsf{consistent}_\sim)`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| [$`(\mathsf{sound}_{\bullet\mathsf{cast}})`$](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |

### Formalizations Followed

The core follows the graded type theory of the [formalization of Abel, Danielsson and Eriksson](https://github.com/graded-type-theory/graded-type-theory/tree/1f720ee636cb16aec130cc1ddc1c32acea8809d0) (ADE), from which it differs by its three modes, its grades, which count the uses at run time and in total, and its levels, which are not terms, and the proofs follow most of its metatheory, from the logical relation to the properties of the usage.
Of the [formalization of the logical relation by Pujet](https://github.com/loic-p/logrel-mltt/tree/ef332527cb2203216ffe9d59b82e98ff13b2db3d), the proofs follow the encoding of the logical relation as a predicate indexed by its interpretation, which needs no induction-recursion, absent from Lean.
The comments `-- ADE:` and `-- Pujet:` on the declarations name their counterparts in these formalizations, at the commits `1f720ee6` of ADE and `ef332527` of Pujet.

## License

Licensed under the [Apache License, Version 2.0](LICENSES/Apache-2.0.txt) with [LLVM Exceptions](LICENSES/LLVM-exception.txt) (`Apache-2.0 WITH LLVM-exception`).
