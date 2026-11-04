# Sic

Metatheory and compilers for the Sic programming language.
Its design is decided by the RFCs of [`sic-lang/rfcs`](https://github.com/sic-lang/rfcs).

## Status

The metatheory, in [`theory/`](theory), formalizes in Lean the core of Sic, as the following RFCs, still under review, specify it, and the [documentation of the metatheory](https://sic-lang.github.io/sic/) presents each of its modules.
The previous version of the formalization is dropped: it follows the previous version of [RFC 24](https://github.com/sic-lang/rfcs/pull/24), and the formalization starts again from the grades.
No compiler exists yet.

Each row names a rule, a formula or a definition as the RFC writes it, with a link to its section, and links to its formalization in Lean once it exists.

### [RFC 33](https://github.com/sic-lang/rfcs/pull/33): Grades

#### [Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#multiplicities)

| Name | Section | Status |
| --- | --- | --- |
| Multiplicities | [Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#multiplicities) | Not yet |

#### [Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#grades)

| Name | Section | Status |
| --- | --- | --- |
| Grades | [Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#grades) | Not yet |
| $`(\mathsf{run}_p)`$ | [Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#grades) | Not yet |

#### [Modes](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modes)

| Name | Section | Status |
| --- | --- | --- |
| Modes | [Modes](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modes) | Not yet |

#### [Meaning](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{uses}_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Not yet |
| $`(\mathsf{best}_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Not yet |
| $`(+_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Not yet |
| $`(\cdot_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Not yet |
| $`(\wedge_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Not yet |
| $`(\le_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | Not yet |
| $`(\mathsf{uses}_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Not yet |
| $`(\mathsf{best}_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Not yet |
| $`(+_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Not yet |
| $`(\cdot_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Not yet |
| $`(\wedge_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Not yet |
| $`(\le_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Not yet |
| $`(\mathsf{sound}_{\mathsf{run}})`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | Not yet |

#### [Properties](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#properties)

| Name | Section | Status |
| --- | --- | --- |
| $`(\cdot_{+})`$ | [Modality](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | Not yet |
| $`(\cdot_{\wedge})`$ | [Modality](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | Not yet |
| $`(+_{\le})`$ | [Modality](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | Not yet |
| $`(\wedge_{\le})`$ | [Modality](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | Not yet |
| $`(\mathbb{0}_{p})`$ | [Modality](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | Not yet |
| $`(\bigwedge_{p})`$ | [Greatest Lower Bounds](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#greatest-lower-bounds) | Not yet |
| $`(\bigwedge_{+})`$ | [Greatest Lower Bounds](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#greatest-lower-bounds) | Not yet |
| $`(\bigwedge_{\cdot})`$ | [Greatest Lower Bounds](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#greatest-lower-bounds) | Not yet |
| $`(\mathsf{run}_{\mathsf{op}})`$ | [Projection](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#projection) | Not yet |
| $`(\mathsf{run}_{\le})`$ | [Projection](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#projection) | Not yet |
| $`(\mathsf{run}_{m})`$ | [Projection](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#projection) | Not yet |
| $`(\mathsf{run}_{\odot})`$ | [Projection](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#projection) | Not yet |

### [RFC 24](https://github.com/sic-lang/rfcs/pull/24): Graded Dependent Core

#### [Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#levels)

| Name | Section | Status |
| --- | --- | --- |
| $`(\rho_0)`$ | [Equality and Order of Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | Not yet |
| $`(\rho_+)`$ | [Equality and Order of Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | Not yet |
| $`(\rho_\sqcup)`$ | [Equality and Order of Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | Not yet |
| $`(=_l)`$ | [Equality and Order of Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | Not yet |
| $`(\le_l)`$ | [Equality and Order of Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | Not yet |

#### [Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#judgments)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{ctx}_\varepsilon)`$ | [Contexts](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#contexts) | Not yet |
| $`(\mathsf{ctx}_x)`$ | [Contexts](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#contexts) | Not yet |
| $`(\mathsf{sig}_\varnothing)`$ | [Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | Not yet |
| $`(\mathsf{sig}_{\mathcal{D}})`$ | [Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | Not yet |
| $`(\mathsf{sig}_{≔})`$ | [Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | Not yet |
| $`(\mathsf{sig}_c)`$ | [Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | Not yet |
| $`(\sqcup_s)`$ | [Declarations](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#declarations) | Not yet |
| $`(\mathsf{ctx}_X)`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| $`(\mathsf{var}_X)`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| $`(\mathsf{tel}_\varepsilon)`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| $`(\mathsf{tel}_{,})`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| $`(\mathsf{tel}_{\equiv\varepsilon})`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| $`(\mathsf{tel}_{\equiv,})`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| $`(\mathsf{var}_{X\equiv})`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| $`(\mathsf{var}_{X\mathsf{m}})`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | Not yet |
| $`(\mathsf{tel}_{\kappa\varepsilon})`$ | [Telescopes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#telescopes) | Not yet |
| $`(\mathsf{tel}_{\kappa,})`$ | [Telescopes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#telescopes) | Not yet |
| $`(\mathsf{arg}_\varepsilon)`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| $`(\mathsf{arg}_x)`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| $`(\mathsf{arg}_X)`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| $`(\mathsf{arg}_{\equiv\varepsilon})`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| $`(\mathsf{arg}_{\equiv x})`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| $`(\mathsf{arg}_{\equiv X})`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| $`(D)`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| $`(D_\equiv)`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | Not yet |
| $`(\mathsf{def})`$ | [Definitions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | Not yet |
| $`(c)`$ | [Definitions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | Not yet |
| $`(c_{\mathsf{m}})`$ | [Definitions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | Not yet |
| $`(\delta)`$ | [Definitions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | Not yet |
| $`(\mathsf{const})`$ | [Constants](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#constants) | Not yet |
| $`(\mathsf{var})`$ | [Variables](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#variables) | Not yet |
| $`(\mathsf{var}_{\mathsf{m}})`$ | [Variables](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#variables) | Not yet |
| $`(\mathsf{refl}_{\mathsf{type}})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| $`(\mathsf{sym}_{\mathsf{type}})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| $`(\mathsf{trans}_{\mathsf{type}})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| $`(\mathsf{refl})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| $`(\mathsf{sym})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| $`(\mathsf{trans})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | Not yet |
| $`(\mathsf{conv})`$ | [Type Conversion](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#type-conversion) | Not yet |
| $`(\mathsf{conv}_\equiv)`$ | [Type Conversion](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#type-conversion) | Not yet |
| $`(\mathsf{sub})`$ | [Usage](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#usage) | Not yet |

#### [Universes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#universes)

| Name | Section | Status |
| --- | --- | --- |
| $`(U)`$ | [Formation of Universes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-universes) | Not yet |
| $`(U_\equiv)`$ | [Formation of Universes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-universes) | Not yet |
| $`(U_{\mathsf{m}})`$ | [Formation of Universes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-universes) | Not yet |
| $`(U_{\mathsf{type}})`$ | [Elements of Universes as Types](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-universes-as-types) | Not yet |
| $`(U_{\mathsf{type}\equiv})`$ | [Elements of Universes as Types](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-universes-as-types) | Not yet |

#### [Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#strict-propositions)

| Name | Section | Status |
| --- | --- | --- |
| $`(\Omega)`$ | [Formation of Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-propositions) | Not yet |
| $`(\Omega_\equiv)`$ | [Formation of Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-propositions) | Not yet |
| $`(\Omega_{\mathsf{m}})`$ | [Formation of Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-propositions) | Not yet |
| $`(\Omega_{\mathsf{type}})`$ | [Elements of Propositions as Types](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-propositions-as-types) | Not yet |
| $`(\Omega_{\mathsf{type}\equiv})`$ | [Elements of Propositions as Types](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-propositions-as-types) | Not yet |
| $`(\mathsf{irr})`$ | [Proof Irrelevance](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#proof-irrelevance) | Not yet |

#### [Meaning](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning)

| Name | Section | Status |
| --- | --- | --- |
| $`(\vDash_{\mathsf{type}\equiv})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`(\vDash_{\mathsf{type}})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`(\vDash_\equiv)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`(\vDash)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`(\mathsf{eq}_\varepsilon)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`(\mathsf{eq}_x)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`(\mathsf{eq}_X)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`({\vDash}\Gamma_{\mathsf{type}\equiv})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`({\vDash}\Gamma_{\mathsf{type}})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`({\vDash}\Gamma_\equiv)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`({\vDash}\Gamma)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`({\vDash}\mathsf{tel}_{\kappa\varepsilon})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`({\vDash}\mathsf{tel}_{\kappa,})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`({\vDash}\mathsf{ctx}_\varepsilon)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`({\vDash}\mathsf{ctx}_x)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`({\vDash}\mathsf{ctx}_X)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | Not yet |
| $`(\vDash_\rho)`$ | [Meaning of the Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-levels) | Not yet |
| $`({\vDash}\mathsf{sig}_\varnothing)`$ | [Meaning of the Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | Not yet |
| $`({\vDash}\mathsf{sig}_{\mathcal{D}})`$ | [Meaning of the Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | Not yet |
| $`({\vDash}\mathsf{sig}_{≔})`$ | [Meaning of the Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | Not yet |
| $`({\vDash}\mathsf{sig}_c)`$ | [Meaning of the Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | Not yet |
| $`(\mathsf{eq}_U)`$ | [Meaning of the Universes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-universes) | Not yet |
| $`(\mathsf{eq}_{\mathsf{true}})`$ | [Meaning of the Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | Not yet |
| $`(\mathsf{eq}_{\mathsf{false}})`$ | [Meaning of the Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | Not yet |
| $`(\vDash_{\equiv\Omega})`$ | [Meaning of the Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | Not yet |
| $`(\mathsf{eq}_\Omega)`$ | [Meaning of the Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | Not yet |
| $`(\mathsf{exact}_\Omega)`$ | [Meaning of the Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | Not yet |
| $`(\mathsf{sound}_{\mathsf{sig}})`$ | [Soundness](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |
| $`(\mathsf{sound}_{\mathsf{ctx}})`$ | [Soundness](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |
| $`(\mathsf{sound}_{\mathsf{type}})`$ | [Soundness](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |
| $`(\mathsf{sound}_{\mathsf{type}\equiv})`$ | [Soundness](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |
| $`(\mathsf{sound})`$ | [Soundness](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |
| $`(\mathsf{sound}_\equiv)`$ | [Soundness](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#soundness) | Not yet |

#### [Properties](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#properties)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{subject})`$ | [Preservation](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#preservation) | Not yet |
| $`(\mathsf{usage}_\beta)`$ | [Preservation](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#preservation) | Not yet |
| $`(\mathsf{normal})`$ | [Normalization and Decidability](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#normalization-and-decidability) | Not yet |
| $`(\mathsf{decidable}_\equiv)`$ | [Normalization and Decidability](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#normalization-and-decidability) | Not yet |
| $`(\mathsf{decidable}_\vdash)`$ | [Normalization and Decidability](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#normalization-and-decidability) | Not yet |
| $`(\mathsf{hyp}_\iota)`$ | [Consistency and Canonicity](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#consistency-and-canonicity) | Not yet |
| $`(\mathsf{consistent})`$ | [Consistency and Canonicity](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#consistency-and-canonicity) | Not yet |
| $`(\mathsf{canonical})`$ | [Consistency and Canonicity](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#consistency-and-canonicity) | Not yet |
| $`(\mathsf{hyp}_\bullet)`$ | [Erasure Properties](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#erasure-properties) | Not yet |
| $`(\mathsf{sound}_\bullet)`$ | [Erasure Properties](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#erasure-properties) | Not yet |
| $`(\mathsf{absent}_\bullet)`$ | [Erasure Properties](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#erasure-properties) | Not yet |
| $`(\mathsf{absent}_\circ)`$ | [Erasure Properties](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#erasure-properties) | Not yet |
| $`(\bullet_\circ)`$ | [Erasure Properties](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#erasure-properties) | Not yet |
| $`(\mathsf{project})`$ | [Projection Lemma](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#projection-lemma) | Not yet |

### [RFC 34](https://github.com/sic-lang/rfcs/pull/34): Data and Codata Types

#### [Declarations](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#declarations)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{data})`$ | [Formation](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#formation) | Not yet |
| $`(\mathsf{codata})`$ | [Formation](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#formation) | Not yet |
| $`(\langle \Theta \rangle_\varepsilon)`$ | [Prelude](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#prelude) | Not yet |
| $`(\langle \Theta \rangle_{,})`$ | [Prelude](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#prelude) | Not yet |
| $`(\langle \bar t \rangle_\varepsilon)`$ | [Prelude](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#prelude) | Not yet |
| $`(\langle \bar t \rangle_{,})`$ | [Prelude](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#prelude) | Not yet |
| $`(\mathsf{lift}_D)`$ | [Liftings](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| $`(\mathsf{lift}_{D'})`$ | [Liftings](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| $`(\mathsf{lift}^{+})`$ | [Liftings](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| $`(\mathsf{lift}^{-})`$ | [Liftings](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| $`(\mathsf{map}_D)`$ | [Liftings](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| $`(\mathsf{map}_{D'})`$ | [Liftings](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| $`(\mathsf{map}^{+})`$ | [Liftings](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| $`(\mathsf{map}^{-})`$ | [Liftings](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| $`(\Pi_D)`$ | [Liftings](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| $`(\Pi_{D'})`$ | [Liftings](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |
| $`(\Pi_X)`$ | [Liftings](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#liftings) | Not yet |

#### [Data Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#data-types)

| Name | Section | Status |
| --- | --- | --- |
| $`(\zeta^{+})`$ | [Usage of Data Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#usage-of-data-types) | Not yet |
| $`(D^{+}_{\mathsf{m}})`$ | [Usage of Data Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#usage-of-data-types) | Not yet |
| $`(D^{+}_{\mathsf{i}})`$ | [Constructors](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#constructors) | Not yet |
| $`(D^{+}_{\mathsf{i}\mathsf{m}})`$ | [Constructors](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#constructors) | Not yet |
| $`(D^{+}_{\mathsf{rec}})`$ | [Recursor](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#recursor) | Not yet |
| $`(D^{+}_{\mathsf{rec}\mathsf{m}})`$ | [Recursor](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#recursor) | Not yet |
| $`(D^{+}_{\mathsf{rec}\beta})`$ | [Recursor](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#recursor) | Not yet |
| $`(D^{+}_\eta)`$ | [Extensionality of Data](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#extensionality-of-data) | Not yet |

#### [Codata Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#codata-types)

| Name | Section | Status |
| --- | --- | --- |
| $`(\zeta^{-})`$ | [Usage of Codata Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#usage-of-codata-types) | Not yet |
| $`(D^{-}_\pi)`$ | [Destructors](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#destructors) | Not yet |
| $`(D^{-}_{\pi\mathsf{m}})`$ | [Destructors](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#destructors) | Not yet |
| $`(\oplus_D)`$ | [Corecursor](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#corecursor) | Not yet |
| $`(\oplus_{D'})`$ | [Corecursor](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#corecursor) | Not yet |
| $`(D^{-}_{\mathsf{i}})`$ | [Corecursor](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#corecursor) | Not yet |
| $`(D^{-}_{\mathsf{i}\mathsf{m}})`$ | [Corecursor](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#corecursor) | Not yet |
| $`(D^{-}_{\pi\beta})`$ | [Corecursor](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#corecursor) | Not yet |
| $`(D^{-}_\eta)`$ | [Extensionality of Codata](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#extensionality-of-codata) | Not yet |

#### [Meaning](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning)

| Name | Section | Status |
| --- | --- | --- |
| $`({\vDash}_{\mathsf{data}})`$ | [Meaning of the Declarations](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-declarations) | Not yet |
| $`({\vDash}_{\mathsf{codata}})`$ | [Meaning of the Declarations](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-declarations) | Not yet |
| $`({\vDash}\mathsf{dtor}_{\kappa\varepsilon})`$ | [Meaning of the Declarations](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-declarations) | Not yet |
| $`({\vDash}\mathsf{dtor}_{\kappa,})`$ | [Meaning of the Declarations](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-declarations) | Not yet |
| $`(\mathsf{eq}_{\mathsf{con}})`$ | [Meaning of the Data Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-data-types) | Not yet |
| $`(\mathsf{true}_{\mathsf{data}})`$ | [Meaning of the Data Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-data-types) | Not yet |
| $`(\mathsf{eq}_\mu)`$ | [Meaning of the Data Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-data-types) | Not yet |
| $`(\mathsf{eq}_{\mathsf{data}})`$ | [Meaning of the Data Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-data-types) | Not yet |
| $`(\mathsf{eq}_{\mathsf{corec}})`$ | [Meaning of the Codata Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-codata-types) | Not yet |
| $`(\mathsf{true}_{\mathsf{codata}})`$ | [Meaning of the Codata Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-codata-types) | Not yet |
| $`(\mathsf{eq}_\nu)`$ | [Meaning of the Codata Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-codata-types) | Not yet |
| $`(\mathsf{eq}_{\mathsf{codata}})`$ | [Meaning of the Codata Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#meaning-of-the-codata-types) | Not yet |
| $`(\mathsf{incomplete}_{\mathsf{typ}})`$ | [Fidelity](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| $`(\mathsf{undecidable}_\vDash)`$ | [Fidelity](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| $`(\mathsf{incomplete}^{+}_{D\equiv})`$ | [Fidelity](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| $`(\mathsf{incomplete}^{-}_{D\equiv})`$ | [Fidelity](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| $`(\mathsf{valid}^{+}_\eta)`$ | [Fidelity](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| $`(\mathsf{valid}^{-}_\eta)`$ | [Fidelity](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| $`(\mathsf{incomplete}^{+}_\eta)`$ | [Fidelity](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |
| $`(\mathsf{incomplete}^{-}_\eta)`$ | [Fidelity](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#fidelity) | Not yet |

#### [Properties](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#properties)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{sound}_{\mathsf{data}})`$ | [Obligations of the Contract](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#obligations-of-the-contract) | Not yet |
| $`(\mathsf{sound}_{\mathsf{codata}})`$ | [Obligations of the Contract](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#obligations-of-the-contract) | Not yet |
| $`(\mathsf{usage}^{\pm}_\beta)`$ | [Obligations of the Contract](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#obligations-of-the-contract) | Not yet |
| $`(\mathsf{project}^{\pm})`$ | [Obligations of the Contract](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#obligations-of-the-contract) | Not yet |
| $`(\mathsf{rec}_{\bigwedge})`$ | [Usage of Recursion](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#usage-of-recursion) | Not yet |
| $`(\top)`$ | [Absorbing Types](https://github.com/sic-lang/rfcs/blob/data-and-codata-types/text/0034-data-and-codata-types.md#absorbing-types) | Not yet |

### [RFC 35](https://github.com/sic-lang/rfcs/pull/35): Observational Equality

#### [Equality](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality)

| Name | Section | Status |
| --- | --- | --- |
| $`(\sim)`$ | [Formation of Equalities](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#formation-of-equalities) | Not yet |
| $`(\sim_{\mathsf{irr}})`$ | [Formation of Equalities](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#formation-of-equalities) | Not yet |
| $`(\sim_{\mathsf{m}})`$ | [Formation of Equalities](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#formation-of-equalities) | Not yet |
| $`(\mathsf{refl})`$ | [Reflexivity](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#reflexivity) | Not yet |
| $`(\mathsf{refl}_{\mathsf{m}})`$ | [Reflexivity](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#reflexivity) | Not yet |
| $`(\mathsf{transp})`$ | [Transport](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#transport) | Not yet |
| $`(\mathsf{transp}_{\mathsf{m}})`$ | [Transport](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#transport) | Not yet |
| $`(\mathsf{ap}_\sim)`$ | [Transport](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#transport) | Not yet |
| $`(\mathsf{cast})`$ | [Cast](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast) | Not yet |
| $`(\mathsf{cast}_{\mathsf{m}})`$ | [Cast](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast) | Not yet |
| $`(\mathsf{cast}_{\mathsf{refl}})`$ | [Cast](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast) | Not yet |

#### [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types)

| Name | Section | Status |
| --- | --- | --- |
| $`(\sim_U)`$ | [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| $`(\sim_\Omega)`$ | [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| $`(\sim_{\mathsf{prop}})`$ | [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| $`(\sim_{\ne})`$ | [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| $`(\sim^{+}_D)`$ | [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| $`(\sim^{-}_D)`$ | [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| $`(\sim_{D\ne})`$ | [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| $`(\sim_{\mathsf{tel}\varepsilon})`$ | [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| $`(\sim_{\mathsf{tel},})`$ | [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| $`(\sim_{\mathsf{dtor}\varepsilon})`$ | [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |
| $`(\sim_{\mathsf{dtor},})`$ | [Equality of Types](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-types) | Not yet |

#### [Equality of Terms](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-terms)

| Name | Section | Status |
| --- | --- | --- |
| $`(\sim^{+})`$ | [Equality of Data](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-data) | Not yet |
| $`(\sim^{+}_{\ne})`$ | [Equality of Data](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-data) | Not yet |
| $`(\sim_{\mathsf{fields}\varepsilon})`$ | [Equality of Data](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-data) | Not yet |
| $`(\sim_{\mathsf{fields},})`$ | [Equality of Data](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-data) | Not yet |
| $`(\sim^{-}_{\mathsf{decl}})`$ | [Equality of Codata](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-codata) | Not yet |
| $`(\sim^{-})`$ | [Equality of Codata](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-of-codata) | Not yet |
| $`(\mathsf{cast}_{\mathsf{tel}\varepsilon})`$ | [Equality and Cast of the Telescopes](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-and-cast-of-the-telescopes) | Not yet |
| $`(\mathsf{cast}_{\mathsf{tel},})`$ | [Equality and Cast of the Telescopes](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#equality-and-cast-of-the-telescopes) | Not yet |

#### [Cast of Terms](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast-of-terms)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{cast}^{+})`$ | [Cast of Data](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast-of-data) | Not yet |
| $`(\mathsf{cast}^{-})`$ | [Cast of Codata](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#cast-of-codata) | Not yet |

#### [Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#quotients)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{quotient})`$ | [Formation of Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#formation-of-quotients) | Not yet |
| $`(D^{/}_{\mathsf{i}})`$ | [Construction and Elimination of Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| $`(D^{/}_{\mathsf{i}\mathsf{m}})`$ | [Construction and Elimination of Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| $`(D^{/}_{\mathsf{rec}})`$ | [Construction and Elimination of Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| $`(D^{/}_{\mathsf{rec}\mathsf{m}})`$ | [Construction and Elimination of Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| $`(D^{/}_{\mathsf{rec}\beta})`$ | [Construction and Elimination of Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| $`(\sim^{/})`$ | [Construction and Elimination of Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| $`(\sim^{/}_{D})`$ | [Construction and Elimination of Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |
| $`(\mathsf{cast}^{/})`$ | [Construction and Elimination of Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#construction-and-elimination-of-quotients) | Not yet |

#### [Meaning](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{true}_\sim)`$ | [Meaning of the Equality](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-equality) | Not yet |
| $`(\mathsf{true}_{\sim\mathsf{type}})`$ | [Meaning of the Equality](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-equality) | Not yet |
| $`(\mathsf{valid}_{\mathsf{cast}})`$ | [Meaning of the Cast](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-cast) | Not yet |
| $`({\vDash}_{\mathsf{quotient}})`$ | [Meaning of the Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-quotients) | Not yet |
| $`(\mathsf{eq}^{/})`$ | [Meaning of the Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-quotients) | Not yet |
| $`(\mathsf{eq}_{\mathsf{quotient}})`$ | [Meaning of the Quotients](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#meaning-of-the-quotients) | Not yet |

#### [Properties](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{sym}_\sim)`$ | [Properties](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| $`(\mathsf{trans}_\sim)`$ | [Properties](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| $`(J_\sim)`$ | [Properties](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| $`(J_{\sim\beta})`$ | [Properties](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| $`(\mathsf{sound}_\sim)`$ | [Properties](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| $`(\mathsf{usage}_{\mathsf{cast}})`$ | [Properties](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| $`(\mathsf{decidable}_{\mathsf{cast}})`$ | [Properties](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| $`(\mathsf{consistent}_\sim)`$ | [Properties](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |
| $`(\mathsf{sound}_{\bullet\mathsf{cast}})`$ | [Properties](https://github.com/sic-lang/rfcs/blob/observational-equality/text/0035-observational-equality.md#properties) | Not yet |

### Formalizations Followed

The core follows the graded type theory of the [formalization of Abel, Danielsson and Eriksson](https://github.com/graded-type-theory/graded-type-theory/tree/1f720ee636cb16aec130cc1ddc1c32acea8809d0) (ADE), from which it differs by its three modes, its grades, which count the uses at run time and in total, and its levels, which are not terms, and the proofs follow most of its metatheory, from the logical relation to the properties of the usage.
Of the [formalization of the logical relation by Pujet](https://github.com/loic-p/logrel-mltt/tree/ef332527cb2203216ffe9d59b82e98ff13b2db3d), the proofs follow the encoding of the logical relation as a predicate indexed by its interpretation, which needs no induction-recursion, absent from Lean.
The comments `-- ADE:` and `-- Pujet:` on the declarations name their counterparts in these formalizations, at the commits `1f720ee6` of ADE and `ef332527` of Pujet.

## License

Licensed under the [Apache License, Version 2.0](LICENSES/Apache-2.0.txt) with [LLVM Exceptions](LICENSES/LLVM-exception.txt) (`Apache-2.0 WITH LLVM-exception`).
