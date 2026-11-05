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
| Multiplicities | [Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#multiplicities) | [`Multiplicity`](https://sic-lang.github.io/sic/Sic/Multiplicity.html#Sic.Multiplicity) |

#### [Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#grades)

| Name | Section | Status |
| --- | --- | --- |
| Grades | [Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#grades) | [`Grade`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade) |
| $`(\mathsf{run}_p)`$ | [Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#grades) | [`Grade.run_mk`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.run_mk) |

#### [Modes](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modes)

| Name | Section | Status |
| --- | --- | --- |
| Modes | [Modes](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modes) | [`Mode`](https://sic-lang.github.io/sic/Sic/Mode.html#Sic.Mode) |
| Modes of ADE | [Modes](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modes) | [`Multiplicity.Mode`](https://sic-lang.github.io/sic/Sic/Mode.html#Sic.Multiplicity.Mode) |
| $`(\mathsf{run}_m)`$ | [Modes](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modes) | [`Mode.run`](https://sic-lang.github.io/sic/Sic/Mode.html#Sic.Mode.run) |

#### [Meaning](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{uses}_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | [`Multiplicity.uses`](https://sic-lang.github.io/sic/Sic/Multiplicity.html#Sic.Multiplicity.uses) |
| $`(\mathsf{best}_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | [`Multiplicity.IsBest`](https://sic-lang.github.io/sic/Sic/Multiplicity.html#Sic.Multiplicity.IsBest) |
| $`(+_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | [`Multiplicity.add_isBest`](https://sic-lang.github.io/sic/Sic/Multiplicity.html#Sic.Multiplicity.add_isBest) |
| $`(\cdot_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | [`Multiplicity.mul_isBest`](https://sic-lang.github.io/sic/Sic/Multiplicity.html#Sic.Multiplicity.mul_isBest) |
| $`(\wedge_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | [`Multiplicity.meet_isBest`](https://sic-lang.github.io/sic/Sic/Multiplicity.html#Sic.Multiplicity.meet_isBest) |
| $`(\le_u)`$ | [Meaning of the Multiplicities](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-multiplicities) | [`Multiplicity.le_iff_uses`](https://sic-lang.github.io/sic/Sic/Multiplicity.html#Sic.Multiplicity.le_iff_uses) |
| $`(\mathsf{uses}_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | [`Grade.uses`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.uses) |
| $`(\mathsf{best}_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | [`Grade.IsBest`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.IsBest) |
| $`(+_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | [`Grade.add_isBest`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.add_isBest) |
| $`(\cdot_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | [`Grade.mul_isBest`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.mul_isBest) |
| $`(\wedge_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | [`Grade.meet_isBest`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.meet_isBest) |
| $`(\le_p)`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | [`Grade.le_iff_uses`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.le_iff_uses) |
| $`(\mathsf{sound}_{\mathsf{run}})`$ | [Meaning of the Grades](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#meaning-of-the-grades) | [`Grade.sound_run`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.sound_run) |

#### [Properties](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#properties)

| Name | Section | Status |
| --- | --- | --- |
| $`(\cdot_{+})`$ | [Modality](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | [`Grade.mul_add`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.mul_add) |
| $`(\cdot_{\wedge})`$ | [Modality](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | [`Grade.mul_meet`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.mul_meet) |
| $`(+_{\le})`$ | [Modality](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | [`Grade.add_le_add_right`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.add_le_add_right) |
| $`(\wedge_{\le})`$ | [Modality](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | [`Grade.le_meet_iff`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.le_meet_iff) |
| $`(\mathbb{0}_{p})`$ | [Modality](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#modality) | [`Grade.zero_well_behaved`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.zero_well_behaved) |
| $`(\bigwedge_{p})`$ | [Greatest Lower Bounds](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#greatest-lower-bounds) | [`Grade.IsGLB`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.IsGLB) |
| $`(\bigwedge_{+})`$ | [Greatest Lower Bounds](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#greatest-lower-bounds) | [`Grade.glb_add`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.glb_add) |
| $`(\bigwedge_{\cdot})`$ | [Greatest Lower Bounds](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#greatest-lower-bounds) | [`Grade.glb_mul`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.glb_mul) |
| $`(\mathsf{run}_{\mathsf{op}})`$ | [Projection](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#projection) | [`Grade.run_op`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.run_op) |
| $`(\mathsf{run}_{\le})`$ | [Projection](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#projection) | [`Grade.run_le`](https://sic-lang.github.io/sic/Sic/Grade.html#Sic.Grade.run_le) |
| $`(\mathsf{run}_{\odot})`$ | [Projection](https://github.com/sic-lang/rfcs/blob/grades/text/0033-grades.md#projection) | [`Mode.run_odot`](https://sic-lang.github.io/sic/Sic/Mode.html#Sic.Mode.run_odot) |

### [RFC 24](https://github.com/sic-lang/rfcs/pull/24): Graded Dependent Core

#### [Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#levels)

| Name | Section | Status |
| --- | --- | --- |
| $`(\rho_0)`$ | [Equality and Order of Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | [`Level.value`](https://sic-lang.github.io/sic/Sic/Core/Level.html#Sic.Core.Level.value) |
| $`(\rho_+)`$ | [Equality and Order of Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | [`Level.value`](https://sic-lang.github.io/sic/Sic/Core/Level.html#Sic.Core.Level.value) |
| $`(\rho_\sqcup)`$ | [Equality and Order of Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | [`Level.value`](https://sic-lang.github.io/sic/Sic/Core/Level.html#Sic.Core.Level.value) |
| $`(=_l)`$ | [Equality and Order of Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | [`Level.Equal`](https://sic-lang.github.io/sic/Sic/Core/Level.html#Sic.Core.Level.Equal) |
| $`(\le_l)`$ | [Equality and Order of Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality-and-order-of-levels) | [`Level.Le`](https://sic-lang.github.io/sic/Sic/Core/Level.html#Sic.Core.Level.Le) |

#### [Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#judgments)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{ctx}_\varepsilon)`$ | [Contexts](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#contexts) | [`WfCtx.empty`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfCtx.empty) |
| $`(\mathsf{ctx}_x)`$ | [Contexts](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#contexts) | [`WfCtx.var`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfCtx.var) |
| $`(\mathsf{sig}_\varnothing)`$ | [Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | [`WfSig.empty`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfSig.empty) |
| $`(\mathsf{sig}_{\mathcal{D}})`$ | [Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | Not yet |
| $`(\mathsf{sig}_{≔})`$ | [Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | [`WfSig.definition`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfSig.definition) |
| $`(\mathsf{sig}_c)`$ | [Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#signatures) | [`WfSig.constant`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfSig.constant) |
| $`(\sqcup_s)`$ | [Declarations](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#declarations) | [`Quality.join`](https://sic-lang.github.io/sic/Sic/Core/Universe.html#Sic.Core.Quality.join) |
| $`(\mathsf{ctx}_X)`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | [`WfCtx.secondOrder`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfCtx.secondOrder) |
| $`(\mathsf{var}_X)`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | [`HasType.secondOrder`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasType.secondOrder) |
| $`(\mathsf{tel}_\varepsilon)`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | [`HasArgs.nil`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasArgs.nil) |
| $`(\mathsf{tel}_{,})`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | [`HasArgs.cons`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasArgs.cons) |
| $`(\mathsf{tel}_{\equiv\varepsilon})`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | [`EqArgs.nil`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqArgs.nil) |
| $`(\mathsf{tel}_{\equiv,})`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | [`EqArgs.cons`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqArgs.cons) |
| $`(\mathsf{var}_{X\equiv})`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | [`EqTerm.secondOrder`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqTerm.secondOrder) |
| $`(\mathsf{var}_{X\mathsf{m}})`$ | [Parameters](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#parameters) | [`Usage.var`](https://sic-lang.github.io/sic/Sic/Core/Usage.html#Sic.Core.Usage.var) |
| $`(\mathsf{tel}_{\kappa\varepsilon})`$ | [Telescopes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#telescopes) | [`WfTelescope.nil`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfTelescope.nil) |
| $`(\mathsf{tel}_{\kappa,})`$ | [Telescopes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#telescopes) | [`WfTelescope.cons`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfTelescope.cons) |
| $`(\mathsf{arg}_\varepsilon)`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | [`HasInstanceArgs.nil`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasInstanceArgs.nil) |
| $`(\mathsf{arg}_x)`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | [`HasInstanceArgs.var`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasInstanceArgs.var) |
| $`(\mathsf{arg}_X)`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | [`HasInstanceArgs.secondOrder`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasInstanceArgs.secondOrder) |
| $`(\mathsf{arg}_{\equiv\varepsilon})`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | [`EqInstanceArgs.nil`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqInstanceArgs.nil) |
| $`(\mathsf{arg}_{\equiv x})`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | [`EqInstanceArgs.var`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqInstanceArgs.var) |
| $`(\mathsf{arg}_{\equiv X})`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | [`EqInstanceArgs.secondOrder`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqInstanceArgs.secondOrder) |
| $`(D)`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | [`HasType.inst`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasType.inst) |
| $`(D_\equiv)`$ | [Instances](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#instances) | [`EqTerm.inst`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqTerm.inst) |
| $`(\mathsf{def})`$ | [Definitions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | [`WfDefinition`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfDefinition) |
| $`(c)`$ | [Definitions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | [`HasType.const`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasType.const) |
| $`(c_{\mathsf{m}})`$ | [Definitions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | [`Usage.const`](https://sic-lang.github.io/sic/Sic/Core/Usage.html#Sic.Core.Usage.const) |
| $`(\delta)`$ | [Definitions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#definitions) | [`EqTerm.delta`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqTerm.delta) |
| $`(\mathsf{const})`$ | [Constants](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#constants) | [`WfConstant`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfConstant) |
| $`(\mathsf{var})`$ | [Variables](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#variables) | [`HasType.var`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasType.var) |
| $`(\mathsf{var}_{\mathsf{m}})`$ | [Variables](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#variables) | [`Usage.var`](https://sic-lang.github.io/sic/Sic/Core/Usage.html#Sic.Core.Usage.var) |
| $`(\mathsf{refl}_{\mathsf{type}})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | [`EqType.refl`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqType.refl) |
| $`(\mathsf{sym}_{\mathsf{type}})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | [`EqType.symm`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqType.symm) |
| $`(\mathsf{trans}_{\mathsf{type}})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | [`EqType.trans`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqType.trans) |
| $`(\mathsf{refl})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | [`EqTerm.refl`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqTerm.refl) |
| $`(\mathsf{sym})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | [`EqTerm.symm`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqTerm.symm) |
| $`(\mathsf{trans})`$ | [Equality](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#equality) | [`EqTerm.trans`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqTerm.trans) |
| $`(\mathsf{conv})`$ | [Type Conversion](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#type-conversion) | [`HasType.conv`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasType.conv) |
| $`(\mathsf{conv}_\equiv)`$ | [Type Conversion](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#type-conversion) | [`EqTerm.conv`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqTerm.conv) |
| $`(\mathsf{sub})`$ | [Usage](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#usage) | [`Usage.sub`](https://sic-lang.github.io/sic/Sic/Core/Usage.html#Sic.Core.Usage.sub) |

#### [Universes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#universes)

| Name | Section | Status |
| --- | --- | --- |
| $`(U)`$ | [Formation of Universes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-universes) | [`HasType.univ`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasType.univ) |
| $`(U_\equiv)`$ | [Formation of Universes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-universes) | [`EqTerm.univ`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqTerm.univ) |
| $`(U_{\mathsf{m}})`$ | [Formation of Universes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-universes) | [`Usage.sort`](https://sic-lang.github.io/sic/Sic/Core/Usage.html#Sic.Core.Usage.sort) |
| $`(U_{\mathsf{type}})`$ | [Elements of Universes as Types](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-universes-as-types) | [`WfType.univType`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfType.univType) |
| $`(U_{\mathsf{type}\equiv})`$ | [Elements of Universes as Types](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-universes-as-types) | [`EqType.univType`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqType.univType) |

#### [Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#strict-propositions)

| Name | Section | Status |
| --- | --- | --- |
| $`(\Omega)`$ | [Formation of Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-propositions) | [`HasType.prop`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.HasType.prop) |
| $`(\Omega_\equiv)`$ | [Formation of Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-propositions) | [`EqTerm.prop`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqTerm.prop) |
| $`(\Omega_{\mathsf{m}})`$ | [Formation of Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#formation-of-propositions) | [`Usage.sort`](https://sic-lang.github.io/sic/Sic/Core/Usage.html#Sic.Core.Usage.sort) |
| $`(\Omega_{\mathsf{type}})`$ | [Elements of Propositions as Types](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-propositions-as-types) | [`WfType.propType`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.WfType.propType) |
| $`(\Omega_{\mathsf{type}\equiv})`$ | [Elements of Propositions as Types](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#elements-of-propositions-as-types) | [`EqType.propType`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqType.propType) |
| $`(\mathsf{irr})`$ | [Proof Irrelevance](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#proof-irrelevance) | [`EqTerm.irr`](https://sic-lang.github.io/sic/Sic/Core/Typing.html#Sic.Core.EqTerm.irr) |

#### [Meaning](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning)

| Name | Section | Status |
| --- | --- | --- |
| $`(\mathsf{prop})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`IsProp`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.IsProp) |
| $`(\mathsf{prop}_\Downarrow)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ComputesToProp`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ComputesToProp) |
| $`(\vDash_{\mathsf{type}\equiv})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ValidEqType₀`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidEqType₀) |
| $`(\vDash_{\mathsf{type}})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ValidType₀`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidType₀) |
| $`(\vDash_\equiv)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ValidEqTerm₀`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidEqTerm₀) |
| $`(\vDash)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ValidTerm₀`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidTerm₀) |
| $`(\mathsf{eq}_\varepsilon)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`EqSubst`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.EqSubst) |
| $`(\mathsf{eq}_x)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`EqSubst`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.EqSubst) |
| $`(\mathsf{eq}_X)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`EqSubst`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.EqSubst) |
| $`({\vDash}\Gamma_{\mathsf{type}\equiv})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ValidEqTypeΓ`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidEqTypeΓ) |
| $`({\vDash}\Gamma_{\mathsf{type}})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ValidTypeΓ`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidTypeΓ) |
| $`({\vDash}\Gamma_\equiv)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ValidEqTermΓ`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidEqTermΓ) |
| $`({\vDash}\Gamma)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ValidTermΓ`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidTermΓ) |
| $`({\vDash}\mathsf{tel}_{\kappa\varepsilon})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ValidEqTelescope₀`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidEqTelescope₀) |
| $`({\vDash}\mathsf{tel}_{\kappa,})`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ValidEqTelescope₀`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidEqTelescope₀) |
| $`({\vDash}\mathsf{ctx}_\varepsilon)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`ValidCtx₀`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidCtx₀) |
| $`({\vDash}\mathsf{ctx}_x)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`validCtx₀_var`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.validCtx₀_var) |
| $`({\vDash}\mathsf{ctx}_X)`$ | [Meaning of the Judgments](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-judgments) | [`validCtx₀_secondOrder`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.validCtx₀_secondOrder) |
| $`(\vDash_\rho)`$ | [Meaning of the Levels](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-levels) | [`ValidEqType`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidEqType) |
| $`({\vDash}\mathsf{sig}_\varnothing)`$ | [Meaning of the Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | [`ValidSig`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidSig) |
| $`({\vDash}\mathsf{sig}_{\mathcal{D}})`$ | [Meaning of the Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | [`ValidSig`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidSig) |
| $`({\vDash}\mathsf{sig}_{≔})`$ | [Meaning of the Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | [`ValidSig`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidSig) |
| $`({\vDash}\mathsf{sig}_c)`$ | [Meaning of the Signatures](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-signatures) | [`ValidSig`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidSig) |
| $`(\mathsf{eq}_U)`$ | [Meaning of the Universes](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-universes) | [`UnivRel.univ`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.UnivRel.univ) |
| $`(\mathsf{eq}_{\mathsf{true}})`$ | [Meaning of the Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | [`HasEq.prop`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.HasEq.prop) |
| $`(\mathsf{eq}_{\mathsf{false}})`$ | [Meaning of the Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | [`HasEq.prop`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.HasEq.prop) |
| $`(\vDash_{\equiv\Omega})`$ | [Meaning of the Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | [`ValidEqTerm₀`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.ValidEqTerm₀) |
| $`(\mathsf{eq}_\Omega)`$ | [Meaning of the Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | [`UnivRel.prop`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.UnivRel.prop) |
| $`(\mathsf{exact}_\Omega)`$ | [Meaning of the Strict Propositions](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#meaning-of-the-strict-propositions) | [`exact_prop`](https://sic-lang.github.io/sic/Sic/Core/Meaning.html#Sic.Core.exact_prop) |
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
| $`(\bullet_\circ)`$ | [Erasure Properties](https://github.com/sic-lang/rfcs/blob/dependent-core/text/0024-graded-dependent-core.md#erasure-properties) | [`Term.extract_ghost`](https://sic-lang.github.io/sic/Sic/Core/Erasure.html#Sic.Core.Term.extract_ghost) |
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
