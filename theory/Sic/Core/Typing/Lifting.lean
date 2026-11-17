module

public import Sic.Core.Lifting.Extension
public import Sic.Core.Typing.Lifting.Context
import Sic.Core.Lifting.Functionality
import Sic.Core.Lifting.Shape
import Sic.Core.Lifting.Substitution
import Sic.Core.Syntax.Signature
import Sic.Core.Typing.Lifting.Destructors
import Sic.Core.Typing.Lifting.Parameters
import Sic.Core.Typing.Presuppositions
import Sic.Core.Typing.Signature

/-!
# Typing of the Liftings

The typing of the liftings of annex 20 of RFC 36: the lifting of a codata type without recursive
destructor of a well-formed signature is a well-formed type declaration in this signature, when each
parameter at which the type is lifted is a type.

The parameters of the lifting form a context, since the lifting of the parameters of the type in
them is typed, and its destructors, those of the type lifted at the parameter `y`, are destructors
of its sort, in the context of this typed lifting.
The lifting declares no parameter in which it is strictly positive, and its destructors, which are
among those of the type, have distinct names.

A well-formed signature holds the liftings that it declares: the rule of the liftings is the only
one that introduces the name of a lifting, and it asks for the destructors of the type lifted, in
the signature before the lifting, of which the signature has the entries.
It thus declares its liftings in order, each after the destructors that it lifts.

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- The lifting of a codata type without recursive destructor of a well-formed signature, at
parameters each of which is a type, is a well-formed type declaration in this signature, when no
entry of the signature introduces its name.
RFC: `\mathsf{lift}_\vdash` -/
theorem WfTypeDeclaration.lifting {sig : Signature} (hsig : WfSig sig) {decl : TypeDeclaration}
    (hd : .typeDeclaration decl ∈ sig) {F : Name} {S : List Nat} {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    (hl : decl.Lifts sig F S body)
    (hF : ∀ ι, ∀ T ∈ decl.codataTypes, T.name = F →
      ∀ r ∈ (T.body ι).recursion decl.names, r = none)
    (hS : ∀ ι, decl.constraint ι → (decl.params ι).LiftsTypes sig S)
    (fresh : ∀ e ∈ sig, ∀ D ∈ (decl.lifting F S ns body).names, D ∉ e.names) :
    WfTypeDeclaration sig (decl.lifting F S ns body) := by
  obtain ⟨T, hT, hn, hb⟩ := hl
  have hT' : sig.HasCodataType F decl T := ⟨hd, hT, hn⟩
  obtain ⟨_, _, hdecl⟩ := hsig.wfTypeDeclaration hd
  have hdecl' : (∃ ι, decl.constraint ι) ∧ T.destructors.Nodup := by
    cases hdecl with
    | data hb' => simp [TypeDeclaration.codataTypes, hb'] at hT
    | codata _ hadm _ _ _ hc _ => exact ⟨hadm, hc T hT⟩
  obtain ⟨⟨ι, hι⟩, hc⟩ := hdecl'
  refine .codata rfl ?_
    (fun I hI => (TypeDeclaration.lifting_typed hsig hT' S body I hI (hS _ hI)).ren.wfCtx)
    (fun I hI T' hT'' => ?_) (fun _ _ _ hT'' _ _ hx => ?_) (fun T' hT'' => ?_) fresh
  · have hq : (List.ofFn ι.sorts ++ [Quality.type]).length = decl.sorts + 1 := by simp
    have hp : (List.ofFn ι.grades ++
        [Grade.unrestrictedUnrestricted, Grade.unrestrictedUnrestricted,
          Grade.unrestrictedUnrestricted]).length = decl.grades + 3 := by simp
    refine ⟨.ofLists _ _ hq hp, ?_⟩
    show decl.constraint (Instance.ofLists _ _ hq hp).lifted
    rw [Instance.lifted_ofLists _ _ _ _ _ _ List.length_ofFn List.length_ofFn,
      Instance.ofLists_ofFn]
    exact hι
  · cases List.mem_singleton.1 hT''
    have hq : (List.ofFn I.lifted.sorts).length = decl.sorts := List.length_ofFn
    have hl : (List.ofFn (Level.lifted (k := decl.levels) S.length)).length = decl.levels :=
      List.length_ofFn
    have hp : (List.ofFn I.lifted.grades).length = decl.grades := List.length_ofFn
    have hI' : decl.constraint (.ofLists _ _ hq hp) :=
      (Instance.ofLists_ofFn I.lifted hq hp).symm ▸ hI
    have hA := decl.liftedInstance_wfType hsig hT' S.length hI
    have hα : TypedRen sig
        (((decl.params I.lifted).substLevels (Level.lifted S.length)).var
          (decl.liftedInstance F S.length I.lifted (.identity decl.scope)))
        Ren.weaken
        ((decl.params (.ofLists _ _ hq hp)).substLevels
          ((List.ofFn (Level.lifted S.length)).getFin hl)) := by
      rw [List.getFin_ofFn, Instance.ofLists_ofFn]
      exact TypedRen.weaken (.var hA)
    have hds : Destructors.Lifts sig I.liftingVariables (decl.liftingSort S I)
        (decl.liftedObservation F S.length I.lifted)
        (Lifting.base S (Lifting.motiveLevel decl.levels S) decl.scope).lift
        ((InstanceArgs.identity decl.scope).rename Ren.weaken).toSubst
        ((T.body (.ofLists _ _ hq hp)).substLevels
          ((List.ofFn (Level.lifted S.length)).getFin hl)) (body I) := by
      rw [List.getFin_ofFn, Instance.ofLists_ofFn]
      exact hb I
    have hκ : ((decl.sort (.ofLists _ _ hq hp)).substLevels
        ((List.ofFn (Level.lifted S.length)).getFin hl)).level ≤ (decl.liftingSort S I).level := by
      rw [List.getFin_ofFn, Instance.ofLists_ofFn]
      exact Level.le_joins _ _ (Level.preorder.refl _)
    exact Destructors.Lifts.wfDestructors hT' hI' hα (.var (.var hA) .zero) hκ _ _ _ _ _ _ _ _ _
      (fun _ _ => rfl) hds (TypeDeclaration.lifting_typed hsig hT' S body I hI (hS _ hI))
      (fun D => by
        show ((Lifting.base S (Lifting.motiveLevel decl.levels S) decl.scope).block D).map _ = none
        rw [Lifting.base_block]
        rfl)
      (InstanceArgs.identity_rename_neutral _) (hF _ T hT hn) (fun h => ⟨h, fun _ => rfl⟩)
  · cases List.mem_singleton.1 hT''
    exact nomatch hx
  · cases List.mem_singleton.1 hT''
    exact (Destructors.Lifts.sublist (hb ⟨fun _ => .type, fun _ => .unrestrictedUnrestricted⟩)).nodup hc

-- ADE: none.
/-- A type declaration of a well-formed signature one of whose types has the name of a lifting is
the lifting of a type of a type declaration of the signature, with the destructors of this type
lifted. -/
theorem WfSig.lifting_inv {E : TypeDeclaration} {F : Name} {S : List Nat} :
    {sig : Signature} → WfSig sig → .typeDeclaration E ∈ sig → Lifting.name F S ∈ E.names →
      ∃ (decl : TypeDeclaration) (F' : Name) (S' : List Nat) (ns : List Name)
        (body : Instance (decl.sorts + 1) (decl.grades + 3) →
          Destructors (decl.levels + S'.length) (.var :: decl.scope.lifted S') ns),
        E = decl.lifting F' S' ns body ∧ .typeDeclaration decl ∈ sig ∧ decl.Lifts sig F' S' body
  | [], _, he, _ => nomatch he
  | _ :: sig, h, he, hn => by
    rcases List.mem_cons.1 he with he | he
    · subst he
      cases h with
      | typeDeclaration _ _ hL => exact absurd hn (hL F S)
      | lifting _ hd hl =>
        exact ⟨_, _, _, _, _, rfl, List.mem_cons_of_mem _ hd,
          hl.extend (List.subset_cons_self _ _)⟩
    · obtain ⟨decl, F', S', ns, body, rfl, hd, hl⟩ :=
        WfSig.lifting_inv (Presuppositions.tail presuppositions h) he hn
      exact ⟨decl, F', S', ns, body, rfl, List.mem_cons_of_mem _ hd,
        hl.extend (List.subset_cons_self _ _)⟩

-- ADE: none.
/-- A well-formed signature holds the lifting that it declares of a type of one of its type
declarations: the destructors with which it declares this lifting are those of the type lifted.
RFC: `\mathsf{sig}_{\uparrow}` -/
theorem WfSig.lifts {sig : Signature} (h : WfSig sig) {decl : TypeDeclaration}
    (hd : .typeDeclaration decl ∈ sig) {D : Name} (hD : D ∈ decl.names) {S : List Nat}
    {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    (hL : .typeDeclaration (decl.lifting D S ns body) ∈ sig) : decl.Lifts sig D S body := by
  obtain ⟨decl', F', S', ns', body', he, hd', hl'⟩ :=
    h.lifting_inv hL (F := D) (S := S) List.mem_cons_self
  have hname : [Lifting.name D S] = [Lifting.name F' S'] :=
    congrArg TypeDeclaration.names he
  obtain ⟨rfl, rfl⟩ := Lifting.name_inj (List.cons.inj hname).1
  obtain ⟨T, hT, hn, hb⟩ := hl'
  cases Entry.typeDeclaration.inj (h.distinct.entry_unique hd hd' (n := D) hD
    (hn ▸ TypeDeclaration.codata_name_mem_names hT))
  obtain rfl := TypeDeclaration.lifting_destructors he
  obtain rfl := TypeDeclaration.lifting_body he
  exact ⟨T, hT, hn, hb⟩

-- ADE: none.
/-- A type declaration of a well-formed signature one of whose types has the name of a lifting is
the lifting of a type of a type declaration of the signature before it, with the destructors of
this type lifted in the signature before it. -/
theorem WfSig.lifting_inv_before {E : TypeDeclaration} {F : Name} {S : List Nat}
    {sig₁ : Signature} :
    (pre : Signature) → WfSig (pre ++ .typeDeclaration E :: sig₁) → Lifting.name F S ∈ E.names →
      ∃ (decl : TypeDeclaration) (F' : Name) (S' : List Nat) (ns : List Name)
        (body : Instance (decl.sorts + 1) (decl.grades + 3) →
          Destructors (decl.levels + S'.length) (.var :: decl.scope.lifted S') ns),
        E = decl.lifting F' S' ns body ∧ .typeDeclaration decl ∈ sig₁ ∧
          decl.Lifts sig₁ F' S' body
  | [], h, hn => by
    cases h with
    | typeDeclaration _ _ hL => exact absurd hn (hL F S)
    | lifting _ hd hl => exact ⟨_, _, _, _, _, rfl, hd, hl⟩
  | _ :: pre, h, hn =>
    WfSig.lifting_inv_before pre (Presuppositions.tail presuppositions h) hn

-- ADE: none.
/-- A well-formed signature declares each of its liftings after the destructors that it lifts: the
rule of the liftings asks for these destructors, lifted in the signature before the lifting. -/
theorem WfSig.liftsInOrder {sig : Signature} (h : WfSig sig) : sig.LiftsInOrder := by
  intro pre sig₁ decl D S ns body he hd hD
  subst he
  obtain ⟨decl', F', S', ns', body', he', hd', hl'⟩ :=
    WfSig.lifting_inv_before pre h (F := D) (S := S) List.mem_cons_self
  have hname : [Lifting.name D S] = [Lifting.name F' S'] :=
    congrArg TypeDeclaration.names he'
  obtain ⟨rfl, rfl⟩ := Lifting.name_inj (List.cons.inj hname).1
  obtain ⟨T, hT, hn, hb⟩ := hl'
  cases Entry.typeDeclaration.inj (h.distinct.entry_unique hd
    (List.mem_append_right pre (List.mem_cons_of_mem _ hd')) (n := D) hD
    (hn ▸ TypeDeclaration.codata_name_mem_names hT))
  obtain rfl := TypeDeclaration.lifting_destructors he'
  obtain rfl := TypeDeclaration.lifting_body he'
  exact ⟨T, hT, hn, hb⟩

end Sic.Core
