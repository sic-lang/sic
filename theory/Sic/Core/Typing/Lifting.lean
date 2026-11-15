module

public import Sic.Core.Typing.Lifting.Context
import Sic.Core.Lifting.Substitution
import Sic.Core.Typing.Lifting.Destructors
import Sic.Core.Typing.Lifting.Parameters
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

ADE have no declared types, and no liftings.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

-- ADE: none.
/-- The lifting of a codata type without recursive destructor of a well-formed signature, at
parameters each of which is a type, is a well-formed type declaration in this signature.
RFC: `\mathsf{lift}_\vdash` -/
theorem WfTypeDeclaration.lifting {sig : Signature} (hsig : WfSig sig) {decl : TypeDeclaration}
    (hd : .typeDeclaration decl ∈ sig) {F : Name} {S : List Nat} {ns : List Name}
    {body : Instance (decl.sorts + 1) (decl.grades + 3) →
      Destructors (decl.levels + S.length) (.var :: decl.scope.lifted S) ns}
    (hl : decl.Lifts sig F S body)
    (hF : ∀ ι, ∀ T ∈ decl.codataTypes, T.name = F →
      ∀ r ∈ (T.body ι).recursion decl.names, r = none)
    (hS : ∀ ι, decl.constraint ι → (decl.params ι).LiftsTypes sig S) :
    WfTypeDeclaration sig (decl.lifting F S ns body) := by
  obtain ⟨T, hT, hn, hb⟩ := hl
  have hT' : sig.HasCodataType F decl T := ⟨hd, hT, hn⟩
  obtain ⟨_, _, hdecl⟩ := hsig.wfTypeDeclaration hd
  have hdecl' : (∃ ι, decl.constraint ι) ∧ T.destructors.Nodup := by
    cases hdecl with
    | data hb' => simp [TypeDeclaration.codataTypes, hb'] at hT
    | codata _ hadm _ _ _ hc => exact ⟨hadm, hc T hT⟩
  obtain ⟨⟨ι, hι⟩, hc⟩ := hdecl'
  refine .codata rfl ?_
    (fun I hI => (TypeDeclaration.lifting_typed hsig hT' S body I hI (hS _ hI)).ren.wfCtx)
    (fun I hI T' hT'' => ?_) (fun _ _ _ hT'' _ _ hx => ?_) (fun T' hT'' => ?_)
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
    exact Destructors.Lifts.wfDestructors hT' hI' hα (.var (.var hA) .zero) hκ _ _ _ _ _ _ _ _
      hds (TypeDeclaration.lifting_typed hsig hT' S body I hI (hS _ hI))
      (InstanceArgs.identity_rename_neutral _) (hF _ T hT hn) (fun h => ⟨h, fun _ => rfl⟩)
  · cases List.mem_singleton.1 hT''
    exact hx.elim
  · cases List.mem_singleton.1 hT''
    exact (Destructors.Lifts.sublist (hb ⟨fun _ => .type, fun _ => .unrestrictedUnrestricted⟩)).nodup hc

end Sic.Core
