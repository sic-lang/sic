module

public import Sic.Core.Ownership
public import Sic.Core.Substitution

/-!
# Renaming of the Ownership

The judgments of ownership of annex 12 of RFC 36 are stable under the renamings: a term whose value
has an ownership, given the ownerships `φ` of the variables of its scope, renamed by `ξ`, has the
same ownership, given ownerships `φ'` that give the image of each variable its ownership by `φ`.

The ownerships of the variables are the same in every premise, as a context is, so that they are
renamed backwards, as the types of a context are: every renaming keeps the ownership, even one that
renames two variables of the same ownership to the same one.
The proof states the judgments substituted by a substitution that gives each variable the
abstraction of its image, as the renaming of the typing does, so that the laws of the substitutions
give the premises of each rule; it is by mutual structural recursion on the derivations, in the
clause `where` of the theorem.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Renamed Ownerships -/

/-- The ownerships of the variables extended by those of the variables of a telescope give the
images of the variables by a renaming lifted under them the same ownerships when the ownerships
before the extension do. -/
theorem Ownership.extendFields_liftN :
    {Γ Δ : Scope} → {φ' : Var Γ .var → Grade} → {φ : Var Δ .var → Grade} → {ξ : Ren Γ Δ} →
      (∀ x, φ' (ξ x) = φ x) → (o g : Grade) → (ps : List Parameter) →
      ∀ x,
        Ownership.extendFields φ' o g ps (Ren.liftN ps.length ξ x) =
          Ownership.extendFields φ o g ps x
  | _, _, _, _, _, h, _, _, [] => h
  | Γ, Δ, _, _, ξ, h, o, g, _ :: ps =>
    Ownership.extendFields_liftN (Γ := .var :: Γ) (Δ := .var :: Δ) (ξ := Ren.lift ξ)
      (fun | .zero => rfl | .succ x => h x) o g ps

/-- The ownerships of the variables extended by those of recursive results give the images of the
variables by a renaming lifted under them the same ownerships when the ownerships before the
extension do. -/
theorem Ownership.extendResults_liftN :
    {Γ Δ : Scope} → {φ' : Var Γ .var → Grade} → {φ : Var Δ .var → Grade} → {ξ : Ren Γ Δ} →
      (∀ x, φ' (ξ x) = φ x) → (p : Grade) → (es : List Grade) → (n : Nat) →
      ∀ x, Ownership.extendResults φ' p es n (Ren.liftN n ξ x) = Ownership.extendResults φ p es n x
  | _, _, _, _, _, h, _, _, 0 => h
  | Γ, Δ, _, _, ξ, h, p, es, n + 1 =>
    Ownership.extendResults_liftN (Γ := .var :: Γ) (Δ := .var :: Δ) (ξ := Ren.lift ξ)
      (fun | .zero => rfl | .succ x => h x) p es.tail n

/-- The ownerships of the variables extended by those of the arguments of a telescope give the
images of the variables by a renaming lifted under them the same ownerships when the ownerships
before the extension do. -/
theorem Ownership.extendArgs_liftN :
    {Γ Δ : Scope} → {φ' : Var Γ .var → Grade} → {φ : Var Δ .var → Grade} → {ξ : Ren Γ Δ} →
      (∀ x, φ' (ξ x) = φ x) → (g : Grade) → (ps : List Parameter) → (os : List Grade) →
      ∀ x,
        Ownership.extendArgs φ' g ps os (Ren.liftN ps.length ξ x) =
          Ownership.extendArgs φ g ps os x
  | _, _, _, _, _, h, _, [], _ => h
  | Γ, Δ, _, _, ξ, h, g, _ :: ps, os =>
    Ownership.extendArgs_liftN (Γ := .var :: Γ) (Δ := .var :: Δ) (ξ := Ren.lift ξ)
      (fun | .zero => rfl | .succ x => h x) g ps os.tail

/-! ## Stability of the Ownership -/

-- ADE: none.
/-- The judgments of ownership are stable under the renamings. -/
structure OwnershipStableUnderRenaming : Prop where
  /-- A term, renamed, has the same ownership, given ownerships of the variables that give the image
  of each variable its ownership.
  RFC: `\mathsf{ren}_{◀}.t` -/
  ownership : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {φ' : Var Γ .var → Grade}
    {φ : Var Δ .var → Grade} {m : Mode} {p : Grade} {t : Term k Δ} (ξ : Ren Γ Δ),
    (∀ x, φ' (ξ x) = φ x) → Ownership sig φ m p t → Ownership sig φ' m p (t.rename ξ)
  /-- Arguments of a telescope, renamed, have the same ownerships, given ownerships of the variables
  that give the image of each variable its ownership.
  RFC: `\mathsf{ren}_{◀}.\bar t` -/
  ownershipArgs : ∀ {sig : Signature} {k : Nat} {Γ Δ : Scope} {ps : List Parameter}
    {φ' : Var Γ .var → Grade} {φ : Var Δ .var → Grade} {m : Mode} {ts : Args k Δ ps}
    {os : List Grade} (ξ : Ren Γ Δ),
    (∀ x, φ' (ξ x) = φ x) → OwnershipArgs sig φ m ts os → OwnershipArgs sig φ' m (ts.rename ξ) os

-- ADE: none.
/-- The judgments of ownership are stable under the renamings.
RFC: `\mathsf{ren}_{◀}.t`
RFC: `\mathsf{ren}_{◀}.\bar t` -/
theorem ownershipStableUnderRenaming : OwnershipStableUnderRenaming :=
  ⟨fun ξ hφ h => by rw [Term.rename_eq_subst]; exact ownership h (fun _ => rfl) hφ,
    fun ξ hφ h => by rw [Args.rename_eq_subst]; exact ownershipArgs h (fun _ => rfl) hφ⟩
where
  ownership {sig : Signature} {k : Nat} {Γ Δ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
      {φ' : Var Γ .var → Grade} {φ : Var Δ .var → Grade} {m : Mode} {p : Grade} {t : Term k Δ} :
      Ownership sig φ m p t → (∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) →
        (∀ x, φ' (ξ x) = φ x) → Ownership sig φ' m p (t.subst θ)
    | .var (x := x), hθ, hφ => by
      rw [Term.var_subst_of (hθ x), ← hφ x]
      exact .var
    | .secondOrder (X := X) hts hp, hθ, hφ => by
      rw [Term.var_subst_of (hθ X)]
      exact .secondOrder (ownershipArgs hts hθ hφ) hp
    | .const h, _, _ => .const h
    | .sort, _, _ => .sort
    | .inst, _, _ => .inst
    | .ctor h hc hq hp hts, hθ, hφ => by
      rw [Term.ctor_subst]
      exact .ctor h hc hq hp (ownershipArgs hts hθ hφ)
    | .recursor (us := us) h hq hp ht hul hus hu, hθ, hφ => by
      refine .recursor h hq hp (ownership ht hθ hφ) ((Branches.length_subst _ us).trans hul) ?_ ?_
      · intro i j T' con hi
        obtain ⟨u, hu'⟩ := hus i j T' con hi
        exact ⟨_, Branches.get_subst _ hu'⟩
      · intro i j T' con u hi hu'
        obtain ⟨u₀, hu₀, rfl⟩ := Branches.get_subst_inv _ hu'
        rw [Branches.grades_subst]
        exact ownership (hu i j T' con u₀ hi hu₀) (Subst.liftN_eta_of _ (Subst.liftN_eta_of _ hθ))
          (Ownership.extendResults_liftN (Ownership.extendFields_liftN hφ _ _ _) _ _ _)
    | .obs h hq hp hd ht hbs hv, hθ, hφ => by
      rw [Term.obs_subst]
      exact .obs h hq hp hd (ownership ht hθ hφ) (ownershipArgs hbs hθ hφ) hv
    | .corec (Ss := Ss) (gs := gs) h hq hp hh hS hss hSl hSs hgl hgs hgo hgr, hθ, hφ => by
      rw [Term.corec_subst]
      refine .corec h hq hp hh (States.get_subst _ hS) (ownershipArgs hss hθ hφ)
        ((States.length_subst _ Ss).trans hSl) ?_ ((CorecBranches.length_subst _ gs).trans hgl)
        ?_ ?_ ?_
      · intro j T' hj
        obtain ⟨ps'', S', hS'⟩ := hSs j T' hj
        exact ⟨ps'', _, States.get_subst _ hS'⟩
      · intro i j T' d ps'' S' hi hS' p q ps₁ Ξ Θ B ψ hd
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        obtain ⟨g, hg⟩ := hgs i j T' d ps'' S₀ hi hS₀ p q ps₁ Ξ Θ B ψ hd
        exact ⟨_, CorecBranches.get_subst _ hg⟩
      · intro i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hS' hd hg hn os' v hos hv
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        obtain ⟨g₀, hg₀, rfl⟩ := CorecBranches.get_subst_inv _ hg
        exact ownership (hgo i j T' d ps'' S₀ p q ps₁ Ξ Θ B ψ g₀ hi hS₀ hd hg₀ hn os' v hos hv)
          (Subst.liftN_eta_of _ (Subst.liftN_eta_of _ hθ))
          (Ownership.extendArgs_liftN (Ownership.extendFields_liftN hφ _ _ _) _ _ _)
      · intro i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g D' hi hS' hd hg hn os' hos
        obtain ⟨S₀, hS₀, rfl⟩ := States.get_subst_inv _ hS'
        obtain ⟨g₀, hg₀, rfl⟩ := CorecBranches.get_subst_inv _ hg
        exact ownership (hgr i j T' d ps'' S₀ p q ps₁ Ξ Θ B ψ g₀ D' hi hS₀ hd hg₀ hn os' hos)
          (Subst.liftN_eta_of _ (Subst.liftN_eta_of _ hθ))
          (Ownership.extendArgs_liftN (Ownership.extendFields_liftN hφ _ _ _) _ _ _)
    | .sub h hle, hθ, hφ => .sub (ownership h hθ hφ) hle
  ownershipArgs {sig : Signature} {k : Nat} {Γ Δ : Scope} {θ : Subst k Γ Δ} {ξ : Ren Γ Δ}
      {ps : List Parameter} {φ' : Var Γ .var → Grade} {φ : Var Δ .var → Grade} {m : Mode}
      {ts : Args k Δ ps} {os : List Grade} :
      OwnershipArgs sig φ m ts os → (∀ {a} (x : Var Δ a), θ x = Var.eta (ξ x)) →
        (∀ x, φ' (ξ x) = φ x) → OwnershipArgs sig φ' m (ts.subst θ) os
    | .nil, _, _ => .nil
    | .cons ht hr hts, hθ, hφ => .cons (ownership ht hθ hφ) hr (ownershipArgs hts hθ hφ)

end Sic.Core
