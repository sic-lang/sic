module

public import Sic.Core.Usage

/-!
# Usage Along the Signatures

The judgments of usage of annex 12 of RFC 36 hold in every signature that has the entries of theirs:
the usage reads its signature only by the entries that it has, the constants, the declared types,
the data types and the codata types, so that a signature with more entries gives the same premises.

The judgment `⊢ Σ ▶` checks the body of each constant definition in the signature before it, while
the program of a signature erases it in the whole signature, which has more entries.
The proof is by mutual structural recursion on the derivations, in the clause `where` of the
theorem.

ADE have no signatures.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-- A signature with every entry of another has its constants. -/
theorem Signature.HasConstant.mono {sig sig' : Signature} (hs : sig ⊆ sig') {f : Name}
    {j k g : Nat} {m : Mode} {p : Grade} {A : Instance j g → Term k []} :
    sig.HasConstant f j k g m p A → sig'.HasConstant f j k g m p A
  | .constantDefinition h => .constantDefinition (hs h)
  | .constantDeclaration h => .constantDeclaration (hs h)

-- ADE: none.
/-- The judgments of usage hold in every signature that has the entries of theirs. -/
structure UsageStableUnderExtension : Prop where
  /-- A term uses its variables in the same way in a signature with more entries.
  RFC: `\mathsf{ext}_{▶}.t` -/
  usage : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {γ : GradeVector Γ.length} {m : Mode}
    {t : Term k Γ}, sig ⊆ sig' → Usage sig γ m t → Usage sig' γ m t
  /-- Arguments of a telescope use their variables in the same way in a signature with more
  entries.
  RFC: `\mathsf{ext}_{▶}.\bar t` -/
  usageArgs : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {γ : GradeVector Γ.length} {m : Mode} {ts : Args k Γ ps},
    sig ⊆ sig' → UsageArgs sig γ m ts → UsageArgs sig' γ m ts
  /-- Arguments of an instance use their variables in the same way in a signature with more
  entries.
  RFC: `\mathsf{ext}_{▶}.\bar a` -/
  usageInstanceArgs : ∀ {sig sig' : Signature} {k : Nat} {Γ Δ : Scope} {γ : GradeVector Γ.length}
    {m : Mode} {ζ : GradeVector Δ.length} {as : InstanceArgs k Γ Δ},
    sig ⊆ sig' → UsageInstanceArgs sig γ m ζ as → UsageInstanceArgs sig' γ m ζ as
  /-- A telescope uses its variables in the same way in a signature with more entries.
  RFC: `\mathsf{ext}_{▶}.\Theta` -/
  usageTelescope : ∀ {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
    {γ : GradeVector Γ.length} {m : Mode} {Θ : Telescope k Γ ps},
    sig ⊆ sig' → UsageTelescope sig γ m Θ → UsageTelescope sig' γ m Θ

-- ADE: none.
/-- The judgments of usage hold in every signature that has the entries of theirs.
RFC: `\mathsf{ext}_{▶}.t`
RFC: `\mathsf{ext}_{▶}.\bar t`
RFC: `\mathsf{ext}_{▶}.\bar a`
RFC: `\mathsf{ext}_{▶}.\Theta` -/
theorem usageStableUnderExtension : UsageStableUnderExtension :=
  ⟨usage, usageArgs, fun hs h => usageInstanceArgs hs h, usageTelescope⟩
where
  usage {sig sig' : Signature} {k : Nat} {Γ : Scope} {γ : GradeVector Γ.length} {m : Mode}
      {t : Term k Γ} (hs : sig ⊆ sig') : Usage sig γ m t → Usage sig' γ m t
    | .var hts => .var (usageArgs hs hts)
    | .const h hm => .const (h.mono hs) hm
    | .sort => .sort
    | .inst h hq hp has => .inst ⟨hs h.1, h.2⟩ hq hp (usageInstanceArgs hs has)
    | .ctor h hc hq hp hts => .ctor ⟨hs h.1, h.2⟩ hc hq hp (usageArgs hs hts)
    | .recursor h hq hp hC ht hul hus hu hg hχ hr hprop =>
      .recursor ⟨hs h.1, h.2⟩ hq hp (fun j n C hC' => usage hs (hC j n C hC')) (usage hs ht) hul
        hus (fun i j T' con u hi hu' => usage hs (hu i j T' con u hi hu')) hg hχ hr hprop
    | .obs h hq hp hd ht hbs hm => .obs ⟨hs h.1, h.2⟩ hq hp hd (usage hs ht) (usageArgs hs hbs) hm
    | .corec h hq hp hh hS hSu hss hgl hSl hSs hgs hgu hδ hδr =>
      .corec ⟨hs h.1, h.2⟩ hq hp hh hS (fun j ps'' S' hS' => usageTelescope hs (hSu j ps'' S' hS'))
        (usageArgs hs hss) hgl hSl hSs hgs
        (fun i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hS' hd hg =>
          usage hs (hgu i j T' d ps'' S' p q ps₁ Ξ Θ B ψ g hi hS' hd hg)) hδ hδr
    | .sub h hle => .sub (usage hs h) hle
  usageArgs {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {γ : GradeVector Γ.length} {m : Mode} {ts : Args k Γ ps} (hs : sig ⊆ sig') :
      UsageArgs sig γ m ts → UsageArgs sig' γ m ts
    | .nil => .nil
    | .cons ht hts => .cons (usage hs ht) (usageArgs hs hts)
  usageInstanceArgs {sig sig' : Signature} {k : Nat} {Γ : Scope} {γ : GradeVector Γ.length}
      {m : Mode} (hs : sig ⊆ sig') :
      {Δ : Scope} → {ζ : GradeVector Δ.length} → {as : InstanceArgs k Γ Δ} →
      UsageInstanceArgs sig γ m ζ as → UsageInstanceArgs sig' γ m ζ as
    -- A pattern of a rule elaborates only when the scope of the parameters is given its first
    -- entry, which the vector `ζ ∙ p` of the conclusion does not give the elaborator.
    | [], _, _, .nil => .nil
    | .var :: _, _, _, .var has ha => .var (usageInstanceArgs hs has) (usage hs ha)
    | .secondOrder _ _ :: _, _, _, .secondOrder has hB =>
      .secondOrder (usageInstanceArgs hs has) (usage hs hB)
  usageTelescope {sig sig' : Signature} {k : Nat} {Γ : Scope} {ps : List Parameter}
      {γ : GradeVector Γ.length} {m : Mode} {Θ : Telescope k Γ ps} (hs : sig ⊆ sig') :
      UsageTelescope sig γ m Θ → UsageTelescope sig' γ m Θ
    | .nil => .nil
    | .cons hA hΘ => .cons (usage hs hA) (usageTelescope hs hΘ)
    | .sub h hle => .sub (usageTelescope hs h) hle

/-- The body of each constant definition of a well-used signature uses no variable, in the mode of
the definition, in the whole signature, which has the entries of the signature before it. -/
theorem UsageSig.constantDefinition_usage {sig : Signature} (hu : UsageSig sig) {d : ConstantDefinition}
    (hd : .constantDefinition d ∈ sig) (ι : Instance d.sorts d.grades) :
    Usage sig 𝟘ᶜ d.mode (d.body ι) := by
  induction hu with
  | empty => exact nomatch hd
  | constantDefinition _ hb ih =>
    rcases List.mem_cons.1 hd with he | hd'
    · cases he
      exact usageStableUnderExtension.usage (List.subset_cons_self _ _) (hb ι)
    · exact usageStableUnderExtension.usage (List.subset_cons_self _ _) (ih hd')
  | constantDeclaration _ ih | data _ _ _ ih | codata _ _ _ ih =>
    rcases List.mem_cons.1 hd with he | hd'
    · exact nomatch he
    · exact usageStableUnderExtension.usage (List.subset_cons_self _ _) (ih hd')

end Sic.Core
