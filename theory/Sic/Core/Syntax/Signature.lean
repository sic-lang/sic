module

public import Sic.Core.Syntax
public import Sic.Grading.GradeSet
import Sic.Core.Syntax.Terms

/-!
# Properties of the Signatures

Properties of the signatures of annex 08 of RFC 36: the names of the type declarations, the entries,
the types, the constructors and the destructors of a signature whose names are distinct are unique,
and so are the parameters of the fields of a constructor, of the arguments of a destructor and the
position of a declared type.
The cases of a block are its constructors, or its destructors, each with the position of its type:
a constructor or a destructor of a type is in a case, and a case holds the position of its type.
In a signature whose names are distinct, what the erasure of a corecursor reads of its type at each
case is found there: the grades and the arguments of the destructors and the types that they
resume, and the case of each branch of a corecursor, with its destructor and its state.
`Signature.ErasesPropDestructors` names the property, which well-formed signatures have, that the
destructors of the blocks of propositions are erased.

ADE have no signatures: their definitions are in their contexts.
-/

@[expose] public section

namespace Sic.Core

open Sic.Grading

/-! ## Signatures

An entry of the signature has sort, level and grade variables, the qualities and the grades of an
instance being given to its type, its body, its parameters and its sort. -/

/-- A signature with every entry of another has its constants. -/
theorem Signature.HasConstant.mono {sig sig' : Signature} (hs : sig ⊆ sig') {f : Name}
    {j k g : Nat} {m : Mode} {p : Grade} {A : Instance j g → Term k []} :
    sig.HasConstant f j k g m p A → sig'.HasConstant f j k g m p A
  | .constantDefinition h => .constantDefinition (hs h)
  | .constantDeclaration h => .constantDeclaration (hs h)

/-- Destructors none of which is recursive have no recursive destructor at any position. -/
theorem Destructors.recursionAt_eq_none {k : Nat} {names : List Name} {Γ : Scope} {ns : List Name}
    {ds : Destructors k Γ ns} (h : ∀ r ∈ ds.recursion names, r = none) (i : Nat) :
    ds.recursionAt names i = none := by
  unfold Destructors.recursionAt
  cases hi : (ds.recursion names)[i]? with
  | none => rfl
  | some r => rw [h r (List.mem_of_getElem? hi)]; rfl

/-- The type of the result of a recursive destructor is a type of the block. -/
theorem Destructors.recursionAt_mem {k : Nat} {names : List Name} {D : Name} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {i : Nat} →
      ds.recursionAt names i = some D → D ∈ names
  | _, _, .nil, _, h => by simp [Destructors.recursionAt, Destructors.recursion] at h
  | _, _, .cons _ _ _ _ B _ _, 0, h => Term.blockName_mem (A := B) (by
      simpa [Destructors.recursionAt, Destructors.recursion] using h)
  | _, _, .cons _ _ _ _ _ _ ds, i + 1, h => Destructors.recursionAt_mem (ds := ds) (i := i)
      (by simpa [Destructors.recursionAt, Destructors.recursion] using h)

/-- A data type of the signature is one of its declared types. -/
theorem Signature.HasDataType.hasDeclaredType {sig : Signature} {D : Name} {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (h : sig.HasDataType D decl T) :
    sig.HasDeclaredType D decl T.usage :=
  ⟨h.1, .inl ⟨T, h.2.1, h.2.2, rfl⟩⟩

/-- A codata type of the signature is one of its declared types. -/
theorem Signature.HasCodataType.hasDeclaredType {sig : Signature} {D : Name}
    {decl : TypeDeclaration} {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T) : sig.HasDeclaredType D decl T.usage :=
  ⟨h.1, .inr ⟨T, h.2.1, h.2.2, rfl⟩⟩

/-- The names of a type declaration are those of its data types and of its codata types, one of
which is empty. -/
theorem TypeDeclaration.names_eq (decl : TypeDeclaration) :
    decl.names = decl.dataTypes.map (·.name) ++ decl.codataTypes.map (·.name) := by
  simp only [TypeDeclaration.names, TypeDeclaration.dataTypes, TypeDeclaration.codataTypes]
  split <;> simp

/-- A data type of a type declaration is named by the declaration. -/
theorem TypeDeclaration.name_mem_names {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes) :
    T.name ∈ decl.names :=
  decl.names_eq ▸ List.mem_append_left _ (List.mem_map_of_mem hT)

/-- A name of a type declaration with a data type is the name of one of its data types. -/
theorem TypeDeclaration.mem_names_of_dataTypes {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    {D : Name} (hD : D ∈ decl.names) : ∃ T' ∈ decl.dataTypes, T'.name = D := by
  unfold TypeDeclaration.dataTypes at hT ⊢
  unfold TypeDeclaration.names at hD
  split at hT
  · rename_i heq
    rw [heq] at hD
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hD
    exact ⟨T', hT', rfl⟩
  · cases hT

/-- A name of a type declaration with a codata type is the name of one of its codata types. -/
theorem TypeDeclaration.mem_names_of_codataTypes {decl : TypeDeclaration}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.codataTypes)
    {D : Name} (hD : D ∈ decl.names) : ∃ T' ∈ decl.codataTypes, T'.name = D := by
  unfold TypeDeclaration.codataTypes at hT ⊢
  unfold TypeDeclaration.names at hD
  split at hT
  · cases hT
  · rename_i heq
    rw [heq] at hD
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hD
    exact ⟨T', hT', rfl⟩

/-- The data types of a type declaration whose names are distinct have distinct names. -/
theorem TypeDeclaration.dataTypes_nodup {decl : TypeDeclaration} (h : decl.names.Nodup) :
    (decl.dataTypes.map (·.name)).Nodup :=
  (List.nodup_append.1 (decl.names_eq ▸ h)).1

/-- The type at a position of the data types of a declaration whose names are distinct is at the
same position of its names. -/
theorem TypeDeclaration.idxOf_dataTypes {decl : TypeDeclaration} (h : decl.names.Nodup) {j : Nat}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hj : decl.dataTypes[j]? = some T) :
    decl.names.idxOf T.name = j := by
  obtain ⟨hj', he⟩ := List.getElem?_eq_some_iff.1 hj
  have hl : j < decl.names.length := by
    rw [decl.names_eq, List.length_append, List.length_map]
    omega
  have hn : decl.names[j] = T.name := by
    have hm : j < (decl.dataTypes.map (·.name)).length := by rw [List.length_map]; exact hj'
    simp only [decl.names_eq]
    rw [List.getElem_append_left hm, List.getElem_map, he]
  rw [← hn]
  exact h.idxOf_getElem j hl

/-- In a signature whose names are distinct, a name is introduced by one entry at most.
RFC: `\mathsf{unique}_\Sigma` -/
theorem Signature.Distinct.entry_unique : {sig : Signature} → sig.Distinct → {e₁ e₂ : Entry} →
    {n : Name} → e₁ ∈ sig → e₂ ∈ sig → n ∈ e₁.names → n ∈ e₂.names → e₁ = e₂ := by
  intro sig
  induction sig with
  | nil => intro _ _ _ _ h₁; cases h₁
  | cons e sig ih =>
    intro hd e₁ e₂ n h₁ h₂ hn₁ hn₂
    obtain ⟨h, -, hfresh, -⟩ := hd
    rcases List.mem_cons.mp h₁ with rfl | h₁' <;> rcases List.mem_cons.mp h₂ with rfl | h₂'
    · rfl
    · exact absurd hn₂ (hfresh _ h₂' n hn₁)
    · exact absurd hn₁ (hfresh _ h₁' n hn₂)
    · exact ih h h₁' h₂' hn₁ hn₂

/-- The names that an entry of a signature whose names are distinct introduces are distinct. -/
theorem Signature.Distinct.nodup : {sig : Signature} → sig.Distinct → {e : Entry} → e ∈ sig →
    e.names.Nodup
  | [], _, _, h => nomatch h
  | _ :: _, ⟨h, hn, _, _⟩, _, he => by
    rcases List.mem_cons.1 he with rfl | he
    · exact hn
    · exact h.nodup he

/-- In a signature whose names are distinct, a constant has one entry, whose variables, mode,
ownership and type are unique. -/
theorem Signature.Distinct.hasConstant_unique {sig : Signature} (hd : sig.Distinct) {f : Name}
    {j₁ k₁ g₁ j₂ k₂ g₂ : Nat} {m₁ m₂ : Mode} {p₁ p₂ : Grade} {A₁ : Instance j₁ g₁ → Term k₁ []}
    {A₂ : Instance j₂ g₂ → Term k₂ []} (h₁ : sig.HasConstant f j₁ k₁ g₁ m₁ p₁ A₁)
    (h₂ : sig.HasConstant f j₂ k₂ g₂ m₂ p₂ A₂) :
    j₁ = j₂ ∧ k₁ = k₂ ∧ g₁ = g₂ ∧ m₁ = m₂ ∧ p₁ = p₂ ∧ HEq A₁ A₂ := by
  cases h₁ with
  | constantDefinition hm₁ =>
    generalize hf : ConstantDefinition.name _ = f at h₂
    cases h₂ with
    | constantDefinition hm₂ =>
      cases hd.entry_unique hm₁ hm₂ (List.mem_singleton_self _) (hf ▸ List.mem_singleton_self _)
      exact ⟨rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩
    | constantDeclaration hm₂ =>
      nomatch hd.entry_unique hm₁ hm₂ (List.mem_singleton_self _) (hf ▸ List.mem_singleton_self _)
  | constantDeclaration hm₁ =>
    generalize hf : ConstantDeclaration.name _ = f at h₂
    cases h₂ with
    | constantDefinition hm₂ =>
      nomatch hd.entry_unique hm₁ hm₂ (List.mem_singleton_self _) (hf ▸ List.mem_singleton_self _)
    | constantDeclaration hm₂ =>
      cases hd.entry_unique hm₁ hm₂ (List.mem_singleton_self _) (hf ▸ List.mem_singleton_self _)
      exact ⟨rfl, rfl, rfl, rfl, rfl, HEq.rfl⟩

/-- In a signature whose names are distinct, a declared type is one data type of one type
declaration. -/
theorem Signature.Distinct.hasDataType_unique {sig : Signature} (hd : sig.Distinct) {D : Name}
    {decl₁ decl₂ : TypeDeclaration} {T₁ : DataType decl₁.sorts decl₁.grades decl₁.levels decl₁.scope}
    {T₂ : DataType decl₂.sorts decl₂.grades decl₂.levels decl₂.scope}
    (h₁ : sig.HasDataType D decl₁ T₁) (h₂ : sig.HasDataType D decl₂ T₂) :
    decl₁ = decl₂ ∧ HEq T₁ T₂ := by
  obtain ⟨hm₁, hT₁, hn₁⟩ := h₁
  obtain ⟨hm₂, hT₂, hn₂⟩ := h₂
  have he := hd.entry_unique hm₁ hm₂ (n := D) (hn₁ ▸ TypeDeclaration.name_mem_names hT₁)
    (hn₂ ▸ TypeDeclaration.name_mem_names hT₂)
  injection he with he
  subst he
  exact ⟨rfl, heq_of_eq (List.eq_of_nodup_map (TypeDeclaration.dataTypes_nodup (hd.nodup hm₁)) hT₁
    hT₂ (hn₁.trans hn₂.symm))⟩

/-- In a signature whose names are distinct, two equal instances of data types are instances of
one data type of one type declaration, with the same sorts, levels, grades and arguments. -/
theorem Signature.Distinct.dataInst_unique {sig : Signature} (hd : sig.Distinct)
    {decl₁ decl₂ : TypeDeclaration} {D₁ D₂ : Name}
    {T₁ : DataType decl₁.sorts decl₁.grades decl₁.levels decl₁.scope}
    {T₂ : DataType decl₂.sorts decl₂.grades decl₂.levels decl₂.scope}
    (h₁ : sig.HasDataType D₁ decl₁ T₁) (h₂ : sig.HasDataType D₂ decl₂ T₂) {k : Nat} {Γ : Scope}
    {qs₁ qs₂ : List Quality} {ls₁ ls₂ : List (Level k)} {ps₁ ps₂ : List Grade}
    {as₁ : InstanceArgs k Γ decl₁.scope} {as₂ : InstanceArgs k Γ decl₂.scope}
    (he : Term.inst D₁ qs₁ ls₁ ps₁ as₁ = Term.inst D₂ qs₂ ls₂ ps₂ as₂) :
    D₁ = D₂ ∧ decl₁ = decl₂ ∧ HEq T₁ T₂ ∧ qs₁ = qs₂ ∧ ls₁ = ls₂ ∧ ps₁ = ps₂ ∧ HEq as₁ as₂ := by
  obtain ⟨-, rfl, rfl, rfl, rfl, has⟩ := Term.inst.inj he
  obtain ⟨rfl, hT⟩ := hd.hasDataType_unique h₁ h₂
  exact ⟨rfl, rfl, hT, rfl, rfl, rfl, has⟩

/-- In a signature whose names are distinct, the constructors of a declared type have distinct
names. -/
theorem Signature.Distinct.constructors_nodup : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : DataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasDataType D decl T → (T.constructors.map (·.name)).Nodup
  | [], _, _, _, _, h => nomatch h.1
  | _ :: _, ⟨hd, _, _, hc⟩, _, _, _, ⟨he, hT, hn⟩ => by
    rcases List.mem_cons.1 he with he | he
    · subst he; exact hc.1 _ hT
    · exact hd.constructors_nodup ⟨he, hT, hn⟩

/-- A codata type of a type declaration is named by the declaration. -/
theorem TypeDeclaration.codata_name_mem_names {decl : TypeDeclaration}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.codataTypes) :
    T.name ∈ decl.names :=
  decl.names_eq ▸ List.mem_append_right _ (List.mem_map_of_mem hT)

/-- The codata types of a type declaration whose names are distinct have distinct names. -/
theorem TypeDeclaration.codataTypes_nodup {decl : TypeDeclaration} (h : decl.names.Nodup) :
    (decl.codataTypes.map (·.name)).Nodup :=
  (List.nodup_append.1 (decl.names_eq ▸ h)).2.1

/-- A type declaration has no data type or no codata type. -/
theorem TypeDeclaration.dataTypes_codataTypes (decl : TypeDeclaration) :
    decl.dataTypes = [] ∨ decl.codataTypes = [] := by
  simp only [TypeDeclaration.dataTypes, TypeDeclaration.codataTypes]
  split <;> simp

/-- The codata type at a position of the codata types of a declaration whose names are distinct is
at the same position of its names. -/
theorem TypeDeclaration.idxOf?_codataTypes {decl : TypeDeclaration} (h : decl.names.Nodup)
    {j : Nat} {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (hj : decl.codataTypes[j]? = some T) : decl.names.idxOf? T.name = some j := by
  have hD : decl.dataTypes = [] := by
    rcases decl.dataTypes_codataTypes with h' | h'
    · exact h'
    · rw [h'] at hj; cases hj
  have hn : decl.names = decl.codataTypes.map (·.name) := by
    rw [decl.names_eq, hD, List.map_nil, List.nil_append]
  refine List.idxOf?_of_getElem? h ?_
  rw [hn, List.getElem?_map, hj]
  rfl

/-- In a signature whose names are distinct, a codata type is one codata type of one type
declaration. -/
theorem Signature.Distinct.hasCodataType_unique {sig : Signature} (hd : sig.Distinct) {D : Name}
    {decl₁ decl₂ : TypeDeclaration}
    {T₁ : CodataType decl₁.sorts decl₁.grades decl₁.levels decl₁.scope}
    {T₂ : CodataType decl₂.sorts decl₂.grades decl₂.levels decl₂.scope}
    (h₁ : sig.HasCodataType D decl₁ T₁) (h₂ : sig.HasCodataType D decl₂ T₂) :
    decl₁ = decl₂ ∧ HEq T₁ T₂ := by
  obtain ⟨hm₁, hT₁, hn₁⟩ := h₁
  obtain ⟨hm₂, hT₂, hn₂⟩ := h₂
  have he := hd.entry_unique hm₁ hm₂ (n := D) (hn₁ ▸ TypeDeclaration.codata_name_mem_names hT₁)
    (hn₂ ▸ TypeDeclaration.codata_name_mem_names hT₂)
  injection he with he
  subst he
  exact ⟨rfl, heq_of_eq (List.eq_of_nodup_map (TypeDeclaration.codataTypes_nodup (hd.nodup hm₁))
    hT₁ hT₂ (hn₁.trans hn₂.symm))⟩

/-- In a signature whose names are distinct, two equal instances of codata types are instances of
one codata type of one type declaration, with the same sorts, levels, grades and arguments. -/
theorem Signature.Distinct.codataInst_unique {sig : Signature} (hd : sig.Distinct)
    {decl₁ decl₂ : TypeDeclaration} {D₁ D₂ : Name}
    {T₁ : CodataType decl₁.sorts decl₁.grades decl₁.levels decl₁.scope}
    {T₂ : CodataType decl₂.sorts decl₂.grades decl₂.levels decl₂.scope}
    (h₁ : sig.HasCodataType D₁ decl₁ T₁) (h₂ : sig.HasCodataType D₂ decl₂ T₂) {k : Nat} {Γ : Scope}
    {qs₁ qs₂ : List Quality} {ls₁ ls₂ : List (Level k)} {ps₁ ps₂ : List Grade}
    {as₁ : InstanceArgs k Γ decl₁.scope} {as₂ : InstanceArgs k Γ decl₂.scope}
    (he : Term.inst D₁ qs₁ ls₁ ps₁ as₁ = Term.inst D₂ qs₂ ls₂ ps₂ as₂) :
    D₁ = D₂ ∧ decl₁ = decl₂ ∧ HEq T₁ T₂ ∧ qs₁ = qs₂ ∧ ls₁ = ls₂ ∧ ps₁ = ps₂ ∧ HEq as₁ as₂ := by
  obtain ⟨-, rfl, rfl, rfl, rfl, has⟩ := Term.inst.inj he
  obtain ⟨rfl, hT⟩ := hd.hasCodataType_unique h₁ h₂
  exact ⟨rfl, rfl, hT, rfl, rfl, rfl, has⟩

/-- In a signature whose names are distinct, a declared type is not both a data type and a codata
type. -/
theorem Signature.Distinct.not_hasDataType_hasCodataType {sig : Signature} (hd : sig.Distinct)
    {D : Name} {decl₁ decl₂ : TypeDeclaration}
    {T₁ : DataType decl₁.sorts decl₁.grades decl₁.levels decl₁.scope}
    {T₂ : CodataType decl₂.sorts decl₂.grades decl₂.levels decl₂.scope}
    (h₁ : sig.HasDataType D decl₁ T₁) (h₂ : sig.HasCodataType D decl₂ T₂) : False := by
  obtain ⟨hm₁, hT₁, hn₁⟩ := h₁
  obtain ⟨hm₂, hT₂, hn₂⟩ := h₂
  have he := hd.entry_unique hm₁ hm₂ (n := D) (hn₁ ▸ TypeDeclaration.name_mem_names hT₁)
    (hn₂ ▸ TypeDeclaration.codata_name_mem_names hT₂)
  injection he with he
  subst he
  rcases decl₁.dataTypes_codataTypes with h | h
  · rw [h] at hT₁; exact nomatch hT₁
  · rw [h] at hT₂; exact nomatch hT₂

/-- In a signature whose names are distinct, the destructors of a codata type have distinct
names. -/
theorem Signature.Distinct.destructors_nodup : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → T.destructors.Nodup
  | [], _, _, _, _, h => nomatch h.1
  | _ :: _, ⟨hd, _, _, hc⟩, _, _, _, ⟨he, hT, hn⟩ => by
    rcases List.mem_cons.1 he with he | he
    · subst he; exact hc.2 _ hT
    · exact hd.destructors_nodup ⟨he, hT, hn⟩

/-- A case of the types `Ts` is an element of one of them. -/
theorem TypeDeclaration.mem_casesFrom {α β : Type} {f : α → List β} :
    {i : Nat} → {Ts : List α} → {x : Nat × α × β} →
      x ∈ TypeDeclaration.casesFrom f i Ts → x.2.1 ∈ Ts ∧ x.2.2 ∈ f x.2.1
  | _, [], _, h => nomatch h
  | _, _ :: _, _, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      exact ⟨List.mem_cons_self, hc⟩
    · obtain ⟨h₁, h₂⟩ := TypeDeclaration.mem_casesFrom h
      exact ⟨List.mem_cons_of_mem _ h₁, h₂⟩

/-- A case of the types `Ts`, the first one at the position `i`, holds the position of its type. -/
theorem TypeDeclaration.getElem?_of_mem_casesFrom {α β : Type} {f : α → List β} :
    {i : Nat} → {Ts : List α} → {j' : Nat} → {T : α} → {c : β} →
      (j', T, c) ∈ TypeDeclaration.casesFrom f i Ts → i ≤ j' ∧ Ts[j' - i]? = some T
  | _, [], _, _, _, h => nomatch h
  | i, _ :: Ts, j', _, _, h => by
    rcases List.mem_append.1 h with h | h
    · obtain ⟨_, _, he⟩ := List.mem_map.1 h
      cases he
      exact ⟨Nat.le_refl _, by simp⟩
    · obtain ⟨hle, hT⟩ := TypeDeclaration.getElem?_of_mem_casesFrom h
      refine ⟨Nat.le_of_succ_le hle, ?_⟩
      have he : j' - i = (j' - (i + 1)) + 1 := by omega
      rw [he, List.getElem?_cons_succ]
      exact hT

/-- An element of the type at the position `j'` of the types `Ts` is a case of them. -/
theorem TypeDeclaration.mem_casesFrom_of {α β : Type} {f : α → List β} :
    {i : Nat} → {Ts : List α} → {j' : Nat} → {T : α} → {c : β} → Ts[j']? = some T → c ∈ f T →
      (i + j', T, c) ∈ TypeDeclaration.casesFrom f i Ts
  | _, [], _, _, _, h, _ => nomatch h
  | i, _ :: Ts, 0, _, _, h, hc => by
    cases h
    exact List.mem_append_left _ (List.mem_map_of_mem hc)
  | i, _ :: Ts, j' + 1, _, _, h, hc => by
    have he : i + (j' + 1) = (i + 1) + j' := by omega
    rw [he]
    exact List.mem_append_right _ (TypeDeclaration.mem_casesFrom_of h hc)

/-- A case of a recursor on a block holds the position of its type among the data types. -/
theorem TypeDeclaration.dataTypes_getElem?_of_cases {decl : TypeDeclaration} {j : Nat}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (h : (j, T, con) ∈ decl.cases) : decl.dataTypes[j]? = some T :=
  (TypeDeclaration.getElem?_of_mem_casesFrom h).2

/-- A case of a corecursor on a block holds the position of its type among the codata types. -/
theorem TypeDeclaration.codataTypes_getElem?_of_codataCases {decl : TypeDeclaration} {j : Nat}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {d : Name}
    (h : (j, T, d) ∈ decl.codataCases) : decl.codataTypes[j]? = some T :=
  (TypeDeclaration.getElem?_of_mem_casesFrom h).2

/-- A constructor of the data type at the position `j` of a block is a case of a recursor on it. -/
theorem TypeDeclaration.mem_cases_of {decl : TypeDeclaration} {j : Nat}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hj : decl.dataTypes[j]? = some T) (hc : con ∈ T.constructors) : (j, T, con) ∈ decl.cases :=
  Nat.zero_add j ▸ TypeDeclaration.mem_casesFrom_of hj hc

/-- A destructor of the codata type at the position `j` of a block is a case of a corecursor on
it. -/
theorem TypeDeclaration.mem_codataCases_of {decl : TypeDeclaration} {j : Nat}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {d : Name}
    (hj : decl.codataTypes[j]? = some T) (hd : d ∈ T.destructors) :
    (j, T, d) ∈ decl.codataCases :=
  Nat.zero_add j ▸ TypeDeclaration.mem_casesFrom_of hj hd

/-- A constructor of a type of a block is in a case of the block, with the position of its type. -/
theorem TypeDeclaration.exists_cases {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hcon : con ∈ T.constructors) :
    ∃ i j : Nat, decl.cases[i]? = some (j, T, con) ∧ decl.dataTypes[j]? = some T := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
  have hmem := TypeDeclaration.mem_cases_of hj hcon
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
  exact ⟨i, j, hi, hj⟩

/-- Each constructor of a data type that an entry of the signature declares has a case. -/
theorem Signature.constructorCase_of_mem {sig : Signature} {decl : TypeDeclaration}
    {T : DataType decl.sorts decl.grades decl.levels decl.scope}
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope}
    (hdecl : .typeDeclaration decl ∈ sig) (hT : T ∈ decl.dataTypes) (hc : con ∈ T.constructors) :
    ∃ i, sig.constructorCase T.name con.name = some i := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
  have hm := TypeDeclaration.mem_cases_of hj hc
  have he : (Entry.constructorCase T.name con.name (.typeDeclaration decl)).isSome := by
    simp only [Entry.constructorCase,
      Entry.lookup_typeDeclaration (TypeDeclaration.name_mem_names hT), List.findIdx?_isSome,
      List.any_eq_true]
    exact ⟨_, hm, show (T.name == T.name && con.name == con.name) = true by
      rw [show (T.name == T.name) = true from decide_eq_true rfl,
        show (con.name == con.name) = true from decide_eq_true rfl]; rfl⟩
  clear hm hj
  induction sig with
  | nil => nomatch hdecl
  | cons e sig ih =>
    show ∃ i, (e :: sig).findSome? (Entry.constructorCase T.name con.name) = some i
    cases he' : Entry.constructorCase T.name con.name e with
    | some i => exact ⟨i, by rw [List.findSome?_cons, he']⟩
    | none =>
      rw [List.findSome?_cons, he']
      rcases List.mem_cons.1 hdecl with h | h
      · subst h
        rw [he'] at he
        nomatch he
      · exact ih h

/-- Each destructor of a codata type that an entry of the signature declares has a case. -/
theorem Signature.destructorCase_of_mem {sig : Signature} {decl : TypeDeclaration}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {d : Name}
    (hdecl : .typeDeclaration decl ∈ sig) (hT : T ∈ decl.codataTypes) (hdm : d ∈ T.destructors) :
    ∃ i, sig.destructorCase T.name d = some i := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
  have hc := TypeDeclaration.mem_codataCases_of hj hdm
  have he : (Entry.destructorCase T.name d (.typeDeclaration decl)).isSome := by
    simp only [Entry.destructorCase,
      Entry.lookup_typeDeclaration (TypeDeclaration.codata_name_mem_names hT), List.findIdx?_isSome,
      List.any_eq_true]
    exact ⟨_, hc, show (T.name == T.name && d == d) = true by
      rw [show (T.name == T.name) = true from decide_eq_true rfl,
        show (d == d) = true from decide_eq_true rfl]; rfl⟩
  clear hc hj
  induction sig with
  | nil => nomatch hdecl
  | cons e sig ih =>
    show ∃ i, (e :: sig).findSome? (Entry.destructorCase T.name d) = some i
    cases he' : Entry.destructorCase T.name d e with
    | some i => exact ⟨i, by rw [List.findSome?_cons, he']⟩
    | none =>
      rw [List.findSome?_cons, he']
      rcases List.mem_cons.1 hdecl with h | h
      · subst h
        rw [he'] at he
        nomatch he
      · exact ih h

/-- The cases of types with distinct names, whose elements have distinct names, have distinct
names of types and of elements. -/
theorem TypeDeclaration.casesFrom_nodup {α β : Type} {f : α → List β} {nα : α → Name}
    {nβ : β → Name} :
    {i : Nat} → {Ts : List α} → (Ts.map nα).Nodup → (∀ T ∈ Ts, ((f T).map nβ).Nodup) →
        ((TypeDeclaration.casesFrom f i Ts).map fun x => (nα x.2.1, nβ x.2.2)).Nodup
  | _, [], _, _ => List.nodup_nil
  | i, T :: Ts, hn, hc => by
    rw [List.map_cons, List.nodup_cons] at hn
    have he : (TypeDeclaration.casesFrom f i (T :: Ts)).map (fun x => (nα x.2.1, nβ x.2.2)) =
        ((f T).map nβ).map (Prod.mk (nα T)) ++
          (TypeDeclaration.casesFrom f (i + 1) Ts).map (fun x => (nα x.2.1, nβ x.2.2)) := by
      simp only [TypeDeclaration.casesFrom, List.map_append, List.map_map]
      rfl
    rw [he]
    refine List.nodup_append.2 ⟨(hc T List.mem_cons_self).map (Prod.mk (nα T))
      (fun _ _ hab he => hab (Prod.mk.inj he).2),
      TypeDeclaration.casesFrom_nodup hn.2 fun T hT => hc T (List.mem_cons_of_mem _ hT), ?_⟩
    intro a ha b hb hab
    obtain ⟨n, _, rfl⟩ := List.mem_map.1 ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    have hn' : nα T = nα x.2.1 := congrArg Prod.fst hab
    exact hn.1 (hn' ▸ List.mem_map_of_mem (TypeDeclaration.mem_casesFrom hx).1)

/-- In a signature whose names are distinct, the cases of a type declaration have distinct names of
types and of constructors. -/
theorem Signature.Distinct.cases_nodup {sig : Signature} (hd : sig.Distinct)
    {decl : TypeDeclaration} (h : .typeDeclaration decl ∈ sig) :
    (decl.cases.map fun x => (x.2.1.name, x.2.2.name)).Nodup :=
  TypeDeclaration.casesFrom_nodup (TypeDeclaration.dataTypes_nodup (hd.nodup h)) fun _ hT => hd.constructors_nodup ⟨h, hT, rfl⟩

/-- In a signature whose names are distinct, the cases of a corecursor on a type declaration have
distinct names of types and of destructors. -/
theorem Signature.Distinct.codataCases_nodup {sig : Signature} (hd : sig.Distinct)
    {decl : TypeDeclaration} (h : .typeDeclaration decl ∈ sig) :
    (decl.codataCases.map fun x => (x.2.1.name, x.2.2)).Nodup :=
  TypeDeclaration.casesFrom_nodup (nβ := id) (TypeDeclaration.codataTypes_nodup (hd.nodup h))
    fun _ hT => by rw [List.map_id]; exact hd.destructors_nodup ⟨h, hT, rfl⟩

/-- An entry that does not introduce the name `D` gives the case of no constructor of `D`. -/
theorem Entry.constructorCase_of_not_mem {D c : Name} :
    {e : Entry} → D ∉ e.names → Entry.constructorCase D c e = none :=
  fun h => Entry.lookup_of_not_mem h

/-- A signature none of whose entries introduces the name `D` gives the case of no constructor of
`D`. -/
theorem Signature.constructorCase_of_not_mem {D c : Name} :
    {sig : Signature} → (∀ e ∈ sig, D ∉ e.names) → sig.constructorCase D c = none
  | [], _ => rfl
  | e :: sig, h => by
    unfold Signature.constructorCase
    rw [List.findSome?_cons_of_isNone
      (by rw [Entry.constructorCase_of_not_mem (h e List.mem_cons_self)]; rfl)]
    exact Signature.constructorCase_of_not_mem fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- In a signature whose names are distinct, the case of a constructor of a data type is its case in
the block of its declaration. -/
theorem Signature.Distinct.constructorCase {c : Name} : {sig : Signature} → sig.Distinct →
    {D : Name} → {decl : TypeDeclaration} →
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} → sig.HasDataType D decl T →
    sig.constructorCase D c = Entry.constructorCase D c (.typeDeclaration decl)
  | [], _, _, _, _, h => nomatch h.1
  | e :: sig, ⟨hd, _, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩ => by
    unfold Signature.constructorCase
    rcases List.mem_cons.1 he with rfl | he'
    · cases hc : Entry.constructorCase D c (.typeDeclaration decl) with
      | some i => rw [List.findSome?_cons_of_isSome (by rw [hc]; rfl), hc]
      | none =>
        rw [List.findSome?_cons_of_isNone (by rw [hc]; rfl)]
        exact Signature.constructorCase_of_not_mem fun e' he'' hDe =>
          hfresh _ he'' D (hD ▸ TypeDeclaration.name_mem_names hT) hDe
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.constructorCase_of_not_mem hDe]; rfl)]
      exact hd.constructorCase ⟨he', hT, hD⟩

/-- An entry that does not introduce the name `D` gives the case of no destructor of `D`. -/
theorem Entry.destructorCase_of_not_mem {D d : Name} :
    {e : Entry} → D ∉ e.names → Entry.destructorCase D d e = none :=
  fun h => Entry.lookup_of_not_mem h

/-- A signature none of whose entries introduces the name `D` gives the case of no destructor of
`D`. -/
theorem Signature.destructorCase_of_not_mem {D d : Name} :
    {sig : Signature} → (∀ e ∈ sig, D ∉ e.names) → sig.destructorCase D d = none
  | [], _ => rfl
  | e :: sig, h => by
    unfold Signature.destructorCase
    rw [List.findSome?_cons_of_isNone
      (by rw [Entry.destructorCase_of_not_mem (h e List.mem_cons_self)]; rfl)]
    exact Signature.destructorCase_of_not_mem fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- In a signature whose names are distinct, the case of a destructor of a codata type is its case in
the block of its declaration. -/
theorem Signature.Distinct.destructorCase {d : Name} : {sig : Signature} → sig.Distinct →
    {D : Name} → {decl : TypeDeclaration} →
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} → sig.HasCodataType D decl T →
    sig.destructorCase D d = Entry.destructorCase D d (.typeDeclaration decl)
  | [], _, _, _, _, h => nomatch h.1
  | e :: sig, ⟨hd, _, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩ => by
    unfold Signature.destructorCase
    rcases List.mem_cons.1 he with rfl | he'
    · cases hc : Entry.destructorCase D d (.typeDeclaration decl) with
      | some i => rw [List.findSome?_cons_of_isSome (by rw [hc]; rfl), hc]
      | none =>
        rw [List.findSome?_cons_of_isNone (by rw [hc]; rfl)]
        exact Signature.destructorCase_of_not_mem fun e' he'' hDe =>
          hfresh _ he'' D (hD ▸ TypeDeclaration.codata_name_mem_names hT) hDe
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.destructorCase_of_not_mem hDe]; rfl)]
      exact hd.destructorCase ⟨he', hT, hD⟩

/-- In a signature whose names are distinct, a case of the corecursors of a block is the case of its
destructor. -/
theorem Signature.Distinct.destructorCase_of_codataCases {sig : Signature} (hd : sig.Distinct)
    {decl : TypeDeclaration} (hdecl : .typeDeclaration decl ∈ sig) {i j : Nat}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} {d : Name}
    (hi : decl.codataCases[i]? = some (j, T, d)) : sig.destructorCase T.name d = some i := by
  have hT := (TypeDeclaration.mem_casesFrom (List.mem_of_getElem? hi)).1
  rw [hd.destructorCase ⟨hdecl, hT, rfl⟩]
  simp only [Entry.destructorCase,
    Entry.lookup_typeDeclaration (TypeDeclaration.codata_name_mem_names hT)]
  show decl.codataCases.findIdx? (fun x => x.2.1.name == T.name && x.2.2 == d) = some i
  have hs := List.findIdx?_isSome_of_mem (p := fun x => x.2.1.name == T.name && x.2.2 == d)
    (List.mem_of_getElem? hi) (by simp only [Bool.and_eq_true, beq_iff_eq, and_self])
  cases h : decl.codataCases.findIdx? (fun x => x.2.1.name == T.name && x.2.2 == d) with
  | none => rw [h] at hs; cases hs
  | some i' =>
    obtain ⟨x, hx, hpx⟩ := List.getElem?_of_findIdx?_eq_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at hpx
    exact congrArg some (List.getElem?_inj_of_nodup_map (hd.codataCases_nodup hdecl) hx hi
      (by rw [hpx.1, hpx.2]))

/-- A type declaration gives the parameters of the fields of a constructor of one of its types, whose
types and constructors have distinct names, at the instance. -/
theorem Entry.fieldParams_of_mem {decl : TypeDeclaration}
    (hn : (decl.dataTypes.map (·.name)).Nodup)
    {T : DataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.dataTypes)
    (hc : (T.constructors.map (·.name)).Nodup)
    {con : Constructor decl.sorts decl.grades decl.levels decl.scope} (hcon : con ∈ T.constructors)
    {qs : List Quality} {ps : List Grade} (hqp : Instance.AsMany decl.sorts decl.grades qs ps) :
    Entry.fieldParams T.name con.name qs ps (.typeDeclaration decl) =
      some (con.params hqp.inst) := by
  simp only [Entry.fieldParams, Entry.lookup_typeDeclaration (TypeDeclaration.name_mem_names hT)]
  split
  · try split
    all_goals first
      | contradiction
      | rw [List.find?_of_nodup_map hn hT, Option.bind_some, List.find?_of_nodup_map hc hcon,
          Option.map_some]
  · contradiction

/-- An entry that does not introduce the name `D` gives the parameters of the fields of no constructor
of `D`. -/
theorem Entry.fieldParams_of_not_mem {D c : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.fieldParams D c qs ps e = none :=
  fun h => Entry.lookup_of_not_mem h

/-- In a signature whose names are distinct, the parameters of the fields of a constructor of a declared
type are those of its telescope at the instance. -/
theorem Signature.Distinct.fieldParams : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : DataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasDataType D decl T → {con : Constructor decl.sorts decl.grades decl.levels decl.scope} →
    con ∈ T.constructors → {qs : List Quality} → {ps : List Grade} →
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps) →
    sig.fieldParams D con.name qs ps = some (con.params hqp.inst)
  | [], _, _, _, _, h, _, _, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, hc⟩, D, decl, T, ⟨he, hT, hD⟩, con, hcon, qs, ps, hqp => by
    unfold Signature.fieldParams
    rcases List.mem_cons.1 he with rfl | he'
    · have hg := Entry.fieldParams_of_mem (TypeDeclaration.dataTypes_nodup hn) hT (hc.1 T hT) hcon
        hqp
      rw [hD] at hg
      rw [List.findSome?_cons_of_isSome (by rw [hg]; rfl), hg]
    · have hDe : D ∉ e.names := fun hDe => hfresh _ he' D hDe (hD ▸ TypeDeclaration.name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.fieldParams_of_not_mem hDe]; rfl)]
      exact hd.fieldParams ⟨he', hT, hD⟩ hcon hqp

/-- The requirement of the recursion on an axis is below the coefficient of each field that the
recursor uses on this axis. -/
theorem Parameter.recursionAxis_le {ϱ π : Multiplicity} (hπ : π ≠ .zero) :
    {xs : List (Multiplicity × Multiplicity)} → (ϱ, π) ∈ xs → Parameter.recursionAxis xs ≤ ϱ * π
  | (ϱ', π') :: xs, h => by
    simp only [Parameter.recursionAxis]
    rcases List.mem_cons.1 h with h | h
    · cases h
      simp only [hπ, ↓reduceIte]
      exact (by decide : ∀ x z : Multiplicity, x ⊓ z ≤ x) _ _
    · have ih := Parameter.recursionAxis_le hπ h
      split
      · exact ih
      · exact (by decide : ∀ y z x : Multiplicity, z ≤ x → y ⊓ z ≤ x) _ _ _ ih

/-- The requirement of the recursion of a recursor that uses its term with the grade `c` is below,
at run time, the coefficient of each recursive field of each constructor of the block that the
recursor uses at run time. -/
theorem Parameter.recursion_run_le {c : Grade} {es : List (List Nat)} {fs : List (List Parameter)}
    {nested : (Grade → Multiplicity) → List (Multiplicity × Multiplicity)}
    {i l : Nat} {e : List Nat} {f : List Parameter} {p : Parameter} (he : es[i]? = some e)
    (hf : fs[i]? = some f) (hl : l ∈ e) (hp : f[l]? = some p) (hc : (c * p.usage).run ≠ .zero) :
    (Parameter.recursion c es fs nested).run ≤ p.requirement.run * (c * p.usage).run := by
  refine Parameter.recursionAxis_le hc (List.mem_append_left _
    (List.mem_map.2 ⟨(p.requirement, c * p.usage), ?_, rfl⟩))
  have hx : (fun l => ((f[l]?).map fun p => (p.requirement, c * p.usage)).getD
      (Grade.unrestrictedUnrestricted, Grade.linearLinear)) l = (p.requirement, c * p.usage) := by
    simp only [hp, Option.map_some, Option.getD_some]
  rw [← hx]
  refine List.mem_flatten.2 ⟨e.map fun l => ((f[l]?).map fun p => (p.requirement, c * p.usage)).getD
    (Grade.unrestrictedUnrestricted, Grade.linearLinear),
    List.mem_of_getElem? (i := i) ?_, List.mem_map_of_mem hl⟩
  rw [List.getElem?_zipWith, he, hf]

/-- An entry that does not introduce the name `D` gives the parameters of the fields of the cases of no
data type named `D`. -/
theorem Entry.caseFieldParams_of_not_mem {D : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.caseFieldParams D qs ps e = none :=
  fun h => Entry.lookup_of_not_mem h

/-- In a signature whose names are distinct, the parameters of the fields of the constructors of the
cases of the block of a data type are those of their telescopes at the instance. -/
theorem Signature.Distinct.caseFieldParams : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : DataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasDataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps) →
    sig.caseFieldParams D qs ps = some (decl.cases.map fun x =>
      x.2.2.params hqp.inst)
  | [], _, _, _, _, h, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hqp => by
    unfold Signature.caseFieldParams
    rcases List.mem_cons.1 he with rfl | he'
    · have hs : Entry.caseFieldParams D qs ps (.typeDeclaration decl) =
          some (decl.cases.map fun x => x.2.2.params hqp.inst) := by
        simp only [Entry.caseFieldParams,
          Entry.lookup_typeDeclaration (TypeDeclaration.name_mem_names hT), hqp, ↓reduceDIte,
          ← hD, List.find?_of_nodup_map (TypeDeclaration.dataTypes_nodup hn) hT, Option.map_some]
      rw [List.findSome?_cons_of_isSome (by rw [hs]; rfl), hs]
    · have hDe : D ∉ e.names := fun hDe => hfresh _ he' D hDe (hD ▸ TypeDeclaration.name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.caseFieldParams_of_not_mem hDe]; rfl)]
      exact hd.caseFieldParams ⟨he', hT, hD⟩ hqp

/-- An entry that does not introduce the name `D` gives the arguments of the destructors of no
codata type named `D`. -/
theorem Entry.destructorArguments_of_not_mem {D : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.destructorArguments D qs ps e = none :=
  fun h => Entry.lookup_of_not_mem h

/-- In a signature whose names are distinct, the arguments of the destructors of the cases of the
block of a codata type are the positions of their types, the parameters of their arguments, the
ownerships of their results and the ownerships that they require of the values that they observe at
the instance. -/
theorem Signature.Distinct.destructorArguments : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps) →
    sig.destructorArguments D qs ps = some (decl.codataCases.map fun x =>
      (x.1, ((x.2.1.body hqp.inst).arguments x.2.2).getD
        ⟨[], ⟨none, fun _ => none⟩, .unrestrictedUnrestricted⟩))
  | [], _, _, _, _, h, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hqp => by
    unfold Signature.destructorArguments
    rcases List.mem_cons.1 he with rfl | he'
    · have hs : Entry.destructorArguments D qs ps (.typeDeclaration decl) =
          some (decl.codataCases.map fun x =>
            (x.1, ((x.2.1.body hqp.inst).arguments x.2.2).getD
              ⟨[], ⟨none, fun _ => none⟩, .unrestrictedUnrestricted⟩)) := by
        simp only [Entry.destructorArguments,
          Entry.lookup_typeDeclaration (TypeDeclaration.codata_name_mem_names hT), hqp,
          ↓reduceDIte, ← hD, List.find?_of_nodup_map (TypeDeclaration.codataTypes_nodup hn) hT,
          Option.map_some]
      rw [List.findSome?_cons_of_isSome (by rw [hs]; rfl), hs]
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.destructorArguments_of_not_mem hDe]; rfl)]
      exact hd.destructorArguments ⟨he', hT, hD⟩ hqp

/-- The destructor at a position in destructors is named by them. -/
theorem Destructors.Pos.mem {k : Nat} {d : Name} {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → Destructors.Pos d p q ς ds Ξ Θ B ψ → d ∈ ns
  | _, _, _, _, _, _, _, .here => List.mem_cons_self
  | _, _, _, _, _, _, _, .there h => List.mem_cons_of_mem _ h.mem

/-- The destructor at a position in destructors is the name at the number of the position. -/
theorem Destructors.Pos.getElem?_index {k : Nat} {d : Name} {p q ς : Grade}
    {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hpos : Destructors.Pos d p q ς ds Ξ Θ B ψ) →
        ns[hpos.index]? = some d
  | _, _, _, _, _, _, _, .here => rfl
  | _, _, _, _, _, _, _, .there h => h.getElem?_index

/-- Destructors with distinct names give the destructor at a position the parameters of its
arguments, the ownership of its result and the ownership that it requires of the value that it
observes. -/
theorem Destructors.Pos.arguments {k : Nat} {d : Name} {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → ns.Nodup → Destructors.Pos d p q ς ds Ξ Θ B ψ →
        ds.arguments d = some ⟨ps, ψ, ς⟩
  | _, _, _, _, _, _, _, _, .here => by simp [Destructors.arguments]
  | _, d' :: _, _, _, _, _, _, hn, .there h => by
    have hne : d' ≠ d := fun he => (List.nodup_cons.1 hn).1 (he ▸ h.mem)
    simp only [Destructors.arguments, hne, ↓reduceIte]
    exact h.arguments (List.nodup_cons.1 hn).2

/-- A type declaration gives the parameters of the arguments of a destructor of one of its codata types,
whose types and destructors have distinct names, at the instance. -/
theorem Entry.argumentParams_of_mem {decl : TypeDeclaration}
    (hn : (decl.codataTypes.map (·.name)).Nodup)
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.codataTypes)
    (hc : T.destructors.Nodup) {qs : List Quality} {ps : List Grade}
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    {d : Name} {p q ς : Grade} {ps' : List Parameter} {Ξ : Scope}
    {Θ : Telescope decl.levels Ξ ps'} {B : Term decl.levels (Ξ.extend ps'.length)}
    {ψ : ResultOwnership Grade ps'.length} (hd : (T.body hqp.inst).Pos d p q ς Ξ Θ B ψ) :
    Entry.argumentParams T.name d qs ps (.typeDeclaration decl) = some ⟨ps', ψ, ς⟩ := by
  simp only [Entry.argumentParams,
    Entry.lookup_typeDeclaration (TypeDeclaration.codata_name_mem_names hT)]
  split
  · try split
    all_goals first
      | contradiction
      | rw [List.find?_of_nodup_map hn hT, Option.bind_some, hd.arguments hc]
  · contradiction

/-- An entry that does not introduce the name `D` gives the parameters of the arguments of no destructor
of `D`. -/
theorem Entry.argumentParams_of_not_mem {D d : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.argumentParams D d qs ps e = none :=
  fun h => Entry.lookup_of_not_mem h

/-- In a signature whose names are distinct, the parameters of the arguments of a destructor of a
declared type, the ownership of its result and the ownership that it requires of the value that it
observes are those of its declaration at the instance. -/
theorem Signature.Distinct.argumentParams : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps) → {d : Name} → {p q ς : Grade} →
    {ps' : List Parameter} → {Ξ : Scope} → {Θ : Telescope decl.levels Ξ ps'} →
    {B : Term decl.levels (Ξ.extend ps'.length)} → {ψ : ResultOwnership Grade ps'.length} →
    (T.body hqp.inst).Pos d p q ς Ξ Θ B ψ →
    sig.argumentParams D d qs ps = some ⟨ps', ψ, ς⟩
  | [], _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, hc⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hqp, _, _, _, _, _, _, _,
      _, _, hpos => by
    unfold Signature.argumentParams
    rcases List.mem_cons.1 he with rfl | he'
    · have hg := Entry.argumentParams_of_mem (TypeDeclaration.codataTypes_nodup hn) hT
        (hc.2 T hT) hqp hpos
      rw [hD] at hg
      rw [List.findSome?_cons_of_isSome (by rw [hg]; rfl), hg]
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.argumentParams_of_not_mem hDe]; rfl)]
      exact hd.argumentParams ⟨he', hT, hD⟩ hqp hpos

/-- Destructors with distinct names give the destructor at a position its grade. -/
theorem Destructors.Pos.grade {k : Nat} {d : Name} {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → ns.Nodup → Destructors.Pos d p q ς ds Ξ Θ B ψ →
        ds.grade d = some p
  | _, _, _, _, _, _, _, _, .here => by simp [Destructors.grade]
  | _, d' :: _, _, _, _, _, _, hn, .there h => by
    have hne : d' ≠ d := fun he => (List.nodup_cons.1 hn).1 (he ▸ h.mem)
    simp only [Destructors.grade, hne, ↓reduceIte]
    exact h.grade (List.nodup_cons.1 hn).2

/-- Destructors with distinct names give the destructor at a position one grade and one telescope
of parameters. -/
theorem Destructors.Pos.params_unique {k : Nat} {d : Name} {p₁ q₁ ς₁ p₂ q₂ ς₂ : Grade}
    {ps₁ ps₂ : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ₁ Ξ₂ : Scope} →
      {Θ₁ : Telescope k Ξ₁ ps₁} → {B₁ : Term k (Ξ₁.extend ps₁.length)} →
      {ψ₁ : ResultOwnership Grade ps₁.length} → {Θ₂ : Telescope k Ξ₂ ps₂} →
      {B₂ : Term k (Ξ₂.extend ps₂.length)} → {ψ₂ : ResultOwnership Grade ps₂.length} → ns.Nodup →
      Destructors.Pos d p₁ q₁ ς₁ ds Ξ₁ Θ₁ B₁ ψ₁ → Destructors.Pos d p₂ q₂ ς₂ ds Ξ₂ Θ₂ B₂ ψ₂ →
        p₁ = p₂ ∧ ps₁ = ps₂
  | _, _, _, _, _, _, _, _, _, _, _, hn, .here, h₂ => by
    cases h₂ with
    | here => exact ⟨rfl, rfl⟩
    | there h => exact absurd h.mem (List.nodup_cons.1 hn).1
  | _, _, _, _, _, _, _, _, _, _, _, hn, .there h₁, h₂ => by
    cases h₂ with
    | here => exact absurd h₁.mem (List.nodup_cons.1 hn).1
    | there h₂ => exact h₁.params_unique (List.nodup_cons.1 hn).2 h₂

/-- What holds at a position of a destructor in destructors with distinct names holds at each of
its positions there, which is this one. -/
theorem Destructors.Pos.forall_of {k : Nat} {d : Name} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → ns.Nodup →
      {motive : ∀ {p q ς : Grade} {ps : List Parameter} {Ξ : Scope} {Θ : Telescope k Ξ ps}
        {B : Term k (Ξ.extend ps.length)} {ψ : ResultOwnership Grade ps.length},
        Destructors.Pos d p q ς ds Ξ Θ B ψ → Prop} →
      ∀ {p₁ q₁ ς₁ : Grade} {ps₁ : List Parameter} {Ξ₁ : Scope} {Θ₁ : Telescope k Ξ₁ ps₁}
        {B₁ : Term k (Ξ₁.extend ps₁.length)} {ψ₁ : ResultOwnership Grade ps₁.length}
        (h₁ : Destructors.Pos d p₁ q₁ ς₁ ds Ξ₁ Θ₁ B₁ ψ₁), motive h₁ →
      ∀ {p₂ q₂ ς₂ : Grade} {ps₂ : List Parameter} {Ξ₂ : Scope} {Θ₂ : Telescope k Ξ₂ ps₂}
        {B₂ : Term k (Ξ₂.extend ps₂.length)} {ψ₂ : ResultOwnership Grade ps₂.length}
        (h₂ : Destructors.Pos d p₂ q₂ ς₂ ds Ξ₂ Θ₂ B₂ ψ₂), motive h₂
  | _, _, _, hn, _, _, _, _, _, _, _, _, _, .here, hm, _, _, _, _, _, _, _, _, h₂ => by
    cases h₂ with
    | here => exact hm
    | there h => exact absurd h.mem (List.nodup_cons.1 hn).1
  | _, _, _, hn, motive, _, _, _, _, _, _, _, _, .there h₁, hm, _, _, _, _, _, _, _, _, h₂ => by
    cases h₂ with
    | here => exact absurd h₁.mem (List.nodup_cons.1 hn).1
    | there h₂ =>
      exact Destructors.Pos.forall_of (List.nodup_cons.1 hn).2
        (motive := fun h => motive (.there h)) h₁ hm h₂

/-- The destructor at a position of destructors whose names are distinct has the result there. -/
theorem Destructors.Pos.resultName {k : Nat} {d : Name} {p q ς : Grade} {ps : List Parameter}
    (names : List Name) :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → ns.Nodup → Destructors.Pos d p q ς ds Ξ Θ B ψ →
        ds.resultName names d = B.blockName names
  | _, _, _, _, _, _, _, _, .here => by simp [Destructors.resultName]
  | _, d' :: _, _, _, _, _, _, hn, .there h => by
    have hne : d' ≠ d := fun he => (List.nodup_cons.1 hn).1 (he ▸ h.mem)
    simp only [Destructors.resultName, hne, ↓reduceIte]
    exact h.resultName names (List.nodup_cons.1 hn).2

/-- The destructor at a position of destructors whose names are distinct has the ownership of its
result there. -/
theorem Destructors.Pos.resultConstant {k : Nat} {d : Name} {p q ς : Grade} {ps : List Parameter} :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → ns.Nodup → Destructors.Pos d p q ς ds Ξ Θ B ψ →
        ds.resultConstant d = ψ.constant
  | _, _, _, _, _, _, _, _, .here => by simp [Destructors.resultConstant]
  | _, d' :: _, _, _, _, _, _, hn, .there h => by
    have hne : d' ≠ d := fun he => (List.nodup_cons.1 hn).1 (he ▸ h.mem)
    simp only [Destructors.resultConstant, hne, ↓reduceIte]
    exact h.resultConstant (List.nodup_cons.1 hn).2

/-- The destructor at a position is recursive, of the type of the block that its result names, at
the number of the position. -/
theorem Destructors.Pos.recursionAt_index {k : Nat} {d : Name} {p q ς : Grade} {ps : List Parameter}
    (names : List Name) :
    {Γ : Scope} → {ns : List Name} → {ds : Destructors k Γ ns} → {Ξ : Scope} →
      {Θ : Telescope k Ξ ps} → {B : Term k (Ξ.extend ps.length)} →
      {ψ : ResultOwnership Grade ps.length} → (hpos : Destructors.Pos d p q ς ds Ξ Θ B ψ) →
        ds.recursionAt names hpos.index = B.blockName names
  | _, _, _, _, _, _, _, .here => by
    simp [Destructors.Pos.index, Destructors.recursionAt, Destructors.recursion]
  | _, _, _, _, _, _, _, .there h => by
    simp only [Destructors.Pos.index, Destructors.recursionAt, Destructors.recursion,
      List.getElem?_cons_succ]
    exact h.recursionAt_index names

/-- A destructor named by destructors has a position in them. -/
theorem Destructors.exists_pos {k : Nat} {d : Name} :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k Γ ns) → d ∈ ns →
      ∃ (p q ς : Grade) (ps : List Parameter) (Ξ : Scope) (Θ : Telescope k Ξ ps)
        (B : Term k (Ξ.extend ps.length)) (ψ : ResultOwnership Grade ps.length),
        Nonempty (Destructors.Pos d p q ς ds Ξ Θ B ψ)
  | _, _, .nil, h => nomatch h
  | _, d' :: _, .cons p q ς Θ B ψ ds, h => by
    by_cases he : d' = d
    · subst he
      exact ⟨p, q, ς, _, _, Θ, B, ψ, ⟨.here⟩⟩
    · have h' : d ∈ _ := (List.mem_cons.1 h).resolve_left fun h'' => he h''.symm
      obtain ⟨p', q', ς', ps', Ξ, Θ', B', ψ', ⟨hpos⟩⟩ := Destructors.exists_pos ds h'
      exact ⟨p', q', ς', ps', Ξ, Θ', B', ψ', ⟨.there hpos⟩⟩

/-- Destructors with distinct names, at their names, all have a grade. -/
theorem Destructors.isSome_grade {k : Nat} :
    {Γ : Scope} → {ns : List Name} → (ds : Destructors k Γ ns) → ns.Nodup → ∀ d ∈ ns,
      ∃ p, ds.grade d = some p := fun ds hn d hd => by
  obtain ⟨p, q, ς, ps, Ξ, Θ, B, ψ, ⟨hpos⟩⟩ := Destructors.exists_pos ds hd
  exact ⟨p, hpos.grade hn⟩

/-- A type declaration gives the grades of the destructors of the cases of its block, whose types
and destructors have distinct names, at the instance: the grade of the destructor of each case. -/
theorem Entry.destructorGrades_of_mem {decl : TypeDeclaration}
    (hn : (decl.codataTypes.map (·.name)).Nodup)
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope} (hT : T ∈ decl.codataTypes)
    (hc : ∀ T ∈ decl.codataTypes, T.destructors.Nodup) {qs : List Quality} {ps : List Grade}
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps) :
    ∃ gs, Entry.destructorGrades T.name qs ps (.typeDeclaration decl) = some gs ∧
      ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope) (d : Name),
        decl.codataCases[i]? = some (j, T', d) → ∀ p, (T'.body hqp.inst).grade d = some p →
          gs[i]? = some p := by
  have hall : ∀ c ∈ decl.codataCases, ∃ p, (c.2.1.body hqp.inst).grade c.2.2 = some p :=
    fun c hcm => by
      obtain ⟨hT', hd⟩ := TypeDeclaration.mem_casesFrom hcm
      exact Destructors.isSome_grade _ (hc _ hT') _ hd
  obtain ⟨gs, hgs⟩ := List.exists_mapM_eq_some hall
  refine ⟨gs, ?_, fun i j T' d hi p hpg => ?_⟩
  · simp only [Entry.destructorGrades,
      Entry.lookup_typeDeclaration (TypeDeclaration.codata_name_mem_names hT)]
    split
    · try split
      all_goals first
        | contradiction
        | rw [List.find?_of_nodup_map hn hT, Option.bind_some, hgs]
    · contradiction
  · obtain ⟨b, hb, hgi⟩ := List.getElem?_of_mapM hgs hi
    rw [hpg] at hb
    cases hb
    exact hgi

/-- An entry that does not introduce the name `D` gives the grades of the destructors of no block
of `D`. -/
theorem Entry.destructorGrades_of_not_mem {D : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.destructorGrades D qs ps e = none :=
  fun h => Entry.lookup_of_not_mem h

/-- In a signature whose names are distinct, the grades of the destructors of the cases of the
block of a codata type are those of its declaration, at the instance. -/
theorem Signature.Distinct.destructorGrades : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps) →
    ∃ gs, sig.destructorGrades D qs ps = some gs ∧
      ∀ (i j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope) (d : Name),
        decl.codataCases[i]? = some (j, T', d) → ∀ p, (T'.body hqp.inst).grade d = some p →
          gs[i]? = some p
  | [], _, _, _, _, h, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, hc⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hqp => by
    unfold Signature.destructorGrades
    rcases List.mem_cons.1 he with rfl | he'
    · obtain ⟨gs, hg, hgs⟩ := Entry.destructorGrades_of_mem (TypeDeclaration.codataTypes_nodup hn)
        hT (hc.2) hqp
      rw [hD] at hg
      exact ⟨gs, by rw [List.findSome?_cons_of_isSome (by rw [hg]; rfl), hg], hgs⟩
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.destructorGrades_of_not_mem hDe]; rfl)]
      exact hd.destructorGrades ⟨he', hT, hD⟩ hqp

/-- An entry that does not introduce the name `D` gives the types resumed by the destructors of no
block of `D`. -/
theorem Entry.resumedTypes_of_not_mem {D : Name} {qs : List Quality} {ps : List Grade} :
    {e : Entry} → D ∉ e.names → Entry.resumedTypes D qs ps e = none :=
  fun h => Entry.lookup_of_not_mem h

/-- In a signature whose names are distinct, the types resumed by the destructors of the cases of the
block of a codata type are the positions of the types that their results name, at the instance. -/
theorem Signature.Distinct.resumedTypes : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → {qs : List Quality} → {ps : List Grade} →
    (hqp : Instance.AsMany decl.sorts decl.grades qs ps) →
    sig.resumedTypes D qs ps = some (decl.codataCases.map fun x =>
      ((x.2.1.body hqp.inst).resultName decl.names x.2.2).bind decl.names.idxOf?)
  | [], _, _, _, _, h, _, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩, qs, ps, hqp => by
    unfold Signature.resumedTypes
    rcases List.mem_cons.1 he with rfl | he'
    · have hg : Entry.resumedTypes D qs ps (.typeDeclaration decl) = some (decl.codataCases.map
          fun x => ((x.2.1.body hqp.inst).resultName decl.names x.2.2).bind
            decl.names.idxOf?) := by
        simp only [Entry.resumedTypes,
          Entry.lookup_typeDeclaration (TypeDeclaration.codata_name_mem_names hT), hqp,
          ↓reduceDIte, ← hD, List.find?_of_nodup_map (TypeDeclaration.codataTypes_nodup hn) hT,
          Option.map_some]
      rw [List.findSome?_cons_of_isSome (by rw [hg]; rfl), hg]
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      rw [List.findSome?_cons_of_isNone (by rw [Entry.resumedTypes_of_not_mem hDe]; rfl)]
      exact hd.resumedTypes ⟨he', hT, hD⟩ hqp

/-- The case `i` of the branches `vs` of a corecursor on a codata type of a block, whose states are
those of the types of the block and whose branches bind the arguments of their destructors, is a
destructor `d` of the type `T'` at a position `j`, of state `S'`, with its branch `g`, and what the
erasure of the corecursor reads at this case: the grade of the destructor, its arguments and the
position of the type of its result in the block. -/
theorem Signature.Distinct.corecCase {sig : Signature} (hd : sig.Distinct) {decl : TypeDeclaration}
    {D : Name} {T : CodataType decl.sorts decl.grades decl.levels decl.scope}
    (h : sig.HasCodataType D decl T)
    {qs : List Quality} {ps : List Grade} (hqp : Instance.AsMany decl.sorts decl.grades qs ps)
    {k : Nat} {Γ : Scope}
    {Ss : States k Γ}
    {vs : DestructorBranches k Γ}
    (hSs : ∀ j T', decl.codataTypes[j]? = some T' → ∃ ps'' S', Ss.get j = some ⟨0, ps'', S'⟩)
    (hgl : vs.length = decl.codataCases.length)
    (hgs : ∀ i j T' d (ps'' : List Parameter) (S' : Telescope k Γ ps''),
      decl.codataCases[i]? = some (j, T', d) → Ss.get j = some ⟨0, ps'', S'⟩ →
      ∀ (p q ς : Grade) (ps₁ : List Parameter) (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁)
        (B : Term decl.levels (Ξ.extend ps₁.length)) (ψ : ResultOwnership Grade ps₁.length),
      (T'.body hqp.inst).Pos d p q ς Ξ Θ B ψ →
      ∃ g, vs.get i = some ⟨0, ps''.length, ps₁.length, g⟩)
    {i : Nat} (hi : i < vs.length) :
    ∃ (j : Nat) (T' : CodataType decl.sorts decl.grades decl.levels decl.scope) (d : Name)
      (ps'' : List Parameter) (S' : Telescope k Γ ps'') (p q ς : Grade) (ps₁ : List Parameter)
      (Ξ : Scope) (Θ : Telescope decl.levels Ξ ps₁) (B : Term decl.levels (Ξ.extend ps₁.length))
      (ψ : ResultOwnership Grade ps₁.length) (g : Term k ((Γ.extend ps''.length).extend ps₁.length)),
      decl.codataCases[i]? = some (j, T', d) ∧ Ss.get j = some ⟨0, ps'', S'⟩ ∧
      Nonempty ((T'.body hqp.inst).Pos d p q ς Ξ Θ B ψ) ∧
      vs.get i = some ⟨0, ps''.length, ps₁.length, g⟩ ∧
      ((sig.destructorGrades D qs ps).getD [])[i]? = some p ∧
      ((sig.destructorArguments D qs ps).getD [])[i]? = some (j, ⟨ps₁, ψ, ς⟩) ∧
      ((sig.resumedTypes D qs ps).getD [])[i]? =
        some ((B.blockName decl.names).bind decl.names.idxOf?) := by
  obtain ⟨grs, hgrs, hgri⟩ := hd.destructorGrades h hqp
  obtain ⟨⟨j, T', d⟩, hc⟩ : ∃ c, decl.codataCases[i]? = some c :=
    ⟨_, List.getElem?_eq_getElem (hgl ▸ hi)⟩
  have hcm := List.mem_of_getElem? hc
  obtain ⟨hT', hdm⟩ := TypeDeclaration.mem_casesFrom hcm
  obtain ⟨ps'', S', hSj⟩ := hSs j T' (TypeDeclaration.codataTypes_getElem?_of_codataCases hcm)
  obtain ⟨p, q, ς, ps₁, Ξ, Θ, B, ψ, ⟨hpos⟩⟩ := Destructors.exists_pos (T'.body _) hdm
  have hnd := hd.destructors_nodup ⟨h.1, hT', rfl⟩
  obtain ⟨g, hg⟩ := hgs i j T' d ps'' S' hc hSj p q ς ps₁ Ξ Θ B ψ hpos
  refine ⟨j, T', d, ps'', S', p, q, ς, ps₁, Ξ, Θ, B, ψ, g, hc, hSj, ⟨hpos⟩, hg, ?_,
    ?_, ?_⟩
  · rw [hgrs]
    exact hgri i j T' d hc p (hpos.grade hnd)
  · simp [hd.destructorArguments h hqp, hc, hpos.arguments hnd]
  · simp [hd.resumedTypes h hqp, hc, hpos.resultName decl.names hnd]

/-- In a signature whose names are distinct, the position of a codata type is its position in the
block of its declaration. -/
theorem Signature.Distinct.position : {sig : Signature} → sig.Distinct → {D : Name} →
    {decl : TypeDeclaration} → {T : CodataType decl.sorts decl.grades decl.levels decl.scope} →
    sig.HasCodataType D decl T → {h' : Nat} → decl.codataTypes[h']? = some T →
    sig.position D = some h'
  | [], _, _, _, _, h, _, _ => nomatch h.1
  | e :: sig, ⟨hd, hn, hfresh, _⟩, D, decl, T, ⟨he, hT, hD⟩, h', hh => by
    unfold Signature.position
    rcases List.mem_cons.1 he with rfl | he'
    · have hc : decl.names = decl.codataTypes.map (·.name) := by
        rw [decl.names_eq]
        rcases decl.dataTypes_codataTypes with h | h
        · rw [h]; rfl
        · rw [h] at hT; exact nomatch hT
      have hp : Entry.position D (.typeDeclaration decl) = some h' := by
        simp only [Entry.position, ← hD,
          Entry.lookup_typeDeclaration (TypeDeclaration.codata_name_mem_names hT)]
        simp only [hc]
        exact List.idxOf?_map_of_nodup (TypeDeclaration.codataTypes_nodup hn) hh
      rw [List.findSome?_cons_of_isSome (by rw [hp]; rfl), hp]
    · have hDe : D ∉ e.names := fun hDe =>
        hfresh _ he' D hDe (hD ▸ TypeDeclaration.codata_name_mem_names hT)
      have hp : Entry.position D e = none := Entry.lookup_of_not_mem hDe
      rw [List.findSome?_cons_of_isNone (by rw [hp]; rfl)]
      exact hd.position ⟨he', hT, hD⟩ hh

/-- The destructors of the codata types of a signature, at an instance that the constraint admits,
of a block of propositions, have grades without use at run time. -/
def Signature.ErasesPropDestructors (sig : Signature) : Prop :=
  ∀ {decl : TypeDeclaration} {D : Name}
    {T : CodataType decl.sorts decl.grades decl.levels decl.scope},
    sig.HasCodataType D decl T → ∀ {qs : List Quality} {ps : List Grade}
      (hqp : Instance.AsMany decl.sorts decl.grades qs ps),
      decl.constraint hqp.inst →
      (decl.sort hqp.inst).quality = .prop →
      ∀ {d : Name} {p q ς : Grade} {ps₁ : List Parameter} {Ξ : Scope}
        {Θ : Telescope decl.levels Ξ ps₁} {B : Term decl.levels (Ξ.extend ps₁.length)}
        {ψ : ResultOwnership Grade ps₁.length},
        (T.body hqp.inst).Pos d p q ς Ξ Θ B ψ → p ∈ Mode.oneOne.erased

end Sic.Core
