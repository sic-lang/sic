module

public import Sic.Core.Nesting

/-!
# Relations Between Nestings

Nestings with the same positions, whose objects are related: the properties of the graph of the
nestings of annex 18 of RFC 36 compare the relations that the graph gives at related positions, of
two nestings for its growth and its symmetry, and of three for its transitivity.
The relation of three nestings is the only one defined, and those of two nestings and of one are
read from it, so that each lemma is proved once: the nesting of a type, the nestings of the
variables under new variables or at the arguments of an instance, and the nestings that functions
give from one nesting, keep the relation, and the positions of the nestings of the fields of a
block hold types of the block.

ADE have no declared types, and no nesting.
-/

@[expose] public section

namespace Sic.Core

variable {k : Nat} {α β γ : Type}

/-! ## Related Nestings -/

mutual

-- ADE: none.
/-- Three nestings have the same positions, whose objects `r` relates. -/
inductive Nest.Rel₃ (r : α → β → γ → Prop) : Nest α → Nest β → Nest γ → Prop where
  /-- No position. -/
  | plain : Nest.Rel₃ r .plain .plain .plain
  /-- A position, whose objects are related. -/
  | direct {a : α} {b : β} {c : γ} (h : r a b c) : Nest.Rel₃ r (.direct a) (.direct b) (.direct c)
  /-- An instance, the nestings of whose arguments are related. -/
  | inst {ns : List (Nest α)} {ms : List (Nest β)} {os : List (Nest γ)}
      (h : Nest.ListRel₃ r ns ms os) : Nest.Rel₃ r (.inst ns) (.inst ms) (.inst os)

-- ADE: none.
/-- The nestings of the arguments of three instances are as many, and related one by one. -/
inductive Nest.ListRel₃ (r : α → β → γ → Prop) :
    List (Nest α) → List (Nest β) → List (Nest γ) → Prop where
  /-- No argument. -/
  | nil : Nest.ListRel₃ r [] [] []
  /-- A first argument, whose nestings are related, and the others. -/
  | cons {n : Nest α} {m : Nest β} {o : Nest γ} {ns : List (Nest α)} {ms : List (Nest β)}
      {os : List (Nest γ)} (h : Nest.Rel₃ r n m o) (hs : Nest.ListRel₃ r ns ms os) :
      Nest.ListRel₃ r (n :: ns) (m :: ms) (o :: os)

end

/-- Two nestings have the same positions, whose objects `r` relates. -/
abbrev Nest.Rel (r : α → β → Prop) (n : Nest α) (m : Nest β) : Prop :=
  Nest.Rel₃ (fun a b _ => r a b) n m m

/-- The objects at the positions of a nesting all satisfy `p`. -/
abbrev Nest.All (p : α → Prop) (n : Nest α) : Prop :=
  Nest.Rel₃ (fun a _ _ => p a) n n n

/-- The nestings of the variables of a scope are related, variable by variable. -/
abbrev Nesting.Rel₃ {Γ : Scope} (r : α → β → γ → Prop) (ν₁ : Nesting α Γ) (ν₂ : Nesting β Γ)
    (ν₃ : Nesting γ Γ) : Prop :=
  ∀ (e : Scope.Entry) (x : Var Γ e), Nest.Rel₃ r (ν₁ x) (ν₂ x) (ν₃ x)

/-- The nestings of the variables of a scope are related, variable by variable. -/
abbrev Nesting.Rel {Γ : Scope} (r : α → β → Prop) (ν₁ : Nesting α Γ) (ν₂ : Nesting β Γ) : Prop :=
  Nesting.Rel₃ (fun a b _ => r a b) ν₁ ν₂ ν₂

/-- The objects at the positions of the nestings of the variables of a scope all satisfy `p`. -/
abbrev Nesting.All {Γ : Scope} (p : α → Prop) (ν : Nesting α Γ) : Prop :=
  Nesting.Rel₃ (fun a _ _ => p a) ν ν ν

/-! ## Related Objects -/

mutual

/-- Related nestings are related by every relation that relates the objects that theirs does. -/
theorem Nest.Rel₃.imp {r r' : α → β → γ → Prop} (hr : ∀ a b c, r a b c → r' a b c)
    {n : Nest α} {m : Nest β} {o : Nest γ} : Nest.Rel₃ r n m o → Nest.Rel₃ r' n m o
  | .plain => .plain
  | .direct h => .direct (hr _ _ _ h)
  | .inst h => .inst (Nest.ListRel₃.imp hr h)

/-- Related nestings of arguments are related by every relation that relates the objects that
theirs does. -/
theorem Nest.ListRel₃.imp {r r' : α → β → γ → Prop} (hr : ∀ a b c, r a b c → r' a b c)
    {ns : List (Nest α)} {ms : List (Nest β)} {os : List (Nest γ)} :
    Nest.ListRel₃ r ns ms os → Nest.ListRel₃ r' ns ms os
  | .nil => .nil
  | .cons h hs => .cons (Nest.Rel₃.imp hr h) (Nest.ListRel₃.imp hr hs)

end

mutual

/-- The first and the last of three related nestings are related, by a relation that relates the
objects that theirs does. -/
theorem Nest.Rel₃.outer {r : α → β → γ → Prop} {r' : α → γ → Prop}
    (hr : ∀ a b c, r a b c → r' a c) {n : Nest α} {m : Nest β} {o : Nest γ} :
    Nest.Rel₃ r n m o → Nest.Rel r' n o
  | .plain => .plain
  | .direct h => .direct (hr _ _ _ h)
  | .inst h => .inst (Nest.ListRel₃.outer hr h)

/-- The first and the last of three related nestings of arguments are related, by a relation that
relates the objects that theirs does. -/
theorem Nest.ListRel₃.outer {r : α → β → γ → Prop} {r' : α → γ → Prop}
    (hr : ∀ a b c, r a b c → r' a c) {ns : List (Nest α)} {ms : List (Nest β)}
    {os : List (Nest γ)} :
    Nest.ListRel₃ r ns ms os → Nest.ListRel₃ (fun a c _ => r' a c) ns os os
  | .nil => .nil
  | .cons h hs => .cons (Nest.Rel₃.outer hr h) (Nest.ListRel₃.outer hr hs)

end

mutual

/-- A nesting is related to itself, by a relation that relates each object to itself. -/
theorem Nest.rel₃_refl {r : α → α → α → Prop} (hr : ∀ a, r a a a) :
    (n : Nest α) → Nest.Rel₃ r n n n
  | .plain => .plain
  | .direct a => .direct (hr a)
  | .inst ns => .inst (Nest.listRel₃_refl hr ns)

/-- The nestings of arguments are related to themselves, by a relation that relates each object to
itself. -/
theorem Nest.listRel₃_refl {r : α → α → α → Prop} (hr : ∀ a, r a a a) :
    (ns : List (Nest α)) → Nest.ListRel₃ r ns ns ns
  | [] => .nil
  | n :: ns => .cons (Nest.rel₃_refl hr n) (Nest.listRel₃_refl hr ns)

end

mutual

/-- A nesting whose objects all satisfy `p` is related to itself, by a relation that relates to
itself each object that satisfies `p`. -/
theorem Nest.All.rel₃ {p : α → Prop} {r : α → α → α → Prop} (hr : ∀ a, p a → r a a a) :
    {n : Nest α} → Nest.All p n → Nest.Rel₃ r n n n
  | _, .plain => .plain
  | _, .direct h => .direct (hr _ h)
  | _, .inst h => .inst (Nest.ListRel₃.diagonal hr h)

/-- The nestings of arguments whose objects all satisfy `p` are related to themselves, by a relation
that relates to itself each object that satisfies `p`. -/
theorem Nest.ListRel₃.diagonal {p : α → Prop} {r : α → α → α → Prop} (hr : ∀ a, p a → r a a a) :
    {ns : List (Nest α)} → Nest.ListRel₃ (fun a _ _ => p a) ns ns ns → Nest.ListRel₃ r ns ns ns
  | _, .nil => .nil
  | _, .cons h hs => .cons (Nest.All.rel₃ hr h) (Nest.ListRel₃.diagonal hr hs)

end

/-! ## Related Positions -/

/-- Related nestings have a position together. -/
theorem Nest.Rel₃.isPlain {r : α → β → γ → Prop} {n : Nest α} {m : Nest β} {o : Nest γ}
    (h : Nest.Rel₃ r n m o) : m.isPlain = n.isPlain ∧ o.isPlain = n.isPlain := by
  cases h <;> exact ⟨rfl, rfl⟩

/-- A nesting has no position when a nesting related to it has none. -/
theorem Nest.Rel₃.eq_plain {r : α → β → γ → Prop} {n : Nest α} {m : Nest β} {o : Nest γ}
    (h : Nest.Rel₃ r n m o) : (m = .plain ↔ n = .plain) ∧ (o = .plain ↔ n = .plain) := by
  cases h <;> simp

/-- Related nestings of arguments have a position together. -/
theorem Nest.ListRel₃.all_isPlain {r : α → β → γ → Prop} {ns : List (Nest α)}
    {ms : List (Nest β)} {os : List (Nest γ)} :
    Nest.ListRel₃ r ns ms os →
      ms.all Nest.isPlain = ns.all Nest.isPlain ∧ os.all Nest.isPlain = ns.all Nest.isPlain
  | .nil => ⟨rfl, rfl⟩
  | .cons h hs => by
    simp only [List.all_cons, h.isPlain.1, h.isPlain.2, hs.all_isPlain.1, hs.all_isPlain.2,
      and_self]

/-- The nestings of instances are related when those of their arguments are. -/
theorem Nest.ofArgs_rel₃ {r : α → β → γ → Prop} {ns : List (Nest α)} {ms : List (Nest β)}
    {os : List (Nest γ)} (h : Nest.ListRel₃ r ns ms os) :
    Nest.Rel₃ r (Nest.ofArgs ns) (Nest.ofArgs ms) (Nest.ofArgs os) := by
  unfold Nest.ofArgs
  rw [h.all_isPlain.1, h.all_isPlain.2]
  split
  · exact .plain
  · exact .inst h

mutual

/-- The nestings that three functions give from a nesting whose objects all satisfy `p` are
related, when what the functions give for an object that satisfies `p` is. -/
theorem Nest.All.map_rel₃ {δ : Type} {p : δ → Prop} {r : α → β → γ → Prop} {f : δ → α}
    {g : δ → β} {h : δ → γ} (hr : ∀ x, p x → r (f x) (g x) (h x)) :
    {n : Nest δ} → Nest.All p n → Nest.Rel₃ r (n.map f) (n.map g) (n.map h)
  | _, .plain => .plain
  | _, .direct hx => .direct (hr _ hx)
  | _, .inst hs => .inst (Nest.ListRel₃.mapList hr hs)

/-- The nestings of arguments that three functions give from nestings whose objects all satisfy
`p` are related, when what the functions give for an object that satisfies `p` is. -/
theorem Nest.ListRel₃.mapList {δ : Type} {p : δ → Prop} {r : α → β → γ → Prop} {f : δ → α}
    {g : δ → β} {h : δ → γ} (hr : ∀ x, p x → r (f x) (g x) (h x)) :
    {ns : List (Nest δ)} → Nest.ListRel₃ (fun a _ _ => p a) ns ns ns →
      Nest.ListRel₃ r (Nest.mapList f ns) (Nest.mapList g ns) (Nest.mapList h ns)
  | _, .nil => .nil
  | _, .cons hn hs => .cons (Nest.All.map_rel₃ hr hn) (Nest.ListRel₃.mapList hr hs)

end

/-- The nestings that three functions give from a nesting are related, when what the functions give
for each object is. -/
theorem Nest.map_rel₃ {δ : Type} {r : α → β → γ → Prop} {f : δ → α} {g : δ → β} {h : δ → γ}
    (hr : ∀ x, r (f x) (g x) (h x)) (n : Nest δ) :
    Nest.Rel₃ r (n.map f) (n.map g) (n.map h) :=
  Nest.All.map_rel₃ (p := fun _ => True) (fun x _ => hr x) (Nest.rel₃_refl (fun _ => trivial) n)

/-- A nesting has a position when the nesting that a function gives from it has one. -/
theorem Nest.map_eq_plain {f : α → β} {n : Nest α} : n.map f = .plain ↔ n = .plain := by
  cases n <;> simp [Nest.map]

/-- A nesting is that of an instance when the nesting that a function gives from it is. -/
theorem Nest.map_eq_inst {f : α → β} {n : Nest α} {ms : List (Nest β)} (h : n.map f = .inst ms) :
    ∃ ns, n = .inst ns := by
  cases n with
  | plain => exact nomatch h
  | direct _ => exact nomatch h
  | inst ns => exact ⟨ns, rfl⟩

/-- The nestings of the variables stay related under a new entry. -/
theorem Nesting.lift_rel₃ {Γ : Scope} {e₀ : Scope.Entry} {r : α → β → γ → Prop}
    {ν₁ : Nesting α Γ} {ν₂ : Nesting β Γ} {ν₃ : Nesting γ Γ} (h : Nesting.Rel₃ r @ν₁ @ν₂ @ν₃) :
    Nesting.Rel₃ r (Nesting.lift (e := e₀) @ν₁) (Nesting.lift @ν₂) (Nesting.lift @ν₃) :=
  fun _ x =>
    match x with
    | .zero => .plain
    | .succ x => h _ x

/-- The nestings of the variables stay related under new variables. -/
theorem Nesting.liftN_rel₃ {r : α → β → γ → Prop} :
    {Γ : Scope} → (n : Nat) → {ν₁ : Nesting α Γ} → {ν₂ : Nesting β Γ} → {ν₃ : Nesting γ Γ} →
      Nesting.Rel₃ r @ν₁ @ν₂ @ν₃ →
      Nesting.Rel₃ r (Nesting.liftN n @ν₁) (Nesting.liftN n @ν₂) (Nesting.liftN n @ν₃)
  | _, 0, _, _, _, h => h
  | _, n + 1, _, _, _, h => Nesting.liftN_rel₃ n (Nesting.lift_rel₃ h)

/-- The nestings of the parameters of a declared type are related at instances whose arguments have
related nestings. -/
theorem Nesting.ofArgs_rel₃ {r : α → β → γ → Prop} :
    {Δ : Scope} → {ns : List (Nest α)} → {ms : List (Nest β)} → {os : List (Nest γ)} →
      Nest.ListRel₃ r ns ms os →
      Nesting.Rel₃ r (Nesting.ofArgs (Δ := Δ) ns) (Nesting.ofArgs ms) (Nesting.ofArgs os)
  | _, _, _, _, .nil, _, x => by cases x <;> exact .plain
  | _, _, _, _, .cons h _, _, .zero => h
  | _, _, _, _, .cons _ hs, _, .succ x => Nesting.ofArgs_rel₃ hs _ x

mutual

/-- The nestings of a type are related at related nestings of the variables, when no type is of a
block. -/
theorem Term.nest_rel₃ {r : α → β → γ → Prop} :
    {Γ : Scope} → {ν₁ : Nesting α Γ} → {ν₂ : Nesting β Γ} → {ν₃ : Nesting γ Γ} →
      Nesting.Rel₃ r @ν₁ @ν₂ @ν₃ → (B : Term k Γ) →
      Nest.Rel₃ r (B.nest (fun _ => none) @ν₁) (B.nest (fun _ => none) @ν₂)
        (B.nest (fun _ => none) @ν₃)
  | _, _, _, _, h, .var x _ => h _ x
  | _, _, _, _, h, .inst _ _ _ _ as => Nest.ofArgs_rel₃ (InstanceArgs.nest_rel₃ h as)
  | _, _, _, _, _, .sort _ => .plain
  | _, _, _, _, _, .const _ _ _ _ => .plain
  | _, _, _, _, _, .ctor _ _ _ _ _ _ _ => .plain
  | _, _, _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => .plain
  | _, _, _, _, _, .obs _ _ _ _ _ _ _ _ => .plain
  | _, _, _, _, _, .corec _ _ _ _ _ _ _ _ _ => .plain

/-- The nestings of the arguments of an instance are related at related nestings of the variables,
when no type is of a block. -/
theorem InstanceArgs.nest_rel₃ {r : α → β → γ → Prop} :
    {Γ Δ : Scope} → {ν₁ : Nesting α Γ} → {ν₂ : Nesting β Γ} → {ν₃ : Nesting γ Γ} →
      Nesting.Rel₃ r @ν₁ @ν₂ @ν₃ → (as : InstanceArgs k Γ Δ) →
      Nest.ListRel₃ r (as.nest (fun _ => none) @ν₁) (as.nest (fun _ => none) @ν₂)
        (as.nest (fun _ => none) @ν₃)
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, h, .snoc as B =>
    .cons (Term.nest_rel₃ (Nesting.liftN_rel₃ _ h) B) (InstanceArgs.nest_rel₃ h as)

end

/-! ## Objects of the Nesting of a Type -/

mutual

/-- The objects at the positions of the nesting of a type all satisfy `p`, when those that the
types of the block are given and those of the nestings of the variables do. -/
theorem Term.nest_all {p : α → Prop} {mark : Name → Option α}
    (hm : ∀ D a, mark D = some a → p a) :
    {Γ : Scope} → {ν : Nesting α Γ} → Nesting.All p @ν → (B : Term k Γ) →
      Nest.All p (B.nest mark @ν)
  | _, _, h, .var x _ => h _ x
  | _, _, h, .inst D _ _ _ as => by
    rw [Term.nest]
    split
    · rename_i a ha
      exact .direct (hm D a ha)
    · exact Nest.ofArgs_rel₃ (InstanceArgs.nest_all hm h as)
  | _, _, _, .sort _ => .plain
  | _, _, _, .const _ _ _ _ => .plain
  | _, _, _, .ctor _ _ _ _ _ _ _ => .plain
  | _, _, _, .recursor _ _ _ _ _ _ _ _ _ _ _ _ => .plain
  | _, _, _, .obs _ _ _ _ _ _ _ _ => .plain
  | _, _, _, .corec _ _ _ _ _ _ _ _ _ => .plain

/-- The objects at the positions of the nestings of the arguments of an instance all satisfy `p`,
when those that the types of the block are given and those of the nestings of the variables do. -/
theorem InstanceArgs.nest_all {p : α → Prop} {mark : Name → Option α}
    (hm : ∀ D a, mark D = some a → p a) :
    {Γ Δ : Scope} → {ν : Nesting α Γ} → Nesting.All p @ν → (as : InstanceArgs k Γ Δ) →
      Nest.ListRel₃ (fun a _ _ => p a) (as.nest mark @ν) (as.nest mark @ν) (as.nest mark @ν)
  | _, _, _, _, .nil => .nil
  | _, _, _, h, .snoc as B =>
    .cons (Term.nest_all hm (Nesting.liftN_rel₃ _ h) B) (InstanceArgs.nest_all hm h as)

end

/-- The positions of the nesting of the type of a field hold types of the block. -/
theorem Term.blockNest_all {Γ : Scope} (names : List Name) (A : Term k Γ) :
    Nest.All (· ∈ names) (A.blockNest names) :=
  Term.nest_all (fun D a h => by
    split at h
    · cases h
      assumption
    · cases h) (fun _ _ => .plain) A

/-- The positions of the nesting of each entry of a telescope hold types of the block. -/
theorem Telescope.nestAt_all {Γ : Scope} (names : List Name) :
    {ps : List Parameter} → (Θ : Telescope k Γ ps) → (i : Nat) →
      Nest.All (· ∈ names) (Θ.nestAt names i)
  | [], .nil, _ => .plain
  | _ :: _, .cons _ _ A _, 0 => Term.blockNest_all names A
  | _ :: _, .cons _ _ _ Θ, i + 1 => Telescope.nestAt_all names Θ i

end Sic.Core
