module

/-!
# Lists

Properties of the lists that Lean does not provide: the positions and the images of the elements of
a list whose images are distinct, the numbered elements of a list of a known length, and the results
of a function defined at every element of a list.
-/

@[expose] public section

/-- Two elements of a list whose images by `f` are distinct, which have the same image, are equal. -/
theorem List.eq_of_nodup_map {α β : Type} {f : α → β} :
    {l : List α} → (l.map f).Nodup → {a b : α} → a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | _ :: _, h, _, _, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (by rw [hab]; exact List.mem_map_of_mem hb') h.1
    · exact absurd (by rw [← hab]; exact List.mem_map_of_mem ha') h.1
    · exact List.eq_of_nodup_map h.2 ha' hb' hab

/-- The element at a position of a list whose elements are distinct has the position as its first
index. -/
theorem List.idxOf?_of_getElem? {α : Type} [BEq α] [LawfulBEq α] :
    {l : List α} → {j : Nat} → {a : α} → l.Nodup → l[j]? = some a → l.idxOf? a = some j
  | _ :: _, 0, _, _, h => by
    cases h
    rw [List.idxOf?_cons, beq_self_eq_true]
    rfl
  | x :: xs, _ + 1, a, hn, h => by
    have hne : (x == a) = false :=
      beq_false_of_ne fun e => (List.nodup_cons.1 hn).1 (e ▸ List.mem_of_getElem? h)
    rw [List.idxOf?_cons, hne, List.idxOf?_of_getElem? (List.nodup_cons.1 hn).2 h]
    rfl

/-- Two positions of a list whose images by `f` are distinct, which hold elements with the same
image, are equal. -/
theorem List.getElem?_inj_of_nodup_map {α β : Type} {f : α → β} :
    {l : List α} → (l.map f).Nodup → {i i' : Nat} → {a b : α} → l[i]? = some a →
      l[i']? = some b → f a = f b → i = i'
  | [], _, _, _, _, _, ha, _, _ => nomatch ha
  | _ :: l, h, i, i', _, _, ha, hb, hab => by
    rw [List.map_cons, List.nodup_cons] at h
    match i, i', ha, hb with
    | 0, 0, _, _ => rfl
    | 0, i' + 1, ha, hb =>
      cases ha
      exact absurd (hab ▸ List.mem_map_of_mem (List.mem_of_getElem? hb)) h.1
    | i + 1, 0, ha, hb =>
      cases hb
      exact absurd (hab.symm ▸ List.mem_map_of_mem (List.mem_of_getElem? ha)) h.1
    | i + 1, i' + 1, ha, hb => exact congrArg (· + 1) (List.getElem?_inj_of_nodup_map h.2 ha hb hab)

/-- The `n` elements of a list of length `n`, numbered. -/
def List.getFin {α : Type} (l : List α) {n : Nat} (h : l.length = n) : Fin n → α :=
  fun i => l.get (i.cast h.symm)

/-- The elements of a list mapped by `f` are the elements of the list mapped by `f`. -/
theorem List.getFin_map {α β : Type} (f : α → β) (l : List α) {n : Nat}
    (h : (l.map f).length = n) :
    (l.map f).getFin h = fun i => f (l.getFin ((List.length_map f).symm.trans h) i) := by
  funext i
  simp [List.getFin]

/-- The numbered elements of a list are the list. -/
theorem List.ofFn_getFin {α : Type} :
    (l : List α) → {n : Nat} → (h : l.length = n) → List.ofFn (l.getFin h) = l
  | [], _, h => by subst h; rfl
  | a :: l, _, h => by
    subst h
    rw [List.ofFn_succ]
    exact congrArg (a :: ·) (List.ofFn_getFin l rfl)

/-- An element of a list whose images by `f` are distinct is the first one with its image. -/
theorem List.find?_of_nodup_map {α β : Type} [BEq β] [LawfulBEq β] {f : α → β} :
    {l : List α} → (l.map f).Nodup → {a : α} → a ∈ l → l.find? (f · == f a) = some a
  | [], _, _, ha => nomatch ha
  | b :: l, h, a, ha => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact List.find?_cons_of_pos (beq_iff_eq.2 rfl)
    · have hne : ¬ (fun x => f x == f a) b = true := fun hb => h.1 (beq_iff_eq.1 hb ▸
        List.mem_map_of_mem ha')
      rw [List.find?_cons_of_neg (p := fun x => f x == f a) (l := l) hne]
      exact List.find?_of_nodup_map h.2 ha'

/-- The results of a function at the elements of a list, all defined, are at the same positions as
the elements. -/
theorem List.getElem?_of_mapM {α β : Type} {f : α → Option β} :
    {l : List α} → {l' : List β} → l.mapM f = some l' → ∀ {i : Nat} {a : α}, l[i]? = some a →
      ∃ b, f a = some b ∧ l'[i]? = some b
  | [], _, _, _, _, ha => nomatch ha
  | a :: l, l', h, i, a', ha => by
    rw [List.mapM_cons] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [hfa, hl] at h
      | some bs =>
        simp only [hfa, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        cases i with
        | zero =>
          cases ha
          exact ⟨b, hfa, rfl⟩
        | succ i => exact List.getElem?_of_mapM hl ha

/-- A function defined at every element of a list is defined at the list. -/
theorem List.exists_mapM_eq_some {α β : Type} {f : α → Option β} :
    {l : List α} → (∀ a ∈ l, ∃ b, f a = some b) → ∃ l', l.mapM f = some l'
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl'⟩ := List.exists_mapM_eq_some (l := l) fun a' ha' =>
      h a' (List.mem_cons_of_mem _ ha')
    exact ⟨b :: l', by simp [List.mapM_cons, hb, hl']⟩

/-- The index of the image of an element in the images of a list, distinct, is its position. -/
theorem List.idxOf?_map_of_nodup {α β : Type} [BEq β] [LawfulBEq β] {f : α → β} :
    {l : List α} → (l.map f).Nodup → {i : Nat} → {a : α} → l[i]? = some a →
      (l.map f).idxOf? (f a) = some i
  | [], _, _, _, ha => nomatch ha
  | b :: l, hn, i, a, ha => by
    rw [List.map_cons, List.nodup_cons] at hn
    cases i with
    | zero =>
      cases ha
      rw [List.map_cons, List.idxOf?_cons, beq_iff_eq.2 rfl, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    | succ i =>
      have hne : f b ≠ f a := fun he => hn.1 (he ▸ List.mem_map_of_mem (List.mem_of_getElem? ha))
      rw [List.map_cons, List.idxOf?_cons, beq_eq_false_iff_ne.2 hne,
        ite_eq_right_of_eq_false _ _ (eq_false Bool.false_ne_true), List.idxOf?_map_of_nodup hn.2 ha]
      rfl
