module

/-!
# Lists

Properties of the lists that Lean does not provide: the positions and the images of the elements of
a list whose images are distinct, the element at the position that `findIdx?` finds, the first
element after a prefix, the pairs of the elements of two lists of the same length, the numbered
elements of a list of a known length, the results of a function defined at every element of a list,
and the length of a list whose distinct elements are all in another.
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

/-- The position that `findIdx?` finds holds an element that satisfies the predicate, as
`List.of_findIdx?_eq_some`, without its choice. -/
theorem List.getElem?_of_findIdx?_eq_some {α : Type} {p : α → Bool} :
    {l : List α} → {i : Nat} → l.findIdx? p = some i → ∃ a, l[i]? = some a ∧ p a = true
  | [], _, h => nomatch h
  | a :: l, i, h => by
    rw [List.findIdx?_cons] at h
    cases ha : p a with
    | true =>
      rw [ha, ite_eq_left_of_eq_true _ _ (eq_true rfl)] at h
      cases h
      exact ⟨a, rfl, ha⟩
    | false =>
      rw [ha, ite_eq_right_of_eq_false _ _ (eq_false Bool.false_ne_true)] at h
      cases hl : l.findIdx? p with
      | none => rw [hl] at h; cases h
      | some i' =>
        rw [hl] at h
        cases h
        show ∃ b, (a :: l)[i' + 1]? = some b ∧ p b = true
        rw [List.getElem?_cons_succ]
        exact List.getElem?_of_findIdx?_eq_some hl

/-- A list with an element that satisfies the predicate has a position that `findIdx?` finds, as
`List.findIdx?_isSome`, without its choice. -/
theorem List.findIdx?_isSome_of_mem {α : Type} {p : α → Bool} :
    {l : List α} → {a : α} → a ∈ l → p a = true → (l.findIdx? p).isSome
  | [], _, h, _ => nomatch h
  | b :: l, a, h, hp => by
    rw [List.findIdx?_cons]
    cases hb : p b with
    | true =>
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      rfl
    | false =>
      rw [ite_eq_right_of_eq_false _ _ (eq_false Bool.false_ne_true)]
      rcases List.mem_cons.1 h with rfl | h'
      · rw [hp] at hb
        cases hb
      · have hs := List.findIdx?_isSome_of_mem h' hp
        cases hl : l.findIdx? p with
        | none => rw [hl] at hs; cases hs
        | some _ => rfl

/-- A list of one element at most that holds `a` is `[a]`. -/
theorem List.eq_singleton_of_mem_of_length_le_one {α : Type} :
    {l : List α} → {a : α} → a ∈ l → l.length ≤ 1 → l = [a]
  | [], _, h, _ => nomatch h
  | [_], _, .head _, _ => rfl
  | [_], _, .tail _ h, _ => nomatch h
  | _ :: _ :: _, _, _, h => absurd h (Nat.not_succ_le_zero _ ∘ Nat.le_of_succ_le_succ)

/-- The first element after the first `i` elements of a list is its element at the position `i`. -/
theorem List.headD_drop {α : Type} {l : List α} {i : Nat} {a d : α} (h : l[i]? = some a) :
    (l.drop i).headD d = a := by
  rw [List.headD_eq_head?_getD, List.head?_drop, h]
  rfl

/-- The elements `ks j` of positions `j < m`, each `none` when the element `gs[j]` satisfies `p`, and
the element of `L` at `j` otherwise, pair the elements of `gs` with those of `L`, of length `m`. -/
theorem List.ofFn_ite_getElem? {α : Type} {m : Nat} (p : α → Prop) [DecidablePred p]
    (gs : Vector α m) (L : List Nat) (hL : L.length = m) :
    List.ofFn (fun j : Fin m => if p gs[j] then none else L[(j : Nat)]?) =
      List.zipWith (fun e l => if p e then none else some l) gs.toList L := by
  apply List.ext_getElem
  · simp [hL]
  · intro j _ h₂
    have hj : j < L.length := by simp at h₂; omega
    simp [List.getElem_ofFn, List.getElem_zipWith, Vector.getElem_toList,
      List.getElem?_eq_getElem hj]

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

/-- A list whose elements are distinct and all in a list `l₂` is not longer than `l₂`, as
`List.Nodup.length_le_of_subset`, without its choice: removing the first element `a` of the list
from `l₂` keeps the others in `l₂` and shortens it by one. -/
theorem List.length_le_of_nodup_subset {α : Type} [BEq α] [LawfulBEq α] :
    {l₁ l₂ : List α} → l₁.Nodup → (∀ a ∈ l₁, a ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, hn, h => by
    have hmem : ∀ {l : List α} {x : α}, x ≠ a → x ∈ l → x ∈ l.erase a := by
      intro l x hx hl
      induction l with
      | nil => cases hl
      | cons b l ih =>
        cases hba : (b == a) with
        | true =>
          simp only [List.erase_cons, hba, ↓reduceIte]
          rcases List.mem_cons.1 hl with rfl | hl
          · exact absurd (beq_iff_eq.1 hba) hx
          · exact hl
        | false =>
          rw [List.erase_cons, hba]
          rcases List.mem_cons.1 hl with rfl | hl
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih hl)
    have hlen : ∀ {l : List α}, a ∈ l → (l.erase a).length + 1 = l.length := by
      intro l hl
      induction l with
      | nil => cases hl
      | cons b l ih =>
        cases hba : (b == a) with
        | true => simp only [List.erase_cons, hba, ↓reduceIte, List.length_cons]
        | false =>
          rw [List.erase_cons, hba]
          rcases List.mem_cons.1 hl with rfl | hl
          · exact absurd (beq_self_eq_true _) (by rw [hba]; exact Bool.false_ne_true)
          · simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, ih hl]
    have ht := List.length_le_of_nodup_subset (l₂ := l₂.erase a) (List.nodup_cons.1 hn).2
      fun x hx => hmem (fun (e : x = a) => (List.nodup_cons.1 hn).1 (e ▸ hx))
        (h x (List.mem_cons_of_mem _ hx))
    have hl := hlen (h a List.mem_cons_self)
    simp only [List.length_cons]
    omega
