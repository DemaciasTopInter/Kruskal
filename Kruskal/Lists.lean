/-
This code was written by Johannes Jasper von Spreckelsen.
-/

universe u

variable {α : Type u} {a b : α} {l : List α} {i j : Nat}


/--
`mem_split` is a theorem that states if an element is in a list, then there exist two lists such that the original list is the concatenation of the first list, the element, and the second list, and the element is not in the first list.
-/
theorem mem_split (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t ∧ a ∉ s := by
  induction l with
  | nil =>
    simp at h
  | cons b r ih =>
    simp [List.mem_cons] at h
    by_cases hb : a = b
    · -- a = b
      simp [hb]
      refine ⟨[], ?_, ?_⟩
      · exact ⟨r, rfl⟩
      · simp
    · -- a ≠ b
      simp [hb] at h
      rcases ih h with ⟨s, t, heq, hnin⟩
      refine ⟨b :: s, t, ?_, ?_⟩
      · --
        rw [heq]
        simp
      · --
        simp
        simp [hnin, hb]


/--
`prop_split` is a theorem that states if there exists an element in a list that satisfies a property, then there exist two lists such that the original list is the concatenation of the first list, a element that satisfies the property, and the second list, and no element in the first list satisfies it.
-/
theorem prop_split (hprop : α → Prop) (h : ∃ a, a ∈ l ∧ hprop a) : ∃ (s t : List α) (a : α), l = s ++ a :: t ∧ hprop a ∧ ∀ b ∈ s, ¬ hprop b := by
  rcases h with ⟨a, ha_in, ha_prop⟩
  induction l with
  | nil =>
    simp at ha_in
  | cons b l ih =>
    simp at ha_in
    by_cases hb : hprop b
    · -- hprop b
      refine ⟨[], l, b, ?_, ?_, ?_⟩
      · simp
      · exact hb
      · simp
    · -- ¬ hprop b
      have hne : a ≠ b := by
        intro heq
        rw [heq] at ha_prop
        contradiction
      simp [hne] at ha_in
      rcases ih ha_in with ⟨s, t, c, heq, hprop_c, hnin⟩
      refine ⟨b :: s, t, c, ?_, ?_, ?_⟩
      · rw [heq]
        simp
      · exact hprop_c
      · simp [hb]
        exact hnin



theorem mem_set_of_neq_index [BEq α] [ReflBEq α] [DecidableEq α] [LawfulBEq α] : a ∈ l → l.idxOf a ≠ i → a ∈ l.set i b := by
  have h_eq_iff_beq : ∀ (x y : α ), x = y ↔ (x == y) = true := by
    intro a b
    by_cases h : a == b
    · simp [h]
      exact LawfulBEq.eq_of_beq (a := a) (b := b) h
    · constructor
      · intro h_eq
        simp [h_eq]
      · intro h
        exact LawfulBEq.eq_of_beq (a := a) (b := b) h
  intro h_a_in h_idx_neq
  induction i generalizing l with
  | zero =>
    induction l with
    | nil =>
      simp at h_a_in
    | cons c as ih₂ =>
      simp [List.set]
      by_cases h :  a = c
      · have h_beq : c == a := by
          simp [h]
        simp [h] at h_idx_neq
      · simp [h] at h_a_in
        simp [h_a_in]
  | succ i ih₁ =>
    induction l with
    | nil =>
      simp at h_a_in
    | cons c as ih₂ =>
      by_cases h : a = c
      · simp [h]
      · have h_beq :  ¬c == a := by
          have h' : c = a ↔ c == a := (h_eq_iff_beq c a)
          intro h_beq
          simp [h_beq] at h'
          simp [h'] at h
        simp [h] at h_a_in
        simp [h_a_in] at ih₂
        have h_idx_neq' := List.idxOf_cons (x := c) (xs := as) (y := a)
        simp [h_beq] at h_idx_neq'
        simp [h_idx_neq'] at h_idx_neq
        simp at ih₁
        have h' := ih₁ h_a_in h_idx_neq
        simp [List.set, h']

theorem idxOf_set (h₁ : i < l.length) (h₃ : ∀ j, (h₂ : j < i) → l[j]'(by simp [Nat.lt_trans h₂ h₁]) ≠ a) [BEq α] [ReflBEq α] [LawfulBEq α] : List.idxOf a (l.set i a) = i := by
  induction l generalizing i with
  | nil =>
    simp at h₁
  | cons b l ih₁ =>
    induction i generalizing l with
    | zero =>
      simp [List.set]
    | succ i ih₂ =>
      simp [List.set, List.idxOf_cons]
      simp at h₁
      simp at h₃
      have h_ne := h₃ 0 (Nat.zero_lt_succ i)
      simp at h_ne
      by_cases h_beq : b == a
      · simp [LawfulBEq.eq_of_beq h_beq] at h_ne
      · simp [h_beq]
        apply ih₁
        · intro j h_j_lt
          have h_j_succ_lt := Nat.succ_lt_succ_iff.mpr h_j_lt
          have h := h₃ j.succ h_j_succ_lt
          simp at h
          exact h
        · exact h₁

theorem mem_or_eq_of_mem_set [BEq α] [ReflBEq α] [DecidableEq α] [LawfulBEq α] : a ∈ l.set i b → a ∈ l ∨ a = b := by
  intro h_a_in
  induction l generalizing i with
  | nil =>
    simp at h_a_in
  | cons c as ih₁ =>
    induction i with
    | zero =>
      simp at h_a_in
      rcases h_a_in with ⟨h_a_eq⟩ | ⟨h_a_in⟩
      · right
        exact h_a_eq
      · left
        simp [h_a_in]
    | succ i ih₂ =>
      simp at h_a_in
      rcases h_a_in with ⟨h_a_eq⟩ | ⟨h_a_in⟩
      · left
        simp [h_a_eq]
      · have h_a_in := ih₁ h_a_in
        rcases h_a_in with ⟨h_a_in⟩ | ⟨h_a_eq⟩
        · left
          simp [h_a_in]
        · right
          exact h_a_eq

theorem getElem_idxOf_self_eq_self (h_in : a ∈ l) [DecidableEq α] [LawfulBEq α] : l[List.idxOf a l]'(List.idxOf_lt_length_of_mem h_in) = a := by
    induction l with
    | nil =>
      simp at h_in
    | cons c as ih =>
      simp at h_in
      by_cases h_eq : a = c
      · simp_all
      · simp_all
        have ih := ih True.intro
        by_cases h_bne : c == a
          -- apply imp_not_comm.mp LawfulBEq.eq_of_beq
        · simp [LawfulBEq.eq_of_beq h_bne]
        · simp [List.idxOf_cons, h_bne, ih]

theorem not_mem_set_idxOf (h_in : a ∈ l) (hneq : b ≠ a) (hnodup : l.Nodup) [DecidableEq α] [LawfulBEq α] : a ∉ l.set (l.idxOf a) b := by
  have h_a_eq := getElem_idxOf_self_eq_self h_in
  generalize hidx : l.idxOf a = n
  induction n generalizing l with
  | zero =>
    induction l with
    | nil =>
      simp
    | cons c as ih =>
      by_cases h_beq : c == a
      · simp [LawfulBEq.eq_of_beq h_beq] at hnodup
        simp [ne_comm.mp hneq, hnodup]
      · simp [hidx] at h_a_eq
        simp [h_a_eq] at h_beq
  | succ i ih₁ =>
    induction l generalizing i with
    | nil =>
      simp
    | cons c as ih₂ =>
      simp
      by_cases h_beq : c == a
      · simp [List.idxOf_cons, h_beq] at hidx
      · by_cases h_eq : a = c
        · simp [h_eq] at h_beq
        · simp [h_eq]
          simp [h_eq] at h_in
          simp [List.idxOf_cons, h_beq] at h_a_eq
          simp [List.idxOf_cons, h_beq] at hidx
          simp at hnodup
          have ih₁ := ih₁ h_in hnodup.right h_a_eq hidx
          exact ih₁
