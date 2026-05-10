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



theorem mem_set_of_neq_index [BEq α] [ReflBEq α] [DecidableEq α] (h_eq_iff_beq : ∀ (x : α) (y : α), x = y ↔ x == y) : a ∈ l → l.idxOf a ≠ i → a ∈ l.set i b := by
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
        simp at h_beq
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
