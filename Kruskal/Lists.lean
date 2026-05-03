/-
This code was written by Johannes Jasper von Spreckelsen.
-/

universe u

variable {α : Type u} {a : α} {l : List α}


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
