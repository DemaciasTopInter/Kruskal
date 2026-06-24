/-
This code was written by Johannes Jasper von Spreckelsen.
-/
import Mathlib.Data.List.Defs
import Mathlib.Data.List.MinMax
-- import Mathlib.Data.Nat.SuccPred

universe u

variable {α β : Type u} {a b : α} {l l' : List α} {i j : Nat}


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



theorem mem_set_of_ne_index [BEq α] [ReflBEq α] [LawfulBEq α] : a ∈ l → l.idxOf a ≠ i → a ∈ l.set i b := by
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

theorem mem_or_eq_of_mem_set [BEq α] [ReflBEq α] [LawfulBEq α] : a ∈ l.set i b → a ∈ l ∨ a = b := by
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
        -- have ih := ih True.intro
        -- by_cases h_bne : c == a
        --   -- apply imp_not_comm.mp LawfulBEq.eq_of_beq
        -- · simp [LawfulBEq.eq_of_beq h_bne]
        -- · simp [List.idxOf_cons, h_bne, ih]

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
          simp only [List.idxOf_cons, h_beq] at h_a_eq
          simp [List.idxOf_cons, h_beq] at hidx
          simp at hnodup
          have ih₁ := ih₁ h_in hnodup.right h_a_eq hidx
          exact ih₁

theorem mem_eraseIdx_or_eq_of_mem_set : a ∈ l.set i b → a ∈ List.eraseIdx l i ∨ a = b := by
  intro h_a_in_set
  have h_eq : l.eraseIdx i = (l.set i b).eraseIdx i := by
    simp [List.eraseIdx_set_eq]
  simp [h_eq]
  by_cases h_i_lt : i < (l.set i b).length
  · by_cases h_a_eq_b : a = b
    · simp [h_a_eq_b]
    · left
      simp [List.mem_eraseIdx_iff_getElem]
      have h := List.getElem_of_mem h_a_in_set
      rcases h with ⟨j, h, h_a_eq⟩
      simp at h
      refine ⟨j, ?_, h, h_a_eq⟩
      by_cases h_j_eq_i : j = i
      · simp [h_j_eq_i] at h_a_eq
        simp [h_a_eq] at h_a_eq_b
      · exact h_j_eq_i
  · simp only [Nat.not_lt] at h_i_lt
    simp [List.eraseIdx_eq_self.mpr h_i_lt, h_a_in_set]

theorem not_mem_erase_of_dodup [BEq α] [ReflBEq α] [LawfulBEq α] : l.Nodup → a ∉ l.erase a := by
  induction l with
  | nil =>
    simp
  | cons b l ih =>
    intro h_nodup
    simp_all
    simp [List.erase_cons]
    by_cases h_a_eq_b : a = b
    · simp [h_a_eq_b, h_nodup]
    · simp [ne_comm.mp h_a_eq_b, h_a_eq_b, ih]

theorem idxOf_eq_idxOf_set [BEq α] [ReflBEq α] [LawfulBEq α] (h₁ : a ≠ b) (h₂ : List.idxOf a l ≠ i) : List.idxOf a (l.set i b) = List.idxOf a l := by
  induction i generalizing l with
  | zero =>
    induction l with
    | nil =>
      simp
    | cons c l ih₂ =>
      simp
      by_cases h_a_beq_c : c == a
      · simp [List.idxOf_cons, h_a_beq_c] at h₂
      · simp [List.idxOf_cons, h_a_beq_c]
        by_cases h_a_beq_b : b == a
        · simp [LawfulBEq.eq_of_beq h_a_beq_b] at h₁
        · simp [h_a_beq_b]
  | succ i ih₁ =>
    induction l with
    | nil =>
      simp
    | cons c l ih₂ =>
      simp
      by_cases h_a_beq_c : c == a
      · simp [List.idxOf_cons, h_a_beq_c]
      · simp [List.idxOf_cons, h_a_beq_c] at h₂
        have h := ih₁ h₂
        simp [List.idxOf_cons, h_a_beq_c, h]

theorem nodup_set_of_not_mem [BEq α] [ReflBEq α] [LawfulBEq α] (h₁ : l.Nodup) (h₂ : a ∉ l) : (l.set i a).Nodup := by
  induction i generalizing l a with
  | zero =>
    induction l with
    | nil =>
      simp
    | cons b l ih =>
      simp_all
  | succ i ih₁ =>
    induction l with
    | nil =>
      simp
    | cons b l ih₂ =>
      simp_all
      intro h
      have h' := mem_or_eq_of_mem_set h
      simp [h₁] at h'
      simp [h'] at h₂

theorem set_eq_self [BEq α] [ReflBEq α] [LawfulBEq α] : List.set l (List.idxOf a l) a = l := by
  induction l with
  | nil =>
    simp
  | cons b l ih =>
    by_cases h : b == a
    · simp [h, List.idxOf_cons]
      have h' := LawfulBEq.eq_of_beq h
      simp [h']
    · simp [h, List.idxOf_cons]
      exact ih

theorem idxOf_ne [BEq α] : List.idxOf a l ≠ List.idxOf b l → a ≠ b := by -- unused
  intro h h'
  simp [h'] at h

theorem prop_erase_of_not_prop (p : α → Prop) (hp : ∃ a, a ∈ l ∧ p a) (h : ¬p a) [BEq α] [ReflBEq α] [LawfulBEq α] : ∃ b, b ∈ (l.erase a) ∧ p b := by
  induction l with
  | nil =>
    simp at hp
  | cons b l ih =>
    by_cases h_eq : a = b
    · simp [h_eq]
      simp [h_eq] at h
      simp [h] at hp
      simp [hp]
    · simp [ne_comm.mp h_eq]
      simp at hp
      by_cases h' : p b
      · simp [h']
      · simp [h']
        simp [h'] at hp
        simp [hp] at ih
        exact ih

theorem choose_erase_of_not_prop (p : α → Prop) (hp : ∃ a, a ∈ l ∧ p a) (h : ¬p a) [DecidablePred p] [BEq α] [ReflBEq α] [LawfulBEq α] : List.choose p l hp = List.choose p (l.erase a) (prop_erase_of_not_prop p hp h) := by
  induction l with
  | nil =>
    simp at hp
  | cons b l ih =>
    by_cases h_eq : b = a
    · simp [h_eq]
      simp [List.choose, List.chooseX, h]
    · simp [h_eq]
      simp at hp
      by_cases h' : p b
      · simp [List.choose, List.chooseX, h']
      · simp [List.choose, List.chooseX, h']
        simp [h'] at hp
        have ih := ih hp
        simp [List.choose] at ih
        exact ih

theorem erase_set_eq_eraseIdx (h_nodup : (l.set i a).Nodup) (h_lt : i < l.length) [BEq α] [ReflBEq α] [LawfulBEq α] : (l.set i a).erase a = l.eraseIdx i := by
  induction i generalizing l with
  | zero =>
    induction l with
    | nil =>
      simp
    | cons b l ih =>
      simp
  | succ i ih₁ =>
    induction l with
    | nil =>
      simp
    | cons b l ih₂ =>
      by_cases h_eq : b == a
      · simp [LawfulBEq.eq_of_beq h_eq] at h_nodup
        simp at h_lt
        have h := List.mem_set h_lt a
        simp [h] at h_nodup
      · simp [h_eq]
        simp_all

theorem choose_findIdx {p : α → Prop} {hp : ∃ a, a ∈ l ∧ p a} [DecidablePred p] [BEq α] [ReflBEq α] [LawfulBEq α] : List.choose p l hp = l[List.findIdx p l]'(by simp [hp]) := by
  induction l with
  | nil =>
    simp at hp
  | cons a l ih =>
    by_cases h : p a
    · simp [h, List.choose, List.chooseX, List.findIdx_cons]
    · simp [h] at hp
      simp [h, List.choose, List.chooseX, List.findIdx_cons]
      simp [List.choose] at ih
      rcases hp with ⟨b, hp⟩
      have ih := ih b hp.left hp.right
      exact ih

theorem getElem_set_of_ne_index (h_lt : j < (l.set i a).length) (h_ne : i ≠ j) [BEq α] [ReflBEq α] [LawfulBEq α] : (l.set i a)[j] = l[j]'(by simp at h_lt; simp [h_lt]) := by
  induction l generalizing j i with
  | nil =>
    simp
  | cons b l ih₁ =>
    induction j with
    | zero =>
      simp [h_ne]
    | succ j ih₂ =>
      cases i with
      | zero =>
        simp
      | succ i =>
        simp at h_ne
        simp [- List.length_set] at h_lt
        have ih₁ := ih₁ h_lt h_ne
        simp [ih₁]

theorem prop_getElem_findIdx {p : α → Prop} {hp : ∃ a, a ∈ l ∧ p a} [DecidablePred p] : p (l[List.findIdx p l]'(by simp [hp])) := by
  induction l with
  | nil =>
    simp at hp
  | cons a l ih =>
    by_cases h : p a
    · simp [h, List.findIdx_cons]
    · simp [h, List.findIdx_cons]
      simp [h] at hp
      simp [hp] at ih
      simp [ih]

theorem findIdx_set_of_not_prop {p : α → Prop} (h_lt : i < l.length) (h₁ : ¬p a) (h₂ : ¬p (l[i]'h_lt)) [DecidablePred p] : List.findIdx p (l.set i a) = List.findIdx p l := by
  induction l generalizing i with
  | nil =>
    simp
  | cons b l ih =>
    cases i with
    | zero =>
      simp at h₂
      simp [h₁, h₂, List.findIdx_cons]
    | succ i =>
      simp [List.findIdx_cons]
      by_cases h : p b
      · simp [h]
      · simp [h]
        apply ih
        · simp at h₂
          exact h₂

theorem findIdx_set_of_prop {p : α → Prop} (h_lt : i < l.length) (h₁ : p a) (h₂ : p (l[i]'h_lt)) [DecidablePred p] : List.findIdx p (l.set i a) = List.findIdx p l := by
  induction l generalizing i with
  | nil =>
    simp
  | cons b l ih =>
    cases i with
    | zero =>
      simp at h₂
      simp [h₁, h₂, List.findIdx_cons]
    | succ i =>
      simp [List.findIdx_cons]
      by_cases h : p b
      · simp [h]
      · simp [h]
        apply ih
        · simp at h₂
          exact h₂

theorem filter_erase_eq_self_of_not_prop {p : α → Prop} [DecidablePred p] [BEq α] [ReflBEq α] [LawfulBEq α] : ¬p a → List.filter p l = List.filter p (l.erase a) := by
  intro h_not_p_a
  induction l with
  | nil =>
    simp
  | cons b l ih =>
    by_cases h_b_beq_a : b == a
    · simp [List.erase, LawfulBEq.eq_of_beq h_b_beq_a, h_not_p_a]
    · simp [List.filter_cons, List.erase, h_b_beq_a]
      by_cases h_p_b : p b
      · simp [h_p_b, ih]
      · simp [h_p_b, ih]

theorem length_filter_erase_le_length_filter {p : α → Prop} [DecidablePred p] [BEq α] [ReflBEq α] [LawfulBEq α] : (List.filter p (l.erase a)).length ≤ (List.filter p l).length := by
  induction l with
  | nil =>
    simp
  | cons b l ih =>
    by_cases h_b_beq_a : b == a
    · by_cases h_p_a : p a
      · simp [List.erase, LawfulBEq.eq_of_beq h_b_beq_a, h_p_a]
      · simp [List.erase, LawfulBEq.eq_of_beq h_b_beq_a, h_p_a]
    · simp [List.filter_cons, List.erase, h_b_beq_a]
      by_cases h_p_b : p b
      · simp [h_p_b, ih]
      · simp [h_p_b, ih]

theorem length_le_of_subset [DecidableEq α] {l₁ l₂ : List α} (h_nodup : l₁.Nodup) (h_sub : ∀ x, x ∈ l₁ → x ∈ l₂) : l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp
  | cons a l₁ ih =>
    simp at h_nodup h_sub
    have h : (∀ (x : α), x ∈ l₁ → x ∈ l₂.erase a) := by
      intro b h_b_in₁
      have h_b_in₂ := h_sub.right b h_b_in₁
      have h_b_ne_a : ¬b = a := by
        intro h_eq
        simp [h_eq, h_nodup.left] at h_b_in₁
      simp [List.mem_erase_of_ne h_b_ne_a, h_b_in₂]
    have ih := ih (l₂ := l₂.erase a) h_nodup.right h
    simp [List.length_erase_of_mem h_sub.left] at ih
    simp
    have ih := Nat.succ_le_succ ih
    cases l₂ with
    | nil =>
      simp at h_sub
    | cons b l₂ =>
      have h' : (b :: l₂).length ≥ 1 := by
        simp
      simp at ih
      simp [ih]

theorem length_eq_of_subset [DecidableEq α] {l₁ l₂ : List α} (h_nodup₁ : l₁.Nodup) (h_nodup₂ : l₂.Nodup) (h_sub₁ : ∀ x, x ∈ l₁ → x ∈ l₂) (h_sub₂ : ∀ x, x ∈ l₂ → x ∈ l₁) : l₁.length = l₂.length := by -- unused
  have h₁ := length_le_of_subset h_nodup₁ h_sub₁
  have h₂ := length_le_of_subset h_nodup₂ h_sub₂
  exact Nat.le_antisymm h₁ h₂

theorem length_lt_of_subset [DecidableEq α] {l₁ l₂ : List α} (h_nodup₁ : l₁.Nodup) (h_nodup₂ : l₂.Nodup) (h_sub : ∀ x, x ∈ l₁ → x ∈ l₂) (h_ex : ∃ x, x ∈ l₂ ∧ x ∉ l₁) : l₁.length < l₂.length := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil =>
      simp at h_ex
    | cons a l₂ =>
      simp
  | cons a l₁ ih =>
    simp at h_nodup₁ h_sub
    have h : (∀ (x : α), x ∈ l₁ → x ∈ l₂.erase a) := by
      intro b h_b_in₁
      have h_b_in₂ := h_sub.right b h_b_in₁
      have h_b_ne_a : ¬b = a := by
        intro h_eq
        simp [h_eq, h_nodup₁.left] at h_b_in₁
      simp [List.mem_erase_of_ne h_b_ne_a, h_b_in₂]
    have h' : ∃ x, x ∈ l₂.erase a ∧ ¬x ∈ l₁ := by
      rcases h_ex with ⟨b, h_b_in, h_b_not_in⟩
      simp at h_b_not_in
      refine ⟨b, ?_, h_b_not_in.right⟩
      simp [List.mem_erase_of_ne h_b_not_in.left, h_b_in]
    have ih := ih (l₂ := l₂.erase a) h_nodup₁.right (List.Nodup.erase a h_nodup₂) h h'
    simp [List.length_erase_of_mem h_sub.left] at ih
    simp
    have ih := Nat.succ_le_succ ih
    cases l₂ with
    | nil =>
      simp at h_sub
    | cons b l₂ =>
      have h' : (b :: l₂).length ≥ 1 := by
        simp
      simp at ih
      simp
      apply Nat.lt_of_lt_of_eq ih rfl

theorem max_eq_maximum [LinearOrder α] (h : l ≠ []) : l.max h = l.maximum := by
  rw [eq_comm]
  -- simp [l.maximum.unbot (List.maximum_ne_bot_of_ne_nil h)]
  apply List.maximum_eq_coe_iff.mpr
  let a := l.max h
  have h_a : l.max h = a := by
    simp [a]
  have h' := (List.max_eq_iff h).mp h_a
  simp [h_a]
  exact h'

-- theorem max_eq_maximum_unbot [LinearOrder α] (h : l ≠ []) : l.max h = l.maximum.unbot (List.maximum_ne_bot_of_ne_nil h) := by
--   simp [WithBot.unbot]
--   rw [eq_comm]
--   apply List.maximum_eq_coe_iff.mpr
--   let a := l.max h
--   have h_a : l.max h = a := by
--     simp [a]
--   have h' := (List.max_eq_iff h).mp h_a
--   simp [h_a]
--   exact h'

theorem perm_nonempty (h : l ≠ []) (h_perm : l.Perm l') : l' ≠ [] := by
  cases l with
  | nil =>
    simp at h
  | cons a l =>
    intro h_contra
    simp [h_contra] at h_perm

-- theorem perm_max_eq [Max α] (h : l ≠ []) (h_perm : l.Perm l') : l.max h = l'.max (perm_nonempty h h_perm) := by
--   set a := l.max h with h_a
--   set b := l'.max (perm_nonempty h h_perm) with h_b
--   have h' := (List.max_eq_iff h).mp h_a.symm

theorem nil_of_length_zero : l.length = 0 → l = [] := by
  cases l with
  | nil =>
    simp
  | cons a l =>
    simp

theorem lenght_ge_of_injectiv {l₁ : List α} {l₂ : List β} {f : α → β} (h_nodup : l₁.Nodup) (h_injectiv : ∀ a ∈ l₁, ∀ b ∈ l₁, f a = f b → a = b) (h_image : ∀ a ∈ l₁, f a ∈ l₂) : l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp
  | cons a l₁ ih =>
    simp at h_image
    rcases h_image with ⟨h_a_in, h_image⟩
    have h_split := mem_split h_a_in
    rcases h_split with ⟨l₂₁, l₂₂, h_split, h_not_in⟩
    simp at h_nodup
    simp [h_split] at h_image
    have h_image : ∀ (a_1 : α), a_1 ∈ l₁ → f a_1 ∈ l₂₁ ∨ f a_1 ∈ l₂₂ := by
      intro c h_c_in
      have h := h_image c h_c_in
      have h_ne : a ≠ c := by
        intro h_eq
        simp [h_eq, h_c_in] at h_nodup
      have h_f_ne := h_injectiv a (by simp) c (by simp [h_c_in])
      simp [h_ne] at h_f_ne
      simp [ne_comm.mp h_f_ne] at h
      exact h
    have ih := ih (l₂ := l₂₁ ++ l₂₂) h_nodup.right
    simp at h_injectiv
    simp at ih
    simp [h_split, ← Nat.add_assoc]
    apply ih
    · intro a' h_a'_in b h_b_in
      have h := h_injectiv.right a' h_a'_in
      have h := h.right b h_b_in
      exact h
    · exact h_image


theorem mem_le_max (h_in : a ∈ l) (h_nonempty : l ≠ []) [Preorder α] [Max α] [Std.IsLinearOrder α] [Std.LawfulOrderMax α] : a ≤ l.max h_nonempty := by
  exact List.le_max_of_mem h_in
  -- set m := l.max h_nonempty with ← h_m
  -- have h := (List.max_eq_iff h_nonempty).mp h_m
  -- apply h.right
  -- exact h_in

-- exact?
-- #min_imports
