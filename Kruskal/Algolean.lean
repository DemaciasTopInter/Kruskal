-- import Mathlib
-- import Kruskal.Basic
-- import Kruskal.Lists
-- import Kruskal.Correctness
-- import Algolean
import Algolean.QueryModel
import Kruskal.Correctness
import Mathlib.Algebra.Order.Monoid.Prod

namespace Kruskal

open Algolean Algorithms

structure found (nodeList : List node) (uF : unionFind nodeList) : Type where
  mk ::
  id : Nat
  ex : ∃ (uFL : unionFindLink nodeList), uFL ∈ uF.linkList ∧ uFL.nodeId = id ∧ uFL.ccId = id

inductive kruskal_query (nodeList : List node) : Type → Type _ where
  | find (uF : unionFind nodeList) (id : Nat) (h : ∃ x ∈ nodeList, x.id = id) : kruskal_query nodeList (found nodeList uF)
  | union (uF : unionFind nodeList) (x y : Nat) (h₁ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = x ∧ a.ccId = x) a) (h₂ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = y ∧ a.ccId = y) a) : kruskal_query nodeList (unionFind nodeList)

def kruskal_model1 (nodeList : List node) : Model (kruskal_query nodeList) (Nat × Nat) where
  evalQuery
    | .find (uF : unionFind nodeList) id h =>
      let cc := connected_component_of_unionFind_of_id uF id h
      have h_ex := exist_unionFindLink_of_connected_component_of_unionFind_of_id uF id h
      ⟨cc, h_ex⟩
    | .union (uF : unionFind nodeList) x y h₁ h₂ => update_unionFind uF x y h₁ h₂
  cost
    | .find _ _ _ => (1, 0)
    | .union _ _ _ _ _ => (0, 1) -- verschiedene Modelle mit unterschiedlichen Kostenfunktionen

def kruskal_model2 (nodeList : List node) : Model (kruskal_query nodeList) (Nat × Nat) where
  evalQuery
    | .find (uF : unionFind nodeList) id h =>
      let cc := connected_component_of_unionFind_of_id uF id h
      have h_ex := exist_unionFindLink_of_connected_component_of_unionFind_of_id uF id h
      ⟨cc, h_ex⟩
    | .union (uF : unionFind nodeList) x y h₁ h₂ => update_unionFind uF x y h₁ h₂
  cost
    | .find _ _ _ => (1, 0)
    | .union _ x y _ _ => if x = y then (0, 0) else (0, 1)

def kruskal_helper_prog (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) : Prog (kruskal_query nodeList) (List edge) := do
  match edgeList with
  | [] => return edgesSoFar
  | e::es =>
    have h : ∃ x ∈ nodeList, x.id = e.node1 := by
      have h : (∃ x ∈ nodeList, e.node1 = x.id) → (∃ x ∈ nodeList, x.id = e.node1) := by simp [eq_comm]
      simp [h (h_matching_edge e List.mem_cons_self).left]
    let found_x : (found nodeList uF) ← kruskal_query.find uF e.node1 h
    let x := found_x.id
    have h' : ∃ x ∈ nodeList, x.id = e.node2 := by
      have h' : (∃ x ∈ nodeList, e.node2 = x.id) → (∃ x ∈ nodeList, x.id = e.node2) := by simp [eq_comm]
      simp [h' (h_matching_edge e List.mem_cons_self).right]
    let found_y : (found nodeList uF) ← kruskal_query.find uF e.node2 h'
    let y := found_y.id
    have h_matching_edge' : ∀ x ∈ es, (∃ y ∈ nodeList, x.node1 = y.id) ∧ ∃ z ∈ nodeList, x.node2 = z.id := by
      intro z h_in
      simp [h_matching_edge z (List.mem_cons_of_mem e h_in)]
    let updated_uF := ← kruskal_query.union uF x y found_x.ex found_y.ex
    let updated_edgesSoFar := update_edgesSoFar edgesSoFar e x y
    return ← kruskal_helper_prog es nodeList updated_uF updated_edgesSoFar h_matching_edge' h_nodup

def kruskal_prog (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) : Prog (kruskal_query nodeList) (List edge) := do
    let edgeListSorted : List edge := edgeList.mergeSort
    let uF : unionFind nodeList := init_unionFind nodeList h_nodup
    have h_matching_edge : matching_edge edgeListSorted nodeList := by
      intro e h_e_in
      simp [edgeListSorted] at h_e_in
      simp [matching_edge] at h_matching_edge
      exact h_matching_edge e h_e_in
    return ← kruskal_helper_prog edgeListSorted nodeList uF [] h_matching_edge h_nodup

theorem kruskal_helper_eval1 (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
  : kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup = (kruskal_helper_prog edgeList nodeList uF edgesSoFar h_matching_edge h_nodup).eval (kruskal_model1 nodeList) := by
  induction edgeList generalizing uF edgesSoFar with
  | nil =>
    simp [kruskal_helper, kruskal_helper_prog]
  | cons e edgeList ih =>
    simp [kruskal_helper, kruskal_helper_prog]
    set updated_uF := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_4 nodeList uF e (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_5 nodeList uF e (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
    set updated_edgesSoFar := update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
    simp [matching_edge] at h_matching_edge ih
    have ih := ih updated_uF updated_edgesSoFar h_matching_edge.right
    simp [ih, kruskal_model1, Prog.eval]
    grind

theorem kruskal_eval1 (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
  : kruskal edgeList nodeList h_matching_edge h_nodup = (kruskal_prog edgeList nodeList h_matching_edge h_nodup).eval (kruskal_model1 nodeList) := by
  simp [kruskal, kruskal_prog, kruskal_helper_eval1]

theorem tupel_add_le_add_iff_left {a b c : Nat × Nat} : a + b ≤ a + c ↔ b ≤ c := by
  simp

theorem kruskal_helper_time1 (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
  : (kruskal_helper_prog edgeList nodeList uF edgesSoFar h_matching_edge h_nodup).time (kruskal_model1 nodeList) ≤ (2 * edgeList.length, edgeList.length) := by
  induction edgeList generalizing uF edgesSoFar with
  | nil =>
    simp [kruskal_helper_prog]
  | cons e edgeList ih =>
    simp [kruskal_helper_prog, kruskal_model1, ← add_assoc, mul_add]
    have h : (2 * edgeList.length + 2, edgeList.length + 1) = (2, 1) + (2 * edgeList.length, edgeList.length) := by
      simp [add_comm]
    simp only [h]
    set updated_uF := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_4 nodeList uF e (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_5 nodeList uF e (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
    set updated_edgesSoFar := update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
    simp [matching_edge] at h_matching_edge ih
    have ih := ih updated_uF updated_edgesSoFar h_matching_edge.right
    apply tupel_add_le_add_iff_left.mpr
    apply le_of_eq_of_le ?_ ih
    simp [kruskal_model1]

theorem kruskal_time1 (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
  : (kruskal_prog edgeList nodeList h_matching_edge h_nodup).time (kruskal_model1 nodeList) ≤ (2 * edgeList.length, edgeList.length) := by
  simp [kruskal_prog]
  simp [matching_edge] at h_matching_edge
  have h := kruskal_helper_time1 (edgeList.mergeSort fun a b => decide (a ≤ b)) nodeList (init_unionFind nodeList h_nodup) [] (by simp [matching_edge]; exact h_matching_edge) h_nodup
  apply le_of_le_of_eq h
  simp

theorem eval_kruskal_model2_eq_eval_kruskal_model1 {nodeList : List node} {p : Prog (kruskal_query nodeList) (List edge)} : p.eval (kruskal_model2 nodeList) = p.eval (kruskal_model1 nodeList) := by
  simp [kruskal_model1, kruskal_model2, Prog.eval]

theorem kruskal_helper_eval2 (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
  : kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup = (kruskal_helper_prog edgeList nodeList uF edgesSoFar h_matching_edge h_nodup).eval (kruskal_model2 nodeList) := by
  simp [eval_kruskal_model2_eq_eval_kruskal_model1, kruskal_helper_eval1]

theorem kruskal_eval2 (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
  : kruskal edgeList nodeList h_matching_edge h_nodup = (kruskal_prog edgeList nodeList h_matching_edge h_nodup).eval (kruskal_model2 nodeList) := by
  simp [eval_kruskal_model2_eq_eval_kruskal_model1, kruskal_eval1]

theorem kruskal_helper_time2_independent_edgesSoFar (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (edgesSoFar' : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
  : (kruskal_helper_prog edgeList nodeList uF edgesSoFar h_matching_edge h_nodup).time (kruskal_model2 nodeList) = (kruskal_helper_prog edgeList nodeList uF edgesSoFar' h_matching_edge h_nodup).time (kruskal_model2 nodeList) := by
  induction edgeList generalizing uF edgesSoFar edgesSoFar' with
  | nil =>
    simp [kruskal_helper_prog]
  | cons e edgeList ih =>
    simp [kruskal_helper_prog, kruskal_model2]
    set updated_uF := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_4 nodeList uF e (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_5 nodeList uF e (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) with ← h_updated_uF
    set updated_edgesSoFar := update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) with ← h_updated_edgesSoFar
    set updated_edgesSoFar' := update_edgesSoFar edgesSoFar' e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) with ← h_updated_edgesSoFar'
    have ih := ih updated_uF updated_edgesSoFar updated_edgesSoFar'
    simp [kruskal_model2] at ih
    apply ih

theorem kruskal_helper_time2_right (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) (n : Nat) (h_lt : (kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup).length < n)
  : ((kruskal_helper_prog edgeList nodeList uF edgesSoFar h_matching_edge h_nodup).time (kruskal_model2 nodeList)).2 ≤ n := by
  induction edgeList generalizing uF edgesSoFar n with
  | nil =>
    simp [kruskal_helper_prog]
  | cons e edgeList ih =>
    simp [kruskal_helper_prog, kruskal_model2, ← add_assoc]
    -- simp [add_comm, add_assoc]
    set updated_uF := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_4 nodeList uF e (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_5 nodeList uF e (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) with ← h_updated_uF
    set updated_edgesSoFar := update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) with ← h_updated_edgesSoFar

    simp [matching_edge] at h_matching_edge ih
    split_ifs with h_con
    · simp
      simp [kruskal_helper, h_updated_uF, h_updated_edgesSoFar] at h_lt
      have ih := ih updated_uF updated_edgesSoFar h_matching_edge.right n h_lt
      apply le_of_eq_of_le ?_ ih
      simp [kruskal_model2]
    · simp
      simp [kruskal_helper, h_updated_uF, update_edgesSoFar, h_con] at h_lt
      have h_nil : e :: edgesSoFar = [] ++ e :: edgesSoFar := by
        simp
      rw [h_nil] at h_lt
      simp only [kruskal_helper.edgesSoFar_append] at h_lt
      simp [← add_assoc] at h_lt
      have h_n' : ∃ (n' : Nat), n = n'.succ := by
        simp
        by_cases h_zero_lt : 0 < n
        · exact h_zero_lt
        · simp at h_zero_lt
          simp [h_zero_lt] at h_lt
      rcases h_n' with ⟨n', h_n'⟩
      simp [h_n']
      rw [add_comm]
      simp
      simp [← List.length_append, ← kruskal_helper.edgesSoFar_append, h_n'] at h_lt
      have ih := ih updated_uF edgesSoFar h_matching_edge.right n' h_lt
      simp [kruskal_model2] at ih
      have h_eq := kruskal_helper_time2_independent_edgesSoFar edgeList nodeList updated_uF edgesSoFar updated_edgesSoFar h_matching_edge.right h_nodup
      simp [kruskal_model2] at h_eq
      simp [← h_eq]
      exact ih

theorem kruskal_helper_time2 (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) (h_nonempty : nodeList ≠ []) (h_length_lt : (kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup).length < (nodeList.max h_nonempty).id.succ)
  : (kruskal_helper_prog edgeList nodeList uF edgesSoFar h_matching_edge h_nodup).time (kruskal_model2 nodeList) ≤ (2 * edgeList.length, (nodeList.max h_nonempty).id.succ) := by
  set n := (nodeList.max h_nonempty).id.succ with ← h_n
  constructor
  · simp
    induction edgeList generalizing uF edgesSoFar with
    | nil =>
      simp [kruskal_helper_prog]
    | cons e edgeList ih =>
      simp [kruskal_helper_prog, kruskal_model2, ← add_assoc, mul_add]
      simp [add_comm, add_assoc]
      set updated_uF := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_4 nodeList uF e (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_5 nodeList uF e (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
      set updated_edgesSoFar := update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
      simp [matching_edge] at h_matching_edge ih
      have h_length_lt' : (kruskal_helper edgeList nodeList updated_uF updated_edgesSoFar h_matching_edge.right h_nodup).length < n := by
        simp [kruskal_helper] at h_length_lt
        grind
      have ih := ih updated_uF updated_edgesSoFar h_matching_edge.right h_length_lt'
      apply le_of_eq_of_le ?_ ih
      simp [kruskal_model2]
      split_ifs
      · simp
      · simp
  · simp
    exact kruskal_helper_time2_right edgeList nodeList uF edgesSoFar h_matching_edge h_nodup n h_length_lt

-- geht auch ohne edgeList.Nodup, abhängig von kruskal_helper.Nodup
-- geht auch ohne edgeList.nodup_con, abhängig von kruskal_helper.nodup_con
theorem kruskal_time2 (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nonempty : nodeList ≠ []) (h_nonempty' : edgeList ≠ []) (h_nodeList : nodeList = nodeList_of_edgeList edgeList) (h_nodup' : edgeList.Nodup) (h_nodup_con : ∀ e1 ∈ edgeList, ∀ e2 ∈ edgeList, e1.node1 = e2.node1 ∧ e1.node2 = e2.node2 ∨ e1.node1 = e2.node2 ∧ e1.node2 = e2.node1 → e1 = e2)
  : (kruskal_prog edgeList nodeList h_matching_edge (by rw[h_nodeList]; exact nodeList_of_edgeList_nodup edgeList)).time (kruskal_model2 nodeList) ≤ (2 * edgeList.length, (nodeList.max h_nonempty).id.succ) := by
  have h_nodup : nodeList.Nodup := by
    rw[h_nodeList]
    exact nodeList_of_edgeList_nodup edgeList
  simp [kruskal_prog]
  simp [matching_edge] at h_matching_edge
  have h_lt : (kruskal_helper (edgeList.mergeSort fun a b => decide (a ≤ b)) nodeList (init_unionFind nodeList h_nodup) [] (kruskal_prog._proof_1 edgeList nodeList h_matching_edge) h_nodup).length < (nodeList.max h_nonempty).id.succ := by
    have h := kruskal_of_edgeList.card_edgeSet edgeList h_nonempty'
    simp [h_nodeList]
    simp only [nodeList_of_edgeList_max_eq edgeList h_nonempty'] at h
    simp [kruskal_of_edgeList, kruskal, nodeList_of_edgeList_max] at h
    grind
  have h := kruskal_helper_time2 (edgeList.mergeSort fun a b => decide (a ≤ b)) nodeList (init_unionFind nodeList h_nodup) [] (by simp [matching_edge]; exact h_matching_edge) h_nodup h_nonempty h_lt
  apply le_of_le_of_eq h
  simp

-- #min_imports
