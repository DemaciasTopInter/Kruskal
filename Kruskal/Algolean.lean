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
    simp only [updated_uF, updated_edgesSoFar]

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
    apply tupel_add_le_add_iff_left.mpr
    set updated_uF := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_4 nodeList uF e (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_5 nodeList uF e (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
    set updated_edgesSoFar := update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
    simp [matching_edge] at h_matching_edge ih
    have ih := ih updated_uF updated_edgesSoFar h_matching_edge.right
    apply le_of_eq_of_le ?_ ih
    simp [kruskal_model1]

theorem kruskal_time1 (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
  : (kruskal_prog edgeList nodeList h_matching_edge h_nodup).time (kruskal_model1 nodeList) ≤ (2 * edgeList.length, edgeList.length) := by
  simp [kruskal_prog]
  simp [matching_edge] at h_matching_edge
  have h := kruskal_helper_time1 (edgeList.mergeSort fun a b => decide (a ≤ b)) nodeList (init_unionFind nodeList h_nodup) [] (by simp [matching_edge]; exact h_matching_edge) h_nodup
  apply le_of_le_of_eq h
  simp




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




structure unionFind_strict (nodeList : List node) : Type where
  mk ::
  uF : unionFind nodeList
  rankInvariant_strict : uF.rankInvariant_strict

inductive kruskal_query_strict (nodeList : List node) : Type → Type _ where
  | find (uF : unionFind nodeList) (id : Nat) (h : ∃ x ∈ nodeList, x.id = id) (h_rankInvariant : uF.rankInvariant_strict) : kruskal_query_strict nodeList (found nodeList uF)
  | union (uF : unionFind nodeList) (x y : Nat) (h₁ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = x ∧ a.ccId = x) a) (h₂ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = y ∧ a.ccId = y) a) (h_rankInvariant : uF.rankInvariant_strict) : kruskal_query_strict nodeList (unionFind_strict nodeList)

def kruskal_model3 (nodeList : List node) : Model (kruskal_query_strict nodeList) (Nat × Nat) where
  evalQuery
    | .find (uF : unionFind nodeList) id h _ =>
      let cc := connected_component_of_unionFind_of_id uF id h
      have h_ex := exist_unionFindLink_of_connected_component_of_unionFind_of_id uF id h
      ⟨cc, h_ex⟩
    | .union (uF : unionFind nodeList) x y h₁ h₂ h_rankInvariant => ⟨update_unionFind uF x y h₁ h₂, update_unionFind.rankInvariant_strict _ _ _ _ _ h_rankInvariant⟩
  cost
    | .find _ _ _ _ => (Nat.log 2 nodeList.length, 0)
    | .union _ x y _ _ _ => if x = y then (0, 0) else (0, 1)

def kruskal_helper_prog_strict (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) (h_rankInvariant : uF.rankInvariant_strict) : Prog (kruskal_query_strict nodeList) (List edge) := do
  match edgeList with
  | [] => return edgesSoFar
  | e::es =>
    have h : ∃ x ∈ nodeList, x.id = e.node1 := by
      have h : (∃ x ∈ nodeList, e.node1 = x.id) → (∃ x ∈ nodeList, x.id = e.node1) := by simp [eq_comm]
      simp [h (h_matching_edge e List.mem_cons_self).left]
    let found_x : (found nodeList uF) ← kruskal_query_strict.find uF e.node1 h h_rankInvariant
    let x := found_x.id
    have h' : ∃ x ∈ nodeList, x.id = e.node2 := by
      have h' : (∃ x ∈ nodeList, e.node2 = x.id) → (∃ x ∈ nodeList, x.id = e.node2) := by simp [eq_comm]
      simp [h' (h_matching_edge e List.mem_cons_self).right]
    let found_y : (found nodeList uF) ← kruskal_query_strict.find uF e.node2 h' h_rankInvariant
    let y := found_y.id
    have h_matching_edge' : ∀ x ∈ es, (∃ y ∈ nodeList, x.node1 = y.id) ∧ ∃ z ∈ nodeList, x.node2 = z.id := by
      intro z h_in
      simp [h_matching_edge z (List.mem_cons_of_mem e h_in)]
    let updated_uF : (unionFind_strict nodeList) ← kruskal_query_strict.union uF x y found_x.ex found_y.ex h_rankInvariant
    let updated_edgesSoFar := update_edgesSoFar edgesSoFar e x y
    return ← kruskal_helper_prog_strict es nodeList updated_uF.uF updated_edgesSoFar h_matching_edge' h_nodup updated_uF.rankInvariant_strict

def kruskal_prog_strict (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) : Prog (kruskal_query_strict nodeList) (List edge) := do
    let edgeListSorted : List edge := edgeList.mergeSort
    let uF : unionFind nodeList := init_unionFind nodeList h_nodup
    have h_matching_edge : matching_edge edgeListSorted nodeList := by
      intro e h_e_in
      simp [edgeListSorted] at h_e_in
      simp [matching_edge] at h_matching_edge
      exact h_matching_edge e h_e_in
    have h_uF_rankInvariant : uF.rankInvariant_strict := by
      exact init_unionFind.rankInvariant_strict _
    return ← kruskal_helper_prog_strict edgeListSorted nodeList uF [] h_matching_edge h_nodup h_uF_rankInvariant




theorem kruskal_helper_eval3 (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) (h_rankInvariant : uF.rankInvariant_strict)
  : kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup = (kruskal_helper_prog_strict edgeList nodeList uF edgesSoFar h_matching_edge h_nodup h_rankInvariant).eval (kruskal_model3 nodeList) := by
  induction edgeList generalizing uF edgesSoFar with
  | nil =>
    simp [kruskal_helper, kruskal_helper_prog_strict]
  | cons e edgeList ih =>
    simp [kruskal_helper, kruskal_helper_prog_strict]
    set updated_uF := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_4 nodeList uF e (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_5 nodeList uF e (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
    set updated_edgesSoFar := update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
    simp [matching_edge] at h_matching_edge ih
    have ih := ih updated_uF updated_edgesSoFar h_matching_edge.right (update_unionFind.rankInvariant_strict _ _ _ _ _ h_rankInvariant)
    simp [ih, kruskal_model3, Prog.eval]
    grind

theorem kruskal_eval3 (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
  : kruskal edgeList nodeList h_matching_edge h_nodup = (kruskal_prog_strict edgeList nodeList h_matching_edge h_nodup).eval (kruskal_model3 nodeList) := by
  simp [kruskal, kruskal_prog_strict]
  exact kruskal_helper_eval3 _ _ _ _ _ _ _

theorem kruskal_helper_time3_independent_edgesSoFar (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (edgesSoFar' : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) (h_rankInvariant : uF.rankInvariant_strict)
  : (kruskal_helper_prog_strict edgeList nodeList uF edgesSoFar h_matching_edge h_nodup h_rankInvariant).time (kruskal_model3 nodeList) = (kruskal_helper_prog_strict edgeList nodeList uF edgesSoFar' h_matching_edge h_nodup h_rankInvariant).time (kruskal_model3 nodeList) := by
  induction edgeList generalizing uF edgesSoFar edgesSoFar' with
  | nil =>
    simp [kruskal_helper_prog_strict]
  | cons e edgeList ih =>
    simp [kruskal_helper_prog_strict, kruskal_model3]
    set updated_uF := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_4 nodeList uF e (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_5 nodeList uF e (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) with ← h_updated_uF
    set updated_edgesSoFar := update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) with ← h_updated_edgesSoFar
    set updated_edgesSoFar' := update_edgesSoFar edgesSoFar' e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) with ← h_updated_edgesSoFar'
    have ih := ih updated_uF updated_edgesSoFar updated_edgesSoFar'
    simp [kruskal_model3] at ih
    apply ih

theorem kruskal_helper_time3_right (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) (n : Nat) (h_lt : (kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup).length < n) (h_rankInvariant : uF.rankInvariant_strict)
  : ((kruskal_helper_prog_strict edgeList nodeList uF edgesSoFar h_matching_edge h_nodup h_rankInvariant).time (kruskal_model3 nodeList)).2 ≤ n := by
    induction edgeList generalizing uF edgesSoFar n with
    | nil =>
      simp [kruskal_helper_prog_strict]
    | cons e edgeList ih =>
      simp [kruskal_helper_prog_strict, kruskal_model3, ← add_assoc]
      set updated_uF := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_4 nodeList uF e (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_5 nodeList uF e (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) with ← h_updated_uF
      set updated_edgesSoFar := update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) with ← h_updated_edgesSoFar
      simp [matching_edge] at h_matching_edge ih
      split_ifs with h_con
      · simp
        simp [kruskal_helper, h_updated_uF, h_updated_edgesSoFar] at h_lt
        have ih := ih updated_uF updated_edgesSoFar h_matching_edge.right n h_lt (update_unionFind.rankInvariant_strict _ _ _ _ _ h_rankInvariant)
        simp [kruskal_model3] at ih
        apply le_of_eq_of_le ?_ ih
        simp [h_updated_uF]
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
        have ih := ih updated_uF edgesSoFar h_matching_edge.right n' h_lt (update_unionFind.rankInvariant_strict _ _ _ _ _ h_rankInvariant)
        simp [kruskal_model3] at ih
        have h_eq := kruskal_helper_time3_independent_edgesSoFar edgeList nodeList updated_uF edgesSoFar updated_edgesSoFar h_matching_edge.right h_nodup (update_unionFind.rankInvariant_strict _ _ _ _ _ h_rankInvariant)
        simp [kruskal_model3, ← h_updated_uF, ← h_updated_edgesSoFar] at h_eq
        rw [← h_eq]
        exact ih

theorem kruskal_helper_time3 (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup) (h_nonempty : nodeList ≠ []) (h_length_lt : (kruskal_helper edgeList nodeList uF edgesSoFar h_matching_edge h_nodup).length < (nodeList.max h_nonempty).id.succ) (h_rankInvariant : uF.rankInvariant_strict)
  : (kruskal_helper_prog_strict edgeList nodeList uF edgesSoFar h_matching_edge h_nodup h_rankInvariant).time (kruskal_model3 nodeList) ≤ (2 * edgeList.length * (Nat.log 2 nodeList.length), (nodeList.max h_nonempty).id.succ) := by
  set n := (nodeList.max h_nonempty).id.succ with ← h_n
  constructor
  · simp
    induction edgeList generalizing uF edgesSoFar with
    | nil =>
      simp [kruskal_helper_prog_strict]
    | cons e edgeList ih =>
      simp [kruskal_helper_prog_strict, kruskal_model3, ← add_assoc, mul_add]
      simp [add_comm, add_assoc]
      set updated_uF := update_unionFind uF (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_4 nodeList uF e (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (kruskal_helper._proof_5 nodeList uF e (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
      set updated_edgesSoFar := update_edgesSoFar edgesSoFar e (connected_component_of_unionFind_of_id uF e.node1 (kruskal_helper._proof_1 nodeList e edgeList h_matching_edge)) (connected_component_of_unionFind_of_id uF e.node2 (kruskal_helper._proof_2 nodeList e edgeList h_matching_edge))
      simp [matching_edge] at h_matching_edge ih
      have h_length_lt' : (kruskal_helper edgeList nodeList updated_uF updated_edgesSoFar h_matching_edge.right h_nodup).length < n := by
        simp [kruskal_helper] at h_length_lt
        grind
      have ih := ih updated_uF updated_edgesSoFar h_matching_edge.right (update_unionFind.rankInvariant_strict _ _ _ _ _ h_rankInvariant) h_length_lt'
      simp [← add_assoc, ← mul_two, add_mul]
      nth_rewrite 1 [mul_comm]
      apply add_le_add
      · split_ifs
        · simp
        · simp
      · simp [kruskal_model3] at ih
        exact ih
  · simp
    exact kruskal_helper_time3_right edgeList nodeList uF edgesSoFar h_matching_edge h_nodup n h_length_lt h_rankInvariant

-- geht auch ohne edgeList.Nodup, abhängig von kruskal_helper.Nodup
-- geht auch ohne edgeList.nodup_con, abhängig von kruskal_helper.nodup_con
theorem kruskal_time3 (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nonempty : nodeList ≠ []) (h_nonempty' : edgeList ≠ []) (h_nodeList : nodeList = nodeList_of_edgeList edgeList) (h_nodup' : edgeList.Nodup) (h_nodup_con : ∀ e1 ∈ edgeList, ∀ e2 ∈ edgeList, e1.node1 = e2.node1 ∧ e1.node2 = e2.node2 ∨ e1.node1 = e2.node2 ∧ e1.node2 = e2.node1 → e1 = e2)
  : (kruskal_prog_strict edgeList nodeList h_matching_edge (by rw[h_nodeList]; exact nodeList_of_edgeList_nodup edgeList)).time (kruskal_model3 nodeList) ≤ (2 * edgeList.length * (Nat.log 2 nodeList.length), (nodeList.max h_nonempty).id.succ) := by
  have h_nodup : nodeList.Nodup := by
    rw[h_nodeList]
    exact nodeList_of_edgeList_nodup edgeList
  simp [kruskal_prog_strict]
  simp [matching_edge] at h_matching_edge
  have h_lt : (kruskal_helper (edgeList.mergeSort fun a b => decide (a ≤ b)) nodeList (init_unionFind nodeList h_nodup) [] (kruskal_prog._proof_1 edgeList nodeList h_matching_edge) h_nodup).length < (nodeList.max h_nonempty).id.succ := by
    have h := kruskal_of_edgeList.card_edgeSet edgeList h_nonempty'
    simp [h_nodeList]
    simp only [nodeList_of_edgeList_max_eq edgeList h_nonempty'] at h
    simp [kruskal_of_edgeList, kruskal, nodeList_of_edgeList_max] at h
    grind
  set uF := init_unionFind nodeList h_nodup
  have h_rankInvariant : uF.rankInvariant_strict := init_unionFind.rankInvariant_strict _
  have h := kruskal_helper_time3 (edgeList.mergeSort fun a b => decide (a ≤ b)) nodeList (init_unionFind nodeList h_nodup) [] (by simp [matching_edge]; exact h_matching_edge) h_nodup h_nonempty h_lt  h_rankInvariant
  apply le_of_le_of_eq h
  simp




structure found_parent {nodeList : List node} (uF : unionFind nodeList) (uFL : unionFindLink nodeList) : Type where
  mk ::
  p : unionFindLink nodeList
  isIn : p ∈ uF.linkList
  rank_gt : p.rank > uFL.rank

inductive find_query (nodeList : List node) : Type → Type _ where
  | parent {uF : unionFind nodeList} (uFL : unionFindLink nodeList) (h_in : uFL ∈ uF.linkList) (h_not_self_con : uFL.nodeId ≠ uFL.ccId) : find_query nodeList (found_parent uF uFL)
  | union (uF : unionFind nodeList) (x y : Nat) (h₁ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = x ∧ a.ccId = x) a) (h₂ : ∃ a ∈ uF.linkList, (fun a => a.nodeId = y ∧ a.ccId = y) a) (h_rankInvariant : uF.rankInvariant_strict) : find_query nodeList (unionFind_strict nodeList)

def connected_component_of_unionFind_of_unionFindLink_prog {nodeList : List node} (uF : unionFind nodeList) (uFL : unionFindLink nodeList) (h_uFL_in : uFL ∈ uF.linkList) : Prog (find_query nodeList) (found nodeList uF) := do
  if h_self_connected : uFL.ccId = uFL.nodeId
    then
      return ⟨uFL.ccId, by refine ⟨uFL, h_uFL_in, h_self_connected.symm, rfl⟩⟩
    else
      let f : (found_parent uF uFL) ← find_query.parent uFL h_uFL_in (ne_comm.mp h_self_connected)
      let p : unionFindLink nodeList := f.p
      have h_p_in : p ∈ uF.linkList := f.isIn
      have h_r : p.rank > uFL.rank := f.rank_gt
      return ← connected_component_of_unionFind_of_unionFindLink_prog uF p h_p_in
termination_by nodeList.length - uFL.rank
  decreasing_by
  grind

def connected_component_of_unionFind_of_id_prog {nodeList : List node} (uF : unionFind nodeList) (id : Nat) (h : ∃ x ∈ nodeList, x.id = id) : Prog (find_query nodeList) (found nodeList uF) := do
  let x : node := { id := id }
  have h_x_in : x ∈ nodeList := by
    rcases h with ⟨y, h_y_in, h_y⟩
    cases y
    simp at h_y
    simp [h_y] at h_y_in
    exact h_y_in
  have h_ex_uFL : ∃ uFL ∈ uF.linkList, uFL.nodeId = id := by
    have h' := uF.matching_nodeId x h_x_in
    rcases h' with ⟨uFL, h_uFL, h_unique⟩
    simp [x] at h_uFL
    refine ⟨uFL, h_uFL.left, h_uFL.right.symm⟩
  let uFL := List.choose _ uF.linkList h_ex_uFL
  have h_uFL : List.choose _ uF.linkList h_ex_uFL = uFL := by
    simp [uFL]
  have h_uFL_in := List.choose_mem _ uF.linkList h_ex_uFL
  have h_uFL_prop := List.choose_property _ uF.linkList h_ex_uFL
  return ← connected_component_of_unionFind_of_unionFindLink_prog uF uFL h_uFL_in




def find_model (nodeList : List node) : Model (find_query nodeList) (Nat × Nat) where
  evalQuery
    | .parent uFL h_in h_not_self_con =>
      let p := parent uFL h_in
      have h_p_in := by
        rename_i uF
        have h_p_in : p ∈ uF.linkList := by
          simp [p, parent, List.choose_mem]
        exact h_p_in
      have h_rank : p.rank > uFL.rank := by
        rename_i uF
        simp [p, parent]
        have h := uF.matching_rank uFL h_in
        simp [h_not_self_con] at h
        exact h
      ⟨p, h_p_in, h_rank⟩
    | .union (uF : unionFind nodeList) x y h₁ h₂ h_rankInvariant => ⟨update_unionFind uF x y h₁ h₂, update_unionFind.rankInvariant_strict _ _ _ _ _ h_rankInvariant⟩
  cost
    | .parent _ _ _ => (1, 0)
    | .union _ x y _ _ _ => if x = y then (0, 0) else (0, 1)

theorem connected_component_of_unionFind_of_unionFindLink_prog_eval {nodeList : List node} (uF : unionFind nodeList) (uFL : unionFindLink nodeList) (h_uFL_in : uFL ∈ uF.linkList)
  : connected_component_of_unionFind_of_unionFindLink uF uFL h_uFL_in = ((connected_component_of_unionFind_of_unionFindLink_prog uF uFL h_uFL_in).eval (find_model nodeList)).id := by
  fun_induction connected_component_of_unionFind_of_unionFindLink with
  | case1 uFL h_uFL_in h_self_con =>
    simp [find_model, h_self_con, connected_component_of_unionFind_of_unionFindLink_prog]
  | case2 uFL h_uFL_in h_not_self_con p h_p_in h_r ih =>
    rw [connected_component_of_unionFind_of_unionFindLink_prog]
    simp [find_model, h_not_self_con, ih]
    have h_p_eq : parent uFL h_uFL_in = p := by
      simp [p, parent]
    simp [h_p_eq]

theorem connected_component_of_unionFind_of_id_prog_eval {nodeList : List node} (uF : unionFind nodeList) (id : Nat) (h : ∃ x ∈ nodeList, x.id = id)
  : connected_component_of_unionFind_of_id uF id h = ((connected_component_of_unionFind_of_id_prog uF id h).eval (find_model nodeList)).id := by
  simp [connected_component_of_unionFind_of_id, connected_component_of_unionFind_of_id_prog]
  exact connected_component_of_unionFind_of_unionFindLink_prog_eval _ _ _

theorem connected_component_of_unionFind_of_unionFindLink_prog_time_log {nodeList : List node} (uF : unionFind nodeList) (uFL : unionFindLink nodeList) (h_uFL_in : uFL ∈ uF.linkList) (h_rankInvariant : uF.rankInvariant_strict) : (connected_component_of_unionFind_of_unionFindLink_prog uF uFL h_uFL_in).time (find_model nodeList) ≤ (Nat.log 2 nodeList.length - uFL.rank.val, 0) := by
  have h_max_rank := max_rank h_rankInvariant
  fun_induction connected_component_of_unionFind_of_unionFindLink_prog with
  | case1 uFL h_uFL_in h_self_con =>
    simp
  | case2 uFL h_uFL_in h_not_self_con ih =>
    set p := parent uFL h_uFL_in with ← h_p
    have h_p_in := by
      have h_p_in : p ∈ uF.linkList := by
        simp [p, parent, List.choose_mem]
      exact h_p_in
    have h_rank : p.rank > uFL.rank := by
      simp [p, parent]
      have h := uF.matching_rank uFL h_uFL_in
      simp [ne_comm.mp h_not_self_con] at h
      exact h
    let f : found_parent uF uFL := ⟨p, h_p_in, h_rank⟩
    have ih := ih f
    simp [find_model, h_p]
    simp [find_model, f] at ih
    have h_le : (1, 0) + (Nat.log 2 nodeList.length - ↑p.rank, 0) ≤ (Nat.log 2 nodeList.length - ↑uFL.rank, 0) := by
      simp
      grind
    apply le_trans ?_ h_le
    apply add_le_add
    · simp
    · exact ih

theorem connected_component_of_unionFind_of_id_prog_time_log {nodeList : List node} (uF : unionFind nodeList) (id : Nat) (h : ∃ x ∈ nodeList, x.id = id) (h_rankInvariant : uF.rankInvariant_strict) : (connected_component_of_unionFind_of_id_prog uF id h).time (find_model nodeList) ≤ (Nat.log 2 nodeList.length, 0) := by
  simp [connected_component_of_unionFind_of_id_prog]
  set uFL := List.choose (fun a => a.nodeId = id) uF.linkList (connected_component_of_unionFind_of_id_prog._proof_2 uF id (connected_component_of_unionFind_of_id_prog._proof_1 id h)) with ← h_uFL
  have h_uFL_in := List.choose_mem (fun a => a.nodeId = id) uF.linkList (connected_component_of_unionFind_of_id_prog._proof_2 uF id (connected_component_of_unionFind_of_id_prog._proof_1 id h))
  simp [h_uFL]
  have h_le : (Nat.log 2 nodeList.length - uFL.rank.val, 0) ≤ (Nat.log 2 nodeList.length, 0) := by
    simp
  apply le_trans ?_ h_le
  exact connected_component_of_unionFind_of_unionFindLink_prog_time_log uF uFL h_uFL_in h_rankInvariant




def reduction {nodeList : List node} : Reduction (kruskal_query_strict nodeList) (find_query nodeList) where
  reduce
    | .find uF id h _ => connected_component_of_unionFind_of_id_prog uF id h
    | .union uF x y h₁ h₂ h_rankInvariant => do find_query.union uF x y h₁ h₂ h_rankInvariant

theorem model_evalQuery_eq {nodeList : List node} : ∀ {l} (q : (kruskal_query_strict nodeList) l), (reduction.reduce q).eval (find_model nodeList) = (kruskal_model3 nodeList).evalQuery q := by
  intro t q
  cases q with
  | find uF id h h_rankInvariant =>
    have h' : (reduction.reduce (kruskal_query_strict.find uF id h h_rankInvariant)).eval (find_model nodeList) = (connected_component_of_unionFind_of_id_prog uF id h).eval (find_model nodeList) := by
      simp [reduction]
    simp [kruskal_model3, h']
    have h_found_eq : ∀ (a b : found nodeList uF), a.id = b.id → a = b := by
      intro a b h_eq
      cases a
      cases b
      simp at h_eq
      simp [h_eq]
    apply h_found_eq
    simp
    exact (connected_component_of_unionFind_of_id_prog_eval _ _ _).symm
  | union uF x y h₁ h₂ =>
    simp [find_model, kruskal_model3, reduction]

theorem model_cost_le {nodeList : List node} : ∀ {l} (q : (kruskal_query_strict nodeList) l), (reduction.reduce q).time (find_model nodeList) ≤ (kruskal_model3 nodeList).cost q := by
  intro t q
  cases q with
  | find uF id h h_rankInvariant =>
    simp [reduction, kruskal_model3]
    exact connected_component_of_unionFind_of_id_prog_time_log _ _ _ h_rankInvariant
  | union uF x y h₁ h₂ _ =>
    simp [find_model, kruskal_model3, reduction]

-- #min_imports
