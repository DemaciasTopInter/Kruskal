import Mathlib
import Kruskal.Basic
import Kruskal.Lists
import Algolean

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

-- theorem test {nodeList : List node} (uF : unionFind nodeList) (id : Nat) (h : ∃ x ∈ nodeList, x.id = id) : (kruskal_query.find uF id h).eval = connected_component_of_unionFind_of_id uF id h := by
--   sorry

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

theorem kruskal_helper_eval (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
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

theorem kruskal_eval (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
  : kruskal edgeList nodeList h_matching_edge h_nodup = (kruskal_prog edgeList nodeList h_matching_edge h_nodup).eval (kruskal_model1 nodeList) := by
  simp [kruskal, kruskal_prog, kruskal_helper_eval]

theorem add_le_add_iff_left {a b c : Nat × Nat} : a + b ≤ a + c ↔ b ≤ c := by
  simp

theorem kruskal_helper_time (edgeList : List edge) (nodeList : List node) (uF : unionFind nodeList) (edgesSoFar : List edge) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
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
    apply add_le_add_iff_left.mpr
    apply le_of_eq_of_le ?_ ih
    simp [kruskal_model1]

theorem kruskal_time (edgeList : List edge) (nodeList : List node) (h_matching_edge : matching_edge edgeList nodeList) (h_nodup : nodeList.Nodup)
  : (kruskal_prog edgeList nodeList h_matching_edge h_nodup).time (kruskal_model1 nodeList) ≤ (2 * edgeList.length, edgeList.length) := by
  simp [kruskal_prog]
  simp [matching_edge] at h_matching_edge
  have h := kruskal_helper_time (edgeList.mergeSort fun a b => decide (a ≤ b)) nodeList (init_unionFind nodeList h_nodup) [] (by simp [matching_edge]; exact h_matching_edge) h_nodup
  apply le_of_le_of_eq h
  simp
