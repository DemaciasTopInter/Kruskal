import Mathlib
import Kruskal.Basic
import Kruskal.Lists

namespace Kruskal


variable {m n : Nat} {α β : Type}

open SimpleGraph

def SimpleGraph.IsSpanningTree (G : SimpleGraph α) (H : SimpleGraph α) : Prop := H ≤ G ∧ H.IsAcyclic ∧ (∀ (x y : α), G.Reachable x y ↔ H.Reachable x y)

theorem spanninTree_connected_iff_connected (G : SimpleGraph α) (H : SimpleGraph α) (h : SimpleGraph.IsSpanningTree G H) : G.Connected ↔ H.Connected := by sorry

theorem nodeList_of_edgeList_nonempty (edgeList : List edge) (h : edgeList ≠ []) : nodeList_of_edgeList edgeList ≠ [] := by sorry

def nodeList_of_edgeList_max (edgeList : List edge) (h : edgeList ≠ []) : node := (nodeList_of_edgeList edgeList).max (nodeList_of_edgeList_nonempty edgeList h)

def fin_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : Type := Fin (nodeList_of_edgeList_max edgeList h).id.succ

def SimpleGraph_of_edgeSet (edgeSet : Set edge) : SimpleGraph (Fin n) := sorry

def SimpleGraph_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : SimpleGraph (fin_of_edgeList edgeList h) := SimpleGraph_of_edgeSet {e | e ∈ edgeList}

theorem kruskal_nonempty (edgeList : List edge) (h : edgeList ≠ []) : kruskal_of_edgeList edgeList ≠ [] := by sorry

def SimpleGraph_of_kruskal (edgeList : List edge) (h : edgeList ≠ []) := SimpleGraph_of_edgeList (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h)

theorem nodeList_of_kruskal_perm (edgeList : List edge) : List.Perm (nodeList_of_edgeList (kruskal_of_edgeList edgeList)) (nodeList_of_edgeList edgeList) := by sorry

theorem SimpleGraph_of_kruskal_IsSubgraph (edgeList : List edge) (h : edgeList ≠ []) : (SimpleGraph_of_kruskal edgeList h) ≤ (SimpleGraph_of_edgeList edgeList h) := by sorry

theorem SimpleGraph_of_kruskal_IsAcyclic (edgeList : List edge) (h : edgeList ≠ []) : (SimpleGraph_of_kruskal edgeList h).IsAcyclic := by sorry

theorem SimpleGraph_of_kruskal_IsEqReachable (edgeList : List edge) (h : edgeList ≠ []) : ∀ (x y), (SimpleGraph_of_edgeList edgeList h).Reachable x y ↔ (SimpleGraph_of_kruskal edgeList h).Reachable x y := by sorry

theorem SimpleGraph_of_kruskal_IsSpanningTree (edgeList : List edge) (h : edgeList ≠ []) : SimpleGraph.IsSpanningTree (SimpleGraph_of_kruskal edgeList h) (SimpleGraph_of_edgeList edgeList h) := by sorry

def cost_of_edgeList : List edge → Nat
  | [] => 0
  | e :: edgeList => e.cost + cost_of_edgeList edgeList

def minimalSpanninTree_of_edgeList (edgeList : List edge) (h₁ : edgeList ≠ []) (G := SimpleGraph_of_edgeList edgeList h₁) (minEdgeList : List edge) (h₂ : minEdgeList ≠ []) (h₃ : SimpleGraph.IsSpanningTree G (SimpleGraph_of_edgeList minEdgeList h₂)) (h₄ : ∀ x ∈ minEdgeList, x ∈ edgeList) : Prop := ∀ (el : List edge), (h₅ : el ≠ []) → (h₆ : ∀ x ∈ el, x ∈ edgeList) → SimpleGraph.IsSpanningTree G (SimpleGraph_of_edgeList el h₅) → (cost_of_edgeList el) ≥ (cost_of_edgeList minEdgeList)

theorem kruskal_minimalSpanninTree_of_edgeList (edgeList : List edge) (h : edgeList ≠ []) : minimalSpanninTree_of_edgeList edgeList h (SimpleGraph_of_edgeList edgeList h₁) (kruskal_of_edgeList edgeList) (kruskal_nonempty edgeList h) := by sorry
