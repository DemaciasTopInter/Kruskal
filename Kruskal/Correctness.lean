import Mathlib
import Kruskal.Basic
import Kruskal.Lists

namespace Kruskal


variable {m n : Nat} {α β : Type}


def spanninTree (G : SimpleGraph α) (H : SimpleGraph α) : Prop := H ≤ G ∧ H.IsAcyclic ∧ (∀ (x y : α), G.Reachable x y ↔ H.Reachable x y)

theorem spanninTree_connected_iff_connected (G : SimpleGraph α) (H : SimpleGraph α) (h : spanninTree G H) : G.Connected ↔ H.Connected := by sorry

def SimpleGraph_of_edgeSet (edgeSet : Set edge) : SimpleGraph node := sorry

def SimpleGraph_of_edgeList (edgeList : List edge) : SimpleGraph node := SimpleGraph_of_edgeSet {e | e ∈ edgeList}

theorem spanninTree_of_kruskal (edgeList : List edge) : spanninTree (SimpleGraph_of_edgeList edgeList) (SimpleGraph_of_edgeList (kruskal_of_edgeList edgeList)) := by sorry

def cost_of_edgeList : List edge → Nat
  | [] => 0
  | e :: edgeList => e.cost + cost_of_edgeList edgeList

def cost_of_edgeSet (edgeSet : Finset edge) : Nat :=
  Finset.fold (fun a b => a + b) 0 (fun e => e.cost) edgeSet

def minimalSpanninTree_of_edgeList (edgeList : List edge) : Set (Set edge) :=
  let p := {e | e ∈ edgeList}.powerset
  let s := {s | s ∈ p ∧ (spanninTree (SimpleGraph_of_edgeList edgeList) (SimpleGraph_of_edgeSet s))}
  have h_isMin := Minimal (fun x => x ∈ (Finset.map (fun x => cost_of_edgeSet x) s))
  {r | r ∈ s ∧ h_isMin (cost_of_edgeSet r)}

theorem kruskal_minimal (edgeList : List edge) : {e | e ∈ (kruskal_of_edgeList edgeList)} ∈ (minimalSpanninTree_of_edgeList edgeList) := by sorry
