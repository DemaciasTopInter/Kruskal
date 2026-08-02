import Mathlib

universe a

variable {V : Type a} {u v : V} {e : Sym2 V} {G : SimpleGraph V} {p : G.Walk u v}

-- theorem reachable_of_le_reachble (G H : SimpleGraph α) (h_le : G ≤ H) : G.Reachable a b → H.Reachable a b := by
--   exact fun a_1 => SimpleGraph.Reachable.mono h_le a_1

-- theorem Walk.symm (G : SimpleGraph α) : Nonempty (G.Walk a b) → Nonempty (G.Walk b a) := by
--   exact fun a_1 =>
--     (fun {α β} f g => (Nonempty.congr f g).mpr) (fun a_2 => id a_2.reverse)
--       (fun a_2 => id a_2.reverse) a_1

-- theorem Reachable.symm (G : SimpleGraph α) : G.Reachable a b → G.Reachable b a := by
--   exact SimpleGraph.Reachable.symm

abbrev _root_.SimpleGraph.Walk.start (_ : G.Walk u v) : V := u

def walk_of_deletet_edge {V : Type u} {u v : V} {e : Sym2 V} {G : SimpleGraph V} {p : G.Walk u v} (h_not_in : e ∉ p.edges) : (G.deleteEdges {e}).Walk u v :=
  match p with
  | .cons h p' =>
    have h' : (G.deleteEdges {e}).Adj u p'.start := by
      simp at h_not_in
      simp [_root_.SimpleGraph.Walk.start, h, ne_comm.mp h_not_in.left]
    .cons h' (walk_of_deletet_edge (by simp at h_not_in; exact h_not_in.right))
  | .nil =>
    .nil

theorem edge_mem_walk {V : Type u} {u v : V} {e : Sym2 V} {G H : SimpleGraph V} (h_eq : G = H.deleteEdges {e}) (h_not_reachable : ¬G.Reachable u v) : ∀ (p : H.Walk u v), e ∈ p.edges := by
  intro p
  by_contra h_not_in
  let w := walk_of_deletet_edge h_not_in
  simp [h_eq, SimpleGraph.Reachable] at h_not_reachable
  have := h_not_reachable.false w
  exact this
