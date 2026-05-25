import Kruskal

open Kruskal

def edgeList : List edge := [
    ⟨0, 0, 5, 14, by simp⟩,
    ⟨1, 0, 2, 9, by simp⟩,
    ⟨2, 0, 1, 1, by simp⟩,
    ⟨3, 4, 5, 9, by simp⟩,
    ⟨4, 2, 5, 2, by simp⟩,
    ⟨5, 1, 2, 10, by simp⟩,
    ⟨6, 3, 4, 6, by simp⟩,
    ⟨7, 2, 3, 11, by simp⟩,
    ⟨8, 1, 3, 15, by simp⟩
  ]

def edgeList' : List edge := edgeList.mergeSort

def nodeList : List node := nodeList_of_edgeList edgeList

def uF : unionFind nodeList := init_unionFind nodeList (nodeList_of_edgeList_nodup edgeList)

-- def e₀ : edge := edgeList'[0]'sorry
-- def x₀ := connected_component_of_unionFind_of_id uF e₀.node1 sorry
-- def y₀ := connected_component_of_unionFind_of_id uF e₀.node2 sorry
-- def uF₀ := update_unionFind uF x₀ y₀ sorry sorry

-- def e₁ : edge := edgeList'[1]'sorry
-- def x₁ := connected_component_of_unionFind_of_id uF e₁.node1 sorry
-- def y₁ := connected_component_of_unionFind_of_id uF e₁.node2 sorry
-- def uF₁ := update_unionFind uF₀ x₁ y₁ sorry sorry

-- def e₂ : edge := edgeList'[2]'sorry
-- def x₂ := connected_component_of_unionFind_of_id uF e₂.node1 sorry
-- def y₂ := connected_component_of_unionFind_of_id uF e₂.node2 sorry
-- -- def uF₂ := update_unionFind uF₁ x₂ y₂ sorry sorry

#eval edgeList
#eval edgeList'
#eval kruskal_of_edgeList edgeList

#eval nodeList

#eval uF.linkList

-- #eval! e₀
-- #eval! x₀
-- #eval! y₀
-- #eval! uF₀.linkList

-- #eval! e₁
-- #eval! x₁
-- #eval! y₁
-- #eval! uF₁.linkList

-- #eval! e₂
-- #eval! x₂
-- #eval! y₂
-- #eval! uF₂.linkList
