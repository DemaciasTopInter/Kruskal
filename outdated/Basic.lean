-- namespace kruskal

variable {m n : Nat}



structure node where
  mk ::
  /--
  The unique `id` of the node.
  -/
  id : Fin n
  /--
  The `id` of the first node in the connected component.

  The `ccId` is initialized with the nod's own `id`.
  -/
  ccId : Fin n -- keine Ahnung wegen funktionale sprache

instance node_BEq : BEq (node (n := n)) where
  beq a b := a.id == b.id

structure edge where
  mk ::
  id : Fin m
  node1 : Fin n
  node2 : Fin n
  cost : Nat
  nodesLt : node1 < node2

instance edge_BEq : BEq (edge (m := m) (n := n)) where
  beq a b := a.id == b.id && a.node1 == b.node1 && a.node2 == b.node2 && a.cost == b.cost

instance edge_LT : LT (edge (m := m) (n := n)) where
  lt a b := LT.lt a.cost b.cost

instance edge_DecidableLT : DecidableLT (edge (m := m) (n := n)) :=
  fun a b => if h : a.cost < b.cost then isTrue h else isFalse h

instance edge_LE : LE (edge (m := m) (n := n)) where
  le a b := LE.le a.cost b.cost

instance edge_DecidableLE : DecidableLE (edge (m := m) (n := n)) :=
  fun a b => if h : a.cost ≤ b.cost then isTrue h else isFalse h

structure graph where
  mk ::
  edges : List (edge (m := m) (n := n))
  nodes : List (node (n := n))
  -- eUnique {i j : Fin edges.length} : i != j ↔ edges[i].id != edges[j].id
  -- nUnique {i j : Fin nodes.length} : i != j ↔ nodes[i].id != nodes[j].id
  eLenM : edges.length = m
  eIdEqPos {j: Fin m} : edges[j].id = j
  nLenN : nodes.length = n
  nIdEqPos {i: Fin n} : nodes[i].id = i



structure update where
  mk ::
  nodes : List (node (n := n))
  nLenN : nodes.length = n
  nIdEqPos {i: Fin n} : nodes[i].id = i


-- Union Find
structure unionFind where
  mk::
  id : Fin n
  nodes : List (node (n := n))
  nLenN : nodes.length = n
  nIdEqPos {i: Fin n} : nodes[i].id = i
-- init
def init_node_list (nodes : List (node (n := n))) : List (node (n := n)) :=
  match nodes with
  | [] => []
  | x::xs => ⟨x.id, x.id⟩::(init_node_list xs)

-- update
def update_node_list (nodes : List (node (n := n.succ))) (pos ccId : Fin n.succ) : List (node (n := n.succ)) :=
  match nodes with
  | [] => []
  | x::xs =>
    if pos == 0
    then
      ⟨x.id, ccId⟩::xs
    else
      x::(update_node_list xs (pos - 1) ccId)

-- find
def find_connected_component {i: Fin n.succ} (x : node (n := n.succ)) (nodes : List (node (n := n.succ))) (nLenN : nodes.length = n.succ) (nIdEqPos : nodes[i].id = i) : unionFind (n := n.succ) :=
  if x.id ≤ x.ccId
  then
    ⟨x.ccId, nodes⟩ -- TODO anpassen
  else
    have h : x.ccId < nodes.length := by sorry
    have h' : x.ccId < x.id := by sorry
    let y := nodes[x.ccId]
    have h'' : y.id < x.id := by sorry
    let rek := (find_connected_component y nodes nLenN nIdEqPos)
    ⟨rek.id, update_node_list nodes x.id rek.id⟩ -- TODO anpassen
  termination_by x.id

-- union
def unite_connected_component {i: Fin n.succ}  (nodes : List (node (n := n.succ))) (ccId1 ccId2 : Fin n.succ) (nLenN : nodes.length = n.succ) (nIdEqPos : nodes[i].id = i) : update (n := n.succ) :=
  if ccId1 > ccId2
  then
    unite_connected_component nodes ccId2 ccId1 nLenN nIdEqPos
  else
    -- match nodes with
    -- | [] => []
    -- | x::xs =>
    --   if x.ccId == ccId2
    --   then
    --     ⟨x.id, ccId1⟩::(unite_connected_component xs ccId1 ccId2)
    --   else
    --     x::(unite_connected_component xs ccId1 ccId2)
    ⟨update_node_list nodes ccId2 ccId1, , ⟩










-- Kruskal
def helper {i: Fin n.succ} (edges : List (edge (m := m) (n := n.succ))) (nodes : List (node (n := n.succ))) (nLenN : nodes.length = n.succ) (nIdEqPos : nodes[i].id = i) : List (edge (m := m) (n := n.succ)) :=
  match edges with
  | [] => []
  | e::rest =>
    let ⟨cc1, nodes', nLenN', nIdEqPos'⟩ := find_connected_component (nodes[e.node1]) nodes nLenN nIdEqPos
    let ⟨cc2, nodes'', nLenN'', nIdEqPos''⟩ := find_connected_component (nodes'[e.node2]) nodes' nLenN' nIdEqPos'
    if cc1 == cc2
    then
      helper rest nodes nLenN nIdEqPos
    else
      --e.node2.ccId = e.node1.ccId
      let ⟨nodes''', nLenN''', nIdEqPos'''⟩ := unite_connected_component nodes'' cc1 cc2 -- TODO datenstruktur anlegen
      e::(helper rest nodes''' nLenN''' nIdEqPos''')

def kruskal (g : graph (m := m) (n := n.succ)) : List (edge (m := m) (n := n.succ)) :=
  let edges := g.edges.mergeSort
  helper edges g.nodes -- TODO anpassen






def hello := "world"
