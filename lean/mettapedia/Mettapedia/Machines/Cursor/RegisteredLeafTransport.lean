import Mettapedia.GSLT.Dynamics.StableOccurrenceContraction

/-!
# Coordinate transport through a registered leaf family

A discrimination index contains structural nodes and optional occurrence
stores. An allocated store remains registered when it becomes empty. The
independent reference walks the tree; the cached realization transforms the
registered stores directly. Their equality preserves every store, including
its occurrence order and repetitions.

The work bound counts node/store visits and coordinate examinations after
registration. Initial tree traversal, dynamic-array allocation, compiled C
and hardware costs are separate obligations. Native controls exercise cache
creation, newly populated nodes, empty-store reuse and detached readers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.RegisteredLeafTransport

/-- Children and siblings encode a finite branching tree. `none` is a
structural node; `some []` is a registered but currently empty store. -/
inductive Tree where
  | empty
  | node (store : Option (List Nat)) (children siblings : Tree)
  deriving DecidableEq, Repr

def registry : Tree → List (List Nat)
  | .empty => []
  | .node store children siblings =>
      store.toList ++ registry children ++ registry siblings

/-- Tree traversal reference: replace each coordinate independently, skipping
only occurrences explicitly removed by the map. -/
def transportTree (coordinate : Nat → Option Nat) : Tree → Tree
  | .empty => .empty
  | .node store children siblings =>
      .node (store.map (List.filterMap coordinate))
        (transportTree coordinate children) (transportTree coordinate siblings)

def transportRegistry (coordinate : Nat → Option Nat)
    (stores : List (List Nat)) : List (List Nat) :=
  stores.map (List.filterMap coordinate)

theorem registry_transport (coordinate : Nat → Option Nat) (tree : Tree) :
    registry (transportTree coordinate tree) =
      transportRegistry coordinate (registry tree) := by
  induction tree with
  | empty => rfl
  | node store children siblings hc hs =>
      cases store <;>
        simp [registry, transportTree, transportRegistry] at hc hs ⊢ <;>
        simp [hc, hs]

/-- Cache insertion order need not be tree traversal order. Permuting the
outer registry preserves its transport correspondence; the order inside
each occurrence store is unchanged. -/
theorem registry_transport_of_perm (coordinate : Nat → Option Nat)
    (tree : Tree) (stores : List (List Nat))
    (registered : stores.Perm (registry tree)) :
    (transportRegistry coordinate stores).Perm
      (registry (transportTree coordinate tree)) := by
  rw [registry_transport]
  exact registered.map (List.filterMap coordinate)

/-- Emptying a store must not remove its registration: later insertions may
reuse its address without registering it a second time. -/
theorem registry_length_preserved (coordinate : Nat → Option Nat) (tree : Tree) :
    (registry (transportTree coordinate tree)).length = (registry tree).length := by
  rw [registry_transport]
  simp [transportRegistry]

def nodeCount : Tree → Nat
  | .empty => 0
  | .node _ children siblings => 1 + nodeCount children + nodeCount siblings

def coordinateCount : Tree → Nat
  | .empty => 0
  | .node store children siblings =>
      (store.getD []).length + coordinateCount children + coordinateCount siblings

theorem registry_length_le_nodes (tree : Tree) :
    (registry tree).length ≤ nodeCount tree := by
  induction tree with
  | empty => simp [registry, nodeCount]
  | node store children siblings hc hs =>
      cases store <;> simp [registry, nodeCount] <;> omega

theorem registry_coordinates_exact (tree : Tree) :
    ((registry tree).map List.length).sum = coordinateCount tree := by
  induction tree with
  | empty => rfl
  | node store children siblings hc hs =>
      cases store <;> simp [registry, coordinateCount, hc, hs, Nat.add_assoc]

def registryWork (stores : List (List Nat)) : Nat :=
  stores.length + (stores.map List.length).sum

def treeWork (tree : Tree) : Nat := nodeCount tree + coordinateCount tree

/-- A prepared registry visits at most as many containers as a whole-tree
walk, and examines exactly the same coordinates. -/
theorem registry_work_le_tree (tree : Tree) :
    registryWork (registry tree) ≤ treeWork tree := by
  unfold registryWork treeWork
  rw [registry_coordinates_exact]
  exact Nat.add_le_add_right (registry_length_le_nodes tree) _

def wrap : Nat → Tree → Tree
  | 0, tree => tree
  | n + 1, tree => .node none (wrap n tree) .empty

theorem registry_wrap (depth : Nat) (tree : Tree) :
    registry (wrap depth tree) = registry tree := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [wrap, registry, ih]

/-- Increasing structural depth does not increase prepared transport work. -/
theorem registry_work_wrap (depth : Nat) (tree : Tree) :
    registryWork (registry (wrap depth tree)) = registryWork (registry tree) := by
  rw [registry_wrap]

theorem tree_work_wrap (depth : Nat) (tree : Tree) :
    treeWork (wrap depth tree) = depth + treeWork tree := by
  induction depth with
  | zero => simp [wrap]
  | succ depth ih =>
      simp only [wrap, treeWork, nodeCount, coordinateCount, Option.getD_none,
        List.length_nil, Nat.add_zero, Nat.zero_add] at ih ⊢
      omega

open Mettapedia.GSLT.Dynamics.StableOccurrenceContraction

/-- An occurrence delivered from a transported store refers to the same row
as before contraction. The coordinate table is the existing independent
stable-contraction compiler, not an arbitrary index rewrite. -/
theorem compiled_occurrence_preserved {Row : Type} (mask : List Bool)
    (rows : List Row) (source target : Nat)
    (mapped : (compile mask rows).sourceToTarget[source]? = some (some target)) :
    rows[source]? = (contract mask rows)[target]? := by
  have exact := sourceToTarget_sound mask rows source target mapped
  rwa [compile_rows_exact] at exact

example : transportRegistry (fun n => if n = 1 then none else some (n / 2))
    [[0, 1, 2, 2], [], [3]] = [[0, 1, 1], [], [1]] := by decide

/-- Omitting a live store changes the transported occurrence family. -/
example : transportRegistry some [[0], [1]] ≠ transportRegistry some [[0]] := by
  decide

/-- Registering one store twice is observably wrong even when its payloads
are equal: the occurrence family gains an extra store. -/
example : transportRegistry some [[0]] ≠ transportRegistry some [[0], [0]] := by
  decide

/-- An emptied store survives registration, whereas a never-populated
structural node contributes no entry. -/
example : registry (transportTree (fun _ => none)
    (.node (some [0]) (.node none .empty .empty) .empty)) = [[]] := by decide

#print axioms registry_transport
#print axioms registry_length_preserved
#print axioms registry_coordinates_exact
#print axioms registry_work_le_tree
#print axioms registry_work_wrap
#print axioms tree_work_wrap
#print axioms compiled_occurrence_preserved

end Mettapedia.Machines.Cursor.RegisteredLeafTransport
