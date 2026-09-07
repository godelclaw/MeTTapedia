import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedInjectiveMeshWidthFactorization
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# An ordered mesh cell need not have a corner-preserving simple rim

The designated branch vertices in an `OrderedInjectiveMesh` are ordered,
but a row and a column may share a segment. Four branch-to-branch subpaths
can therefore have a pendant designated corner. Loop erasure cannot turn
their union into a simple cycle while retaining that corner.

This specimen uses the vertex and edge numbering of the dodecahedral
control in `v24_ordered_mesh_cell_gate.json`. The finite proofs here check
the actual ordered mesh, cubic ambient degrees, and the cycle obstruction.
The rotation-system/spherical receipt is checked by the geometric lab;
no spherical or non-colourability premise is asserted by this module.
-/

namespace Mettapedia.GraphTheory.FourColor.OrderedMeshCellBoundaryCounterexample

open GoertzelV24BoundaryEssentialGluing GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization

def ambient : Multigraph (Fin 20) (Fin 30) where
  fst := ![0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 5, 5, 6, 6, 7,
    8, 8, 9, 10, 10, 11, 12, 12, 13, 14, 15, 15, 16, 17, 18]
  snd := ![1, 2, 5, 4, 6, 3, 8, 4, 10, 12, 7, 9, 7, 13, 16,
    9, 11, 15, 11, 14, 17, 13, 14, 18, 19, 16, 17, 18, 19, 19]

theorem ambient_loopless : ∀ e, ambient.fst e ≠ ambient.snd e := by decide +kernel

theorem ambient_cubic : ∀ v : Fin 20,
    (Finset.univ.filter fun e => ambient.fst e = v ∨ ambient.snd e = v).card = 3 := by
  decide +kernel

def row0 : MeshPath ambient where
  len := 2
  vert := ![10, 14, 12]
  edge := ![19, 22]
  edge_ends := by decide +kernel

def row1 : MeshPath ambient where
  len := 1
  vert := ![17, 19]
  edge := ![28]
  edge_ends := by decide +kernel

def col0 : MeshPath ambient where
  len := 2
  vert := ![10, 11, 17]
  edge := ![18, 20]
  edge_ends := by decide +kernel

def col1 : MeshPath ambient where
  len := 2
  vert := ![12, 14, 19]
  edge := ![22, 24]
  edge_ends := by decide +kernel

def mesh : Mesh ambient 2 2 where
  row := ![row0, row1]
  col := ![col0, col1]
  branch := ![![10, 12], ![17, 19]]
  branch_mem_row := by decide +kernel
  branch_mem_col := by decide +kernel
  row_edges_disjoint := by decide +kernel
  col_edges_disjoint := by decide +kernel

def rowPosition : (i j : Fin 2) → Fin ((mesh.row i).len + 1) :=
  Fin.cases ![0, 2] (fun _ => ![0, 1])

def colPosition : (i j : Fin 2) → Fin ((mesh.col j).len + 1) :=
  fun i => Fin.cases (if i = 0 then 0 else 2) (fun _ => if i = 0 then 0 else 2)

/-- The specimen inhabits the route's existing ordered-mesh carrier. -/
def ordered : OrderedInjectiveMesh ambient 2 2 where
  toMesh := mesh
  rowVertexInjective := by decide +kernel
  colVertexInjective := by decide +kernel
  branchInjective := by decide +kernel
  rowBranchPosition := rowPosition
  colBranchPosition := colPosition
  rowBranchPosition_spec := by decide +kernel
  colBranchPosition_spec := by decide +kernel
  rowBranchPosition_strictMono := by decide +kernel
  colBranchPosition_strictMono := by decide +kernel

/-- Even the stronger within-family vertex-disjointness holds. -/
theorem families_vertex_disjoint :
    (∀ i j : Fin 2, i ≠ j → ∀ s t, (mesh.row i).vert s ≠ (mesh.row j).vert t) ∧
    (∀ i j : Fin 2, i ≠ j → ∀ s t, (mesh.col i).vert s ≠ (mesh.col j).vert t) := by
  decide +kernel

/-- These are the actual edges of the four trimmed paths, not a chosen
subgraph discarding inconvenient edges. -/
def cellEdges : Finset (Fin 30) :=
  (Finset.univ.biUnion fun i => Finset.univ.image (mesh.row i).edge) ∪
  (Finset.univ.biUnion fun j => Finset.univ.image (mesh.col j).edge)

theorem cellEdges_eq : cellEdges = {18, 19, 20, 22, 24, 28} := by decide +kernel

def cellGraph : SimpleGraph (Fin 20) where
  Adj u v := ∃ e ∈ cellEdges,
    (ambient.fst e = u ∧ ambient.snd e = v) ∨
    (ambient.fst e = v ∧ ambient.snd e = u)
  symm := by
    constructor
    rintro u v ⟨e, he, h⟩
    exact ⟨e, he, h.symm⟩
  loopless := by
    constructor
    rintro u ⟨e, _, h | h⟩ <;> exact ambient_loopless e (h.1.trans h.2.symm)

instance : DecidableRel cellGraph.Adj := fun _ _ => inferInstanceAs
  (Decidable (∃ e ∈ cellEdges,
    (ambient.fst e = _ ∧ ambient.snd e = _) ∨
    (ambient.fst e = _ ∧ ambient.snd e = _)))

/-- Concatenating the four subpaths, with the closing vertex implicit. -/
def rim : List (Fin 20) := [10, 14, 12, 14, 19, 17, 11]

theorem rim_eq_four_sides : rim =
    (List.ofFn row0.vert).dropLast ++ (List.ofFn col1.vert).dropLast ++
    (List.ofFn row1.vert).reverse.dropLast ++ (List.ofFn col0.vert).reverse.dropLast := by
  decide +kernel

theorem rim_not_simple : ¬ rim.Nodup := by decide +kernel

/-- The cell contains every ambient edge induced on its vertex set. -/
theorem cellEdges_induced : cellEdges = Finset.univ.filter
    (fun e => ambient.fst e ∈ rim.toFinset ∧ ambient.snd e ∈ rim.toFinset) := by
  decide +kernel

theorem complete_boundary_card : (boundaryEdges ambient rim.toFinset).card = 6 := by
  decide +kernel

/-- The induced side fails the inside-majority requirement at its corner. -/
theorem corner_internal_edge_count :
    (cellEdges.filter fun e => ambient.fst e = 12 ∨ ambient.snd e = 12).card = 1 := by
  decide +kernel

theorem corner_is_branch : mesh.branch 0 1 = 12 := rfl

theorem corner_neighbors : ∀ v, cellGraph.Adj 12 v ↔ v = 14 := by decide +kernel

/-- No simple cycle using only the four subpaths can retain corner 12.
In particular, corner-preserving loop erasure cannot repair the rim. -/
theorem no_cycle_at_corner (p : cellGraph.Walk 12 12) : ¬ p.IsCycle := by
  intro hp
  have hfirst := (corner_neighbors p.snd).mp (p.adj_snd hp.not_nil)
  have hlast := (corner_neighbors p.penultimate).mp
    (p.adj_penultimate hp.not_nil).symm
  exact hp.snd_ne_penultimate (hfirst.trans hlast.symm)

/-- Changing the root of the cycle does not avoid the obstruction. -/
theorem corner_not_on_cycle {v : Fin 20} (p : cellGraph.Walk v v) (hp : p.IsCycle) :
    12 ∉ p.support := by
  intro hmem
  exact no_cycle_at_corner (p.rotate 12 hmem) (hp.rotate hmem)

/-- Erasing the backtrack does leave a cycle, but loses the designated corner. -/
def erased : cellGraph.Walk 10 10 :=
  .cons (show cellGraph.Adj 10 14 from by decide +kernel)
    (.cons (show cellGraph.Adj 14 19 from by decide +kernel)
    (.cons (show cellGraph.Adj 19 17 from by decide +kernel)
    (.cons (show cellGraph.Adj 17 11 from by decide +kernel)
    (.cons (show cellGraph.Adj 11 10 from by decide +kernel) .nil))))

theorem erased_is_cycle : erased.IsCycle where
  edges_nodup := by decide +kernel
  ne_nil := by simp [erased]
  support_nodup := by decide +kernel

theorem erased_support : erased.support = [10, 14, 19, 17, 11, 10] := by decide +kernel

/-- The exact ordered-mesh assertion and its failed cell consequence. -/
theorem ordered_cell_obstruction :
    Nonempty (OrderedInjectiveMesh ambient 2 2) ∧
    ¬ ∃ p : cellGraph.Walk (mesh.branch 0 1) (mesh.branch 0 1), p.IsCycle :=
  ⟨⟨ordered⟩, fun ⟨p, hp⟩ => no_cycle_at_corner p hp⟩

end Mettapedia.GraphTheory.FourColor.OrderedMeshCellBoundaryCounterexample
