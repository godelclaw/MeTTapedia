import Mettapedia.GraphTheory.FourColor.BoundaryChains

namespace Mettapedia.GraphTheory.FourColor.Examples

/-- Vertices of the tetrahedron. -/
inductive TetraVertex
  | v0 | v1 | v2 | v3
  deriving DecidableEq, Fintype, Repr

/-- Edges of the tetrahedron, named by their endpoint indices. -/
inductive TetraEdge
  | e01 | e02 | e03 | e12 | e13 | e23
  deriving DecidableEq, Fintype, Repr

namespace Tetrahedron

/-- Incidence relation for the six tetrahedron edges. -/
def incident : TetraVertex → Finset TetraEdge
  | .v0 => {.e01, .e02, .e03}
  | .v1 => {.e01, .e12, .e13}
  | .v2 => {.e02, .e12, .e23}
  | .v3 => {.e03, .e13, .e23}

/-- The four triangular faces of the tetrahedron. -/
def faces : Finset (Finset TetraEdge) :=
  { {.e01, .e02, .e12},
    {.e01, .e03, .e13},
    {.e02, .e03, .e23},
    {.e12, .e13, .e23} }

theorem faces_are_triangles : ∀ f ∈ faces, f.card = 3 := by
  intro f hf
  simp [faces] at hf
  rcases hf with h | h | h | h <;> simp [h]

/-- Each triangular face contributes either zero or two incident edges at each vertex. -/
theorem face_parity (γ : Color) (f : Finset TetraEdge) (hf : f ∈ faces) :
    ∀ v : TetraVertex, ∑ e ∈ incident v, faceBoundaryChain γ f e = 0 := by
  intro v
  simp [faces] at hf
  rcases hf with h | h | h | h
  · cases v <;> simp [h, incident, faceBoundaryChain, indicatorChain]
  · cases v <;> simp [h, incident, faceBoundaryChain, indicatorChain]
  · cases v <;> simp [h, incident, faceBoundaryChain, indicatorChain]
  · cases v <;> simp [h, incident, faceBoundaryChain, indicatorChain]

/-- The closed tetrahedron has no boundary edges in this finite sanity model. -/
def boundaryEdges : Finset TetraEdge := ∅

theorem interior_edge_covered :
    ∀ e : TetraEdge, e ∉ boundaryEdges → ∃ f ∈ faces, e ∈ f := by
  intro e _he
  cases e <;> simp [faces]

/-- Two tetrahedron faces are adjacent when they are distinct and share one edge. -/
def dualAdj (f g : Finset TetraEdge) : Prop :=
  f ≠ g ∧ (f ∩ g).card = 1

theorem dualAdj_symm {f g : Finset TetraEdge} :
    dualAdj f g → dualAdj g f := by
  intro ⟨hne, hcard⟩
  exact ⟨hne.symm, by simpa [Finset.inter_comm] using hcard⟩

/-- The three neighboring faces of a tetrahedron face in the finite dual graph. -/
noncomputable def dualNeighbors (f : Finset TetraEdge) : Finset (Finset TetraEdge) := by
  classical
  exact {g ∈ faces | dualAdj f g}

theorem dual_is_cubic :
    ∀ f ∈ faces, (dualNeighbors f).card = 3 := by
  intro f hf
  simp [faces] at hf
  rcases hf with hf | hf | hf | hf <;> simp [dualNeighbors, hf, faces, dualAdj] <;> decide

/-- The trivial four-vertex coloring of K4. -/
def fourColoring : TetraVertex → Fin 4
  | .v0 => 0
  | .v1 => 1
  | .v2 => 2
  | .v3 => 3

theorem fourColoring_proper (u v : TetraVertex) (h : u ≠ v) :
    fourColoring u ≠ fourColoring v := by
  cases u <;> cases v <;> simp [fourColoring] at h ⊢

end Tetrahedron

end Mettapedia.GraphTheory.FourColor.Examples
