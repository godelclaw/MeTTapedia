import Mettapedia.GraphTheory.FourColor.SphericalBoundedFaceSize

/-!
# Bounded-face mesh-free reduction from actual vertex largeness

Large vertex count supplies a long face-dual axis; exact mesh exclusion
then constructs a strictly nested family of bounded exact-support nodes.
Taking more nodes than the existing finite state count contradicts physical
splice minimality. This proves an explicit vertex bound in the bounded-face
case. Fixed-mesh exclusion, the long-face case and the generating-base check
are not assumptions disguised as conclusions here; they remain separate.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalContourSeparators

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24TwoEdgeCutMinimality GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24RotationMultigraphAdapter GoertzelV24MeshIsoperimetry
open GoertzelV24InjectiveMeshWidthExclusion

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

noncomputable section

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- The bounded-face geometric transfer supplies all n nodes from vertex count. -/
theorem exists_nested_nodes_of_bounded_faces_large (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (a b B n : ℕ) (ha : 2 ≤ a)
    (hfaces : ∀ f, (orbitFaceBoundary data.toRotationSystem f).card ≤ B)
    (hno : ¬ ∃ M : Mesh (toMultigraph data.toRotationSystem) a b, IsVertexInjective M)
    (hlarge : boundedFaceSizeBound B (n * a) < Fintype.card V) :
    ∃ nodes : Fin n → ConnectedShoreNode (G := G) (3 * (b - 1)) (3 * (b - 1)),
      ∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore := by
  obtain ⟨root, far, hd⟩ := exists_dual_distance_ge_of_large_vertex_card
    data minimal.toBridgelessSphericalCubicMapData B (n * a) hfaces hlarge
  exact exists_nested_contour_nodes data minimal root far a b n ha hd hno

/-- Computable threshold, independent of the unknown least-counterexample size. -/
def boundedFaceReductionBound (a b B : ℕ) : ℕ :=
  boundedFaceSizeBound B ((contourStateBound (3 * (b - 1)) + 1) * a)

/-- An exact mesh-free least counterexample with face sizes at most B
has at most the displayed explicit number of vertices. -/
theorem vertex_card_le_of_noMesh_and_bounded_faces (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (a b B : ℕ) (ha : 2 ≤ a)
    (hfaces : ∀ f, (orbitFaceBoundary data.toRotationSystem f).card ≤ B)
    (hno : ¬ ∃ M : Mesh (toMultigraph data.toRotationSystem) a b, IsVertexInjective M) :
    Fintype.card V ≤ boundedFaceReductionBound a b B := by
  by_contra hn
  obtain ⟨nodes, hnested⟩ := exists_nested_nodes_of_bounded_faces_large data minimal a b B
    (contourStateBound (3 * (b - 1)) + 1) ha hfaces hno (Nat.lt_of_not_le hn)
  have := le_contourStateBound_of_nested_nodes data minimal nodes hnested
  omega

end
end Mettapedia.GraphTheory.FourColor.SphericalContourSeparators
