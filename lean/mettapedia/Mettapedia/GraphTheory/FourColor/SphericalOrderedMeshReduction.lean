import Mettapedia.GraphTheory.FourColor.SphericalOrderedContourMesh
import Mettapedia.GraphTheory.FourColor.SphericalMeshFreeRawDecomposition

/-!
# Ordered-mesh exclusion supplies the exact target-class size bound

The ordered mesh-or-bond alternative supplies one complete bond in each
depth window. The existing localization and Count-node arguments bound the
dual radius; complete cotree cuts then bound the vertex count. This closes
the pre-existing `RawDecompositionOfNoOrderedInjectiveMesh` premise.

Fixed ordered-mesh exclusion itself and verification of the actual
generating base remain separate hypotheses. No general planar grid theorem,
configuration catalogue, or permissive-mesh exclusion is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalOrderedMeshReduction

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open GoertzelV24PrimalCycleFacialBond
open GoertzelV24RotationMultigraphAdapter GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24ConnectedShoreLiteralNode GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24SimpleGraphTaitBridge GoertzelV24SphericalReductiveAssembly
open SphericalContourSeparators SphericalCotreePathChain SphericalMeshFreeRawDecomposition

noncomputable section

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Construct the nodes from distance and absence of the ordered carrier.
The construction needs spherical geometry, not minimality or zero Count. -/
theorem exists_nested_nodes_of_no_orderedMesh_of_spherical (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : GoertzelV24OrbitFaceTwoSided.OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (a b n : ℕ)
    (ha : 2 ≤ a) (hd : n * a ≤ (orbitFaceDualGraph data).dist root far)
    (hno : ¬ Nonempty (OrderedInjectiveMesh (toMultigraph data.toRotationSystem) a b)) :
    ∃ nodes : Fin n → ConnectedShoreNode (G := G)
        (3 * (orderedLinkageSize a b - 1)) (3 * (orderedLinkageSize a b - 1)),
      ∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore := by
  classical
  have hdepth (t : Fin n) : t.val * a + a ≤ (orbitFaceDualGraph data).dist root far := by
    have hmul := Nat.mul_le_mul_right a (Nat.succ_le_of_lt t.isLt)
    simp only [Nat.succ_mul] at hmul
    exact hmul.trans hd
  have hcut (t : Fin n) : Nonempty (OrderedContourBond data root far
      (t.val * a) (t.val * a + a - 1) (3 * (orderedLinkageSize a b - 1))) :=
    (exists_orderedMesh_or_contour_bond data ambient
      htwo root far (t.val * a) a b ha (hdepth t)).resolve_left hno
  let cuts := fun t : Fin n => Classical.choice (hcut t)
  have hnested := ordered_contour_bonds_nested data ambient htwo root far a n _ ha hd cuts
  let nodes := fun t => (cuts t).toConnectedNode data ambient
    htwo root far (by have := hdepth t; omega) (by have := hdepth t; omega)
  exact ⟨nodes, fun i j hij => (hnested i j hij).2⟩

/-- The original target-class interface is a specialization of the geometric supplier. -/
theorem exists_nested_nodes_of_no_orderedMesh (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (root far : OrbitFace data.toRotationSystem) (a b n : ℕ)
    (ha : 2 ≤ a) (hd : n * a ≤ (orbitFaceDualGraph data).dist root far)
    (hno : ¬ Nonempty (OrderedInjectiveMesh (toMultigraph data.toRotationSystem) a b)) :
    ∃ nodes : Fin n → ConnectedShoreNode (G := G)
        (3 * (orderedLinkageSize a b - 1)) (3 * (orderedLinkageSize a b - 1)),
      ∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore :=
  exists_nested_nodes_of_no_orderedMesh_of_spherical data
    minimal.toBridgelessSphericalCubicMapData minimal.facesTwoSided root far a b n ha hd hno

/-- No ordered mesh implies an explicit full face-dual diameter bound. -/
theorem dual_distance_lt_of_no_orderedMesh (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (root far : OrbitFace data.toRotationSystem) (a b : ℕ) (ha : 2 ≤ a)
    (hno : ¬ Nonempty (OrderedInjectiveMesh (toMultigraph data.toRotationSystem) a b)) :
    (orbitFaceDualGraph data).dist root far <
      (contourStateBound (3 * (orderedLinkageSize a b - 1)) + 1) * a := by
  by_contra hn
  obtain ⟨nodes, hnested⟩ := exists_nested_nodes_of_no_orderedMesh data minimal root far a b
    (contourStateBound (3 * (orderedLinkageSize a b - 1)) + 1) ha (Nat.le_of_not_gt hn) hno
  have := le_contourStateBound_of_nested_nodes data minimal nodes hnested
  omega

/-- Reuse the existing explicit arithmetic bound with the enlarged linkage width. -/
def orderedMeshFreeVertexBound (a b : ℕ) : ℕ :=
  meshFreeVertexBound a (orderedLinkageSize a b)

/-- All geometry is supplied from the exact target class and ordered exclusion. -/
theorem vertex_card_le_of_no_orderedMesh (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (a b : ℕ) (ha : 2 ≤ a)
    (hno : ¬ Nonempty (OrderedInjectiveMesh (toMultigraph data.toRotationSystem) a b)) :
    Fintype.card V ≤ orderedMeshFreeVertexBound a b := by
  classical
  let root := dartOrbitFace data.toRotationSystem data.toRotationSystem.outer
  let h := (contourStateBound (3 * (orderedLinkageSize a b - 1)) + 1) * a
  have hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h := by
    intro f
    exact Nat.le_of_lt (dual_distance_lt_of_no_orderedMesh data minimal f root a b ha hno)
  by_contra hlarge
  have hlarge' : 4 ^ ((contourStateBound (2 * h + 1) + 1) + 2 * (2 * h + 1)) <
      Fintype.card V := Nat.lt_of_not_ge hlarge
  obtain ⟨nodes, hnested⟩ := exists_nested_nodes_of_large_card data minimal root h
    (contourStateBound (2 * h + 1) + 1) hradius hlarge'
  have := le_contourStateBound_of_nested_nodes data minimal nodes hnested
  omega

/-- Positive form: a larger target instance supplies an actual ordered mesh. -/
theorem exists_orderedMesh_of_large_card (data : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (a b : ℕ) (ha : 2 ≤ a) (hlarge : orderedMeshFreeVertexBound a b < Fintype.card V) :
    Nonempty (OrderedInjectiveMesh (toMultigraph data.toRotationSystem) a b) := by
  by_contra hno
  exact (Nat.not_lt_of_ge (vertex_card_le_of_no_orderedMesh data minimal a b ha hno)) hlarge

/-- Discharge the pre-existing wall-facing raw-decomposition premise. -/
theorem rawDecompositionOfNoOrderedInjectiveMesh (a b : ℕ) (ha : 2 ≤ a) :
    RawDecompositionOfNoOrderedInjectiveMesh.{u} a b (orderedMeshFreeVertexBound a b) := by
  intro V _ _ G _ data minimal hno
  classical
  letI : G.LocallyFinite := fun _ => Subtype.fintype _
  have hsize := vertex_card_le_of_no_orderedMesh data minimal a b ha hno
  have hthree : 3 ≤ Fintype.card G.edgeSet := by
    let v := data.toRotationSystem.vertOf data.toRotationSystem.outer
    have hc := incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      data minimal.spherical.cubic v
    exact hc ▸ Finset.card_le_univ (incidentEdgeFinset G v)
  obtain ⟨d⟩ := exists_rooted_decomposition hthree
  exact ⟨d, widthAtMost_of_card_le d _ hsize⟩

/-- The old headline now needs no separate decomposition supplier. -/
theorem combinatorialFourColorStatement_of_fixedOrderedMeshExclusion_and_base
    (a b : ℕ) (ha : 2 ≤ a)
    (exclude : FixedOrderedInjectiveMeshExclusion.{u} a b)
    (base : TaitBaseVerifiedAt.{u}
      (rawVertexBound (orderedMeshFreeVertexBound a b) (orderedMeshFreeVertexBound a b))) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  GoertzelV24OrderedInjectiveMeshWidthFactorization.combinatorialFourColorStatement_of_fixedOrderedMeshExclusion_and_base
    a b (orderedMeshFreeVertexBound a b) exclude
    (rawDecompositionOfNoOrderedInjectiveMesh a b ha) base

/-- Use the smaller direct base threshold; fixed exclusion and base remain open. -/
theorem combinatorialFourColorStatement_of_fixedOrderedMeshExclusion_and_direct_base
    (a b : ℕ) (ha : 2 ≤ a)
    (exclude : FixedOrderedInjectiveMeshExclusion.{u} a b)
    (base : TaitBaseVerifiedAt.{u} (orderedMeshFreeVertexBound a b)) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} := by
  apply GoertzelV24SphericalGraphPresentation.combinatorialFourColorStatement_iff_spherical.mpr
  apply GoertzelV24SphericalMinimalCounterexampleSelection.sphericalFourColorStatement_of_no_minimal
  intro V _ _ G _ data minimal
  classical
  letI : G.LocallyFinite := fun _ => Subtype.fintype _
  exact minimal.notColorable (base data minimal.toBridgelessSphericalCubicMapData
    (vertex_card_le_of_no_orderedMesh data minimal a b ha (exclude data minimal)))

end
end Mettapedia.GraphTheory.FourColor.SphericalOrderedMeshReduction
