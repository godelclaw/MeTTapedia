import Mettapedia.GraphTheory.FourColor.SphericalContourSeparators
import Mettapedia.GraphTheory.FourColor.VertexSplitPaths

/-!
# Construct a linkage or a complete ordered cut between spherical contours

Apply the finite vertex Menger construction to the entire mixed frontiers.
The large branch supplies vertex-disjoint ambient paths, including distinct
endpoints. The small branch supplies a vertex separator and then constructs
the connected shores, full crossing-edge and port bounds, and complementary
first-return boundary orders. Neither a linkage nor a separator is assumed.

This is the local alternative needed by the global contour/mesh argument.
Compatibility across multiple cuts and recursive seam accounting remain
separate geometric obligations.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalContourSeparators

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24DeletedRegionRotationSplice GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open VertexSeparatorBond VertexSplitCut

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The separator/linkage alternatives are derived from the actual carrier. -/
theorem exists_linkage_or_ordered_bond (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {i j : ℕ} (hij : i ≠ j)
    (hi : i < (orbitFaceDualGraph data).dist root far)
    (hj : j < (orbitFaceDualGraph data).dist root far) (k : ℕ) :
    Nonempty (Linkage G (frontier data root far i) (frontier data root far j) k) ∨
    ∃ deleted : Finset V,
      frontier data root far i ⊆ {v | deletedRegionKeep deleted v} ∧
      frontier data root far j ⊆ {v | ¬ deletedRegionKeep deleted v} ∧
      (G.induce {v | deletedRegionKeep deleted v}).Connected ∧
      (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected ∧
      (edgeBoundary G {v | deletedRegionKeep deleted v}).card ≤ 3 * (k - 1) ∧
      Fintype.card (BoundaryDart data.toRotationSystem (deletedRegionKeep deleted)) ≤ 3 * (k - 1) ∧
      CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem deleted ∧
      retainedRegionBoundarySuccessor data.toRotationSystem (deletedRegionKeep deleted) =
        (deletedRegionBoundarySuccessor data.toRotationSystem deleted)⁻¹ := by
  rcases exists_linkage_or_separator G (frontier data root far i) (frontier data root far j) k
    with hL | ⟨X, hcard, hX⟩
  · exact Or.inl hL
  · obtain ⟨deleted, hA, hB, hS, hSc, he, hp, hf, ho⟩ :=
      exists_ordered_bond_between_frontiers data hclass htwo root far hij hi hj X hX
    have hb : 3 * X.card ≤ 3 * (k - 1) := by omega
    exact Or.inr ⟨deleted, hA, hB, hS, hSc, he.trans hb, hp.trans hb, hf, ho⟩

end Mettapedia.GraphTheory.FourColor.SphericalContourSeparators
