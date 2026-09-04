import Mettapedia.GraphTheory.FourColor.Compositional.CoherentResidualReturnSweep
import Mettapedia.GraphTheory.FourColor.Compositional.FullProfileGeometricAlternative

/-!
# Complete-profile compression on coherent deletion sweeps

The sparse deletion atlas already chooses two common-core-compatible
colourings with one absent colour.  This module upgrades both unchanged
geometric sweep receipts to the complete-profile single-site alternative.
No witness is reselected, so the connectivity comparison between the two
deletion states remains available downstream.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CoherentFullProfileSweep

open CoherentResidualReturnSweep
open AlternatingSiteGeometry
open DeletionAtlasPath
open DeletionColorMatching
open DeletionPathConnectivity
open DeletionPathLocalization
open DeletionSiteGeometry
open FullProfileGeometricAlternative
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairColoringAtlas.PairDeletionColoringFamily
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24ResidualDefectDescent
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open Mettapedia.Logic
open SparseNoncentralMeshAtlas
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- One deletion-colouring sweep with the ambient shallow branch eliminated
by complete Count profiles. -/
structure DeletionFullProfileSweepReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (minimizer : ResidualDefectMinimizer G)
    (data : AdjacentPairData G)
    (state : DeletionMatchingState data) where
  base : DeletionGeometricSweepReceipt rotation minimal minimizer data state
  alternative : ∀ depth spacing : Nat,
    2 * (spacing + 1) * (1 + 1) ^ 2 <
        base.base.base.base.bond.site.cycle.tail.support.length →
      FullProfileStrictFamilyAlternative rotation minimal
        (cubicIncidentEdgeTriples rotation minimal) minimizer.pairing
        minimizer.supported base.base.base.base.bond depth spacing

/-- Upgrade one deletion receipt without reselecting its physical data. -/
def DeletionFullProfileSweepReceipt.ofGeometric
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (minimizer : ResidualDefectMinimizer G)
    (data : AdjacentPairData G)
    (state : DeletionMatchingState data)
    (receipt : DeletionGeometricSweepReceipt
      rotation minimal minimizer data state) :
    DeletionFullProfileSweepReceipt rotation minimal minimizer data state where
  base := receipt
  alternative := fun depth spacing hmany =>
    hasFullProfileStrictFamilyAlternative rotation minimal
      (cubicIncidentEdgeTriples rotation minimal) minimizer.pairing
      minimizer.supported receipt.base.base.base.bond depth spacing hmany

/-- The coherent atlas pair with both endpoint sweeps upgraded and all
original path, colour, and connectivity provenance retained in `base`. -/
structure CoherentFullProfileSweepPairReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G) where
  base : CoherentGeometricSweepPairReceipt rotation minimal family minimizer
  firstSweep : Nonempty (DeletionFullProfileSweepReceipt rotation minimal
    minimizer (family.data base.first)
    (matchingState rotation minimal family base.pathSection base.first))
  secondSweep : Nonempty (DeletionFullProfileSweepReceipt rotation minimal
    minimizer (family.data base.second)
    (matchingState rotation minimal family base.pathSection base.second))

/-- Upgrade a coherent geometric pair pointwise, retaining the same
colourings and common-core path. -/
theorem nonempty_fullProfilePair_of_geometricPair
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (pair : CoherentGeometricSweepPairReceipt
      rotation minimal family minimizer) :
    Nonempty (CoherentFullProfileSweepPairReceipt
      rotation minimal family minimizer) := by
  rcases pair.firstSweep with ⟨firstSweep⟩
  rcases pair.secondSweep with ⟨secondSweep⟩
  exact ⟨{
    base := pair
    firstSweep := ⟨DeletionFullProfileSweepReceipt.ofGeometric rotation minimal
      minimizer (family.data pair.first)
        (matchingState rotation minimal family pair.pathSection pair.first)
        firstSweep⟩
    secondSweep := ⟨DeletionFullProfileSweepReceipt.ofGeometric rotation minimal
      minimizer (family.data pair.second)
        (matchingState rotation minimal family pair.pathSection pair.second)
        secondSweep⟩ }⟩

variable {a : Nat}

/-- On a sparse row atlas, either the existing branching/boundary horn is
visible or the coherent pair carries complete-profile alternatives at both
of its unchanged deletion coordinates. -/
theorem branchingOrBoundary_or_hasCoherentFullProfileSweepPair
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G) (row : Fin a) :
    (∃ assignment : TaitAssignment
        (coloringFamily rotation minimal ordered minimizer row),
      HasBranchingOrBoundary
        (coloringFamily rotation minimal ordered minimizer row) assignment) ∨
      Nonempty (CoherentFullProfileSweepPairReceipt rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer) := by
  rcases branchingOrBoundary_or_hasCoherentGeometricSweepPair rotation minimal
      ordered minimizer row with hhorn | hpair
  · exact Or.inl hhorn
  · rcases hpair with ⟨pair⟩
    exact Or.inr
      (nonempty_fullProfilePair_of_geometricPair rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer pair)

end

end CoherentFullProfileSweep

end Mettapedia.GraphTheory.FourColor.Compositional
