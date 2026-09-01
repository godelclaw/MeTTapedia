import Mettapedia.GraphTheory.FourColor.Compositional.AmbientReturnAttachmentCompression
import Mettapedia.GraphTheory.FourColor.Compositional.DeletionPathConnectivity
import Mettapedia.GraphTheory.FourColor.Compositional.SparseNoncentralMeshAtlas

/-!
# Geometric sweeps on a coherent pair of deletion colorings

The sparse deletion atlas supplies two coordinates whose deletion colorings
belong to one common-core-compatible path and omit the same Tait color.  The
local residual-return development separately supplies finite geometric sweep
alternatives for any complete two-sector receipt.

This module joins those interfaces without changing either choice.  Thus the
two sweep alternatives retain the coherent deletion colorings selected by the
atlas, instead of replacing them by unrelated pointwise witnesses.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace CoherentResidualReturnSweep

open AmbientReturnAttachmentCompression
open AlternatingSiteGeometry
open DeletionAtlasPath
open DeletionColorMatching
open DeletionPathConnectivity
open DeletionPathLocalization
open DeletionSiteGeometry
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

/-- A two-sector receipt from an arbitrary deletion coloring, together with
the fully compressed geometric alternative on its unchanged physical site. -/
structure DeletionGeometricSweepReceipt
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (minimizer : ResidualDefectMinimizer G)
    (data : AdjacentPairData G)
    (state : DeletionMatchingState data) where
  base : DeletionTwoSectorReturnReceipt
    rotation minimal minimizer data state
  alternative : ∀ depth spacing : Nat,
    2 * (spacing + 1) * (1 + 1) ^ 2 <
        base.base.base.bond.site.cycle.tail.support.length →
      FullyCompressedGeometricAlternative rotation minimal
        (cubicIncidentEdgeTriples rotation minimal) minimizer.pairing
        minimizer.supported base.base.base.bond depth spacing

/-- Add both-coordinate compression to an existing deletion-coloring receipt
without reselecting its coloring, matching, alternating site, or facial bond. -/
def DeletionGeometricSweepReceipt.ofTwoSector
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (minimizer : ResidualDefectMinimizer G)
    (data : AdjacentPairData G)
    (state : DeletionMatchingState data)
    (receipt : DeletionTwoSectorReturnReceipt
      rotation minimal minimizer data state) :
    DeletionGeometricSweepReceipt
      rotation minimal minimizer data state where
  base := receipt
  alternative := fun depth spacing hmany =>
    hasFullyCompressedGeometricAlternative rotation minimal
      (cubicIncidentEdgeTriples rotation minimal) minimizer.pairing
      minimizer.supported receipt.base.base.bond depth spacing hmany

/-- The coherent atlas outcome with both selected coordinates upgraded to
their fully compressed residual-return sweep alternatives. -/
def HasCoherentGeometricSweepPair
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G) : Prop :=
  ∃ pathSection : PathConstraint.Section
      (fun index : Fin 9 => TaitColoringAt family index)
      (ConsecutiveRepairCompatible family),
    pathSection.state (Fin.last 8) =
        (baseAssignment family) (Fin.last 8) ∧
      ∃ first second : Fin 9, first ≠ second ∧
        (matchingState rotation minimal family pathSection first).absentColor =
          (matchingState rotation minimal family pathSection second).absentColor ∧
        Nonempty (DeletionGeometricSweepReceipt rotation minimal minimizer
          (family.data first)
          (matchingState rotation minimal family pathSection first)) ∧
        Nonempty (DeletionGeometricSweepReceipt rotation minimal minimizer
          (family.data second)
          (matchingState rotation minimal family pathSection second)) ∧
        (SimpleGraph.edgeDisagreementFinset
          (pathAlternatingGraph rotation minimal family pathSection minimizer
            first)
          (pathAlternatingGraph rotation minimal family pathSection minimizer
            second)).card ≤ 45

/-- Upgrade the two coherent two-sector receipts supplied by the deletion
atlas while retaining its path, terminal state, coordinates, and common
absent color. -/
theorem hasCoherentGeometricSweepPair_of_twoSectorPair
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (family : PairDeletionColoringFamily (G := G) (Fin 9))
    (minimizer : ResidualDefectMinimizer G)
    (hpair : HasCoherentTwoSectorPair rotation minimal family minimizer) :
    HasCoherentGeometricSweepPair rotation minimal family minimizer := by
  rcases hpair with
    ⟨pathSection, hterminal, first, second, hne, hcolor,
      ⟨firstReceipt⟩, ⟨secondReceipt⟩⟩
  refine ⟨pathSection, hterminal, first, second, hne, hcolor,
    ⟨DeletionGeometricSweepReceipt.ofTwoSector rotation minimal minimizer
      (family.data first)
      (matchingState rotation minimal family pathSection first)
      firstReceipt⟩,
    ⟨DeletionGeometricSweepReceipt.ofTwoSector rotation minimal minimizer
      (family.data second)
      (matchingState rotation minimal family pathSection second)
      secondReceipt⟩, ?_⟩
  simpa only [pathAlternatingGraph] using
    (card_alternatingGraph_edgeDisagreement_le rotation minimal family
      pathSection minimizer.pairing minimizer.supported first second hcolor)

variable {a : Nat}

/-- **Coherent mesh-sweep alternative.**  On a sparse row atlas, either a
branching/boundary horn is already exposed, or two common-core-compatible
deletion colorings with the same absent color both carry the complete finite
geometric sweep alternative. -/
theorem branchingOrBoundary_or_hasCoherentGeometricSweepPair
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (ordered : OrderedInjectiveMesh
      (toMultigraph rotation.toRotationSystem) a 20)
    (minimizer : ResidualDefectMinimizer G) (row : Fin a) :
    (∃ assignment : TaitAssignment
        (coloringFamily rotation minimal ordered minimizer row),
      HasBranchingOrBoundary
        (coloringFamily rotation minimal ordered minimizer row) assignment) ∨
      HasCoherentGeometricSweepPair rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer := by
  rcases branchingOrBoundary_or_hasCoherentTwoSectorPair
      rotation minimal ordered minimizer row with hhorn | hpair
  · exact Or.inl hhorn
  · exact Or.inr
      (hasCoherentGeometricSweepPair_of_twoSectorPair rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer hpair)

end

end CoherentResidualReturnSweep

end Mettapedia.GraphTheory.FourColor.Compositional
