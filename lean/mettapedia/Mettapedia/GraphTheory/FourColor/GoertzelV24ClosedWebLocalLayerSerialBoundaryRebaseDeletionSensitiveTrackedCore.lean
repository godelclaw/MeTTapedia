import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletionSensitivePortResidualFactorContraction

/-!
# The tracked Cell rebase core as an exact deletion-sensitive receipt

The cumulative tracked graph immediately before a Cell boundary rebase is not
stable under deleting the four named switch roles: an ordinary component
partition does not determine connectivity after graph vertices are removed.
The generic deletion-sensitive receipt therefore carries the exact residual
code after applying the current finite removal mask.

This file connects that generic correction to the literal source Cell.  With
all four rebase roles selected, restricting the pre-rebase tracked graph is
definitionally the tracked core already used by the successor recurrence.
Consequently the core receipt is not a new assumption or a parallel state: it
is the exact finite semantics of the boundary switch required by the source's
cumulative `Count` factorization.

No reachable closure, profile count, or Seed-Lemma conclusion is asserted
here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseDeletionSensitiveTrackedCore

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24FaceOrbitIncidence
open GoertzelV24CorridorProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance boundaryRebaseDeletionSensitiveTrackedCoreEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Every rebase role is selected by the literal Cell boundary switch. -/
def allBoundaryRebaseRolesRemoved :
    SourceLocalLayerBoundaryRebaseRole → Bool :=
  fun _ => true

/-- Surviving all selected rebase roles is exactly exclusion from the literal
four-role switch support. -/
theorem survivesMask_allBoundaryRebaseRolesRemoved_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (edge : G.edgeSet) :
    survivesMask
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
        allBoundaryRebaseRolesRemoved edge ↔
      edge ∉ sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset
        hnext := by
  rw [mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff]
  simp only [survivesMask, allBoundaryRebaseRolesRemoved, true_implies]
  constructor
  · intro hsurvives hexists
    obtain ⟨role, hrole⟩ := hexists
    exact hsurvives role hrole.symm
  · intro hnot role heq
    exact hnot ⟨role, heq.symm⟩

/-- The literal four-role removal of the cumulative pre-rebase tracked graph
is exactly the unchanged tracked core used by the successor recurrence. -/
theorem restrictedPreRebaseTrackedGraph_eq_coreTrackedGraphForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    restrictedByMask
        (regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          color (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
        allBoundaryRebaseRolesRemoved =
      coreTrackedGraphForColorAt corridor hunique offset hnext color pair := by
  ext left right
  simp only [restrictedByMask, supportRestriction_adj,
    regionalTrackedEdgeGraph, coreTrackedGraphForColorAt,
    sourceLocalLayerBoundaryRebaseFaceCoreRegionAt, Finset.mem_sdiff]
  rw [survivesMask_allBoundaryRebaseRolesRemoved_iff corridor hunique offset
    hnext left,
    survivesMask_allBoundaryRebaseRolesRemoved_iff corridor hunique offset
      hnext right]
  aesop

/-- The exact finite deletion-sensitive receipt for one literal tracked Cell
rebase and one arbitrary compatible colouring. -/
noncomputable def trackedDeletionSensitiveCoreReceiptForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    BoundedDeletionSensitivePortResidualCode
      SourceLocalLayerBoundaryRebaseRole (Fin 2) :=
  exactDeletionSensitivePortResidualCode
    (regionalTrackedEdgeGraph web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      color (trackedColorPairColors pair).1 (trackedColorPairColors pair).2)
    (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
    (sourceLocalLayerRightCrossingAt corridor hunique offset)
    allBoundaryRebaseRolesRemoved

/-- The generic deletion-sensitive receipt's core is literally the exact
supported residual code of the source-specific tracked rebase core. -/
theorem trackedDeletionSensitiveCoreReceiptForColorAt_core
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet → Color) (pair : TrackedColorPair) :
    (trackedDeletionSensitiveCoreReceiptForColorAt corridor hunique offset
      hnext color pair).core =
      GoertzelV24SimpleGraphSupportedPortResidualFactorContraction.exactSupportedPortResidualCode
        (coreTrackedGraphForColorAt corridor hunique offset hnext color pair)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
        (sourceLocalLayerRightCrossingAt corridor hunique offset) := by
  unfold trackedDeletionSensitiveCoreReceiptForColorAt
  change GoertzelV24SimpleGraphSupportedPortResidualFactorContraction.exactSupportedPortResidualCode
      (restrictedByMask
        (regionalTrackedEdgeGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          color (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
        allBoundaryRebaseRolesRemoved)
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext)
      (sourceLocalLayerRightCrossingAt corridor hunique offset) = _
  rw [restrictedPreRebaseTrackedGraph_eq_coreTrackedGraphForColorAt corridor
    hunique offset hnext color pair]

/-- At the ambient web colouring, the corrected generic receipt is exactly
the deletion-safe tracked core state already consumed by the literal rebase
recurrence.  Thus the correction changes the advertised finite input state,
not the source graph semantics or the proved successor closure. -/
theorem trackedDeletionSensitiveCoreReceiptForColorAt_ambient_core
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (pair : TrackedColorPair) :
    (trackedDeletionSensitiveCoreReceiptForColorAt corridor hunique offset
      hnext coloring pair).core =
      (sourceLocalLayerBoundaryRebaseTrackedCoreStateAt corridor hunique offset
        hnext).coreResidual pair := by
  rw [trackedDeletionSensitiveCoreReceiptForColorAt_core]
  rfl

end

end GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseDeletionSensitiveTrackedCore

end Mettapedia.GraphTheory.FourColor
