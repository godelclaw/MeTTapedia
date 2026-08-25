import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric

/-!
# A colouring-parametric supported boundary-rebase letter

The literal Cell may carry a colouring different from the accumulated ambient
prefix.  The preceding modules exposed the boundary-rebase tracked closure and
complete successor decoder at an arbitrary colour function.  Here they are
assembled into the executable finite support relation used by the source
serial word.

The input endpoint remains explicit: the rebase support predicate certifies
the bounded collar and its exact successor decoder, while the following
Cell--rebase composition theorem supplies the actual spliced pre-rebase input.
No reachable closure or converse source-realizability claim is made here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSupportColorParametric

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolOutput
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolReceipt
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseOutputColorParametric
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedColorParametric
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24WindingClassification
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance boundaryRebaseSupportColorParametricEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

private theorem boundaryRebaseEdgeAt_mem_trackedCollar
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (role : SourceLocalLayerBoundaryRebaseRole) :
    sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role ∈
      sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
        hnext := by
  apply (web.annular.RS.mem_edgeAdjacencyClosedCarrier_iff _ _).2
  exact Or.inl
    ((mem_sourceLocalLayerBoundaryRebaseSwitchAt_iff corridor hunique offset
      hnext _).2 ⟨role, rfl⟩)

private theorem trackedCollarCodeForColorAt_point_role
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (color : G.edgeSet -> Color)
    (role : SourceLocalLayerBoundaryRebaseRole) :
    (ofGraphFamilyCode
      (trackedCollarCodeForColorAt corridor hunique offset hnext color)).point
        (sourceLocalLayerBoundaryRebaseRoleEquivFin role) =
      carrierCoordinate
        (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
          hnext)
        ⟨sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role,
          boundaryRebaseEdgeAt_mem_trackedCollar corridor hunique offset hnext
            role⟩ := by
  change
    carrierCoordinate
        (sourceLocalLayerBoundaryRebaseTrackedCollarAt corridor hunique offset
          hnext)
        (sourceLocalLayerBoundaryRebaseTrackedCollarPointAt corridor hunique
          offset hnext (sourceLocalLayerBoundaryRebaseRoleEquivFin role)) = _
  apply congrArg
  apply Subtype.ext
  simp [sourceLocalLayerBoundaryRebaseTrackedCollarPointAt]

/-- Complete finite rebase data at an arbitrary local colouring and an
explicit predecessor endpoint. -/
noncomputable def finiteBoolSupportLetterForColorAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (input : BoundedCorridorCutProfile 2 0 4)
    (color : G.edgeSet -> Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0) : SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter where
  input := input
  output := terminalInputBoundedProfileForColorAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext) color
      (successorCrossingNonzeroForColorAt corridor hunique offset hnext color
        hrole)
  trackedCode := ofGraphFamilyCode
    (trackedCollarCodeForColorAt corridor hunique offset hnext color)
  outputCode := finiteBoolOutputLetterCodeForColorAt corridor hunique offset
    hnext color hrole

/-- Every literal rebase collar is supported at the supplied colouring.  The
tracked clause is the exact two-factor closure theorem; the facial clauses are
the already proved occurrence-sensitive receipt and therefore do not change
with colours. -/
theorem finiteBoolSupportLetterForColorAt_supports
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (input : BoundedCorridorCutProfile 2 0 4)
    (color : G.edgeSet -> Color)
    (hrole : ∀ role, color
      (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext role) ≠
        0) :
    SourceLocalLayerBoundaryRebaseFiniteSupportsBool
      (finiteBoolSupportLetterForColorAt corridor hunique offset hnext input
        color hrole) = true := by
  have hambient :=
    sourceLocalLayerBoundaryRebaseFiniteBoolSupportLetterAt_supports corridor
      hunique offset hnext
  rw [SourceLocalLayerBoundaryRebaseFiniteSupportsBool, decide_eq_true_eq] at hambient
  dsimp only [sourceLocalLayerBoundaryRebaseFiniteBoolSupportLetterAt] at hambient
  rw [SourceLocalLayerBoundaryRebaseFiniteSupportsBool, decide_eq_true_eq]
  dsimp only [finiteBoolSupportLetterForColorAt]
  refine ⟨
    (finiteBoolOutputLetterCodeForColorAt_outputProfile_eq corridor hunique
      offset hnext color hrole).symm, ?_, ?_, ?_⟩
  · intro pair left right
    apply Bool.eq_iff_iff.mpr
    simp only [trackedConnectedBool_eq_true_iff,
      SourceLocalLayerBoundaryRebaseTrackedClosureConnectedBool,
      Bool.and_eq_true, decide_eq_true_eq]
    rw [trackedCollarCodeForColorAt_point_role,
      trackedCollarCodeForColorAt_point_role,
      trackedFiniteClosureBool_ofGraphFamilyCode_eq_true_iff]
    rw [← successorTrackedForColor_reachable_iff_collarCode corridor hunique
      offset hnext color pair
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseEdgeAt corridor hunique offset hnext
          right)
        (boundaryRebaseEdgeAt_mem_trackedCollar corridor hunique offset hnext
          left)
        (boundaryRebaseEdgeAt_mem_trackedCollar corridor hunique offset hnext
          right)]
    dsimp only [finiteBoolOutputLetterCodeForColorAt]
    rw [successorTrackedStateForColorAt_connected_iff,
      regionalTrackedConnectivity_eq_true_iff]
    simp only [decide_eq_true_eq, strandColorOfNonzero_toColor,
      successorTrackedStateForColorAt, successorTrackedGraphForColorAt]
    simp only [and_assoc]
  · simpa only [finiteBoolOutputLetterCodeForColorAt,
      SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode.outputFaceSlot]
      using hambient.2.2.1
  · simpa only [finiteBoolOutputLetterCodeForColorAt,
      SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode.outputFaceSlot]
      using hambient.2.2.2

end

end GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseSupportColorParametric

end Mettapedia.GraphTheory.FourColor
