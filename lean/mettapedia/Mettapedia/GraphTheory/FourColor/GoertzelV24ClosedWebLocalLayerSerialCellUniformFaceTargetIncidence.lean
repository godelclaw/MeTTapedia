import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetState

/-!
# Oriented target incidences in the uniform facial carrier

The rolling target interface is obtained by forgetting coordinates from the
uniform Cell--rebase carrier.  Connectivity contraction alone does not say
where an oriented target face incidence enters the new strict exterior.  Its
endpoint has exactly two possible finite descriptions: it is either a
forgotten uniform coordinate, or it already lies in a strict-exterior
component of the uniform interface.

This file records that direction-sensitive entry and proves its literal
meaning.  It is the finite address needed before exterior face-length weights
can be contracted without observing the cumulative prefix again.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetIncidence

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceRecurrence
open GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetCode
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance uniformFaceTargetIncidenceEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance uniformFaceTargetIncidenceOpenedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- A live oriented target incidence enters either at a uniform coordinate
which the target forgets, or at an oriented strict-exterior incidence of the
uniform carrier. -/
abbrev SourceLocalLayerSerialCellRebaseUniformFaceTargetEntry
    (uniformCount : Nat) :=
  Fin uniformCount ⊕ (Fin uniformCount × Bool)

/-- Direction-sensitive finite address of one target facial incidence.

The outer guard is literal incidence presence.  When the exterior endpoint is
still represented by the uniform carrier, the left branch returns its
coordinate.  Otherwise the active target dart itself is represented in the
uniform carrier, and the right branch returns the corresponding oriented
uniform incidence. -/
noncomputable def sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card × Bool) :
    Option (SourceLocalLayerSerialCellRebaseUniformFaceTargetEntry
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card) := by
  classical
  let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
    hunique offset hnext
  let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    (sourceLocalLayerNextOffset offset hnext)
  let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
    corridor hunique offset hnext
  let targetDartAt := fun slot : Fin target.card =>
    ((carrierCoordinate target).symm slot).1
  let uniformDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
    corridor hunique offset hnext
  let outside := faceInterfaceIncidenceVertex web.annular.RS targetDartAt
    incidence
  if hpresent : ExteriorIncidencePresent graph targetDartAt Prod.fst
      (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) incidence then
    if houtsideUniform : outside ∈ uniform then
      exact some (.inl (carrierCoordinate uniform ⟨outside, houtsideUniform⟩))
    else
      have htargetSupport : targetDartAt incidence.1 ∈ graph.support :=
        (SimpleGraph.mem_support graph).2 ⟨outside, hpresent.2⟩
      have htargetUniform : targetDartAt incidence.1 ∈ uniform :=
        sourceLocalLayerSerialCellRebase_activeFaceTarget_mem_uniform graphData
          minimal caps coloring web corridor hunique offset hnext
            (targetDartAt incidence.1)
            ((carrierCoordinate target).symm incidence.1).2 htargetSupport
      exact some (.inr
        (carrierCoordinate uniform ⟨targetDartAt incidence.1, htargetUniform⟩,
          incidence.2))
  else
    exact none

/-- The entry decoder succeeds exactly for a live target incidence. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_isSome_iff
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card × Bool) :
    (sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt graphData minimal
      caps coloring web corridor hunique offset hnext incidence).isSome ↔
      let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
        hunique offset hnext
      let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
        hunique (sourceLocalLayerNextOffset offset hnext)
      let targetDartAt := fun slot : Fin target.card =>
        ((carrierCoordinate target).symm slot).1
      ExteriorIncidencePresent graph targetDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS targetDartAt) incidence := by
  classical
  unfold sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt
  dsimp only
  split <;> rename_i hpresent
  · split
    · constructor
      · intro _
        exact hpresent
      · intro _
        rfl
    · constructor
      · intro _
        exact hpresent
      · intro _
        rfl
  · simp [hpresent]

/-- A left-branch entry is literally the target incidence endpoint, and no
target coordinate is retained at that uniform slot. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_left
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card × Bool)
    (uniformSlot : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card)
    (hentry :
      sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt graphData minimal
        caps coloring web corridor hunique offset hnext incidence =
          some (.inl uniformSlot)) :
    let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique (sourceLocalLayerNextOffset offset hnext)
    let targetDartAt := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    sourceLocalLayerSerialCellRebaseUniformFaceDartAt corridor hunique offset
        hnext uniformSlot =
          faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence ∧
      ∀ targetSlot,
        sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt corridor
          hunique offset hnext targetSlot ≠ some uniformSlot := by
  classical
  dsimp only
  unfold sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt at hentry
  dsimp only at hentry
  split at hentry <;> rename_i hpresent
  · split at hentry <;> rename_i houtsideUniform
    · simp only [Option.some.injEq, Sum.inl.injEq] at hentry
      subst uniformSlot
      constructor
      · simp [sourceLocalLayerSerialCellRebaseUniformFaceDartAt]
      · intro targetSlot hsource
        have hdart :=
          sourceLocalLayerSerialCellRebaseUniformFaceTargetSourceAt_dart_eq
            corridor hunique offset hnext targetSlot
              (carrierCoordinate
                (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
                  corridor hunique offset hnext)
                ⟨faceInterfaceIncidenceVertex web.annular.RS
                    (fun slot : Fin
                      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor
                        hunique (sourceLocalLayerNextOffset offset hnext)).card =>
                      ((carrierCoordinate
                        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor
                          hunique (sourceLocalLayerNextOffset offset hnext))).symm
                            slot).1)
                    incidence,
                  houtsideUniform⟩)
              hsource
        exact hpresent.1 targetSlot (by
          simpa [sourceLocalLayerSerialCellRebaseUniformFaceDartAt] using
            hdart)
    · cases hentry
  · cases hentry

set_option maxHeartbeats 800000 in
/-- A right-branch entry is the corresponding live strict-exterior incidence
of the uniform carrier. -/
theorem sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt_right
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (incidence : Fin
      (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)).card × Bool)
    (uniformIncidence : Fin
      (sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt corridor
        hunique offset hnext).card × Bool)
    (hentry :
      sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt graphData minimal
        caps coloring web corridor hunique offset hnext incidence =
          some (.inr uniformIncidence)) :
    let graph := sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
      hunique offset hnext
    let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique (sourceLocalLayerNextOffset offset hnext)
    let targetDartAt := fun slot : Fin target.card =>
      ((carrierCoordinate target).symm slot).1
    let uniformDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
      corridor hunique offset hnext
    faceInterfaceIncidenceVertex web.annular.RS uniformDartAt uniformIncidence =
        faceInterfaceIncidenceVertex web.annular.RS targetDartAt incidence ∧
      ExteriorIncidencePresent graph uniformDartAt Prod.fst
        (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt)
        uniformIncidence := by
  classical
  dsimp only
  unfold sourceLocalLayerSerialCellRebaseUniformFaceTargetEntryAt at hentry
  dsimp only at hentry
  split at hentry <;> rename_i hpresent
  · split at hentry <;> rename_i houtsideUniform
    · cases hentry
    · simp only [Option.some.injEq, Sum.inr.injEq] at hentry
      subst uniformIncidence
      let target := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
        hunique (sourceLocalLayerNextOffset offset hnext)
      let uniform := sourceLocalLayerSerialCellRebaseFaceInteractionCarrierAt
        corridor hunique offset hnext
      let targetDartAt := fun slot : Fin target.card =>
        ((carrierCoordinate target).symm slot).1
      let uniformDartAt := sourceLocalLayerSerialCellRebaseUniformFaceDartAt
        corridor hunique offset hnext
      have hbase : uniformDartAt
          (carrierCoordinate uniform
            ⟨targetDartAt incidence.1,
              sourceLocalLayerSerialCellRebase_activeFaceTarget_mem_uniform
                graphData minimal caps coloring web corridor hunique offset
                  hnext (targetDartAt incidence.1)
                  ((carrierCoordinate target).symm incidence.1).2
                  ((SimpleGraph.mem_support
                    (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor
                      hunique offset hnext)).2
                    ⟨faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                        incidence,
                      hpresent.2⟩)⟩) =
            targetDartAt incidence.1 := by
        simp [uniformDartAt,
          sourceLocalLayerSerialCellRebaseUniformFaceDartAt, uniform]
      have hvertex :
          faceInterfaceIncidenceVertex web.annular.RS uniformDartAt
              (carrierCoordinate uniform
                ⟨targetDartAt incidence.1,
                  sourceLocalLayerSerialCellRebase_activeFaceTarget_mem_uniform
                    graphData minimal caps coloring web corridor hunique offset
                      hnext (targetDartAt incidence.1)
                      ((carrierCoordinate target).symm incidence.1).2
                      ((SimpleGraph.mem_support
                        (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt
                          corridor hunique offset hnext)).2
                        ⟨faceInterfaceIncidenceVertex web.annular.RS
                            targetDartAt incidence,
                          hpresent.2⟩)⟩,
                incidence.2) =
            faceInterfaceIncidenceVertex web.annular.RS targetDartAt
              incidence := by
        rcases incidence with ⟨slot, direction⟩
        cases direction <;> simp_all
      refine ⟨hvertex, ?_⟩
      unfold ExteriorIncidencePresent
      constructor
      · intro uniformSlot heq
        apply houtsideUniform
        have hmem : uniformDartAt uniformSlot ∈ uniform := by
          exact ((carrierCoordinate uniform).symm uniformSlot).2
        have heq' :
            faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                incidence = uniformDartAt uniformSlot :=
          hvertex.symm.trans heq
        rw [← heq'] at hmem
        exact hmem
      · have hadj := hpresent.2
        change
          (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
            offset hnext).Adj
              (targetDartAt incidence.1)
              (faceInterfaceIncidenceVertex web.annular.RS targetDartAt
                incidence) at hadj
        change
          (sourceLocalLayerBoundaryRebaseSuccessorFaceGraphAt corridor hunique
            offset hnext).Adj
              (uniformDartAt
                (carrierCoordinate uniform
                  ⟨targetDartAt incidence.1, _⟩))
              (faceInterfaceIncidenceVertex web.annular.RS uniformDartAt
                (carrierCoordinate uniform
                  ⟨targetDartAt incidence.1, _⟩, incidence.2))
        rw [hbase, hvertex]
        exact hadj
  · cases hentry

end

end GoertzelV24ClosedWebLocalLayerSerialCellUniformFaceTargetIncidence

end Mettapedia.GraphTheory.FourColor
