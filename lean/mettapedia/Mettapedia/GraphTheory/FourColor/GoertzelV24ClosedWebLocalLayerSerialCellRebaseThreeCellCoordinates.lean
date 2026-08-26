import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellRebaseSuccessorCoordinates

/-!
# The literal three-Cell coordinate window

Strict historical locality reduces every surviving facial-collar alias to the
immediate predecessor Cell.  This file aligns that predecessor with the
current source witness, so the predecessor--current and current--successor rail
shapes can be inspected in one bounded window.

Only dependent-coordinate alignment is proved here.  The following module may
case-split the two retained `SourceLocalRailShape` certificates without making
another witness choice.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace Instance

namespace LocalLayerFormation

/-- A serial successor computed from an index whose value is one below the
current index is literally the current index. -/
theorem sourceLocalLayerNextOffset_eq_of_val_add_one_eq
    {blockLength : Nat}
    (prior offset : Fin (blockLength - 3))
    (hnext : prior.val + 1 < blockLength - 3)
    (heq : prior.val + 1 = offset.val) :
    sourceLocalLayerNextOffset prior hnext = offset := by
  apply Fin.ext
  exact heq

/-- The independently selected source witnesses at an immediate predecessor
and the current Cell carry one literal successor package, with all four flank
edges identified in the serial coordinates. -/
theorem exists_sourceLocalLayerSerialCellRebase_predecessor_coordinates
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (prior offset : Fin (blockLength - 3))
    (heq : prior.val + 1 = offset.val) :
    ∃ hpriorNext : prior.val + 1 < blockLength - 3,
      let target := sourceLocalLayerNextOffset prior hpriorNext
      let priorWitness := localLayerPairWitnessOfCorridor corridor hunique
        (sourceLocalLayerInteriorAt prior)
        (sourceLocalLayerInteriorAt_hasNext prior)
      let currentWitness := localLayerPairWitnessOfCorridor corridor hunique
        (sourceLocalLayerInteriorAt target)
        (sourceLocalLayerInteriorAt_hasNext target)
      target = offset ∧
        ∃ successor : SourceLocalRailSuccessor
            (sourceLocalLayerInteriorAt_hasNext prior)
            priorWitness.placement priorWitness.before priorWitness.after
            priorWitness.outgoing_after_before priorWitness.after_after_outgoing
            currentWitness.placement,
          successor.rightOutgoingBefore = currentWitness.before ∧
            successor.rightOutgoingAfter = currentWitness.after ∧
            web.annular.RS.edgeOf
                (faceCycleDart web.annular.RS currentWitness.placement.root
                  successor.rightBefore.1) =
              sourceLocalLayerRightCrossingAt corridor hunique prior
                (0 : Fin 2) ∧
            web.annular.RS.edgeOf
                (faceCycleDart web.annular.RS currentWitness.placement.root
                  successor.rightAfter.1) =
              sourceLocalLayerRightCrossingAt corridor hunique prior
                (1 : Fin 2) ∧
            web.annular.RS.edgeOf
                (faceCycleDart web.annular.RS currentWitness.placement.root
                  successor.rightOutgoingBefore.1) =
              sourceLocalLayerLeftCrossingAt corridor hunique target
                (0 : Fin 2) ∧
            web.annular.RS.edgeOf
                (faceCycleDart web.annular.RS currentWitness.placement.root
                  successor.rightOutgoingAfter.1) =
              sourceLocalLayerLeftCrossingAt corridor hunique target
                (1 : Fin 2) := by
  have hpriorNext : prior.val + 1 < blockLength - 3 := by
    rw [heq]
    exact offset.isLt
  have htarget : sourceLocalLayerNextOffset prior hpriorNext = offset :=
    sourceLocalLayerNextOffset_eq_of_val_add_one_eq prior offset hpriorNext heq
  refine ⟨hpriorNext, ?_⟩
  dsimp only
  exact ⟨htarget,
    exists_sourceLocalLayerSerialCellRebase_successor_coordinates corridor
      hunique prior hpriorNext⟩

/-- One immediate historical predecessor, the current Cell, and its successor
are controlled by two retained rail-shape certificates.  Thus every remaining
locality argument is a finite product of the three one-Cell shapes. -/
theorem exists_sourceLocalLayerSerialCellRebase_threeCell_window
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (prior offset : Fin (blockLength - 3))
    (heq : prior.val + 1 = offset.val)
    (hnext : offset.val + 1 < blockLength - 3) :
    ∃ hpriorNext : prior.val + 1 < blockLength - 3,
      let current := sourceLocalLayerNextOffset prior hpriorNext
      let priorWitness := localLayerPairWitnessOfCorridor corridor hunique
        (sourceLocalLayerInteriorAt prior)
        (sourceLocalLayerInteriorAt_hasNext prior)
      let computedCurrentWitness := localLayerPairWitnessOfCorridor corridor
        hunique (sourceLocalLayerInteriorAt current)
          (sourceLocalLayerInteriorAt_hasNext current)
      let currentWitness := localLayerPairWitnessOfCorridor corridor hunique
        (sourceLocalLayerInteriorAt offset)
        (sourceLocalLayerInteriorAt_hasNext offset)
      let target := sourceLocalLayerNextOffset offset hnext
      let targetWitness := localLayerPairWitnessOfCorridor corridor hunique
        (sourceLocalLayerInteriorAt target)
        (sourceLocalLayerInteriorAt_hasNext target)
      current = offset ∧
        Nonempty (SourceLocalRailSuccessor
          (sourceLocalLayerInteriorAt_hasNext prior)
          priorWitness.placement priorWitness.before priorWitness.after
          priorWitness.outgoing_after_before priorWitness.after_after_outgoing
          computedCurrentWitness.placement) ∧
        Nonempty (SourceLocalRailSuccessor
          (sourceLocalLayerInteriorAt_hasNext offset)
          currentWitness.placement currentWitness.before currentWitness.after
          currentWitness.outgoing_after_before currentWitness.after_after_outgoing
          targetWitness.placement) := by
  rcases exists_sourceLocalLayerSerialCellRebase_predecessor_coordinates
      corridor hunique prior offset heq with
    ⟨hpriorNext, hcurrent, predecessorSuccessor,
      _predecessorCoordinates⟩
  rcases exists_sourceLocalLayerSerialCellRebase_successor_coordinates
      corridor hunique offset hnext with
    ⟨successor, _successorCoordinates⟩
  refine ⟨hpriorNext, ?_⟩
  dsimp only
  exact ⟨hcurrent, ⟨predecessorSuccessor⟩, ⟨successor⟩⟩

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
