import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferCycle

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace GoertzelV24AdjacentPairInsertion.AdjacentPairData

open GoertzelV24AdjacentPairBoundary.AdjacentPairData
open GoertzelV24FourDefectBoundary.DegreeTwoBoundaryData

attribute [local instance]
  fusionFaceNetworkGraphEdgeSetDecidableEq
  fusionFaceNetworkRetainedVertexFintype
  fusionFaceNetworkRetainedVertexDecidableEq

variable {graphData : Data G}
  {minimal : GraphBackedVertexMinimalTaitCounterexample graphData}
  {baseData : AdjacentPairData G}

namespace ClosureRecoveryFaceTransferCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- At saturation, the restoring arc of a transfer is exactly the
localized loss arc of its position-monodromy successor. -/
theorem recoveryArc_eq_lossArc_positionMonodromy
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    (circuit.transferAt position).recovery.recoveryArc =
      (circuit.transferAt
        (circuit.positionMonodromy hminimal hlength position)).lossArc := by
  let current := circuit.transferAt position
  let matched := circuit.transferAt
    (circuit.positionMonodromy hminimal hlength position)
  have hposition : matched.lossPosition =
      current.recovery.restoringPosition := by
    simpa [matched, current, lossPositionAt, restoringPositionAt] using
      circuit.lossPositionAt_positionMonodromy hminimal hlength position
  change current.recovery.recoveryArc = matched.lossArc
  calc
    current.recovery.recoveryArc =
        (rebaseCircuit.first :: rebaseCircuit.rest).get
          current.recovery.restoringPosition :=
      current.recovery.get_restoringPosition.symm
    _ = (rebaseCircuit.first :: rebaseCircuit.rest).get
          matched.lossPosition := by rw [hposition]
    _ = matched.lossArc := matched.get_lossPosition

/-- The shared gain/loss arc is selected on the matched transfer's source
face, equivalently on the current transfer's target face. -/
theorem selectedFace_recoveryArc_eq_sourceFace_positionMonodromy
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    (circuit.transferAt position).recovery.recoveryArc.selectedFace =
      (circuit.transferAt
        (circuit.positionMonodromy hminimal hlength position)).recovery.sourceFace := by
  rw [circuit.recoveryArc_eq_lossArc_positionMonodromy hminimal hlength]
  exact (circuit.transferAt
    (circuit.positionMonodromy hminimal hlength position)).lossArc_selectedFace

/-- The current transfer's code is gained across the shared saturated
arc. -/
theorem currentCode_gain_across_recoveryArc
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    let current := circuit.transferAt position
    current.recovery.edge.1 ∉
        current.recovery.channel.edges current.recovery.recoveryArc.source ∧
      current.recovery.edge.1 ∈
        current.recovery.channel.edges current.recovery.recoveryArc.target := by
  exact ⟨(circuit.transferAt position).recovery.edge_not_mem_recoverySource,
    (circuit.transferAt position).recovery.edge_mem_recoveryTarget⟩

/-- The monodromy successor's code is lost across that same saturated
arc. -/
theorem matchedCode_loss_across_recoveryArc
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    let current := circuit.transferAt position
    let matched := circuit.transferAt
      (circuit.positionMonodromy hminimal hlength position)
    matched.recovery.edge.1 ∈
        matched.recovery.channel.edges current.recovery.recoveryArc.source ∧
      matched.recovery.edge.1 ∉
        matched.recovery.channel.edges current.recovery.recoveryArc.target := by
  let current := circuit.transferAt position
  let matched := circuit.transferAt
    (circuit.positionMonodromy hminimal hlength position)
  have harc : current.recovery.recoveryArc = matched.lossArc :=
    circuit.recoveryArc_eq_lossArc_positionMonodromy
      hminimal hlength position
  change matched.recovery.edge.1 ∈
      matched.recovery.channel.edges current.recovery.recoveryArc.source ∧
    matched.recovery.edge.1 ∉
      matched.recovery.channel.edges current.recovery.recoveryArc.target
  rw [harc]
  exact ⟨matched.edge_mem_lossSource, matched.edge_not_mem_lossTarget⟩

/-- The gained support edge lies on the selected face of the shared
rebase arc. -/
theorem currentEdge_mem_recoveryArc_selectedFace
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    (circuit.transferAt position).recovery.edge ∈
      orbitFaceBoundary graphData.toRotationSystem
        (circuit.transferAt position).recovery.recoveryArc.selectedFace := by
  rw [(circuit.transferAt position).recovery.recoveryArc_selectedFace]
  exact (circuit.transferAt position).recovery.edge_mem_targetFace

/-- The support edge lost at a saturated shared arc lies off that arc's
selected face. -/
theorem matchedEdge_not_mem_recoveryArc_selectedFace
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    (circuit.transferAt
        (circuit.positionMonodromy hminimal hlength position)).recovery.edge ∉
      orbitFaceBoundary graphData.toRotationSystem
        (circuit.transferAt position).recovery.recoveryArc.selectedFace := by
  let matched := circuit.transferAt
    (circuit.positionMonodromy hminimal hlength position)
  have hface := circuit.selectedFace_recoveryArc_eq_sourceFace_positionMonodromy
    hminimal hlength position
  change matched.recovery.edge ∉ orbitFaceBoundary
    graphData.toRotationSystem
      (circuit.transferAt position).recovery.recoveryArc.selectedFace
  rw [hface]
  exact matched.recovery.edge_not_mem_sourceFace

/-- Hence the gained and lost edges of a saturated local support swap are
different, independently of their closure channels. -/
theorem currentEdge_ne_matchedEdge
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    (circuit.transferAt position).recovery.edge ≠
      (circuit.transferAt
        (circuit.positionMonodromy hminimal hlength position)).recovery.edge := by
  intro hedge
  apply circuit.matchedEdge_not_mem_recoveryArc_selectedFace
    hminimal hlength position
  rw [← hedge]
  exact circuit.currentEdge_mem_recoveryArc_selectedFace position

/-- Consequently the finite recovery codes on the two sides of a
saturated local support swap are different. -/
theorem currentCode_ne_matchedCode
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    (circuit.transferAt position).recovery.code ≠
      (circuit.transferAt
        (circuit.positionMonodromy hminimal hlength position)).recovery.code := by
  intro hcode
  exact circuit.currentEdge_ne_matchedEdge hminimal hlength position
    (congrArg Prod.snd hcode)

/-- At saturation, every displayed rebase position has a unique transfer
whose localized loss occurs there. -/
theorem existsUnique_lossPositionAt_eq
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin rebaseCircuit.arcLength) :
    ∃! transferPosition : Fin circuit.arcLength,
      circuit.lossPositionAt transferPosition = position := by
  rcases hminimal.lossPositionAt_bijective_of_arcLength_eq hlength with
    ⟨hinjective, hsurjective⟩
  rcases hsurjective position with ⟨transferPosition, hposition⟩
  exact ⟨transferPosition, hposition,
    fun other hother => hinjective (hother.trans hposition.symm)⟩

/-- At saturation, every displayed rebase position also has a unique
transfer whose restoring gain occurs there. -/
theorem existsUnique_restoringPositionAt_eq
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin rebaseCircuit.arcLength) :
    ∃! transferPosition : Fin circuit.arcLength,
      circuit.restoringPositionAt transferPosition = position := by
  rcases hminimal.restoringPositionAt_bijective_of_arcLength_eq hlength with
    ⟨hinjective, hsurjective⟩
  rcases hsurjective position with ⟨transferPosition, hposition⟩
  exact ⟨transferPosition, hposition,
    fun other hother => hinjective (hother.trans hposition.symm)⟩

/-- Thus every displayed rebase position realizes one gain transfer and
one different loss transfer. -/
theorem exists_distinct_gain_loss_transferPositions
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin rebaseCircuit.arcLength) :
    ∃ gainPosition lossPosition : Fin circuit.arcLength,
      circuit.restoringPositionAt gainPosition = position ∧
        circuit.lossPositionAt lossPosition = position ∧
        gainPosition ≠ lossPosition := by
  rcases circuit.existsUnique_restoringPositionAt_eq hminimal hlength
      position with ⟨gainPosition, hgain, _⟩
  rcases circuit.existsUnique_lossPositionAt_eq hminimal hlength position with
    ⟨lossPosition, hloss, _⟩
  refine ⟨gainPosition, lossPosition, hgain, hloss, ?_⟩
  intro heq
  subst lossPosition
  exact circuit.lossPositionAt_ne_restoringPositionAt gainPosition
    (hloss.trans hgain.symm)

end ClosureRecoveryFaceTransferCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
