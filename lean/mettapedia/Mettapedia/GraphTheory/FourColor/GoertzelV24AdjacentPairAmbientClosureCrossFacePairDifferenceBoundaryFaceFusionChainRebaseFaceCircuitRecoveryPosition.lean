import Mathlib.Data.List.Rotate
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryCycle

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

namespace ClosureRecoveryFaceArc

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The first displayed position of the restoring rebase arc. -/
noncomputable def restoringPosition
    (arc : ClosureRecoveryFaceArc rebaseCircuit) :
    Fin rebaseCircuit.arcLength := by
  classical
  exact ⟨(rebaseCircuit.first :: rebaseCircuit.rest).idxOf arc.recoveryArc,
    by
      rw [CrossCentralExactFaceCertifiedRebaseCircuit.arcLength]
      exact List.idxOf_lt_length_iff.mpr arc.recoveryArc_mem_displayed⟩

/-- Reading the underlying rebase circuit at the stored position recovers
the concrete restoring arc. -/
@[simp] theorem get_restoringPosition
    (arc : ClosureRecoveryFaceArc rebaseCircuit) :
    (rebaseCircuit.first :: rebaseCircuit.rest).get
      arc.restoringPosition = arc.recoveryArc := by
  classical
  apply List.idxOf_get

/-- The face selected at the restoring position is the dependency target
face. -/
@[simp] theorem selectedFace_get_restoringPosition
    (arc : ClosureRecoveryFaceArc rebaseCircuit) :
    ((rebaseCircuit.first :: rebaseCircuit.rest).get
      arc.restoringPosition).selectedFace = arc.targetFace := by
  rw [arc.get_restoringPosition]
  exact arc.recoveryArc_selectedFace

end ClosureRecoveryFaceArc

namespace ClosureRecoveryFaceCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- The cyclic target-face list of a concrete recovery circuit. -/
def targetFaces (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    List (OrbitFace graphData.toRotationSystem) :=
  (circuit.first :: circuit.rest).map ClosureRecoveryFaceArc.targetFace

private theorem map_targetFace_eq_map_sourceFace_tail_append
    (first : ClosureRecoveryFaceArc rebaseCircuit)
    (rest : List (ClosureRecoveryFaceArc rebaseCircuit))
    (endFace : OrbitFace graphData.toRotationSystem)
    (consecutive : List.IsChain ClosureRecoveryFaceArc.Follows
      (first :: rest))
    (lastTarget :
      ((first :: rest).getLast (by simp)).targetFace = endFace) :
    (first :: rest).map ClosureRecoveryFaceArc.targetFace =
      rest.map ClosureRecoveryFaceArc.sourceFace ++ [endFace] := by
  induction rest generalizing first with
  | nil =>
      simpa using lastTarget
  | cons second rest ih =>
      have hparts := List.isChain_cons_cons.mp consecutive
      have hlast :
          ((second :: rest).getLast (by simp)).targetFace = endFace := by
        simpa only [List.getLast_cons_cons] using lastTarget
      rw [List.map_cons, hparts.1]
      rw [ih second hparts.2 hlast]
      simp

/-- Target faces are the one-step cyclic rotation of source faces. -/
theorem targetFaces_eq_sourceFaces_rotate_one
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    circuit.targetFaces = circuit.sourceFaces.rotate 1 := by
  have hclosing :
      (((circuit.first :: circuit.rest).getLast (by simp)).targetFace) =
        circuit.first.sourceFace := by
    exact circuit.closing
  rw [targetFaces, sourceFaces]
  rw [map_targetFace_eq_map_sourceFace_tail_append circuit.first
    circuit.rest circuit.first.sourceFace circuit.consecutive hclosing]
  simp

/-- Source and target faces carry the same cyclic multiset. -/
theorem targetFaces_perm_sourceFaces
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    circuit.targetFaces.Perm circuit.sourceFaces := by
  rw [circuit.targetFaces_eq_sourceFaces_rotate_one]
  exact List.rotate_perm circuit.sourceFaces 1

/-- A shortest concrete recovery circuit also visits no target face
twice. -/
theorem IsLengthMinimal.targetFaces_nodup
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.targetFaces.Nodup := by
  exact circuit.targetFaces_perm_sourceFaces.nodup_iff.mpr
    hminimal.sourceFaces_nodup

/-- The displayed positions of the restoring arcs on the underlying
rebase circuit. -/
noncomputable def restoringPositions
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    List (Fin rebaseCircuit.arcLength) :=
  (circuit.first :: circuit.rest).map
    ClosureRecoveryFaceArc.restoringPosition

@[simp] theorem restoringPositions_length
    (circuit : ClosureRecoveryFaceCircuit rebaseCircuit) :
    circuit.restoringPositions.length = circuit.arcLength := by
  simp [restoringPositions, arcLength]

/-- Distinct target faces on a shortest recovery circuit force distinct
restoring positions on the underlying rebase circuit. -/
theorem IsLengthMinimal.restoringPositions_nodup
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.restoringPositions.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  unfold restoringPositions
  rw [List.pairwise_map]
  have htarget : List.Pairwise
      (fun first second : ClosureRecoveryFaceArc rebaseCircuit =>
        first.targetFace ≠ second.targetFace)
      (circuit.first :: circuit.rest) := by
    rw [← List.pairwise_map, ← List.nodup_iff_pairwise_ne]
    exact hminimal.targetFaces_nodup
  apply htarget.imp
  intro first second hface hposition
  apply hface
  have harc : first.recoveryArc = second.recoveryArc := by
    calc
      first.recoveryArc =
          (rebaseCircuit.first :: rebaseCircuit.rest).get
            first.restoringPosition := first.get_restoringPosition.symm
      _ = (rebaseCircuit.first :: rebaseCircuit.rest).get
            second.restoringPosition := by rw [hposition]
      _ = second.recoveryArc := second.get_restoringPosition
  calc
    first.targetFace = first.recoveryArc.selectedFace :=
      first.recoveryArc_selectedFace.symm
    _ = second.recoveryArc.selectedFace := by rw [harc]
    _ = second.targetFace := second.recoveryArc_selectedFace

/-- A shortest concrete recovery cycle uses no more restoring positions
than the underlying rebase circuit has arcs. -/
theorem IsLengthMinimal.arcLength_le_rebase_arcLength
    {circuit : ClosureRecoveryFaceCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤ rebaseCircuit.arcLength := by
  rw [← circuit.restoringPositions_length]
  simpa using hminimal.restoringPositions_nodup.length_le_card

end ClosureRecoveryFaceCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
