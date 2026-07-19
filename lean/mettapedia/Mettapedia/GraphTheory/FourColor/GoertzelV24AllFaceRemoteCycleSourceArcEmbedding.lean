import Mettapedia.GraphTheory.FourColor.GoertzelV24AllFaceRemotePrimalCutProfile

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FourDefectBoundary
open GoertzelV24MinimalFaceIntersections
open GoertzelV24RecoveredAdjacentPairData
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

namespace CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Every indexed vertex of a remote dual cycle occurs at a physical
position of the source certified rebase circuit. -/
theorem exists_sourcePosition
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    ∃ position : Fin rebaseCircuit.arcLength,
      (rebaseCircuit.arcAt position).dualFace =
        cycle.walk.getVert step := by
  have hsupport : cycle.walk.getVert step ∈ cycle.walk.support :=
    cycle.walk.getVert_mem_support step
  rcases cycle.exists_rebaseArc_of_mem_support hsupport with
    ⟨arc, harc, hface⟩
  obtain ⟨position, hposition⟩ := List.get_of_mem harc
  exact ⟨position, congrArg
    CrossCentralExactFaceCertifiedRebaseArc.dualFace hposition |>.trans
      hface⟩

/-- A canonical physical source position chosen for each indexed remote
cycle face. -/
def sourcePosition
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) : Fin rebaseCircuit.arcLength :=
  Classical.choose (cycle.exists_sourcePosition step)

/-- The source arc at the chosen physical position has exactly the
corresponding remote-cycle face. -/
theorem arcAt_sourcePosition_dualFace
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    (rebaseCircuit.arcAt (cycle.sourcePosition step)).dualFace =
      cycle.walk.getVert step :=
  Classical.choose_spec (cycle.exists_sourcePosition step)

/-- Distinct vertices of the simple remote cycle occupy distinct physical
positions in the source rebase circuit. -/
theorem sourcePosition_injective
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) :
    Function.Injective cycle.sourcePosition := by
  intro first second hposition
  apply Fin.ext
  apply cycle.isCycle.getVert_injOn'
  · simp only [Set.mem_setOf_eq]
    have hfirst := first.isLt
    have hthree := cycle.isCycle.three_le_length
    omega
  · simp only [Set.mem_setOf_eq]
    have hsecond := second.isLt
    have hthree := cycle.isCycle.three_le_length
    omega
  · rw [← cycle.arcAt_sourcePosition_dualFace first,
      ← cycle.arcAt_sourcePosition_dualFace second, hposition]

/-- The primal edge crossed at an indexed remote-cycle step. -/
def crossingAt
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) : G.edgeSet :=
  dualWalkCrossingEdge
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
    (pairwiseUniqueSharedInteriorEdges graphData minimal)
    cycle.walk step

/-- The crossed primal edge lies on the selected face of its left source
arc anchor. -/
theorem crossingAt_mem_sourceFace
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    cycle.crossingAt step ∈ orbitFaceBoundary
      graphData.toRotationSystem
        (rebaseCircuit.arcAt (cycle.sourcePosition step)).selectedFace := by
  have hface :
      (rebaseCircuit.arcAt
          (cycle.sourcePosition step)).selectedFace =
        (cycle.walk.getVert step).1 := by
    simpa [CrossCentralExactFaceCertifiedRebaseArc.dualFace] using
      congrArg Subtype.val (cycle.arcAt_sourcePosition_dualFace step)
  rw [hface]
  exact dualWalkCrossingEdge_mem_leftFace
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
    (pairwiseUniqueSharedInteriorEdges graphData minimal)
    cycle.walk step

/-- The same crossed edge lies on the selected face of the cyclically next
source arc anchor. -/
theorem crossingAt_mem_successorSourceFace
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    cycle.crossingAt step ∈ orbitFaceBoundary
      graphData.toRotationSystem
        (rebaseCircuit.arcAt
          (cycle.sourcePosition (finRotate cycle.walk.length step))).selectedFace := by
  have hnext :=
    GoertzelV24DualCycleChord.getVert_succ_eq_getVert_finRotate_of_isCycle
      cycle.isCycle step
  have hsourceFace :
      (rebaseCircuit.arcAt
          (cycle.sourcePosition
            (finRotate cycle.walk.length step))).selectedFace =
        (cycle.walk.getVert (step.val + 1)).1 := by
    have hanchor := cycle.arcAt_sourcePosition_dualFace
      (finRotate cycle.walk.length step)
    have hanchorValue := congrArg Subtype.val hanchor
    have hnextValue := congrArg Subtype.val hnext
    simpa [CrossCentralExactFaceCertifiedRebaseArc.dualFace] using
      hanchorValue.trans hnextValue.symm
  rw [hsourceFace]
  exact dualWalkCrossingEdge_mem_rightFace
    (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
    (pairwiseUniqueSharedInteriorEdges graphData minimal)
    cycle.walk step

/-- The two source-arc anchors incident to one remote-cycle crossing are
distinct physical positions. -/
theorem sourcePosition_finRotate_ne
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    cycle.sourcePosition (finRotate cycle.walk.length step) ≠
      cycle.sourcePosition step := by
  have htwo : 2 ≤ cycle.walk.length :=
    le_trans (by omega) cycle.isCycle.three_le_length
  have hrotate : finRotate cycle.walk.length step ≠ step := by
    rw [← Equiv.Perm.mem_support,
      support_finRotate_of_le htwo]
    exact Finset.mem_univ _
  intro hposition
  exact hrotate (cycle.sourcePosition_injective hposition)

/-- The physical arc list splits exactly at any chosen remote-cycle
anchor. -/
theorem sourcePosition_split
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    rebaseCircuit.first :: rebaseCircuit.rest =
      (rebaseCircuit.first :: rebaseCircuit.rest).take
          (cycle.sourcePosition step).val ++
        rebaseCircuit.arcAt (cycle.sourcePosition step) ::
          (rebaseCircuit.first :: rebaseCircuit.rest).drop
            ((cycle.sourcePosition step).val + 1) := by
  let arcs := rebaseCircuit.first :: rebaseCircuit.rest
  let position := cycle.sourcePosition step
  have hposition : position.val < arcs.length := by
    simpa [arcs, position,
      CrossCentralExactFaceCertifiedRebaseCircuit.arcLength] using
        position.isLt
  have harcAt : arcs[position.val] =
      rebaseCircuit.arcAt position := by
    rfl
  have hsplit :
      arcs.take position.val ++ [arcs[position.val]] ++
          arcs.drop (position.val + 1) = arcs := by
    rw [List.append_assoc, List.singleton_append,
      List.cons_getElem_drop_succ (h := hposition),
      List.take_append_drop]
  change arcs = arcs.take position.val ++
    rebaseCircuit.arcAt position :: arcs.drop (position.val + 1)
  calc
    arcs = arcs.take position.val ++ [arcs[position.val]] ++
        arcs.drop (position.val + 1) := hsplit.symm
    _ = arcs.take position.val ++ rebaseCircuit.arcAt position ::
        arcs.drop (position.val + 1) := by
      rw [harcAt, List.append_assoc, List.singleton_append]

/-- Rotate the certified source circuit so that the arc anchored at a
chosen remote-cycle face is displayed first. -/
def rotateAtSourcePosition
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal
      baseData :=
  rebaseCircuit.rotateAtSplit
    (rebaseCircuit.arcAt (cycle.sourcePosition step))
    ((rebaseCircuit.first :: rebaseCircuit.rest).take
      (cycle.sourcePosition step).val)
    ((rebaseCircuit.first :: rebaseCircuit.rest).drop
      ((cycle.sourcePosition step).val + 1))
    (cycle.sourcePosition_split step)

/-- The chosen remote-cycle anchor is literally the first arc after
rotation. -/
@[simp] theorem rotateAtSourcePosition_first
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    (cycle.rotateAtSourcePosition step).first =
      rebaseCircuit.arcAt (cycle.sourcePosition step) := by
  simp [rotateAtSourcePosition]

/-- The first face of the rotated representative is exactly the chosen
remote-cycle face. -/
theorem rotateAtSourcePosition_first_dualFace
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    (cycle.rotateAtSourcePosition step).first.dualFace =
      cycle.walk.getVert step := by
  rw [cycle.rotateAtSourcePosition_first]
  exact cycle.arcAt_sourcePosition_dualFace step

/-- Re-anchoring at a remote-cycle face preserves the certified circuit
length. -/
@[simp] theorem rotateAtSourcePosition_arcLength
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit)
    (step : Fin cycle.walk.length) :
    (cycle.rotateAtSourcePosition step).arcLength =
      rebaseCircuit.arcLength := by
  unfold rotateAtSourcePosition
  exact rebaseCircuit.rotateAtSplit_arcLength _ _ _ _

/-- The remote dual cycle cannot have more vertices than the physical
source rebase circuit has certified arcs. -/
theorem walk_length_le_rebase_arcLength
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) :
    cycle.walk.length ≤ rebaseCircuit.arcLength := by
  simpa using Fintype.card_le_of_injective cycle.sourcePosition
    cycle.sourcePosition_injective

/-- The finite set of physical source positions occupied by remote-cycle
faces. -/
def sourcePositions
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) : Finset (Fin rebaseCircuit.arcLength) :=
  Finset.univ.image cycle.sourcePosition

/-- The source-position set has exactly one anchor for every remote-cycle
vertex. -/
@[simp] theorem sourcePositions_card
    (cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit) :
    cycle.sourcePositions.card = cycle.walk.length := by
  rw [sourcePositions,
    Finset.card_image_of_injective _ cycle.sourcePosition_injective]
  simp

/-- A singleton-star remote triangle therefore supplies exactly three
distinct certified source positions. -/
theorem SingletonPrimalCutProfile.sourcePositions_card_eq_three
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    (profile : cycle.SingletonPrimalCutProfile) :
    cycle.sourcePositions.card = 3 := by
  rw [cycle.sourcePositions_card, profile.length_eq_three]

/-- An adjacent-pair remote four-cycle supplies exactly four distinct
certified source positions. -/
theorem AdjacentPairPrimalCutProfile.sourcePositions_card_eq_four
    {cycle :
      CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle
        rebaseCircuit}
    (profile : cycle.AdjacentPairPrimalCutProfile) :
    cycle.sourcePositions.card = 4 := by
  rw [cycle.sourcePositions_card, profile.length_eq_four]

end CrossCentralExactFaceCertifiedRebaseCircuit.RemoteDualCycle

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
