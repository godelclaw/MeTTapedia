import Mathlib.GroupTheory.Perm.Fin
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferOverlap

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

private theorem rel_next_of_isChain_of_closing
    {α : Type*} [DecidableEq α]
    {relation : α → α → Prop}
    (entries : List α)
    (hne : entries ≠ [])
    (hnodup : entries.Nodup)
    (hchain : entries.IsChain relation)
    (hclosing : relation (entries.getLast hne) (entries.head hne))
    (entry : α) (hentry : entry ∈ entries) :
    relation entry (entries.next entry hentry) := by
  obtain ⟨index, hindex, rfl⟩ := List.getElem_of_mem hentry
  by_cases hnext : index + 1 < entries.length
  · rw [List.next_getElem entries hnodup index hindex]
    have hrel := hchain.getElem index hnext
    simpa [Nat.mod_eq_of_lt hnext] using hrel
  · have hindexLast : index = entries.length - 1 := by omega
    have hentryLast : entries[index] = entries.getLast hne := by
      rw [List.getLast_eq_getElem hne]
      exact getElem_congr_idx hindexLast
    let nextEntry : {entry // entry ∈ entries} → α := fun entry =>
      entries.next entry.1 entry.2
    have hsubtype : (⟨entries[index], hentry⟩ :
        {entry // entry ∈ entries}) =
        ⟨entries.getLast hne, List.getLast_mem hne⟩ := by
      exact Subtype.ext hentryLast
    have hnextLast : entries.next entries[index] hentry =
        entries.head hne := by
      calc
        entries.next entries[index] hentry =
            nextEntry ⟨entries[index], hentry⟩ := rfl
        _ = nextEntry ⟨entries.getLast hne,
              List.getLast_mem hne⟩ := congrArg nextEntry hsubtype
        _ = entries.head hne :=
          List.next_getLast_eq_head entries hne hnodup
    rw [hnextLast, hentryLast]
    exact hclosing

namespace ClosureRecoveryFaceTransferCircuit

variable {rebaseCircuit :
  CrossCentralExactFaceCertifiedRebaseCircuit graphData minimal baseData}

/-- Shortest-cycle source-face injectivity also makes the displayed
transfer list itself duplicate-free. -/
theorem IsLengthMinimal.transfers_nodup
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    (circuit.first :: circuit.rest).Nodup := by
  apply List.Nodup.of_map
    (fun transfer : ClosureRecoveryFaceTransfer rebaseCircuit =>
      transfer.recovery.sourceFace)
  exact hminimal.sourceFaces_nodup

/-- Two displayed transfers of a shortest circuit with the same source
face are equal. -/
theorem IsLengthMinimal.transfer_eq_of_mem_of_mem_of_sourceFace_eq
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    {first second : ClosureRecoveryFaceTransfer rebaseCircuit}
    (hfirst : first ∈ circuit.first :: circuit.rest)
    (hsecond : second ∈ circuit.first :: circuit.rest)
    (hsource : first.recovery.sourceFace =
      second.recovery.sourceFace) :
    first = second := by
  have hnodup := hminimal.sourceFaces_nodup
  unfold sourceFaces at hnodup
  exact List.inj_on_of_nodup_map hnodup hfirst hsecond hsource

/-- Reading a transfer-circuit position always returns a displayed
transfer. -/
theorem transferAt_mem
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    circuit.transferAt position ∈ circuit.first :: circuit.rest := by
  exact List.get_mem _ _

/-- The intrinsic cyclic successor of the transfer displayed at a
position. -/
noncomputable def nextTransferAt
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (_hminimal : circuit.IsLengthMinimal)
    (position : Fin circuit.arcLength) :
    ClosureRecoveryFaceTransfer rebaseCircuit := by
  classical
  exact (circuit.first :: circuit.rest).next
    (circuit.transferAt position) (circuit.transferAt_mem position)

/-- The intrinsic successor remains a displayed transfer. -/
theorem nextTransferAt_mem
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (position : Fin circuit.arcLength) :
    circuit.nextTransferAt hminimal position ∈
      circuit.first :: circuit.rest := by
  classical
  exact List.next_mem _ _ _

/-- The displayed transfer at a position is followed by its intrinsic
cyclic successor. -/
theorem transferAt_follows_nextTransferAt
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (position : Fin circuit.arcLength) :
    ClosureRecoveryFaceTransfer.Follows
      (circuit.transferAt position)
      (circuit.nextTransferAt hminimal position) := by
  classical
  let entries := circuit.first :: circuit.rest
  have hne : entries ≠ [] := by simp [entries]
  have hclosing : ClosureRecoveryFaceTransfer.Follows
      (entries.getLast hne) (entries.head hne) := by
    simpa [entries] using circuit.closing
  exact rel_next_of_isChain_of_closing entries hne
    hminimal.transfers_nodup circuit.consecutive hclosing
      (circuit.transferAt position) (circuit.transferAt_mem position)

/-- The positional reading of a shortest transfer circuit is injective. -/
theorem IsLengthMinimal.transferAt_injective
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    Function.Injective circuit.transferAt := by
  intro first second htransfer
  have hinjective : Function.Injective
      (circuit.first :: circuit.rest).get :=
    List.nodup_iff_injective_get.mp hminimal.transfers_nodup
  exact hinjective htransfer

/-- Intrinsic list successor is the standard one-step rotation of the
finite position type. -/
theorem nextTransferAt_eq_transferAt_finRotate
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (position : Fin circuit.arcLength) :
    circuit.nextTransferAt hminimal position =
      circuit.transferAt (finRotate circuit.arcLength position) := by
  classical
  have hnext := List.next_getElem
    (circuit.first :: circuit.rest) hminimal.transfers_nodup
      position.1 position.2
  change (circuit.first :: circuit.rest).next
      ((circuit.first :: circuit.rest).get position)
        (circuit.transferAt_mem position) =
    (circuit.first :: circuit.rest).get
      (finRotate circuit.arcLength position)
  convert hnext using 1
  · congr 1
  · rw [List.get_eq_getElem]
    apply getElem_congr_idx
    haveI : NeZero circuit.arcLength := position.neZero
    rw [finRotate_apply]
    rw [Fin.val_add, Fin.val_one',
      Nat.mod_eq_of_lt circuit.two_le_arcLength]
    rfl

/-- In the saturated branch, position monodromy is not an auxiliary
permutation: it selects exactly the intrinsic next transfer in cyclic
list order. -/
theorem transferAt_positionMonodromy_eq_nextTransferAt
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    circuit.transferAt
        (circuit.positionMonodromy hminimal hlength position) =
      circuit.nextTransferAt hminimal position := by
  apply hminimal.transfer_eq_of_mem_of_mem_of_sourceFace_eq
  · exact circuit.transferAt_mem _
  · exact circuit.nextTransferAt_mem hminimal position
  · calc
      (circuit.transferAt
          (circuit.positionMonodromy hminimal hlength position)).recovery.sourceFace =
          (circuit.transferAt position).recovery.targetFace :=
        circuit.sourceFace_positionMonodromy_eq_targetFace
          hminimal hlength position
      _ = (circuit.nextTransferAt hminimal position).recovery.sourceFace :=
        circuit.transferAt_follows_nextTransferAt hminimal position

/-- Therefore saturated recovery monodromy is exactly the standard
one-step cyclic rotation on transfer positions. -/
theorem positionMonodromy_eq_finRotate
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    circuit.positionMonodromy hminimal hlength =
      finRotate circuit.arcLength := by
  apply Equiv.ext
  intro position
  apply hminimal.transferAt_injective
  calc
    circuit.transferAt
        (circuit.positionMonodromy hminimal hlength position) =
      circuit.nextTransferAt hminimal position :=
        circuit.transferAt_positionMonodromy_eq_nextTransferAt
          hminimal hlength position
    _ = circuit.transferAt (finRotate circuit.arcLength position) :=
      circuit.nextTransferAt_eq_transferAt_finRotate hminimal position

/-- In particular the saturated position monodromy consists of one
cycle through all transfer positions. -/
theorem positionMonodromy_isCycle
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    (circuit.positionMonodromy hminimal hlength).IsCycle := by
  rw [circuit.positionMonodromy_eq_finRotate hminimal hlength]
  exact isCycle_finRotate_of_le circuit.two_le_arcLength

/-- Equivalently, every saturated restoring arc is the loss arc of the
intrinsic cyclic successor. -/
theorem recoveryArc_eq_lossArc_nextTransferAt
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    (circuit.transferAt position).recovery.recoveryArc =
      (circuit.nextTransferAt hminimal position).lossArc := by
  calc
    (circuit.transferAt position).recovery.recoveryArc =
        (circuit.transferAt
          (circuit.positionMonodromy hminimal hlength position)).lossArc :=
      circuit.recoveryArc_eq_lossArc_positionMonodromy
        hminimal hlength position
    _ = (circuit.nextTransferAt hminimal position).lossArc := by
      rw [circuit.transferAt_positionMonodromy_eq_nextTransferAt
        hminimal hlength position]

end ClosureRecoveryFaceTransferCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
