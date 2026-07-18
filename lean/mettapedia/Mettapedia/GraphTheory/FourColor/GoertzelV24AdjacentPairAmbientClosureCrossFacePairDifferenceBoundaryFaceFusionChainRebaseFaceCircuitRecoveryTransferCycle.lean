import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryLossProvenance

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

/-- The number of provenance-retaining dependencies in a transfer
circuit. -/
def arcLength
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) : Nat :=
  (circuit.first :: circuit.rest).length

@[simp] theorem arcLength_eq_rest_length_add_one
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    circuit.arcLength = circuit.rest.length + 1 := by
  simp [arcLength, Nat.add_comm]

/-- Forgetting loss provenance preserves transfer-circuit length. -/
@[simp] theorem toRecoveryFaceCircuit_arcLength_eq_arcLength
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    circuit.toRecoveryFaceCircuit.arcLength = circuit.arcLength := by
  simpa [arcLength] using circuit.toRecoveryFaceCircuit_arcLength

/-- A transfer circuit cannot consist of one self-transfer. -/
theorem rest_ne_nil
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    circuit.rest ≠ [] := by
  intro hrest
  have hclosing : circuit.first.recovery.targetFace =
      circuit.first.recovery.sourceFace := by
    simpa [ClosureRecoveryFaceTransfer.Follows, hrest] using
      circuit.closing
  exact circuit.first.recovery.targetFace_ne_sourceFace hclosing

theorem two_le_arcLength
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    2 ≤ circuit.arcLength := by
  rw [circuit.arcLength_eq_rest_length_add_one]
  have hlengthNe : circuit.rest.length ≠ 0 := by
    intro hzero
    exact circuit.rest_ne_nil (List.length_eq_zero_iff.mp hzero)
  omega

/-- A transfer circuit is shortest among all provenance-retaining
transfer circuits carried by the same rebase circuit. -/
def IsLengthMinimal
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) : Prop :=
  ∀ other : ClosureRecoveryFaceTransferCircuit rebaseCircuit,
    circuit.arcLength ≤ other.arcLength

/-- Every nonempty family of transfer circuits has a shortest member. -/
theorem exists_lengthMinimal
    (circuits : Nonempty
      (ClosureRecoveryFaceTransferCircuit rebaseCircuit)) :
    ∃ circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit,
      circuit.IsLengthMinimal := by
  classical
  rcases circuits with ⟨seed⟩
  let occurs : Nat → Prop := fun length =>
    ∃ circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit,
      circuit.arcLength = length
  have hexists : ∃ length, occurs length :=
    ⟨seed.arcLength, seed, rfl⟩
  rcases Nat.find_spec hexists with ⟨circuit, hcircuit⟩
  refine ⟨circuit, ?_⟩
  intro other
  rw [hcircuit]
  exact Nat.find_min' hexists ⟨other, rfl⟩

/-- Equal source faces at two displayed transfer positions close the
intervening segment to a strictly shorter provenance-retaining circuit. -/
theorem exists_strict_subcircuit_of_split_sourceFace_eq
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (first second : ClosureRecoveryFaceTransfer rebaseCircuit)
    (before between after : List
      (ClosureRecoveryFaceTransfer rebaseCircuit))
    (hsplit : circuit.first :: circuit.rest =
      before ++ (first :: (between ++ (second :: after))))
    (hsource : first.recovery.sourceFace =
      second.recovery.sourceFace) :
    ∃ subcircuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit,
      subcircuit.arcLength < circuit.arcLength ∧
      subcircuit.first :: subcircuit.rest = first :: between := by
  let segment := first :: between
  have hfullChain : List.IsChain ClosureRecoveryFaceTransfer.Follows
      (before ++ (segment ++ (second :: after))) := by
    have hchain := circuit.consecutive
    rw [hsplit] at hchain
    simpa [segment, List.append_assoc] using hchain
  have hsegmentAfterChain :
      List.IsChain ClosureRecoveryFaceTransfer.Follows
        (segment ++ (second :: after)) :=
    (List.isChain_append.mp hfullChain).2.1
  have hparts := List.isChain_append.mp hsegmentAfterChain
  have hsegmentChain :
      List.IsChain ClosureRecoveryFaceTransfer.Follows segment :=
    hparts.1
  have hsegmentNe : segment ≠ [] := by simp [segment]
  let last := segment.getLast hsegmentNe
  have hlastMem : last ∈ segment.getLast? := by
    rw [List.getLast?_eq_getLast_of_ne_nil hsegmentNe]
    simp [last]
  have hlastFollows : ClosureRecoveryFaceTransfer.Follows last second :=
    hparts.2.2 last hlastMem second (by simp)
  let subcircuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit := {
    first := first
    rest := between
    consecutive := by simpa [segment] using hsegmentChain
    closing := by
      change last.recovery.targetFace = first.recovery.sourceFace
      exact hlastFollows.trans hsource.symm }
  refine ⟨subcircuit, ?_, rfl⟩
  change segment.length < (circuit.first :: circuit.rest).length
  rw [hsplit]
  simp [segment]
  omega

/-- The cyclic source-face list of a provenance-retaining transfer
circuit. -/
def sourceFaces
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    List (OrbitFace graphData.toRotationSystem) :=
  (circuit.first :: circuit.rest).map
    (fun transfer => transfer.recovery.sourceFace)

@[simp] theorem sourceFaces_length
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    circuit.sourceFaces.length = circuit.arcLength := by
  simp [sourceFaces, arcLength]

/-- Every source face of a closed transfer circuit is selected by the
underlying rebase circuit. -/
theorem sourceFace_mem_selectedFaces_of_mem
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    {transfer : ClosureRecoveryFaceTransfer rebaseCircuit}
    (htransfer : transfer ∈ circuit.first :: circuit.rest) :
    transfer.recovery.sourceFace ∈ rebaseCircuit.selectedFaces := by
  apply circuit.toRecoveryFaceCircuit.sourceFace_mem_selectedFaces_of_mem
  rw [circuit.toRecoveryFaceCircuit_dependencies]
  exact List.mem_map_of_mem
    (f := ClosureRecoveryFaceTransfer.recovery) htransfer

/-- A shortest provenance-retaining circuit visits no source face
twice. -/
theorem IsLengthMinimal.sourceFaces_nodup
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.sourceFaces.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  unfold sourceFaces
  rw [List.pairwise_map]
  let transfers := circuit.first :: circuit.rest
  have suffixPairwise : ∀ (before suffix : List
      (ClosureRecoveryFaceTransfer rebaseCircuit)),
      transfers = before ++ suffix →
        List.Pairwise (fun first second =>
          first.recovery.sourceFace ≠ second.recovery.sourceFace)
          suffix := by
    intro before suffix
    induction suffix generalizing before with
    | nil =>
        intro _
        exact List.Pairwise.nil
    | cons first rest ih =>
        intro hsplit
        apply List.pairwise_cons.mpr
        constructor
        · intro second hsecond
          rcases List.mem_iff_append.mp hsecond with
            ⟨between, after, hrest⟩
          intro hsource
          rcases
              circuit.exists_strict_subcircuit_of_split_sourceFace_eq
                first second before between after (by
                  simpa [transfers, hrest] using hsplit) hsource with
            ⟨subcircuit, hshorter, _⟩
          exact (Nat.not_lt_of_ge (hminimal subcircuit)) hshorter
        · apply ih (before ++ [first])
          calc
            transfers = before ++ (first :: rest) := hsplit
            _ = (before ++ [first]) ++ rest := by simp
  simpa [transfers] using suffixPairwise [] transfers (by simp)

/-- A shortest transfer circuit has at most one source occurrence per
selected face. -/
theorem IsLengthMinimal.arcLength_le_selectedFaces_card
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤ rebaseCircuit.selectedFaces.card := by
  classical
  have hsubset : circuit.sourceFaces.toFinset ⊆
      rebaseCircuit.selectedFaces := by
    intro face hface
    have hlist : face ∈ circuit.sourceFaces := by simpa using hface
    rcases List.mem_map.mp hlist with ⟨transfer, htransfer, rfl⟩
    exact circuit.sourceFace_mem_selectedFaces_of_mem htransfer
  calc
    circuit.arcLength = circuit.sourceFaces.length :=
      circuit.sourceFaces_length.symm
    _ = circuit.sourceFaces.toFinset.card :=
      (List.toFinset_card_of_nodup hminimal.sourceFaces_nodup).symm
    _ ≤ rebaseCircuit.selectedFaces.card := Finset.card_le_card hsubset

/-- A shortest transfer circuit has no more arcs than there are ambient
faces. -/
theorem IsLengthMinimal.arcLength_le_card_faces
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤
      Fintype.card (OrbitFace graphData.toRotationSystem) := by
  rw [← circuit.sourceFaces_length]
  exact hminimal.sourceFaces_nodup.length_le_card

/-- The cyclic target-face list of a provenance-retaining transfer
circuit. -/
def targetFaces
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    List (OrbitFace graphData.toRotationSystem) :=
  (circuit.first :: circuit.rest).map
    (fun transfer => transfer.recovery.targetFace)

@[simp] theorem targetFaces_length
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    circuit.targetFaces.length = circuit.arcLength := by
  simp [targetFaces, arcLength]

/-- Source and target faces carry the same cyclic multiset after loss
provenance is forgotten. -/
theorem targetFaces_perm_sourceFaces
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    circuit.targetFaces.Perm circuit.sourceFaces := by
  have hperm :=
    circuit.toRecoveryFaceCircuit.targetFaces_perm_sourceFaces
  simpa [targetFaces, sourceFaces,
    ClosureRecoveryFaceCircuit.targetFaces,
    ClosureRecoveryFaceCircuit.sourceFaces,
    ClosureRecoveryFaceTransferCircuit.toRecoveryFaceCircuit,
    Function.comp_def]
    using hperm

/-- A shortest provenance-retaining circuit also visits no target face
twice. -/
theorem IsLengthMinimal.targetFaces_nodup
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.targetFaces.Nodup := by
  exact circuit.targetFaces_perm_sourceFaces.nodup_iff.mpr
    hminimal.sourceFaces_nodup

/-- The displayed positions where the transfer codes are lost. -/
noncomputable def lossPositions
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    List (Fin rebaseCircuit.arcLength) :=
  (circuit.first :: circuit.rest).map
    ClosureRecoveryFaceTransfer.lossPosition

@[simp] theorem lossPositions_length
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    circuit.lossPositions.length = circuit.arcLength := by
  simp [lossPositions, arcLength]

/-- Distinct source faces on a shortest transfer circuit force distinct
loss positions on the underlying rebase circuit. -/
theorem IsLengthMinimal.lossPositions_nodup
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.lossPositions.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  unfold lossPositions
  rw [List.pairwise_map]
  have hsource : List.Pairwise
      (fun first second : ClosureRecoveryFaceTransfer rebaseCircuit =>
        first.recovery.sourceFace ≠ second.recovery.sourceFace)
      (circuit.first :: circuit.rest) := by
    rw [← List.pairwise_map, ← List.nodup_iff_pairwise_ne]
    exact hminimal.sourceFaces_nodup
  apply hsource.imp
  intro first second hface hposition
  apply hface
  have harc : first.lossArc = second.lossArc := by
    calc
      first.lossArc =
          (rebaseCircuit.first :: rebaseCircuit.rest).get
            first.lossPosition := first.get_lossPosition.symm
      _ = (rebaseCircuit.first :: rebaseCircuit.rest).get
            second.lossPosition := by rw [hposition]
      _ = second.lossArc := second.get_lossPosition
  calc
    first.recovery.sourceFace = first.lossArc.selectedFace :=
      first.lossArc_selectedFace.symm
    _ = second.lossArc.selectedFace := by rw [harc]
    _ = second.recovery.sourceFace := second.lossArc_selectedFace

/-- The displayed positions where the transfer codes are restored. -/
noncomputable def restoringPositions
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    List (Fin rebaseCircuit.arcLength) :=
  (circuit.first :: circuit.rest).map
    (fun transfer => transfer.recovery.restoringPosition)

@[simp] theorem restoringPositions_length
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit) :
    circuit.restoringPositions.length = circuit.arcLength := by
  simp [restoringPositions, arcLength]

/-- Distinct target faces on a shortest transfer circuit force distinct
restoring positions on the underlying rebase circuit. -/
theorem IsLengthMinimal.restoringPositions_nodup
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.restoringPositions.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  unfold restoringPositions
  rw [List.pairwise_map]
  have htarget : List.Pairwise
      (fun first second : ClosureRecoveryFaceTransfer rebaseCircuit =>
        first.recovery.targetFace ≠ second.recovery.targetFace)
      (circuit.first :: circuit.rest) := by
    rw [← List.pairwise_map, ← List.nodup_iff_pairwise_ne]
    exact hminimal.targetFaces_nodup
  apply htarget.imp
  intro first second hface hposition
  apply hface
  have harc : first.recovery.recoveryArc =
      second.recovery.recoveryArc := by
    calc
      first.recovery.recoveryArc =
          (rebaseCircuit.first :: rebaseCircuit.rest).get
            first.recovery.restoringPosition :=
        first.recovery.get_restoringPosition.symm
      _ = (rebaseCircuit.first :: rebaseCircuit.rest).get
            second.recovery.restoringPosition := by rw [hposition]
      _ = second.recovery.recoveryArc :=
        second.recovery.get_restoringPosition
  calc
    first.recovery.targetFace =
        first.recovery.recoveryArc.selectedFace :=
      first.recovery.recoveryArc_selectedFace.symm
    _ = second.recovery.recoveryArc.selectedFace := by rw [harc]
    _ = second.recovery.targetFace :=
      second.recovery.recoveryArc_selectedFace

/-- Either positional realization of a shortest transfer circuit embeds
into the displayed rebase trace. -/
theorem IsLengthMinimal.arcLength_le_rebase_arcLength
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    circuit.arcLength ≤ rebaseCircuit.arcLength := by
  rw [← circuit.lossPositions_length]
  simpa using hminimal.lossPositions_nodup.length_le_card

/-- The concrete transfer displayed at a transfer-circuit position. -/
def transferAt
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    ClosureRecoveryFaceTransfer rebaseCircuit :=
  (circuit.first :: circuit.rest).get position

/-- The underlying rebase loss position assigned to a transfer-circuit
position. -/
noncomputable def lossPositionAt
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    Fin rebaseCircuit.arcLength :=
  (circuit.transferAt position).lossPosition

/-- The underlying rebase restoring position assigned to a
transfer-circuit position. -/
noncomputable def restoringPositionAt
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    Fin rebaseCircuit.arcLength :=
  (circuit.transferAt position).recovery.restoringPosition

/-- On a shortest transfer circuit, the loss-position assignment into
the rebase circuit is injective. -/
theorem IsLengthMinimal.lossPositionAt_injective
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    Function.Injective circuit.lossPositionAt := by
  intro first second hposition
  have hinjective : Function.Injective circuit.lossPositions.get :=
    List.nodup_iff_injective_get.mp hminimal.lossPositions_nodup
  let first' : Fin circuit.lossPositions.length :=
    Fin.cast circuit.lossPositions_length.symm first
  let second' : Fin circuit.lossPositions.length :=
    Fin.cast circuit.lossPositions_length.symm second
  have hget : circuit.lossPositions.get first' =
      circuit.lossPositions.get second' := by
    change ((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceTransfer.lossPosition).get first' =
      ((circuit.first :: circuit.rest).map
        ClosureRecoveryFaceTransfer.lossPosition).get second'
    simp only [List.get_eq_getElem, List.getElem_map]
    simpa [first', second', lossPositionAt, transferAt,
      List.get_eq_getElem] using hposition
  exact Fin.cast_injective circuit.lossPositions_length.symm
    (hinjective hget)

/-- On a shortest transfer circuit, the restoring-position assignment
into the rebase circuit is injective. -/
theorem IsLengthMinimal.restoringPositionAt_injective
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal) :
    Function.Injective circuit.restoringPositionAt := by
  intro first second hposition
  have hinjective : Function.Injective circuit.restoringPositions.get :=
    List.nodup_iff_injective_get.mp hminimal.restoringPositions_nodup
  let first' : Fin circuit.restoringPositions.length :=
    Fin.cast circuit.restoringPositions_length.symm first
  let second' : Fin circuit.restoringPositions.length :=
    Fin.cast circuit.restoringPositions_length.symm second
  have hget : circuit.restoringPositions.get first' =
      circuit.restoringPositions.get second' := by
    change ((circuit.first :: circuit.rest).map
        (fun transfer : ClosureRecoveryFaceTransfer rebaseCircuit =>
          transfer.recovery.restoringPosition)).get first' =
      ((circuit.first :: circuit.rest).map
        (fun transfer : ClosureRecoveryFaceTransfer rebaseCircuit =>
          transfer.recovery.restoringPosition)).get second'
    simp only [List.get_eq_getElem, List.getElem_map]
    simpa [first', second', restoringPositionAt, transferAt,
      List.get_eq_getElem] using hposition
  exact Fin.cast_injective circuit.restoringPositions_length.symm
    (hinjective hget)

/-- Equality in the positional bound makes the loss-position assignment
a bijection onto the whole rebase trace. -/
theorem IsLengthMinimal.lossPositionAt_bijective_of_arcLength_eq
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    Function.Bijective circuit.lossPositionAt := by
  apply (Fintype.bijective_iff_injective_and_card
    circuit.lossPositionAt).2
  exact ⟨hminimal.lossPositionAt_injective, by simpa using hlength⟩

/-- Equality in the positional bound also makes the restoring-position
assignment a bijection onto the whole rebase trace. -/
theorem IsLengthMinimal.restoringPositionAt_bijective_of_arcLength_eq
    {circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit}
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    Function.Bijective circuit.restoringPositionAt := by
  apply (Fintype.bijective_iff_injective_and_card
    circuit.restoringPositionAt).2
  exact ⟨hminimal.restoringPositionAt_injective, by simpa using hlength⟩

/-- In the saturated case, transfer positions and their concrete loss
positions are equivalent finite alphabets. -/
noncomputable def lossPositionEquiv
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    Fin circuit.arcLength ≃ Fin rebaseCircuit.arcLength :=
  Equiv.ofBijective circuit.lossPositionAt
    (hminimal.lossPositionAt_bijective_of_arcLength_eq hlength)

/-- In the saturated case, transfer positions and their concrete
restoring positions are equivalent finite alphabets. -/
noncomputable def restoringPositionEquiv
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    Fin circuit.arcLength ≃ Fin rebaseCircuit.arcLength :=
  Equiv.ofBijective circuit.restoringPositionAt
    (hminimal.restoringPositionAt_bijective_of_arcLength_eq hlength)

/-- In the saturated case, matching each restoring position to the
unique transfer losing at that rebase position defines a permutation of
the transfer circuit. -/
noncomputable def positionMonodromy
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength) :
    Equiv.Perm (Fin circuit.arcLength) :=
  (circuit.restoringPositionEquiv hminimal hlength).trans
    (circuit.lossPositionEquiv hminimal hlength).symm

/-- The position monodromy is characterized by matching a restoring
position to the equal loss position. -/
@[simp] theorem lossPositionAt_positionMonodromy
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    circuit.lossPositionAt
        (circuit.positionMonodromy hminimal hlength position) =
      circuit.restoringPositionAt position := by
  change (circuit.lossPositionEquiv hminimal hlength)
      ((circuit.lossPositionEquiv hminimal hlength).symm
        ((circuit.restoringPositionEquiv hminimal hlength) position)) =
    (circuit.restoringPositionEquiv hminimal hlength) position
  exact Equiv.apply_symm_apply _ _

/-- At each transfer position, the concrete loss and restoring positions
on the rebase trace are different. -/
theorem lossPositionAt_ne_restoringPositionAt
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (position : Fin circuit.arcLength) :
    circuit.lossPositionAt position ≠
      circuit.restoringPositionAt position := by
  exact (circuit.transferAt position).lossPosition_ne_restoringPosition

/-- The saturated position monodromy has no fixed transfer position. -/
theorem positionMonodromy_ne_self
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    circuit.positionMonodromy hminimal hlength position ≠ position := by
  intro hfixed
  apply circuit.lossPositionAt_ne_restoringPositionAt position
  rw [← circuit.lossPositionAt_positionMonodromy hminimal hlength,
    hfixed]

/-- Position matching transports the source face at the matched loss to
the target face at the restoring transfer. -/
theorem sourceFace_positionMonodromy_eq_targetFace
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    (circuit.transferAt
        (circuit.positionMonodromy hminimal hlength position)).recovery.sourceFace =
      (circuit.transferAt position).recovery.targetFace := by
  let current := circuit.transferAt position
  let matched := circuit.transferAt
    (circuit.positionMonodromy hminimal hlength position)
  have hposition : matched.lossPosition =
      current.recovery.restoringPosition := by
    simpa [matched, current, lossPositionAt, restoringPositionAt] using
      circuit.lossPositionAt_positionMonodromy hminimal hlength position
  change matched.recovery.sourceFace = current.recovery.targetFace
  calc
    matched.recovery.sourceFace =
        ((rebaseCircuit.first :: rebaseCircuit.rest).get
          matched.lossPosition).selectedFace :=
      matched.selectedFace_at_lossPosition.symm
    _ = ((rebaseCircuit.first :: rebaseCircuit.rest).get
          current.recovery.restoringPosition).selectedFace := by
      rw [hposition]
    _ = current.recovery.targetFace :=
      current.recovery.selectedFace_get_restoringPosition

/-- Thus the saturated position monodromy follows the directed cyclic
face relation of the transfer circuit. -/
theorem transferAt_follows_positionMonodromy
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hminimal : circuit.IsLengthMinimal)
    (hlength : circuit.arcLength = rebaseCircuit.arcLength)
    (position : Fin circuit.arcLength) :
    ClosureRecoveryFaceTransfer.Follows
      (circuit.transferAt position)
      (circuit.transferAt
        (circuit.positionMonodromy hminimal hlength position)) := by
  exact (circuit.sourceFace_positionMonodromy_eq_targetFace
    hminimal hlength position).symm

/-- Below saturation, at least one displayed rebase position carries no
localized loss from the transfer circuit. -/
theorem exists_rebasePosition_not_lossPositionAt_of_lt
    (circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit)
    (hlength : circuit.arcLength < rebaseCircuit.arcLength) :
    ∃ position : Fin rebaseCircuit.arcLength,
      ∀ transferPosition : Fin circuit.arcLength,
        circuit.lossPositionAt transferPosition ≠ position := by
  by_contra hnone
  push Not at hnone
  have hsurjective : Function.Surjective circuit.lossPositionAt := by
    intro position
    rcases hnone position with ⟨transferPosition, hposition⟩
    exact ⟨transferPosition, hposition⟩
  have hcard := Fintype.card_le_of_surjective
    circuit.lossPositionAt hsurjective
  have hcard' : rebaseCircuit.arcLength ≤ circuit.arcLength := by
    simpa using hcard
  exact (Nat.not_le_of_gt hlength) hcard'

/-- Total outgoing provenance-retaining transfer on the selected faces
supplies a shortest concrete transfer circuit. -/
theorem exists_lengthMinimal_of_forall_outgoing
    (rebaseCircuit : CrossCentralExactFaceCertifiedRebaseCircuit graphData
      minimal baseData)
    (houtgoing : ∀ sourceFace ∈ rebaseCircuit.selectedFaces,
      ∃ targetFace,
        rebaseCircuit.ClosureRecoveryFaceTransferDependency
          sourceFace targetFace) :
    ∃ circuit : ClosureRecoveryFaceTransferCircuit rebaseCircuit,
      circuit.IsLengthMinimal := by
  exact exists_lengthMinimal
    (rebaseCircuit.exists_recoveryFaceTransferCircuit_of_forall_outgoing
      houtgoing)

end ClosureRecoveryFaceTransferCircuit

end GoertzelV24AdjacentPairInsertion.AdjacentPairData

end

end Mettapedia.GraphTheory.FourColor
