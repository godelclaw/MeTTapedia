import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedSwitchState

/-!
# Sliding the stable tracked switch between source Cells

The stable boundary-rebase switch has eight slots.  When the source corridor
advances by one literal Cell, four of those slots have literal predecessors:
the current Cell's two output crossings become predecessor-output roles, and
the two crossings exposed by the current rebase become successor-input roles.
The other four successor slots are its two output crossings and the two
crossings exposed by its own following rebase.

This file makes that four-plus-four partition exact and proves that the four
inherited names denote definitionally the same ambient edges on the two sides
of the slide.  It deliberately does not say that their tracked state values
are unchanged: adding the next literal Cell can change reachability.  The
partition is coordinate glue for that still-separate semantic update.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

/-- Four literal ports carried across one slide: two old outputs and two
newly exposed successor inputs. -/
abbrev BoundedSerialBoundaryRebaseSlidingPort := Fin 2 ⊕ Fin 2

/-- The current switch slots whose literal edges survive into the successor
switch. -/
def boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot :
    BoundedSerialBoundaryRebaseSlidingPort →
      BoundedSerialBoundaryRebaseTrackedSwitchSlot
  | .inl output => .inl (.inl (.inr output))
  | .inr crossing => .inr crossing

/-- The successor switch names for the four edges inherited from the current
switch. -/
def boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot :
    BoundedSerialBoundaryRebaseSlidingPort →
      BoundedSerialBoundaryRebaseTrackedSwitchSlot
  | .inl previousOutput => .inl (.inr previousOutput)
  | .inr currentInput => .inl (.inl (.inl currentInput))

/-- The eight successor slots split exactly into four inherited slots and four
fresh output/rebase slots.  The fresh half has the same syntactic shape as the
current outgoing half, ready for the next slide. -/
def boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv :
    BoundedSerialBoundaryRebaseTrackedSwitchSlot ≃
      (BoundedSerialBoundaryRebaseSlidingPort ⊕
        BoundedSerialBoundaryRebaseSlidingPort) where
  toFun
    | .inl (.inl (.inl input)) => .inl (.inr input)
    | .inl (.inl (.inr output)) => .inr (.inl output)
    | .inl (.inr previousOutput) => .inl (.inl previousOutput)
    | .inr nextCrossing => .inr (.inr nextCrossing)
  invFun
    | .inl inherited =>
        boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot inherited
    | .inr fresh =>
        boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot fresh
  left_inv slot := by
    rcases slot with current | nextCrossing
    · rcases current with current | previousOutput
      · rcases current with input | output <;> rfl
      · rfl
    · rfl
  right_inv side := by
    rcases side with inherited | fresh
    · rcases inherited with previousOutput | currentInput <;> rfl
    · rcases fresh with output | nextCrossing <;> rfl

@[simp] theorem boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv_inherited
    (port : BoundedSerialBoundaryRebaseSlidingPort) :
    boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv
        (boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot port) =
      .inl port := by
  rcases port with previousOutput | currentInput <;> rfl

@[simp] theorem boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv_fresh
    (port : BoundedSerialBoundaryRebaseSlidingPort) :
    boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv
        (boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot port) =
      .inr port := by
  rcases port with output | nextCrossing <;> rfl

/-- No inherited successor slot is silently reused as a fresh successor slot. -/
theorem boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot_ne_fresh
    (inherited fresh : BoundedSerialBoundaryRebaseSlidingPort) :
    boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot inherited ≠
      boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot fresh := by
  intro heq
  have := congrArg boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv heq
  simp at this

namespace SourceTrail

namespace AnnularEmbedding

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableTrackedSwitchSuccessorSlotsEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The dependent current-switch roles represented by the four outgoing
stable slots. -/
def sourceCorridorSerialBoundaryRebaseCurrentOutgoingSwitchRole
    {blockLength : Nat} {offset : Fin (blockLength - 3)} :
    BoundedSerialBoundaryRebaseSlidingPort →
      SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset
  | .inl output => .inl (.inl (.inr output))
  | .inr crossing => .inr crossing

/-- The corresponding dependent roles after advancing one source Cell. -/
def sourceCorridorSerialBoundaryRebaseSuccessorInheritedSwitchRole
    {blockLength : Nat} (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedSerialBoundaryRebaseSlidingPort →
      SourceCorridorSerialBoundaryRebaseTrackedSwitchRole
        (sourceCorridorSerialNextOffset offset hnext) :=
  fun port => .inl
    (sourceCorridorSerialBoundaryRebaseSuccessorRole offset hnext port)

@[simp]
theorem sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot_currentOutgoingRole
    {blockLength : Nat} {offset : Fin (blockLength - 3)}
    (port : BoundedSerialBoundaryRebaseSlidingPort) :
    sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot
        (@sourceCorridorSerialBoundaryRebaseCurrentOutgoingSwitchRole
          blockLength offset port) =
      boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot port := by
  rcases port with output | crossing <;> rfl

@[simp]
theorem sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot_successorInheritedRole
    {blockLength : Nat} (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : BoundedSerialBoundaryRebaseSlidingPort) :
    sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot
        (sourceCorridorSerialBoundaryRebaseSuccessorInheritedSwitchRole
          offset hnext port) =
      boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot port := by
  rcases port with previousOutput | currentInput <;> rfl

/-- The four inherited stable slots denote literally the same ambient edges
before and after the slide.  This is an equality of edge names, not of the
tracked reachability state computed around those edges. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt_currentOutgoing_eq_successorInherited
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hnextNext :
      (sourceCorridorSerialNextOffset offset hnext).val + 1 < blockLength - 3)
    (port : BoundedSerialBoundaryRebaseSlidingPort) :
    sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization hcubic
        hrotation htwoSided hunique offset hnext
        (sourceCorridorSerialBoundaryRebaseCurrentOutgoingSwitchRole port) =
      sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization hcubic
        hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) hnextNext
        (sourceCorridorSerialBoundaryRebaseSuccessorInheritedSwitchRole
          offset hnext port) := by
  rcases port with output | crossing <;> rfl

end

end AnnularEmbedding

end SourceTrail

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
