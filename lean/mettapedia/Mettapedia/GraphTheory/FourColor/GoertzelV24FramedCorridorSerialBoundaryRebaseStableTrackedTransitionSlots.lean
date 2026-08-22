import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedSwitchSuccessorSlots

/-!
# A stable twelve-slot carrier for one tracked source transition

The current and successor eight-slot switches overlap in four literal edges.
Keeping two disjoint copies would obscure that overlap; retaining only the
successor switch would discard four current attachment names which the rebase
may still use.  The exact fixed transition carrier therefore consists of all
eight current slots plus only the four fresh successor slots.

This file defines that twelve-slot ABI and embeds both switches into it.  The
successor embedding is injective, inherited slots land on their current names,
and fresh slots land on the new half.  The source interpretation proves both
families name their literal ambient edges.  This is still coordinate geometry,
not the tracked reachability update on the carrier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

/-- Eight current switch names together with the four genuinely fresh names
of the successor switch. -/
abbrev BoundedSerialBoundaryRebaseTrackedTransitionSlot :=
  BoundedSerialBoundaryRebaseTrackedSwitchSlot ⊕
    BoundedSerialBoundaryRebaseSlidingPort

@[simp] theorem card_boundedSerialBoundaryRebaseTrackedTransitionSlot :
    Fintype.card BoundedSerialBoundaryRebaseTrackedTransitionSlot = 12 := by
  simp [BoundedSerialBoundaryRebaseTrackedTransitionSlot]

/-- Include every current switch slot in the transition carrier. -/
def boundedSerialBoundaryRebaseCurrentSwitchTransitionSlot
    (slot : BoundedSerialBoundaryRebaseTrackedSwitchSlot) :
    BoundedSerialBoundaryRebaseTrackedTransitionSlot :=
  .inl slot

/-- Include a successor switch slot, sharing inherited names with the current
half and allocating only its four fresh names on the new half. -/
def boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot
    (slot : BoundedSerialBoundaryRebaseTrackedSwitchSlot) :
    BoundedSerialBoundaryRebaseTrackedTransitionSlot :=
  match boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv slot with
  | .inl inherited => .inl
      (boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot inherited)
  | .inr fresh => .inr fresh

@[simp]
theorem boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot_inherited
    (port : BoundedSerialBoundaryRebaseSlidingPort) :
    boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot
        (boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot port) =
      boundedSerialBoundaryRebaseCurrentSwitchTransitionSlot
        (boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot port) := by
  simp [boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot,
    boundedSerialBoundaryRebaseCurrentSwitchTransitionSlot]

@[simp]
theorem boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot_fresh
    (port : BoundedSerialBoundaryRebaseSlidingPort) :
    boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot
        (boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot port) =
      .inr port := by
  simp [boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot]

/-- Distinct current outgoing ports have distinct stable switch names. -/
theorem boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot_injective :
    Function.Injective boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot := by
  intro first second heq
  have hencoded := congrArg
    boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv heq
  simpa using hencoded

/-- Distinct inherited ports have distinct successor switch names. -/
theorem boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot_injective :
    Function.Injective
      boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot := by
  intro first second heq
  have hencoded := congrArg
    boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv heq
  simpa using hencoded

/-- The successor switch loses no names when embedded into the twelve-slot
transition carrier. -/
theorem boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot_injective :
    Function.Injective
      boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot := by
  intro first second heq
  apply boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv.injective
  generalize hfirst :
      boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv first = firstSide
  generalize hsecond :
      boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv second = secondSide
  rw [boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot, hfirst,
    boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot, hsecond] at heq
  rcases firstSide with inherited | fresh <;>
    rcases secondSide with inherited' | fresh'
  · exact congrArg Sum.inl
      (boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot_injective
        (Sum.inl.inj heq))
  · cases heq
  · cases heq
  · exact congrArg Sum.inr (Sum.inr.inj heq)

namespace SourceTrail

namespace AnnularEmbedding

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableTrackedTransitionSlotsEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The four genuinely fresh dependent roles of the successor switch: its
Cell outputs and its following-rebase crossings. -/
def sourceCorridorSerialBoundaryRebaseSuccessorFreshSwitchRole
    {blockLength : Nat} (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    BoundedSerialBoundaryRebaseSlidingPort →
      SourceCorridorSerialBoundaryRebaseTrackedSwitchRole
        (sourceCorridorSerialNextOffset offset hnext)
  | .inl output => .inl (.inl (.inr output))
  | .inr nextCrossing => .inr nextCrossing

@[simp]
theorem sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot_successorFreshRole
    {blockLength : Nat} (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (port : BoundedSerialBoundaryRebaseSlidingPort) :
    sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot
        (sourceCorridorSerialBoundaryRebaseSuccessorFreshSwitchRole
          offset hnext port) =
      boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot port := by
  rcases port with output | nextCrossing <;> rfl

/-- Interpret one stable transition slot as a literal ambient edge when its
source role is present.  Only the two current predecessor slots at offset zero
can decode to `none`; every fresh successor role is real. -/
noncomputable def sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot?
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
      (sourceCorridorSerialNextOffset offset hnext).val + 1 < blockLength - 3) :
    BoundedSerialBoundaryRebaseTrackedTransitionSlot → Option G.edgeSet
  | .inl currentSlot =>
      (sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?
        offset currentSlot).map
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
            hcubic hrotation htwoSided hunique offset hnext)
  | .inr fresh => some
      (sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
        hcubic hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) hnextNext
        (sourceCorridorSerialBoundaryRebaseSuccessorFreshSwitchRole
          offset hnext fresh))

/-- Every actual current switch role has its exact edge in the transition
carrier. -/
@[simp]
theorem sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot?_currentRole
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
    (role : SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset) :
    sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot? realization
        hcubic hrotation htwoSided hunique offset hnext hnextNext
        (.inl (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot role)) =
      some (sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
        hcubic hrotation htwoSided hunique offset hnext role) := by
  simp [sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot?]

/-- The inherited successor half is interpreted by the same literal edges as
its current outgoing names. -/
@[simp]
theorem sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot?_successorInherited
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
    sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot? realization
        hcubic hrotation htwoSided hunique offset hnext hnextNext
        (boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot
          (boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot port)) =
      some (sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
        hcubic hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) hnextNext
        (sourceCorridorSerialBoundaryRebaseSuccessorInheritedSwitchRole
          offset hnext port)) := by
  rcases port with previousOutput | currentInput <;> rfl

/-- The fresh successor half is interpreted by its literal Cell-output and
following-rebase edges. -/
@[simp]
theorem sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot?_successorFresh
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
    sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot? realization
        hcubic hrotation htwoSided hunique offset hnext hnextNext
        (boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot
          (boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot port)) =
      some (sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
        hcubic hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) hnextNext
        (sourceCorridorSerialBoundaryRebaseSuccessorFreshSwitchRole
          offset hnext port)) := by
  rcases port with output | nextCrossing <;> rfl

end


end AnnularEmbedding

end SourceTrail

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
