import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedTransitionFactorization

/-!
# The actual finite edge carrier of one stable tracked transition

The twelve stable transition slots are source names, and distinct names may
denote the same literal edge.  This file interprets them as one finite edge
set.  The two unavailable predecessor names at the first offset are sent to
an already present current crossing, so the total interpretation introduces
no fictitious edge.

The resulting carrier has cardinality at most twelve and contains both the
current and successor eight-edge rebase switches.  No injectivity of source
names is asserted, and no connectivity recurrence is proved here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableTrackedTransitionFiniteSwitchEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Total interpretation of the twelve transition names.  An unavailable
initial predecessor name falls back to the first current rebase crossing,
which is already a literal edge of both the name image and the transition. -/
noncomputable def sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot
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
    (slot : BoundedSerialBoundaryRebaseTrackedTransitionSlot) : G.edgeSet :=
  (sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot? realization
      hcubic hrotation htwoSided hunique offset hnext hnextNext slot).getD
    (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic hrotation
      htwoSided hunique offset hnext 0)

/-- The actual finite switch is the quotient-aware image of the twelve source
names under their literal-edge interpretation. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableTransitionFiniteSwitchAt
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
    Finset G.edgeSet :=
  Finset.univ.image
    (sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot realization
      hcubic hrotation htwoSided hunique offset hnext hnextNext)

/-- Every interpreted slot belongs to the finite transition switch. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot_mem_finiteSwitch
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
    (slot : BoundedSerialBoundaryRebaseTrackedTransitionSlot) :
    sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot realization
        hcubic hrotation htwoSided hunique offset hnext hnextNext slot ∈
      sourceCorridorSerialBoundaryRebaseStableTransitionFiniteSwitchAt
        realization hcubic hrotation htwoSided hunique offset hnext
          hnextNext := by
  exact Finset.mem_image.2 ⟨slot, Finset.mem_univ _, rfl⟩

/-- Quotienting repeated names can only decrease the twelve-slot bound. -/
theorem sourceCorridorSerialBoundaryRebaseStableTransitionFiniteSwitchAt_card_le_twelve
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
    (sourceCorridorSerialBoundaryRebaseStableTransitionFiniteSwitchAt
      realization hcubic hrotation htwoSided hunique offset hnext hnextNext
      ).card ≤ 12 := by
  calc
    _ ≤ (Finset.univ : Finset
        BoundedSerialBoundaryRebaseTrackedTransitionSlot).card :=
      Finset.card_image_le
    _ = 12 := by simp

/-- A current dependent switch role retains its literal edge under the total
transition interpretation. -/
@[simp] theorem sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot_currentRole
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
    sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot realization
        hcubic hrotation htwoSided hunique offset hnext hnextNext
        (.inl (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot role)) =
      sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization hcubic
        hrotation htwoSided hunique offset hnext role := by
  simp [sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot]

/-- Every actual edge in the current exact switch occurs in the twelve-edge
transition carrier. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteSwitchAt_subset_stableTransitionFiniteSwitch
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
    sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
        hrotation htwoSided hunique offset hnext ⊆
      sourceCorridorSerialBoundaryRebaseStableTransitionFiniteSwitchAt
        realization hcubic hrotation htwoSided hunique offset hnext
          hnextNext := by
  intro edge hedge
  let carrier := sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
    hcubic hrotation htwoSided hunique offset hnext
  let coordinate := carrierCoordinate carrier ⟨edge, hedge⟩
  let role := sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtCoordinate
    realization hcubic hrotation htwoSided hunique offset hnext coordinate
  have hslot :=
    sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot_mem_finiteSwitch
      realization hcubic hrotation htwoSided hunique offset hnext hnextNext
        (.inl (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot role))
  rw [sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot_currentRole]
    at hslot
  rw [sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt_roleAtCoordinate]
    at hslot
  change ((carrierCoordinate carrier).symm coordinate).1 ∈ _ at hslot
  simpa [coordinate] using hslot

/-- Every successor dependent role retains its literal edge when embedded in
the stable transition carrier. -/
@[simp] theorem sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot_successorRole
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
    (role : SourceCorridorSerialBoundaryRebaseTrackedSwitchRole
      (sourceCorridorSerialNextOffset offset hnext)) :
    sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot realization
        hcubic hrotation htwoSided hunique offset hnext hnextNext
        (boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot role)) =
      sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization hcubic
        hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) hnextNext role := by
  generalize hside :
      boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv
        (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot role) = side
  rcases side with inherited | fresh
  · have hslot :
        sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot role =
          boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot inherited := by
      apply boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv.injective
      simpa using hside
    have hrole : role =
        sourceCorridorSerialBoundaryRebaseSuccessorInheritedSwitchRole
          offset hnext inherited := by
      apply Option.some.inj
      calc
        some role = sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?
            (sourceCorridorSerialNextOffset offset hnext)
            (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot role) := by
          symm
          apply sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?_slot
        _ = sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?
            (sourceCorridorSerialNextOffset offset hnext)
            (boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot
              inherited) := congrArg _ hslot
        _ = some
            (sourceCorridorSerialBoundaryRebaseSuccessorInheritedSwitchRole
              offset hnext inherited) := by
          rw [← sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot_successorInheritedRole
            offset hnext inherited]
          apply sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?_slot
    subst role
    rw [sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot_successorInheritedRole]
    unfold sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot
    change
      (sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot?
        realization hcubic hrotation htwoSided hunique offset hnext hnextNext
        (boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot
          (boundedSerialBoundaryRebaseSuccessorInheritedSwitchSlot inherited))
        ).getD _ = _
    rw [sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot?_successorInherited]
    rfl
  · have hslot :
        sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot role =
          boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot fresh := by
      apply boundedSerialBoundaryRebaseSuccessorSwitchSlotEquiv.injective
      simpa using hside
    have hrole : role =
        sourceCorridorSerialBoundaryRebaseSuccessorFreshSwitchRole
          offset hnext fresh := by
      apply Option.some.inj
      calc
        some role = sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?
            (sourceCorridorSerialNextOffset offset hnext)
            (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot role) := by
          symm
          apply sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?_slot
        _ = sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?
            (sourceCorridorSerialNextOffset offset hnext)
            (boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot fresh) :=
          congrArg _ hslot
        _ = some
            (sourceCorridorSerialBoundaryRebaseSuccessorFreshSwitchRole
              offset hnext fresh) := by
          rw [← sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot_successorFreshRole
            offset hnext fresh]
          apply sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?_slot
    subst role
    rw [sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot_successorFreshRole]
    unfold sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot
    change
      (sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot?
        realization hcubic hrotation htwoSided hunique offset hnext hnextNext
        (boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot
          (boundedSerialBoundaryRebaseCurrentOutgoingSwitchSlot fresh))
        ).getD _ = _
    rw [sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot?_successorFresh]
    rfl

/-- Every actual edge in the successor exact switch occurs in the same
twelve-edge transition carrier. -/
theorem sourceCorridorSerialBoundaryRebaseSuccessorFiniteSwitchAt_subset_stableTransitionFiniteSwitch
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
    sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
        hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) hnextNext ⊆
      sourceCorridorSerialBoundaryRebaseStableTransitionFiniteSwitchAt
        realization hcubic hrotation htwoSided hunique offset hnext
          hnextNext := by
  intro edge hedge
  let successorOffset := sourceCorridorSerialNextOffset offset hnext
  let carrier := sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
    hcubic hrotation htwoSided hunique successorOffset hnextNext
  let coordinate := carrierCoordinate carrier ⟨edge, hedge⟩
  let role := sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtCoordinate
    realization hcubic hrotation htwoSided hunique successorOffset hnextNext
      coordinate
  have hslot :=
    sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot_mem_finiteSwitch
      realization hcubic hrotation htwoSided hunique offset hnext hnextNext
        (boundedSerialBoundaryRebaseSuccessorSwitchTransitionSlot
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot role))
  rw [sourceCorridorSerialBoundaryRebaseTrackedTransitionEdgeAtSlot_successorRole]
    at hslot
  rw [sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt_roleAtCoordinate]
    at hslot
  change ((carrierCoordinate carrier).symm coordinate).1 ∈ _ at hslot
  simpa [coordinate] using hslot

end AnnularEmbedding

end SourceTrail

end


end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
