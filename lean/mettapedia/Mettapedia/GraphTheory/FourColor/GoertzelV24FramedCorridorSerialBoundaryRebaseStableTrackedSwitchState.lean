import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedStep
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseTrackedSwitchRoles

/-!
# Stable eight-slot tracked state for a serial boundary rebase

The six predecessor slots do not by themselves name the two successor
crossings whose interaction with the accumulated prefix is queried by a
boundary rebase.  This file adds exactly those two slots.  The resulting
eight-slot state records the old regional tracked graph relative to the old
displayed ports, including every old/new and new/new component question.

This is a finite source-image state, not an arbitrary component matrix.  It
identifies the smallest tracked state on which the complete rebase recurrence
can be stated.  Computing the next eight-slot state from this state and the
literal heterogeneous one-step receipt remains separate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

/-- Fixed names for the six predecessor contacts and the two newly displayed
successor crossings. -/
abbrev BoundedSerialBoundaryRebaseTrackedSwitchSlot :=
  BoundedSerialBoundaryRebaseOldAttachmentSlot ⊕ Fin 2

@[simp] theorem card_boundedSerialBoundaryRebaseTrackedSwitchSlot :
    Fintype.card BoundedSerialBoundaryRebaseTrackedSwitchSlot = 8 := by
  simp [BoundedSerialBoundaryRebaseTrackedSwitchSlot]

namespace SourceTrail

namespace AnnularEmbedding

/-- Erase only the predecessor proof in a dependent literal switch role. -/
def sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot
    {blockLength : Nat} {offset : Fin (blockLength - 3)} :
    SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset →
      BoundedSerialBoundaryRebaseTrackedSwitchSlot
  | .inl role => .inl
      (sourceCorridorSerialBoundaryRebaseOldAttachmentSlot role)
  | .inr step => .inr step

/-- Recover the dependent literal switch role represented by a stable slot,
when the predecessor contact exists. -/
noncomputable def sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?
    {blockLength : Nat} (offset : Fin (blockLength - 3)) :
    BoundedSerialBoundaryRebaseTrackedSwitchSlot →
      Option (SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset)
  | .inl slot =>
      (sourceCorridorSerialBoundaryRebaseOldAttachmentRoleAtSlot? offset slot
        ).map Sum.inl
  | .inr step => some (.inr step)

@[simp] theorem sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?_slot
    {blockLength : Nat} (offset : Fin (blockLength - 3))
    (role : SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset) :
    sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot? offset
        (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot role) =
      some role := by
  rcases role with role | step
  · simp [sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot,
      sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?]
  · rfl

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableTrackedSwitchStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The literal ambient edge named by one dependent switch role. -/
noncomputable def sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt
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
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset → G.edgeSet
  | .inl role =>
      sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
        hcubic hrotation htwoSided hunique offset role
  | .inr step =>
      sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
        hrotation htwoSided hunique offset hnext step

/-- Exact supported old-prefix state on all eight dependent switch roles. -/
noncomputable def sourceCorridorSerialBoundaryRebaseSwitchSupportedTrackedCodeAt
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
    (color : G.edgeSet → Color) :
    TrackedColorPair → BoundedSupportedPortResidualCode
      (SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset) (Fin 2) :=
  fun pair => exactSupportedPortResidualCode
    (regionalTrackedEdgeGraph
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges color
      (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2)
    (sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization hcubic
      hrotation htwoSided hunique offset hnext)
    ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).nextLocalLayerPrefixCrossing)

/-- Uniform eight-slot old-prefix state for all tracked colour pairs. -/
abbrev BoundedSerialBoundaryRebaseStableSwitchSupportedTrackedCode :=
  TrackedColorPair → BoundedSupportedPortResidualCode
    BoundedSerialBoundaryRebaseTrackedSwitchSlot (Fin 2)

/-- Transport the exact dependent switch state onto the stable eight slots. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableSwitchSupportedTrackedCodeAt
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
    (color : G.edgeSet → Color) :
    BoundedSerialBoundaryRebaseStableSwitchSupportedTrackedCode :=
  fun pair => padSupportedPortResidualCode
    (sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot? offset)
    (sourceCorridorSerialBoundaryRebaseSwitchSupportedTrackedCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color pair)

/-- The graph-free interpretation of the stable eight-slot state through an
incoming complete profile. -/
abbrev boundedSerialBoundaryRebaseStableSwitchProfileFactoredTrackedStep :=
  @boundedSupportedProfileFactoredTrackedStep
    BoundedSerialBoundaryRebaseTrackedSwitchSlot

/-- The dependent eight-role state and the incoming profile recover literal
old-prefix reachability exactly. -/
theorem sourceCorridorSerialBoundaryRebaseSwitchProfileFactoredTrackedStep_iff
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
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0)
    (pair : TrackedColorPair)
    (left right : SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset) :
    boundedSupportedProfileFactoredTrackedStep
        (sourceCorridorSerialBoundaryRebaseSwitchSupportedTrackedCodeAt
          realization hcubic hrotation htwoSided hunique offset hnext color)
        (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
          hrotation htwoSided hunique offset color hcolor)
        pair left right ↔
      (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
            hcubic hrotation htwoSided hunique offset hnext left)
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
            hcubic hrotation htwoSided hunique offset hnext right) := by
  let graph := regionalTrackedEdgeGraph
    embedded.cellulation.rotation.toRotationSystem
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges color
    (trackedColorPairColors pair).1
    (trackedColorPairColors pair).2
  let interfaceVertex :=
    sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization hcubic
      hrotation htwoSided hunique offset hnext
  let portVertex := fun port : Fin 2 =>
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
      offset).nextLocalLayerPrefixCrossing port
  let input := sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
    hrotation htwoSided hunique offset color hcolor
  let portConnected := fun leftPort rightPort : Fin 2 =>
    input.profile.strandConnected pair (.inl leftPort) (.inl rightPort) = true
  have hportSound : ∀ first second,
      portConnected first second →
        graph.Reachable (portVertex first) (portVertex second) := by
    intro first second hconnected
    let data := sourceCorridorSerialPrefixCutDataAt realization hcubic
      hrotation htwoSided hunique offset
    have hraw :
        (data.regionalProfile color hcolor).strandConnected pair
            (.inl first) (.inl second) = true := by
      simpa [input, sourceCorridorSerialPrefixBoundedProfileAt,
        sourceCorridorSerialPrefixCutDataAt, regionalBoundaryBoundedProfile,
        data, portConnected]
        using hconnected
    exact (data.regionalProfile_strandConnected_eq_true_iff
      color hcolor pair (.inl first) (.inl second)).1 hraw |>.2.2.2.2
  have hportComplete : ∀ first second,
      portVertex first ∈ graph.support →
      portVertex second ∈ graph.support →
      graph.Reachable (portVertex first) (portVertex second) →
        portConnected first second := by
    intro first second hfirstSupport hsecondSupport hreachable
    let data := sourceCorridorSerialPrefixCutDataAt realization hcubic
      hrotation htwoSided hunique offset
    rcases (SimpleGraph.mem_support graph).1 hfirstSupport with
      ⟨firstNeighbor, hfirstAdj⟩
    rcases (SimpleGraph.mem_support graph).1 hsecondSupport with
      ⟨secondNeighbor, hsecondAdj⟩
    have hraw :
        (data.regionalProfile color hcolor).strandConnected pair
            (.inl first) (.inl second) = true :=
      (data.regionalProfile_strandConnected_eq_true_iff
        color hcolor pair (.inl first) (.inl second)).2
        ⟨sourceCorridorSerialPrefixCutDataAt_portsInRegion realization hcubic
            hrotation htwoSided hunique offset (.inl first),
          sourceCorridorSerialPrefixCutDataAt_portsInRegion realization hcubic
            hrotation htwoSided hunique offset (.inl second),
          hfirstAdj.1.2.1, hsecondAdj.1.2.1, hreachable⟩
    simpa [input, sourceCorridorSerialPrefixBoundedProfileAt,
      sourceCorridorSerialPrefixCutDataAt, regionalBoundaryBoundedProfile,
      data, portConnected] using hraw
  change SupportedPortResidualFactoredReachability
      (exactSupportedPortResidualCode graph interfaceVertex portVertex)
      portConnected left right ↔
    graph.Reachable (interfaceVertex left) (interfaceVertex right)
  exact (reachable_iff_exactSupportedPortResidualFactoredReachability graph
    interfaceVertex portVertex portConnected hportSound hportComplete left
      right).symm

/-- On every encoded actual role, the stable eight-slot state has the same
exact old-prefix interpretation. -/
theorem sourceCorridorSerialBoundaryRebaseStableSwitchProfileFactoredTrackedStep_slot_iff
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
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0)
    (pair : TrackedColorPair)
    (left right : SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset) :
    boundedSerialBoundaryRebaseStableSwitchProfileFactoredTrackedStep
        (sourceCorridorSerialBoundaryRebaseStableSwitchSupportedTrackedCodeAt
          realization hcubic hrotation htwoSided hunique offset hnext color)
        (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
          hrotation htwoSided hunique offset color hcolor)
        pair
        (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot left)
        (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot right) ↔
      (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
            hcubic hrotation htwoSided hunique offset hnext left)
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
            hcubic hrotation htwoSided hunique offset hnext right) := by
  change boundedSupportedProfileFactoredTrackedStep
      (fun tracked => padSupportedPortResidualCode
        (sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot? offset)
        (sourceCorridorSerialBoundaryRebaseSwitchSupportedTrackedCodeAt
          realization hcubic hrotation htwoSided hunique offset hnext color
            tracked))
      (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color hcolor)
      pair
      (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot left)
      (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot right) ↔ _
  rw [boundedSerialBoundaryRebaseStableProfileFactoredTrackedStep_pad_iff
    (sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot? offset)
    (sourceCorridorSerialBoundaryRebaseSwitchSupportedTrackedCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color)
    (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
      htwoSided hunique offset color hcolor)
    pair
    (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot left)
    (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot right)
    left right
    (sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?_slot offset
      left)
    (sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtSlot?_slot offset
      right)]
  exact sourceCorridorSerialBoundaryRebaseSwitchProfileFactoredTrackedStep_iff
    realization hcubic hrotation htwoSided hunique offset hnext color hcolor
      pair left right

/-- Stable name chosen for each coordinate of the exact finite switch.  The
choice respects the literal-edge quotient already present in that carrier. -/
noncomputable def sourceCorridorSerialBoundaryRebaseTrackedSwitchSlotAtCoordinate
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
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext
          (fun _ => 0)).vertexCount.val) :
    BoundedSerialBoundaryRebaseTrackedSwitchSlot :=
  sourceCorridorSerialBoundaryRebaseTrackedSwitchSlot
    (sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtCoordinate
      realization hcubic hrotation htwoSided hunique offset hnext coordinate)

/-- The literal edge of the chosen role is the edge represented by the finite
switch coordinate. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt_roleAtCoordinate
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
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext
          (fun _ => 0)).vertexCount.val) :
    sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization hcubic
        hrotation htwoSided hunique offset hnext
        (sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtCoordinate
          realization hcubic hrotation htwoSided hunique offset hnext
            coordinate) =
      ((carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext)).symm coordinate).1 := by
  let carrier := sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
    hcubic hrotation htwoSided hunique offset hnext
  let role :=
    sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtCoordinate
      realization hcubic hrotation htwoSided hunique offset hnext coordinate
  have hrole (named : SourceCorridorSerialBoundaryRebaseTrackedSwitchRole
      offset) :
      ((carrierCoordinate carrier).symm
        (sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt
          realization hcubic hrotation htwoSided hunique offset hnext
            named)).1 =
        sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
          hcubic hrotation htwoSided hunique offset hnext named := by
    rcases named with old | step
    · change
        ((carrierCoordinate carrier).symm
          ((carrierCoordinate carrier)
            ⟨sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
                hcubic hrotation htwoSided hunique offset old,
              sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt_mem_finiteSwitch
                realization hcubic hrotation htwoSided hunique offset hnext
                  old⟩)).1 = _
      rw [Equiv.symm_apply_apply]
      rfl
    · rw [sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_new,
        sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_point]
      change
        ((carrierCoordinate carrier).symm
          ((carrierCoordinate carrier)
            ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
                hrotation htwoSided hunique offset hnext step,
              sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
                realization hcubic hrotation htwoSided hunique offset hnext
                  step⟩)).1 = _
      rw [Equiv.symm_apply_apply]
      rfl
  have hcoordinate :=
    sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_roleAtCoordinate
      realization hcubic hrotation htwoSided hunique offset hnext coordinate
  calc
    sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization hcubic
        hrotation htwoSided hunique offset hnext role =
        ((carrierCoordinate carrier).symm
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt
            realization hcubic hrotation htwoSided hunique offset hnext
              role)).1 := (hrole role).symm
    _ = ((carrierCoordinate carrier).symm coordinate).1 := by rw [hcoordinate]

/-- The entire formerly prefix-extracted `oldComponent` matrix is computed by
the incoming profile and the stable eight-slot residual state. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_oldComponent_iff_stableSwitchState
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
    (color : G.edgeSet → Color)
    (hcolor : ∀ step,
      color ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0)
    (pair : TrackedColorPair)
    (left right : Fin
      (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).localCode.vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).oldComponent pair left
          right = true ↔
      boundedSerialBoundaryRebaseStableSwitchProfileFactoredTrackedStep
        (sourceCorridorSerialBoundaryRebaseStableSwitchSupportedTrackedCodeAt
          realization hcubic hrotation htwoSided hunique offset hnext color)
        (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic
          hrotation htwoSided hunique offset color hcolor)
        pair
        (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlotAtCoordinate
          realization hcubic hrotation htwoSided hunique offset hnext left)
        (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlotAtCoordinate
          realization hcubic hrotation htwoSided hunique offset hnext right) := by
  let leftRole :=
    sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtCoordinate realization
      hcubic hrotation htwoSided hunique offset hnext left
  let rightRole :=
    sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtCoordinate realization
      hcubic hrotation htwoSided hunique offset hnext right
  rw [sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_oldComponent_eq_true_iff]
  have hstate :=
    sourceCorridorSerialBoundaryRebaseStableSwitchProfileFactoredTrackedStep_slot_iff
      realization hcubic hrotation htwoSided hunique offset hnext color hcolor
        pair leftRole rightRole
  rw [sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt_roleAtCoordinate,
    sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt_roleAtCoordinate]
    at hstate
  exact hstate.symm

end


end AnnularEmbedding

end SourceTrail

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
