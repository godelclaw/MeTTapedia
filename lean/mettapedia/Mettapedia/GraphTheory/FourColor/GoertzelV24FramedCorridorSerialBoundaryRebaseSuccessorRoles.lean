import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseTrackedStepState
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebasePortCarrier

/-!
# Successor-state roles of a literal serial boundary rebase

The finite rebase switch has two displayed crossings in addition to its old
attachment roles.  They are not anonymous extra state: definitionally, they
are the two input crossings of the successor source Cell.  At the same time,
the outgoing crossings of the current Cell become the unique predecessor
output roles of that successor.

This file records the resulting four-port map into the successor residual
state.  It is the coordinate glue needed to alternate the finite Cell decoder
with the finite boundary-rebase decoder.  It also reads the successor input
profile's tracked-connectivity matrix exactly from the finite rebase step
code.  It does not yet construct the complete alternating recurrence or
update the occurrence-sensitive facial state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseSuccessorRolesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The four named rebase ports, viewed as exact roles of the successor
residual state.  Old output ports become predecessor-output roles; newly
displayed ports become current-input roles. -/
def sourceCorridorSerialBoundaryRebaseSuccessorRole
    {blockLength : Nat}
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin 2 ⊕ Fin 2 →
      SourceCorridorSerialBoundaryRebaseOldAttachmentRole
        (sourceCorridorSerialNextOffset offset hnext)
  | .inl old => .inr (⟨offset, rfl⟩, old)
  | .inr new => .inl (.inl new)

/-- The four named rebase ports occupy distinct syntactic roles in the
successor state. -/
theorem sourceCorridorSerialBoundaryRebaseSuccessorRole_injective
    {blockLength : Nat}
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Function.Injective
      (sourceCorridorSerialBoundaryRebaseSuccessorRole
        offset hnext) := by
  intro first second heq
  rcases first with old | new <;> rcases second with old' | new'
  · simp only [sourceCorridorSerialBoundaryRebaseSuccessorRole,
      Sum.inr.injEq, Prod.mk.injEq] at heq
    exact congrArg Sum.inl heq.2
  · simp [sourceCorridorSerialBoundaryRebaseSuccessorRole] at heq
  · simp [sourceCorridorSerialBoundaryRebaseSuccessorRole] at heq
  · simp only [sourceCorridorSerialBoundaryRebaseSuccessorRole,
      Sum.inl.injEq] at heq
    exact congrArg Sum.inr heq

/-- The ambient edge named by each successor role is exactly the corresponding
old-or-new port of the literal rebase. -/
theorem sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt_successorRole
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
    (port : Fin 2 ⊕ Fin 2) :
    sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization hcubic
        hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext)
        (sourceCorridorSerialBoundaryRebaseSuccessorRole
          offset hnext port) =
      (sourceCorridorSerialBoundaryRebasePortAt realization hcubic hrotation
        htwoSided hunique offset hnext port).1 := by
  rcases port with old | new <;>
    rfl

/-- In particular, the two formerly unclassified switch crossings are the
successor state's two current-input roles. -/
theorem sourceCorridorSerialBoundaryRebaseCrossingAt_eq_successorInputRole
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
    (hnext : offset.val + 1 < blockLength - 3) (step : Fin 2) :
    sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic hrotation
        htwoSided hunique offset hnext step =
      sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization hcubic
        hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) (.inl (.inl step)) := by
  rfl

/-- The current output ports are exactly the predecessor-output roles of the
successor state. -/
theorem sourceSlabOutputCrossingAt_eq_successorPredecessorRole
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
    (hnext : offset.val + 1 < blockLength - 3) (step : Fin 2) :
    (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing step =
      sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization hcubic
        hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext)
        (.inr (⟨offset, rfl⟩, step)) := by
  rfl

/-- The successor input profile's tracked-connectivity coordinate is computed
exactly by the finite rebase step code.  This is the tracked half of the
boundary-rebase decoder equation; the occurrence-sensitive face coordinates
remain separate. -/
theorem sourceCorridorSerialInputBoundedProfileAt_next_strandConnected_eq_true_iff_trackedStepCode
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
        hunique (sourceCorridorSerialNextOffset offset hnext))
        |>.localLayerPrefixCrossing step) ≠ 0)
    (pair : TrackedColorPair) (left right : Fin 2) :
    ((sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
      htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
      hcolor).profile.strandConnected pair (.inl left) (.inl right) = true) ↔
      IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (sourceCorridorSerialBoundaryRebaseCrossingAt realization
            hcubic hrotation htwoSided hunique offset hnext left)) ∧
        IsTrackedColor (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2
          (color (sourceCorridorSerialBoundaryRebaseCrossingAt realization
            hcubic hrotation htwoSided hunique offset hnext right)) ∧
        Relation.ReflTransGen
          (boundedSerialBoundaryRebaseTrackedComponentStep
            (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
              hcubic hrotation htwoSided hunique offset hnext color) pair)
          ((sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
            hcubic hrotation htwoSided hunique offset hnext color
            ).localCode.point left)
          ((sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
            hcubic hrotation htwoSided hunique offset hnext color
            ).localCode.point right) := by
  let data := sourceCorridorSerialInputCutDataAt realization hcubic hrotation
    htwoSided hunique (sourceCorridorSerialNextOffset offset hnext)
  change
    ((data.regionalProfile color hcolor).strandConnected pair
      (.inl left) (.inl right) = true) ↔ _
  rw [data.regionalProfile_strandConnected_eq_true_iff]
  constructor
  · rintro ⟨_leftMem, _rightMem, hleft, hright, hreachable⟩
    refine ⟨hleft, hright, ?_⟩
    exact
      (sourceCorridorSerialInputTrackedGraph_next_reachable_iff_trackedStepCode
        realization hcubic hrotation htwoSided hunique offset hnext color pair
        left right).1 hreachable
  · rintro ⟨hleft, hright, hreachable⟩
    refine ⟨
      sourceCorridorSerialInputCutDataAt_portsInRegion realization hcubic
        hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) (.inl left),
      sourceCorridorSerialInputCutDataAt_portsInRegion realization hcubic
        hrotation htwoSided hunique
        (sourceCorridorSerialNextOffset offset hnext) (.inl right),
      hleft, hright, ?_⟩
    exact
      (sourceCorridorSerialInputTrackedGraph_next_reachable_iff_trackedStepCode
        realization hcubic hrotation htwoSided hunique offset hnext color pair
        left right).2 hreachable

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
