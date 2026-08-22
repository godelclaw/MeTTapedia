import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseSuccessorRoles

/-!
# Exhaustive named roles for the tracked boundary-rebase switch

The tracked boundary-rebase step is carried by at most eight literal edges:
at most six old-prefix attachment roles and the two newly displayed successor
crossings.  Earlier files gave each family its own coordinate in the finite
switch.  This file proves that those named coordinates exhaust the switch.

The result turns any later recurrence proof into an explicit old/new case
split.  On the old/old block the accumulated component matrix is already
computed exactly by the incoming residual-aware profile state.  Cases
involving a newly displayed crossing remain genuine recurrence obligations;
they are not filled by an arbitrary matrix or hidden in a padded coordinate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseTrackedSwitchRolesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The literal names of all possible tracked-switch coordinates: an old
attachment role or one of the two newly displayed successor crossings. -/
abbrev SourceCorridorSerialBoundaryRebaseTrackedSwitchRole
    {blockLength : Nat} (offset : Fin (blockLength - 3)) :=
  SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset ⊕ Fin 2

/-- Send every literal old/new switch role to the coordinate used by the
finite tracked rebase code. -/
noncomputable def sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt
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
    SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset →
      Fin (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext
          (fun _ => 0)).vertexCount.val
  | .inl role =>
      sourceCorridorSerialBoundaryRebaseOldAttachmentCoordinateAt realization
        hcubic hrotation htwoSided hunique offset hnext role
  | .inr step =>
      (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext
          (fun _ => 0)).point step

@[simp]
theorem sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_old
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
    (role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
        hcubic hrotation htwoSided hunique offset hnext (.inl role) =
      sourceCorridorSerialBoundaryRebaseOldAttachmentCoordinateAt realization
        hcubic hrotation htwoSided hunique offset hnext role :=
  rfl

@[simp]
theorem sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_new
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
    (step : Fin 2) :
    sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
        hcubic hrotation htwoSided hunique offset hnext (.inr step) =
      (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext
          (fun _ => 0)).point step :=
  rfl

/-- The six old roles and two new crossings exhaust the exact finite switch.
The map need not be injective: a literal edge may have more than one valid
source role, and retaining that quotient is the faithful representation. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_surjective
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
    Function.Surjective
      (sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
        hcubic hrotation htwoSided hunique offset hnext) := by
  intro coordinate
  let carrier := sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
    hcubic hrotation htwoSided hunique offset hnext
  let edge := (carrierCoordinate carrier).symm coordinate
  have hedge : edge.1 ∈
      sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeSetAt realization
          hcubic hrotation htwoSided hunique offset ∪
        sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
          hrotation htwoSided hunique offset hnext := by
    exact edge.2
  rcases Finset.mem_union.mp hedge with hold | hnew
  · rcases Finset.mem_image.mp hold with ⟨role, _hrole, hedgeRole⟩
    refine ⟨.inl role, ?_⟩
    change carrierCoordinate carrier
        ⟨sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
            hcubic hrotation htwoSided hunique offset role,
          sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt_mem_finiteSwitch
            realization hcubic hrotation htwoSided hunique offset hnext role⟩ =
      coordinate
    rw [← (carrierCoordinate carrier).apply_symm_apply coordinate]
    exact congrArg (carrierCoordinate carrier) (Subtype.ext hedgeRole)
  · rcases (mem_indexedCrossingEdgeSet_iff _ _).mp hnew with
      ⟨step, hedgeStep⟩
    refine ⟨.inr step, ?_⟩
    rw [sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_new,
      sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_point]
    change carrierCoordinate carrier
        ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
            hrotation htwoSided hunique offset hnext step,
          sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
            realization hcubic hrotation htwoSided hunique offset hnext step⟩ =
      coordinate
    rw [← (carrierCoordinate carrier).apply_symm_apply coordinate]
    have hsub :
        (⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
              hrotation htwoSided hunique offset hnext step,
            sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
              realization hcubic hrotation htwoSided hunique offset hnext
                step⟩ : {edge // edge ∈ carrier}) = edge := by
      apply Subtype.ext
      exact hedgeStep
    exact congrArg (carrierCoordinate carrier) hsub

/-- Choose one literal role for every finite switch coordinate.  The choice
is intentionally only a right inverse: when old and new presentations name
the same literal edge, quotienting those names is the correct behavior. -/
noncomputable def sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtCoordinate
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
    SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset :=
  Classical.choose
    (sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_surjective
      realization hcubic hrotation htwoSided hunique offset hnext coordinate)

/-- The chosen literal role decodes back to the original finite switch
coordinate. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_roleAtCoordinate
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
    sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
        hcubic hrotation htwoSided hunique offset hnext
        (sourceCorridorSerialBoundaryRebaseTrackedSwitchRoleAtCoordinate
          realization hcubic hrotation htwoSided hunique offset hnext
            coordinate) = coordinate :=
  Classical.choose_spec
    (sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_surjective
      realization hcubic hrotation htwoSided hunique offset hnext coordinate)

/-- On the old/old block of the exhaustive switch-role presentation, the
prefix matrix is exactly the residual-aware relation computed from the
incoming two-port profile and finite residual state. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_switchOld_iff_residualProfileFactored
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
    (left right : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset) :
    (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).oldComponent pair
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt
            realization hcubic hrotation htwoSided hunique offset hnext
              (.inl left))
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt
            realization hcubic hrotation htwoSided hunique offset hnext
              (.inl right)) = true ↔
      sourceCorridorSerialBoundaryRebaseResidualProfileFactoredTrackedStep
        realization hcubic hrotation htwoSided hunique offset color hcolor pair
          left right := by
  exact
    sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_oldRole_iff_residualProfileFactored
      realization hcubic hrotation htwoSided hunique offset hnext color hcolor
        pair left right

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
