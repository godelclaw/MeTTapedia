import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseTrackedSwitchRoles

/-!
# Exact old-state decoding on the exhaustive tracked rebase switch

The finite rebase switch has six old attachment roles and two newly displayed
successor crossings.  The old/old block of its accumulated component matrix is
already read exactly from the incoming residual-aware profile state.  This file
shows that the same description covers the whole switch as soon as one literal
geometric statement is available: every newly displayed crossing which was
already present in the old prefix has one of the recorded old attachment roles.

Under that coverage statement, the complete old-component matrix is exactly
the identity relation, together with the incoming residual-aware relation
transported along equal switch coordinates.  The statement permits literal
role overlap and therefore does not assume that old and new presentations are
disjoint.  It also keeps the remaining coverage fact visible; no arbitrary
Boolean block is inserted for the two new crossings.
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
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseTrackedSwitchCoverageEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A nontrivial path in a regional tracked graph has both endpoints in the
region.  The equality case is retained because graph reachability is
reflexive even at a vertex outside the region. -/
theorem regionalTrackedEdgeGraph_reachable_eq_or_mem_region
    {E : Type*} [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (region : Finset E) (color : E → Color)
    (first second : Color) {left right : E}
    (hreachable :
      (regionalTrackedEdgeGraph RS region color first second).Reachable
        left right) :
    left = right ∨ (left ∈ region ∧ right ∈ region) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreachable
  induction hreachable with
  | refl => exact Or.inl rfl
  | @tail middle finish _ hadj ih =>
      apply Or.inr
      have hmiddle : middle ∈ region := hadj.2.1
      have hfinish : finish ∈ region := hadj.2.2
      rcases ih with hstart | hstart
      · exact ⟨hstart ▸ hmiddle, hfinish⟩
      · exact ⟨hstart.1, hfinish⟩

namespace SourceTrail

namespace AnnularEmbedding

/-- The ambient edge denoted by one exhaustive old/new switch role. -/
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

/-- The exhaustive switch coordinate is the carrier coordinate of the edge
named by its role. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_eq_edge
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
    (role : SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset) :
    sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
        hcubic hrotation htwoSided hunique offset hnext role =
      carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext)
        ⟨sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
            hcubic hrotation htwoSided hunique offset hnext role,
          by
            rcases role with old | new
            · exact
                sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt_mem_finiteSwitch
                  realization hcubic hrotation htwoSided hunique offset hnext
                    old
            · exact
                sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
                  realization hcubic hrotation htwoSided hunique offset hnext
                    new⟩ := by
  rcases role with old | new
  · rfl
  · exact sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_point
      realization hcubic hrotation htwoSided hunique offset hnext (fun _ => 0)
        new

/-- The exact geometric coverage premise left by the finite recurrence: a
successor crossing which was already in the old prefix must coincide with a
recorded old attachment role. -/
def SourceCorridorSerialBoundaryRebaseNewInOldCovered
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
    (hnext : offset.val + 1 < blockLength - 3) : Prop :=
  ∀ step : Fin 2,
    sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic hrotation
        htwoSided hunique offset hnext step ∈
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges →
    ∃ role : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset,
      sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
          hrotation htwoSided hunique offset hnext step =
        sourceCorridorSerialBoundaryRebaseOldAttachmentEdgeAt realization
          hcubic hrotation htwoSided hunique offset role

/-- A role whose edge lies in the old prefix has an equal old-role coordinate,
provided the two new crossings satisfy the exact coverage premise. -/
theorem exists_oldRole_coordinate_eq_of_switchEdge_mem_old
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
    (hcovered : SourceCorridorSerialBoundaryRebaseNewInOldCovered realization
      hcubic hrotation htwoSided hunique offset hnext)
    (switchRole : SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset)
    (hmem : sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt realization
        hcubic hrotation htwoSided hunique offset hnext switchRole ∈
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges) :
    ∃ oldRole : SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset,
      sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
          hcubic hrotation htwoSided hunique offset hnext switchRole =
        sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
          hcubic hrotation htwoSided hunique offset hnext (.inl oldRole) := by
  rcases switchRole with old | new
  · exact ⟨old, rfl⟩
  · rcases hcovered new hmem with ⟨old, hedge⟩
    refine ⟨old, ?_⟩
    rw [sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_eq_edge,
      sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_eq_edge]
    apply congrArg (carrierCoordinate
      (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
        hrotation htwoSided hunique offset hnext))
    apply Subtype.ext
    exact hedge

/-- Under new-in-old coverage, the complete accumulated-prefix component
matrix on the exhaustive switch is exactly identity plus the incoming
residual-aware relation transported along old-role coordinates. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_switch_iff_identity_or_residualProfileFactored
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
    (hcovered : SourceCorridorSerialBoundaryRebaseNewInOldCovered realization
      hcubic hrotation htwoSided hunique offset hnext)
    (pair : TrackedColorPair)
    (left right : SourceCorridorSerialBoundaryRebaseTrackedSwitchRole offset) :
    (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).oldComponent pair
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt
            realization hcubic hrotation htwoSided hunique offset hnext left)
          (sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt
            realization hcubic hrotation htwoSided hunique offset hnext right) =
        true ↔
      sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
          hcubic hrotation htwoSided hunique offset hnext left =
        sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
          hcubic hrotation htwoSided hunique offset hnext right ∨
      ∃ oldLeft oldRight :
          SourceCorridorSerialBoundaryRebaseOldAttachmentRole offset,
        sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
            hcubic hrotation htwoSided hunique offset hnext left =
          sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
            hcubic hrotation htwoSided hunique offset hnext (.inl oldLeft) ∧
        sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
            hcubic hrotation htwoSided hunique offset hnext right =
          sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
            hcubic hrotation htwoSided hunique offset hnext (.inl oldRight) ∧
        sourceCorridorSerialBoundaryRebaseResidualProfileFactoredTrackedStep
          realization hcubic hrotation htwoSided hunique offset color hcolor
            pair oldLeft oldRight := by
  let oldRegion :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let leftEdge := sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt
    realization hcubic hrotation htwoSided hunique offset hnext left
  let rightEdge := sourceCorridorSerialBoundaryRebaseTrackedSwitchEdgeAt
    realization hcubic hrotation htwoSided hunique offset hnext right
  constructor
  · intro hcomponent
    by_cases heq :
        sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
            hcubic hrotation htwoSided hunique offset hnext left =
          sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt realization
            hcubic hrotation htwoSided hunique offset hnext right
    · exact Or.inl heq
    · apply Or.inr
      have hcomponentCode := hcomponent
      rw [sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_oldComponent_eq_true_iff]
        at hcomponent
      have hleftEdge :
          ((carrierCoordinate
            (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
              hcubic hrotation htwoSided hunique offset hnext)).symm
            (sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt
              realization hcubic hrotation htwoSided hunique offset hnext
                left)).1 = leftEdge := by
        rw [sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_eq_edge,
          Equiv.symm_apply_apply]
      have hrightEdge :
          ((carrierCoordinate
            (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
              hcubic hrotation htwoSided hunique offset hnext)).symm
            (sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt
              realization hcubic hrotation htwoSided hunique offset hnext
                right)).1 = rightEdge := by
        rw [sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_eq_edge,
          Equiv.symm_apply_apply]
      rw [hleftEdge, hrightEdge] at hcomponent
      have hedgesNe : leftEdge ≠ rightEdge := by
        intro hedge
        apply heq
        rw [sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_eq_edge,
          sourceCorridorSerialBoundaryRebaseTrackedSwitchCoordinateAt_eq_edge]
        apply congrArg (carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
            hrotation htwoSided hunique offset hnext))
        apply Subtype.ext
        exact hedge
      have hmem := regionalTrackedEdgeGraph_reachable_eq_or_mem_region
        embedded.cellulation.rotation.toRotationSystem oldRegion color
          (trackedColorPairColors pair).1 (trackedColorPairColors pair).2
            hcomponent
      rcases hmem with hedge | hmem
      · exact (hedgesNe hedge).elim
      · rcases exists_oldRole_coordinate_eq_of_switchEdge_mem_old
          realization hcubic hrotation htwoSided hunique offset hnext hcovered
            left hmem.1 with ⟨oldLeft, hleft⟩
        rcases exists_oldRole_coordinate_eq_of_switchEdge_mem_old
          realization hcubic hrotation htwoSided hunique offset hnext hcovered
            right hmem.2 with ⟨oldRight, hright⟩
        refine ⟨oldLeft, oldRight, hleft, hright, ?_⟩
        apply
          (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_switchOld_iff_residualProfileFactored
            realization hcubic hrotation htwoSided hunique offset hnext color
              hcolor pair oldLeft oldRight).1
        rw [← hleft, ← hright]
        exact hcomponentCode
  · rintro (heq | ⟨oldLeft, oldRight, hleft, hright, hresidual⟩)
    · rw [heq]
      apply
        (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_oldComponent_eq_true_iff
          realization hcubic hrotation htwoSided hunique offset hnext color _ _
            _).2
      exact SimpleGraph.Reachable.refl _
    · rw [hleft, hright]
      apply
        (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_switchOld_iff_residualProfileFactored
          realization hcubic hrotation htwoSided hunique offset hnext color
            hcolor pair oldLeft oldRight).2
      exact hresidual

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
