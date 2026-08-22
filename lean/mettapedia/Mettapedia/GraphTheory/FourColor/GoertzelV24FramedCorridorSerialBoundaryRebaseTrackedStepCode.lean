import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFiniteSwitch

/-!
# A finite tracked step code for one literal serial rebase

The successor tracked graph is already contracted to an at-most-eight-edge
switch interface.  This file moves all three component relations onto finite
coordinates.  The two local factors are read from the existing literal rebase
receipt; the accumulated old-prefix factor is retained as a finite Boolean
component matrix on the same coordinates.

The resulting successor connectivity equation is graph-free and exact.  The
old matrix is deliberately named as state rather than disguised as part of a
history-independent letter: its recurrence from the preceding residual-aware
state and the next literal receipt remains the next obligation.  Capped facial
progress is also separate.
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
open GoertzelV24SimpleGraphThreeFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

/-- A finite tracked successor step.  `local` contains the new-edge and seam
graphs from the literal rebase receipt.  `oldComponent` is the accumulated
prefix component relation on exactly the same finite coordinates. -/
structure BoundedSerialBoundaryRebaseTrackedStepCode where
  localCode : BoundedCarrierGraphFamilyCode 8 2
    SourceTrail.AnnularEmbedding.SourceCorridorSerialBoundaryRebaseTrackedFactor
  oldComponent : TrackedColorPair →
    Fin localCode.vertexCount.val → Fin localCode.vertexCount.val → Bool

noncomputable instance :
    DecidableEq BoundedSerialBoundaryRebaseTrackedStepCode :=
  Classical.decEq _

private def boundedSerialBoundaryRebaseTrackedStepCodeEquiv :
    BoundedSerialBoundaryRebaseTrackedStepCode ≃
      Σ localCode : BoundedCarrierGraphFamilyCode 8 2
          SourceTrail.AnnularEmbedding.SourceCorridorSerialBoundaryRebaseTrackedFactor,
        TrackedColorPair →
          Fin localCode.vertexCount.val → Fin localCode.vertexCount.val → Bool where
  toFun code := ⟨code.localCode, code.oldComponent⟩
  invFun code :=
    { localCode := code.1
      oldComponent := code.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    Fintype BoundedSerialBoundaryRebaseTrackedStepCode :=
  Fintype.ofEquiv _ boundedSerialBoundaryRebaseTrackedStepCodeEquiv.symm

/-- One finite component move through the old state, the new-edge graph, or
the residual seam graph. -/
def boundedSerialBoundaryRebaseTrackedComponentStep
    (code : BoundedSerialBoundaryRebaseTrackedStepCode)
    (pair : TrackedColorPair)
    (left right : Fin code.localCode.vertexCount.val) : Prop :=
  code.oldComponent pair left right = true ∨
    (code.localCode.graph (false, pair)).Reachable left right ∨
    (code.localCode.graph (true, pair)).Reachable left right

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseTrackedStepCodeEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Both literal rebase graph factors are supported on the exact eight-edge
switch interface. -/
theorem sourceCorridorSerialBoundaryRebaseTrackedGraphAt_support_subset_finiteSwitch
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
    (factor : SourceCorridorSerialBoundaryRebaseTrackedFactor) :
    (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext color factor).support ⊆
      sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
        hrotation htwoSided hunique offset hnext := by
  rcases factor with ⟨flag, pair⟩
  cases flag
  · intro edge hedge
    rcases (SimpleGraph.mem_support _).1 hedge with ⟨neighbor, hadj⟩
    exact Finset.mem_union_right _ hadj.2.1
  · exact
      sourceCorridorSerialBoundaryRebaseTrackedSeamAt_support_subset_finiteSwitch
        realization hcubic hrotation htwoSided hunique offset hnext color
          (trackedColorPairColors pair).1 (trackedColorPairColors pair).2

/-- The new-edge and seam factors transported together onto the exact finite
switch interface, retaining the two successor ports. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt
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
    BoundedCarrierGraphFamilyCode 8 2
      SourceCorridorSerialBoundaryRebaseTrackedFactor :=
  boundedCarrierGraphFamilyCode
    (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
      hrotation htwoSided hunique offset hnext)
    8 2
    (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt_card_le_eight
      realization hcubic hrotation htwoSided hunique offset hnext)
    (fun step =>
      ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
          hrotation htwoSided hunique offset hnext step,
        sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
          realization hcubic hrotation htwoSided hunique offset hnext step⟩)
    (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext color)

/-- The two distinguished coordinates of the finite switch code are exactly
the successor crossings transported by the carrier equivalence. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_point
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
    (color : G.edgeSet → Color) (step : Fin 2) :
    (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color).point step =
      carrierCoordinate
        (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
          hrotation htwoSided hunique offset hnext)
        ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
            hrotation htwoSided hunique offset hnext step,
          sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
            realization hcubic hrotation htwoSided hunique offset hnext step⟩ := by
  rfl

/-- The finite local code preserves each factor's ambient reachability between
all switch vertices. -/
theorem sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_reachable_iff
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
    (factor : SourceCorridorSerialBoundaryRebaseTrackedFactor)
    (first second : {edge // edge ∈
      sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
        hrotation htwoSided hunique offset hnext}) :
    ((sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color).graph factor
      ).Reachable
        (carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
            hrotation htwoSided hunique offset hnext) first)
        (carrierCoordinate
          (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
            hrotation htwoSided hunique offset hnext) second) ↔
      (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
        hrotation htwoSided hunique offset hnext color factor).Reachable
          first.1 second.1 := by
  exact boundedCarrierGraphFamilyCode_reachable_iff_of_support_subset
    (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization hcubic
      hrotation htwoSided hunique offset hnext)
    8 2
    (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt_card_le_eight
      realization hcubic hrotation htwoSided hunique offset hnext)
    (fun step =>
      ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
          hrotation htwoSided hunique offset hnext step,
        sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
          realization hcubic hrotation htwoSided hunique offset hnext step⟩)
    (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
      hrotation htwoSided hunique offset hnext color)
    factor
    (sourceCorridorSerialBoundaryRebaseTrackedGraphAt_support_subset_finiteSwitch
      realization hcubic hrotation htwoSided hunique offset hnext color factor)
    first second

/-- Extract the exact finite tracked state-and-letter step at one source
rebase.  The old component matrix is the only prefix-dependent field. -/
noncomputable def sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt
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
    BoundedSerialBoundaryRebaseTrackedStepCode := by
  classical
  let carrier := sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
    hcubic hrotation htwoSided hunique offset hnext
  let localCode := sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt
    realization hcubic hrotation htwoSided hunique offset hnext color
  refine {
    localCode := localCode
    oldComponent := fun pair left right => by
      exact decide
        ((regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
            htwoSided hunique offset).regionEdges color
          (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
            ((carrierCoordinate carrier).symm left).1
            ((carrierCoordinate carrier).symm right).1) }

@[simp]
theorem sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_oldComponent_eq_true_iff
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
    (color : G.edgeSet → Color) (pair : TrackedColorPair)
    (left right : Fin
      (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).localCode.vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext color).oldComponent pair left
        right = true ↔
      (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges color
        (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2).Reachable
          ((carrierCoordinate
            (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
              hcubic hrotation htwoSided hunique offset hnext)).symm left).1
          ((carrierCoordinate
            (sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
              hcubic hrotation htwoSided hunique offset hnext)).symm right).1 := by
  simp [sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt]

/-- The exact successor tracked connectivity is computed solely by closure of
the finite old-component matrix and the two finite literal rebase graphs. -/
theorem sourceCorridorSerialInputTrackedGraph_next_reachable_iff_trackedStepCode
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
    (color : G.edgeSet → Color) (pair : TrackedColorPair)
    (left right : Fin 2) :
    (regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialCutRegionAt realization hcubic hrotation
          htwoSided hunique (sourceCorridorSerialNextOffset offset hnext))
        color (trackedColorPairColors pair).1
          (trackedColorPairColors pair).2).Reachable
      (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
        hrotation htwoSided hunique offset hnext left)
      (sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
        hrotation htwoSided hunique offset hnext right) ↔
    Relation.ReflTransGen
      (boundedSerialBoundaryRebaseTrackedComponentStep
        (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext color) pair)
      ((sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).localCode.point left)
      ((sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).localCode.point right) := by
  let carrier := sourceCorridorSerialBoundaryRebaseFiniteSwitchAt realization
    hcubic hrotation htwoSided hunique offset hnext
  let coordinate := carrierCoordinate carrier
  let code := sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext color
  rw [sourceCorridorSerialInputTrackedGraph_next_reachable_iff_finiteSwitchClosure
    realization hcubic hrotation htwoSided hunique offset hnext color
      (trackedColorPairColors pair).1 (trackedColorPairColors pair).2]
  have hstep (first second : {edge // edge ∈ carrier}) :
      SelectedThreeFactorComponentStep
          (regionalTrackedEdgeGraph
            embedded.cellulation.rotation.toRotationSystem
            (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
              htwoSided hunique offset).regionEdges color
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
          (regionalTrackedEdgeGraph
            embedded.cellulation.rotation.toRotationSystem
            (sourceCorridorSerialBoundaryRebaseEdgeSetAt realization hcubic
              hrotation htwoSided hunique offset hnext) color
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
          (sourceCorridorSerialBoundaryRebaseTrackedSeamAt realization hcubic
            hrotation htwoSided hunique offset hnext color
            (trackedColorPairColors pair).1
            (trackedColorPairColors pair).2)
          (fun edge => edge ∈ carrier) first second ↔
        boundedSerialBoundaryRebaseTrackedComponentStep code pair
          (coordinate first) (coordinate second) := by
    constructor
    · rintro (hold | hnew | hseam)
      · exact Or.inl ((sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_oldComponent_eq_true_iff
          realization hcubic hrotation htwoSided hunique offset hnext color
            pair (coordinate first) (coordinate second)).2 (by
              simpa [coordinate, carrier] using hold))
      · exact Or.inr (Or.inl
          ((sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_reachable_iff
            realization hcubic hrotation htwoSided hunique offset hnext color
              (false, pair) first second).2 (by
                simpa [sourceCorridorSerialBoundaryRebaseTrackedGraphAt] using hnew)))
      · exact Or.inr (Or.inr
          ((sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_reachable_iff
            realization hcubic hrotation htwoSided hunique offset hnext color
              (true, pair) first second).2 (by
                simpa [sourceCorridorSerialBoundaryRebaseTrackedGraphAt] using hseam)))
    · rintro (hold | hnew | hseam)
      · exact Or.inl (by
          have := (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_oldComponent_eq_true_iff
            realization hcubic hrotation htwoSided hunique offset hnext color
              pair (coordinate first) (coordinate second)).1 hold
          simpa [coordinate, carrier] using this)
      · exact Or.inr (Or.inl (by
          have := (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_reachable_iff
            realization hcubic hrotation htwoSided hunique offset hnext color
              (false, pair) first second).1 hnew
          simpa [sourceCorridorSerialBoundaryRebaseTrackedGraphAt] using this))
      · exact Or.inr (Or.inr (by
          have := (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_reachable_iff
            realization hcubic hrotation htwoSided hunique offset hnext color
              (true, pair) first second).1 hseam
          simpa [sourceCorridorSerialBoundaryRebaseTrackedGraphAt] using this))
  constructor
  · intro hclosure
    have hlift := Relation.ReflTransGen.lift coordinate
      (fun first second h => (hstep first second).1 h) hclosure
    have hleftPoint :
        coordinate
            ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
                hrotation htwoSided hunique offset hnext left,
              sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
                realization hcubic hrotation htwoSided hunique offset hnext
                  left⟩ =
          code.localCode.point left := by
      change
        carrierCoordinate carrier
            ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
                hrotation htwoSided hunique offset hnext left,
              sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
                realization hcubic hrotation htwoSided hunique offset hnext
                  left⟩ =
          (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt
            realization hcubic hrotation htwoSided hunique offset hnext
              color).point left
      exact
        (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_point
          realization hcubic hrotation htwoSided hunique offset hnext color
            left).symm
    have hrightPoint :
        coordinate
            ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
                hrotation htwoSided hunique offset hnext right,
              sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
                realization hcubic hrotation htwoSided hunique offset hnext
                  right⟩ =
          code.localCode.point right := by
      change
        carrierCoordinate carrier
            ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
                hrotation htwoSided hunique offset hnext right,
              sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
                realization hcubic hrotation htwoSided hunique offset hnext
                  right⟩ =
          (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt
            realization hcubic hrotation htwoSided hunique offset hnext
              color).point right
      exact
        (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_point
          realization hcubic hrotation htwoSided hunique offset hnext color
            right).symm
    rw [hleftPoint, hrightPoint] at hlift
    exact hlift
  · intro hclosure
    have hlift := Relation.ReflTransGen.lift coordinate.symm
      (fun first second h => (hstep (coordinate.symm first)
        (coordinate.symm second)).2 (by simpa using h)) hclosure
    have hleftPoint :
        coordinate.symm (code.localCode.point left) =
          ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
              hrotation htwoSided hunique offset hnext left,
            sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
              realization hcubic hrotation htwoSided hunique offset hnext
                left⟩ := by
      change
        (carrierCoordinate carrier).symm
            ((sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt
              realization hcubic hrotation htwoSided hunique offset hnext
                color).point left) = _
      rw [sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_point]
      exact (carrierCoordinate carrier).symm_apply_apply _
    have hrightPoint :
        coordinate.symm (code.localCode.point right) =
          ⟨sourceCorridorSerialBoundaryRebaseCrossingAt realization hcubic
              hrotation htwoSided hunique offset hnext right,
            sourceCorridorSerialBoundaryRebaseCrossingAt_mem_finiteSwitch
              realization hcubic hrotation htwoSided hunique offset hnext
                right⟩ := by
      change
        (carrierCoordinate carrier).symm
            ((sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt
              realization hcubic hrotation htwoSided hunique offset hnext
                color).point right) = _
      rw [sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt_point]
      exact (carrierCoordinate carrier).symm_apply_apply _
    rw [hleftPoint, hrightPoint] at hlift
    exact hlift

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
