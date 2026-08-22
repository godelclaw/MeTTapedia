import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedSwitchState

/-!
# A graph-free tracked decoder for one serial boundary rebase

The literal tracked-step code formerly stored its accumulated old-prefix
component matrix by re-reading the ambient regional graph.  The stable
eight-slot residual state already proves that this matrix is determined by
the incoming bounded profile.  This file packages that theorem as an actual
finite decoder.

The decoder takes three finite inputs: the incoming profile, the stable
eight-slot residual state, and the literal local two-factor code.  A source
agreement theorem proves that its result is exactly the previously extracted
literal tracked-step code.  Thus the tracked output of one boundary rebase no
longer depends on an unbounded prefix graph.  Updating the stable residual
state itself, and the separate capped facial state, remain later obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

namespace SourceTrail

namespace AnnularEmbedding

/-- Reconstruct a complete tracked-step code from finite state only.

`slotAtCoordinate` records which stable residual slot names each vertex of
the local switch code.  The old-prefix component bit is then computed by the
exact residual/profile factorization; no ambient graph or prefix carrier is
an input. -/
noncomputable def boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch
    {faceFragmentBound : Nat}
    (input : BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (state : BoundedSerialBoundaryRebaseStableSwitchSupportedTrackedCode)
    (localCode : BoundedCarrierGraphFamilyCode 8 2
      SourceTrail.AnnularEmbedding.SourceCorridorSerialBoundaryRebaseTrackedFactor)
    (slotAtCoordinate : Fin localCode.vertexCount.val →
      BoundedSerialBoundaryRebaseTrackedSwitchSlot) :
    BoundedSerialBoundaryRebaseTrackedStepCode := by
  classical
  exact {
    localCode := localCode
    oldComponent := fun pair left right => decide
      (boundedSerialBoundaryRebaseStableSwitchProfileFactoredTrackedStep
        state input pair (slotAtCoordinate left) (slotAtCoordinate right)) }

@[simp] theorem boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch_localCode
    {faceFragmentBound : Nat}
    (input : BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (state : BoundedSerialBoundaryRebaseStableSwitchSupportedTrackedCode)
    (localCode : BoundedCarrierGraphFamilyCode 8 2
      SourceTrail.AnnularEmbedding.SourceCorridorSerialBoundaryRebaseTrackedFactor)
    (slotAtCoordinate : Fin localCode.vertexCount.val →
      BoundedSerialBoundaryRebaseTrackedSwitchSlot) :
    (boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch input state
      localCode slotAtCoordinate).localCode = localCode := by
  rfl

@[simp] theorem boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch_oldComponent_eq_true_iff
    {faceFragmentBound : Nat}
    (input : BoundedCorridorCutProfile 2 0 faceFragmentBound)
    (state : BoundedSerialBoundaryRebaseStableSwitchSupportedTrackedCode)
    (localCode : BoundedCarrierGraphFamilyCode 8 2
      SourceTrail.AnnularEmbedding.SourceCorridorSerialBoundaryRebaseTrackedFactor)
    (slotAtCoordinate : Fin localCode.vertexCount.val →
      BoundedSerialBoundaryRebaseTrackedSwitchSlot)
    (pair : TrackedColorPair)
    (left right : Fin localCode.vertexCount.val) :
    (boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch input state
      localCode slotAtCoordinate).oldComponent pair left right = true ↔
      boundedSerialBoundaryRebaseStableSwitchProfileFactoredTrackedStep
        state input pair (slotAtCoordinate left) (slotAtCoordinate right) := by
  simp [boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableTrackedStepDecoderEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The finite tracked-step decoder specialized to one literal source rebase.
All ambient data occur only while extracting the three finite inputs. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt
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
        hunique offset).nextLocalLayerPrefixCrossing step) ≠ 0) :
    BoundedSerialBoundaryRebaseTrackedStepCode :=
  boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch
    (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
      htwoSided hunique offset color hcolor)
    (sourceCorridorSerialBoundaryRebaseStableSwitchSupportedTrackedCodeAt
      realization hcubic hrotation htwoSided hunique offset hnext color)
    (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext color)
    (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlotAtCoordinate realization
      hcubic hrotation htwoSided hunique offset hnext)

/-- The graph-free finite decoder reconstructs every accumulated old-prefix
component bit of the literal tracked-step code. -/
theorem sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt_oldComponent_eq_true_iff_literal
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
      (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext color
          ).localCode.vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext color hcolor
        ).oldComponent pair left right = true ↔
      (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).oldComponent pair left
          right = true := by
  change
    (boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch
      (sourceCorridorSerialPrefixBoundedProfileAt realization hcubic hrotation
        htwoSided hunique offset color hcolor)
      (sourceCorridorSerialBoundaryRebaseStableSwitchSupportedTrackedCodeAt
        realization hcubic hrotation htwoSided hunique offset hnext color)
      (sourceCorridorSerialBoundaryRebaseFiniteSwitchTrackedCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext color)
      (sourceCorridorSerialBoundaryRebaseTrackedSwitchSlotAtCoordinate
        realization hcubic hrotation htwoSided hunique offset hnext)
      ).oldComponent pair left right = true ↔ _
  rw [boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch_oldComponent_eq_true_iff]
  exact
    (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt_oldComponent_iff_stableSwitchState
      realization hcubic hrotation htwoSided hunique offset hnext color hcolor
        pair left right).symm

/-- Replacing the graph-extracted old matrix by the stable decoder preserves
the complete one-step component relation, including both literal local
factors. -/
theorem sourceCorridorSerialBoundaryRebaseStableTrackedComponentStep_iff_literal
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
      (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext color
          ).localCode.vertexCount.val) :
    boundedSerialBoundaryRebaseTrackedComponentStep
        (sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext color hcolor)
        pair left right ↔
      boundedSerialBoundaryRebaseTrackedComponentStep
        (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext color)
        pair left right := by
  constructor
  · rintro (hold | hnew | hseam)
    · exact Or.inl
        ((sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt_oldComponent_eq_true_iff_literal
          realization hcubic hrotation htwoSided hunique offset hnext color
            hcolor pair left right).1 hold)
    · exact Or.inr (Or.inl (by
        simpa [sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt,
          boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch,
          sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt]
          using hnew))
    · exact Or.inr (Or.inr (by
        simpa [sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt,
          boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch,
          sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt]
          using hseam))
  · rintro (hold | hnew | hseam)
    · exact Or.inl
        ((sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt_oldComponent_eq_true_iff_literal
          realization hcubic hrotation htwoSided hunique offset hnext color
            hcolor pair left right).2 hold)
    · exact Or.inr (Or.inl (by
        simpa [sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt,
          boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch,
          sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt]
          using hnew))
    · exact Or.inr (Or.inr (by
        simpa [sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt,
          boundedSerialBoundaryRebaseTrackedStepCodeOfStableSwitch,
          sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt]
          using hseam))

/-- Consequently the finite reflexive-transitive closure used for successor
tracked connectivity is unchanged by the graph-free reconstruction. -/
theorem sourceCorridorSerialBoundaryRebaseStableTrackedClosure_iff_literal
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
      (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext color
          ).localCode.vertexCount.val) :
    Relation.ReflTransGen
        (boundedSerialBoundaryRebaseTrackedComponentStep
          (sourceCorridorSerialBoundaryRebaseStableTrackedStepCodeAt realization
            hcubic hrotation htwoSided hunique offset hnext color hcolor) pair)
        left right ↔
      Relation.ReflTransGen
        (boundedSerialBoundaryRebaseTrackedComponentStep
          (sourceCorridorSerialBoundaryRebaseTrackedStepCodeAt realization
            hcubic hrotation htwoSided hunique offset hnext color) pair)
        left right := by
  constructor
  · exact Relation.ReflTransGen.mono (fun first second step =>
      (sourceCorridorSerialBoundaryRebaseStableTrackedComponentStep_iff_literal
        realization hcubic hrotation htwoSided hunique offset hnext color
          hcolor pair first second).1 step)
  · exact Relation.ReflTransGen.mono (fun first second step =>
      (sourceCorridorSerialBoundaryRebaseStableTrackedComponentStep_iff_literal
        realization hcubic hrotation htwoSided hunique offset hnext color
          hcolor pair first second).2 step)

end

end AnnularEmbedding

end SourceTrail

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
