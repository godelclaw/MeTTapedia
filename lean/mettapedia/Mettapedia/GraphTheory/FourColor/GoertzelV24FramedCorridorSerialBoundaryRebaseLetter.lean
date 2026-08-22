import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceCoordinates
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebasePortCarrier

/-!
# One finite letter for the literal serial boundary rebase

Consecutive literal source Cells do not share the same cut presentation.
After one Cell is adjoined, the next input presentation retains two new
displayed crossing edges.  The resulting boundary rebase is therefore a
distinct letter in the heterogeneous corridor word.

This file packages all already-proved finite local data for that letter:

* the two successor crossing colours;
* the tracked two-colour graphs and their residual seams on one common
  sixteen-edge carrier which retains both old and new port pairs; and
* the occurrence-sensitive facial seams, indexed by the successor profile's
  exact boundary-fragment coordinates.

Every literal source rebase supplies such a letter, with exact component
identifications.  This is a finite receipt, not yet its semantic decoder: the
next theorem must prove that the old five-field profile together with this
receipt determines the successor profile.
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
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24WindingClassification
open SimpleGraph
open SimpleGraphDartRotation

/-- The complete finite local receipt of one serial boundary rebase.  The
tracked and facial components retain common local coordinates internally;
the two successor colours are the remaining manuscript profile coordinate. -/
structure BoundedSerialBoundaryRebaseLetterCode where
  outputEdgeColor : Fin 2 → StrandColor
  tracked : BoundedCarrierGraphFamilyCode 16 4
    SourceTrail.AnnularEmbedding.SourceCorridorSerialBoundaryRebaseTrackedFactor
  face : BoundedFaceSeamFamilyCode 4 14

noncomputable instance : DecidableEq BoundedSerialBoundaryRebaseLetterCode :=
  Classical.decEq _

private def boundedSerialBoundaryRebaseLetterCodeEquiv :
    BoundedSerialBoundaryRebaseLetterCode ≃
      (Fin 2 → StrandColor) ×
        BoundedCarrierGraphFamilyCode 16 4
          SourceTrail.AnnularEmbedding.SourceCorridorSerialBoundaryRebaseTrackedFactor ×
        BoundedFaceSeamFamilyCode 4 14 where
  toFun code := ⟨code.outputEdgeColor, code.tracked, code.face⟩
  invFun code :=
    { outputEdgeColor := code.1
      tracked := code.2.1
      face := code.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype BoundedSerialBoundaryRebaseLetterCode :=
  Fintype.ofEquiv _ boundedSerialBoundaryRebaseLetterCodeEquiv.symm

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseLetterEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Extract the complete finite receipt of one literal boundary rebase. -/
noncomputable def sourceCorridorSerialBoundaryRebaseLetterCodeAt
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
        |>.localLayerPrefixCrossing step) ≠ 0) :
    BoundedSerialBoundaryRebaseLetterCode where
  outputEdgeColor :=
    (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
      htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
      hcolor).profile.edgeColor
  tracked := sourceCorridorSerialBoundaryRebasePortTrackedCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext color
  face := sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt realization
    hcubic hrotation htwoSided hunique offset hnext

/-- The receipt stores the successor profile's two crossing colours exactly. -/
theorem sourceCorridorSerialBoundaryRebaseLetterCodeAt_outputEdgeColor
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
    (step : Fin 2) :
    (sourceCorridorSerialBoundaryRebaseLetterCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext color hcolor).outputEdgeColor
        step =
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).profile.edgeColor step := by
  rfl

/-- The receipt's tracked component is the common-coordinate graph family of
the literal rebase. -/
theorem sourceCorridorSerialBoundaryRebaseLetterCodeAt_tracked
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
        |>.localLayerPrefixCrossing step) ≠ 0) :
    (sourceCorridorSerialBoundaryRebaseLetterCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext color hcolor).tracked =
      sourceCorridorSerialBoundaryRebasePortTrackedCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color := by
  rfl

/-- The tracked part of the finite rebase receipt preserves exactly the
ambient local/remainder connectivity between any two named old-or-new ports.
This is an observation theorem for the literal letter, not yet the statement
that the incoming profile determines every attachment through the old
prefix. -/
theorem sourceCorridorSerialBoundaryRebaseLetterCodeAt_port_reachable_iff
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
    (factor : SourceCorridorSerialBoundaryRebaseTrackedFactor)
    (first second : Fin 2 ⊕ Fin 2) :
    ((sourceCorridorSerialBoundaryRebaseLetterCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color hcolor).tracked.graph
          factor).Reachable
        ((sourceCorridorSerialBoundaryRebaseLetterCodeAt realization hcubic
          hrotation htwoSided hunique offset hnext color hcolor).tracked.point
            (finSumFinEquiv first))
        ((sourceCorridorSerialBoundaryRebaseLetterCodeAt realization hcubic
          hrotation htwoSided hunique offset hnext color hcolor).tracked.point
            (finSumFinEquiv second)) ↔
      (sourceCorridorSerialBoundaryRebaseTrackedGraphAt realization hcubic
        hrotation htwoSided hunique offset hnext color factor).Reachable
          (sourceCorridorSerialBoundaryRebasePortAt realization hcubic
            hrotation htwoSided hunique offset hnext first).1
          (sourceCorridorSerialBoundaryRebasePortAt realization hcubic
            hrotation htwoSided hunique offset hnext second).1 := by
  change
    ((sourceCorridorSerialBoundaryRebasePortTrackedCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).graph factor).Reachable
        ((sourceCorridorSerialBoundaryRebasePortTrackedCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext color).point
            (finSumFinEquiv first))
        ((sourceCorridorSerialBoundaryRebasePortTrackedCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext color).point
            (finSumFinEquiv second)) ↔ _
  exact
    sourceCorridorSerialBoundaryRebasePortTrackedCodeAt_port_reachable_iff
      realization hcubic hrotation htwoSided hunique offset hnext color factor
      first second

/-- The two named old-profile crossings remain distinct in the bundled
tracked carrier. -/
theorem sourceCorridorSerialBoundaryRebaseLetterCodeAt_oldPoint_injective
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
        |>.localLayerPrefixCrossing step) ≠ 0) :
    Function.Injective (fun step : Fin 2 =>
      (sourceCorridorSerialBoundaryRebaseLetterCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color hcolor).tracked.point
          (finSumFinEquiv (Sum.inl step : Fin 2 ⊕ Fin 2))) := by
  intro first second heq
  change
    (sourceCorridorSerialBoundaryRebasePortTrackedCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext color).point
        (finSumFinEquiv (Sum.inl first : Fin 2 ⊕ Fin 2)) =
      (sourceCorridorSerialBoundaryRebasePortTrackedCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).point
          (finSumFinEquiv (Sum.inl second : Fin 2 ⊕ Fin 2)) at heq
  rw [sourceCorridorSerialBoundaryRebasePortTrackedCodeAt_oldPoint,
    sourceCorridorSerialBoundaryRebasePortTrackedCodeAt_oldPoint] at heq
  have hports := (carrierCoordinate _).injective heq
  apply (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
    offset).nextLocalLayerPrefixCrossing_injective
  exact congrArg Subtype.val hports

/-- The two named successor-input crossings likewise remain distinct in the
same bundled tracked carrier. -/
theorem sourceCorridorSerialBoundaryRebaseLetterCodeAt_newPoint_injective
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
        |>.localLayerPrefixCrossing step) ≠ 0) :
    Function.Injective (fun step : Fin 2 =>
      (sourceCorridorSerialBoundaryRebaseLetterCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color hcolor).tracked.point
          (finSumFinEquiv (Sum.inr step : Fin 2 ⊕ Fin 2))) := by
  intro first second heq
  change
    (sourceCorridorSerialBoundaryRebasePortTrackedCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext color).point
        (finSumFinEquiv (Sum.inr first : Fin 2 ⊕ Fin 2)) =
      (sourceCorridorSerialBoundaryRebasePortTrackedCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext color).point
          (finSumFinEquiv (Sum.inr second : Fin 2 ⊕ Fin 2)) at heq
  rw [sourceCorridorSerialBoundaryRebasePortTrackedCodeAt_newPoint,
    sourceCorridorSerialBoundaryRebasePortTrackedCodeAt_newPoint] at heq
  have hports := (carrierCoordinate _).injective heq
  apply (sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
    (sourceCorridorSerialNextOffset offset hnext))
      |>.localLayerPrefixCrossing_injective
  exact congrArg Subtype.val hports

/-- The bundled face family is the exact successor-coordinate seam code. -/
theorem sourceCorridorSerialBoundaryRebaseLetterCodeAt_face
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
        |>.localLayerPrefixCrossing step) ≠ 0) :
    (sourceCorridorSerialBoundaryRebaseLetterCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext color hcolor).face =
      sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext := by
  rfl

/-- The receipt's facial component is indexed by exactly the successor
profile's real boundary fragments. -/
theorem sourceCorridorSerialBoundaryRebaseLetterCodeAt_face_count
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
        |>.localLayerPrefixCrossing step) ≠ 0) :
    ((sourceCorridorSerialBoundaryRebaseLetterCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext color hcolor).face
        |>.faceFragmentCount) =
      (sourceCorridorSerialInputBoundedProfileAt realization hcubic hrotation
        htwoSided hunique (sourceCorridorSerialNextOffset offset hnext) color
        hcolor).faceFragmentCount := by
  exact sourceCorridorSerialBoundaryRebaseFaceCoordinateCodeAt_count_eq_profile
    realization hcubic hrotation htwoSided hunique offset hnext color hcolor

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
