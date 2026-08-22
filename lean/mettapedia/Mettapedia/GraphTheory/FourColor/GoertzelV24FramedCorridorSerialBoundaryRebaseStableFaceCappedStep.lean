import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableFaceCappedState

/-!
# Stable facial caps agree with the literal per-face receipt

The stable facial state counts a predecessor component in the root-free
regional dart graph.  The earlier per-face rebase receipt counts the same
component in cyclic coordinates relative to one chosen face.  This file proves
that the two counts agree and hence that the stable sixteen-slot cap is exactly
the cap consumed by the existing per-face update.

This is a representation bridge.  It does not yet compute the successor
sixteen-slot state or a reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableFaceCappedStepEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The root-relative predecessor component and the root-free literal dart
component have the same cardinality.  The proof first shows that every dart
reachable from the selected coordinate stays on the selected orbit face. -/
theorem sourceCorridorSerialBoundaryRebaseOldFaceComponentSupport_card_eq_dart
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt realization
        hcubic hrotation htwoSided hunique offset hnext root coordinate).card =
      (faceRegionalDartComponentSupport
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges
        (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate).1).card := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let region :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  let carrier := sourceCorridorSerialBoundaryRebaseFaceSwitchPositionsAt
    realization hcubic hrotation htwoSided hunique offset hnext root
  let startPosition := ((carrierCoordinate carrier).symm coordinate).1
  let startOccurrence :=
    sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
      hcubic hrotation htwoSided hunique offset hnext root coordinate
  have hstartDart : startOccurrence.1 = faceCycleDart RS root startPosition := by
    change
      (sourceCorridorSerialBoundaryRebaseFaceSwitchPositionDartOccurrenceAt
        realization hcubic hrotation htwoSided hunique offset hnext root
          ((carrierCoordinate carrier).symm coordinate)).1.1 = _
    rfl
  have hpositionDart (position : Fin (RS.faceOrbit root).card) :
      (faceRegionalAmbientPositionGraph RS root region).Reachable
          startPosition position ↔
        (faceRegionalDartGraph RS region).Reachable
          startOccurrence.1 (faceCycleDart RS root position) := by
    rw [hstartDart]
    exact
      (faceRegionalAmbientPositionGraph_reachable_iff_dartOrbit RS root region
        startPosition position).trans
        (faceRegionalDartGraph_reachable_iff_induce_faceOrbit RS root region
          (faceCycleDartOrbitEquiv RS root startPosition)
          (faceCycleDartOrbitEquiv RS root position)).symm
  refine Finset.card_bij
    (fun position _ => faceCycleDart RS root position) ?_ ?_ ?_
  · intro position hposition
    rw [mem_faceRegionalDartComponentSupport_iff]
    rw [mem_sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt_iff]
      at hposition
    exact ⟨hposition.1, (hpositionDart position).1 hposition.2⟩
  · intro left _ right _ heq
    exact faceCycleDart_injective RS root heq
  · intro dart hdart
    rw [mem_faceRegionalDartComponentSupport_iff] at hdart
    have hstartOrbit : startOccurrence.1 ∈ RS.faceOrbit root := by
      rw [hstartDart]
      exact faceCycleDart_mem RS root startPosition
    have hstartFace :
        dartOrbitFace RS startOccurrence.1 = dartOrbitFace RS root :=
      (Quotient.sound ((RS.mem_faceOrbit).1 hstartOrbit)).symm
    have hdartFace : dartOrbitFace RS dart = dartOrbitFace RS root :=
      (faceRegionalDartGraph_reachable_dartOrbitFace_eq RS region
        hdart.2).symm.trans hstartFace
    have hdartOrbit : dart ∈ RS.faceOrbit root := by
      rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit RS root,
        mem_orbitFaceDarts_iff]
      exact hdartFace
    rcases existsUnique_faceCycleDart_eq RS root dart hdartOrbit with
      ⟨position, hpositionDartEq, _huniquePosition⟩
    refine ⟨position, ?_, hpositionDartEq⟩
    rw [mem_sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt_iff]
    refine ⟨?_, (hpositionDart position).2 ?_⟩
    · change RS.edgeOf (faceCycleDart RS root position) ∈ region
      simpa [region, RS, hpositionDartEq] using hdart.1
    · simpa [region, RS, hpositionDartEq] using hdart.2

/-- On every literal per-face coordinate, the cap read from the fixed
sixteen-slot state is exactly the cap stored by the existing per-face rebase
receipt. -/
theorem sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt_componentCap_eq_step
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
    (root : embedded.cellulation.rotation.toRotationSystem.D)
    (coordinate : Fin
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root
          ).localCode.vertexCount.val) :
    let occurrence :=
      sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
        hcubic hrotation htwoSided hunique offset hnext root coordinate
    let slot := sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt
      realization hcubic hrotation htwoSided hunique offset hnext occurrence
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext).componentCap slot =
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldComponentCap
          coordinate := by
  dsimp only
  have hstable :=
    sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt_occurrence
      realization hcubic hrotation htwoSided hunique offset hnext
      (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
        hcubic hrotation htwoSided hunique offset hnext root coordinate)
  have hcap := hstable.2.2.1
  apply Fin.ext
  rw [hcap]
  change min
      (faceRegionalDartComponentSupport
        embedded.cellulation.rotation.toRotationSystem
        (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
          htwoSided hunique offset).regionEdges
        (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate).1).card
        5 =
    min
      (sourceCorridorSerialBoundaryRebaseOldFaceComponentSupportAt realization
        hcubic hrotation htwoSided hunique offset hnext root coordinate).card 5
  rw [sourceCorridorSerialBoundaryRebaseOldFaceComponentSupport_card_eq_dart
    realization hcubic hrotation htwoSided hunique offset hnext root coordinate]

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
