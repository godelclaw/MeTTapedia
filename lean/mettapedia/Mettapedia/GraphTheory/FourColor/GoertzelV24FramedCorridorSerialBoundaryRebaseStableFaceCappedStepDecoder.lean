import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableFaceCappedStep

/-!
# A graph-free capped facial decoder for one serial boundary rebase

The fixed sixteen-slot facial state contains exactly the predecessor data
read by each literal per-face rebase receipt: residual connectivity through
the old boundary-fragment ports, support activity, literal presence, and the
cap at five of the predecessor component.

This file packages those data as an executable finite decoder.  A source
agreement theorem proves that every field reconstructed from the stable state
agrees with the earlier graph-extracted receipt.  Ambient geometry is used
only to extract the finite state, the local two-factor code, and the coordinate
map; it is not an input to the decoder itself.

This is the predecessor decoder.  It does not yet compute the successor
sixteen-slot state or a reachable closure.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph
open SimpleGraphDartRotation

/-- Reconstruct a complete capped facial step receipt from finite state only.

`slotAtCoordinate` names the fixed occurrence slot represented by each vertex
of the literal local code.  Old connectivity is interpreted through the
finite residual-or-port factorization. -/
noncomputable def boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable
    {Port : Type*}
    (state : BoundedCappedSupportedPortResidualCode (Fin 16) Port)
    (portConnected : Port → Port → Prop)
    (localCode : BoundedCarrierGraphFamilyCode 8 0 Bool)
    (slotAtCoordinate : Fin localCode.vertexCount.val → Fin 16) :
    BoundedCappedSerialBoundaryRebaseFaceStepCode := by
  classical
  exact {
    toBoundedSupportedSerialBoundaryRebaseFaceStepCode := {
      toBoundedSerialBoundaryRebaseFaceStepCode := {
        localCode := localCode
        oldComponent := fun left right => decide
          (SupportedPortResidualFactoredReachability
            state.toBoundedSupportedPortResidualCode portConnected
            (slotAtCoordinate left) (slotAtCoordinate right)) }
      oldActive := fun coordinate =>
        state.interfaceActive (slotAtCoordinate coordinate) }
    oldPresent := fun coordinate =>
      state.interfacePresent (slotAtCoordinate coordinate)
    oldComponentCap := fun coordinate =>
      state.componentCap (slotAtCoordinate coordinate) }

@[simp] theorem boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable_localCode
    {Port : Type*}
    (state : BoundedCappedSupportedPortResidualCode (Fin 16) Port)
    (portConnected : Port → Port → Prop)
    (localCode : BoundedCarrierGraphFamilyCode 8 0 Bool)
    (slotAtCoordinate : Fin localCode.vertexCount.val → Fin 16) :
    (boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable state portConnected
      localCode slotAtCoordinate).localCode = localCode := by
  rfl

@[simp] theorem boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable_oldComponent_eq_true_iff
    {Port : Type*}
    (state : BoundedCappedSupportedPortResidualCode (Fin 16) Port)
    (portConnected : Port → Port → Prop)
    (localCode : BoundedCarrierGraphFamilyCode 8 0 Bool)
    (slotAtCoordinate : Fin localCode.vertexCount.val → Fin 16)
    (left right : Fin localCode.vertexCount.val) :
    (boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable state portConnected
      localCode slotAtCoordinate).oldComponent left right = true ↔
      SupportedPortResidualFactoredReachability
        state.toBoundedSupportedPortResidualCode portConnected
        (slotAtCoordinate left) (slotAtCoordinate right) := by
  simp [boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableFaceCappedStepDecoderEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The graph-free capped decoder specialized to one literal source face.
All ambient data occur only while extracting its finite inputs. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt
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
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    BoundedCappedSerialBoundaryRebaseFaceStepCode :=
  boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext)
    (fun leftPort rightPort => leftPort = rightPort)
    (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext root)
    (fun coordinate =>
      sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization hcubic
        hrotation htwoSided hunique offset hnext
        (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
          hcubic hrotation htwoSided hunique offset hnext root coordinate))

/-- The stable decoder reconstructs every accumulated predecessor component
bit of the literal per-face capped receipt. -/
theorem sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt_oldComponent_eq_true_iff_literal
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
    (left right : Fin
      (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext root).oldComponent
        left right = true ↔
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldComponent
          left right = true := by
  let leftOccurrence :=
    sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
      hcubic hrotation htwoSided hunique offset hnext root left
  let rightOccurrence :=
    sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
      hcubic hrotation htwoSided hunique offset hnext root right
  have hleft :=
    sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt_occurrence
      realization hcubic hrotation htwoSided hunique offset hnext leftOccurrence
  have hright :=
    sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt_occurrence
      realization hcubic hrotation htwoSided hunique offset hnext rightOccurrence
  have hresidualAgreement :
      (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext).residualConnected
          (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
            hcubic hrotation htwoSided hunique offset hnext leftOccurrence)
          (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
            hcubic hrotation htwoSided hunique offset hnext rightOccurrence) =
        (sourceCorridorSerialBoundaryRebaseResidualFaceCodeAt realization hcubic
          hrotation htwoSided hunique offset hnext).residualConnected
            leftOccurrence rightOccurrence := by
    calc
      _ = (sourceCorridorSerialBoundaryRebaseCappedFaceCodeAt realization hcubic
            hrotation htwoSided hunique offset hnext).residualConnected
            leftOccurrence rightOccurrence := hleft.2.2.2.2 rightOccurrence
      _ = _ := rfl
  have hleftAttachAgreement (port) :
      (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext).attaches
          (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
            hcubic hrotation htwoSided hunique offset hnext leftOccurrence) port =
        (sourceCorridorSerialBoundaryRebaseResidualFaceCodeAt realization hcubic
          hrotation htwoSided hunique offset hnext).attaches
            leftOccurrence port := by
    calc
      _ = (sourceCorridorSerialBoundaryRebaseCappedFaceCodeAt realization hcubic
            hrotation htwoSided hunique offset hnext).attaches
            leftOccurrence port := hleft.2.2.2.1 port
      _ = _ := rfl
  have hrightAttachAgreement (port) :
      (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext).attaches
          (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
            hcubic hrotation htwoSided hunique offset hnext rightOccurrence) port =
        (sourceCorridorSerialBoundaryRebaseResidualFaceCodeAt realization hcubic
          hrotation htwoSided hunique offset hnext).attaches
            rightOccurrence port := by
    calc
      _ = (sourceCorridorSerialBoundaryRebaseCappedFaceCodeAt realization hcubic
            hrotation htwoSided hunique offset hnext).attaches
            rightOccurrence port := hright.2.2.2.1 port
      _ = _ := rfl
  change
    (boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable
      (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext)
      (fun leftPort rightPort => leftPort = rightPort)
      (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root)
      (fun coordinate =>
        sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
          hcubic hrotation htwoSided hunique offset hnext
          (sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt
            realization hcubic hrotation htwoSided hunique offset hnext root
              coordinate))).oldComponent left right = true ↔
      (sourceCorridorSerialBoundaryRebaseFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldComponent
          left right = true
  rw [boundedCappedSerialBoundaryRebaseFaceStepCodeOfStable_oldComponent_eq_true_iff]
  rw [sourceCorridorSerialBoundaryRebaseFaceStepCodeAt_oldComponent_iff_residualFactored]
  change
    SupportedPortResidualFactoredReachability
        (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext
            ).toBoundedSupportedPortResidualCode
        (fun leftPort rightPort => leftPort = rightPort)
        (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
          hcubic hrotation htwoSided hunique offset hnext leftOccurrence)
        (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
          hcubic hrotation htwoSided hunique offset hnext rightOccurrence) ↔
      sourceCorridorSerialBoundaryRebaseResidualFaceFactoredStep realization
        hcubic hrotation htwoSided hunique offset hnext leftOccurrence
          rightOccurrence
  simp only [SupportedPortResidualFactoredReachability,
    sourceCorridorSerialBoundaryRebaseResidualFaceFactoredStep,
    PortResidualFactoredReachability]
  constructor
  · rintro (hresidual | ⟨leftPort, rightPort, hleftAttach,
      hports, hrightAttach⟩)
    · rw [hresidualAgreement] at hresidual
      exact Or.inl hresidual
    · rw [hleftAttachAgreement leftPort] at hleftAttach
      rw [hrightAttachAgreement rightPort] at hrightAttach
      exact Or.inr ⟨leftPort, rightPort, hleftAttach, hports, hrightAttach⟩
  · rintro (hresidual | ⟨leftPort, rightPort, hleftAttach,
      hports, hrightAttach⟩)
    · rw [← hresidualAgreement] at hresidual
      exact Or.inl hresidual
    · rw [← hleftAttachAgreement leftPort] at hleftAttach
      rw [← hrightAttachAgreement rightPort] at hrightAttach
      exact Or.inr ⟨leftPort, rightPort, hleftAttach, hports, hrightAttach⟩

/-- The stable decoder reads the same predecessor support bit as the literal
per-face receipt. -/
theorem sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt_oldActive_eq_literal
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
      (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext root).oldActive coordinate =
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldActive coordinate := by
  let occurrence :=
    sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
      hcubic hrotation htwoSided hunique offset hnext root coordinate
  have hstable :=
    sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt_occurrence
      realization hcubic hrotation htwoSided hunique offset hnext occurrence
  change
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).interfaceActive
        (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
          hcubic hrotation htwoSided hunique offset hnext occurrence) =
      (sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext).interfaceActive occurrence
  exact hstable.1

/-- The stable decoder retains literal old-region presence, including an
isolated occurrence which is present but inactive. -/
theorem sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt_oldPresent_eq_literal
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
      (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext root).oldPresent coordinate =
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldPresent coordinate := by
  let occurrence :=
    sourceCorridorSerialBoundaryRebaseFaceStepCoordinateDartAt realization
      hcubic hrotation htwoSided hunique offset hnext root coordinate
  have hstable :=
    sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt_occurrence
      realization hcubic hrotation htwoSided hunique offset hnext occurrence
  change
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext).interfacePresent
        (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
          hcubic hrotation htwoSided hunique offset hnext occurrence) =
      (sourceCorridorSerialBoundaryRebaseCappedFaceCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext).interfacePresent occurrence
  exact hstable.2.1

/-- The stable decoder reads exactly the same cap-at-five as the literal
per-face receipt. -/
theorem sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt_oldComponentCap_eq_literal
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
      (sourceCorridorSerialBoundaryRebaseFaceLocalCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).vertexCount.val) :
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceStepCodeAt realization
      hcubic hrotation htwoSided hunique offset hnext root).oldComponentCap
        coordinate =
      (sourceCorridorSerialBoundaryRebaseCappedFaceStepCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext root).oldComponentCap
          coordinate := by
  exact
    sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt_componentCap_eq_step
      realization hcubic hrotation htwoSided hunique offset hnext root coordinate

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
