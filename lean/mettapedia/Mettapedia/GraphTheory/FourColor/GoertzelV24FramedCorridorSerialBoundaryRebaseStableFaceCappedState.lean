import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseFaceCappedState
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableTrackedState

/-!
# A stable capped facial state for one serial boundary rebase

The exact predecessor facial state was indexed by the dependent type of dart
occurrences over one literal rebase switch.  This file transports that state
to sixteen fixed occurrence slots, the proved uniform bound for the eight-edge
switch.  Unused slots are explicitly absent and inactive.

The state retains four pieces which a sound face update needs: residual
component data relative to the predecessor boundary fragments, support
activity, literal regional presence (which distinguishes an isolated
singleton from an absent occurrence), and the cap at five of each predecessor
component.  The latter is defined intrinsically on the root-free dart graph.

This is a source-image stabilization.  It does not yet compute the successor
state, a reachable closure, or a numerical threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationFaceRegionalDartGraph
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

/-- A support-sensitive residual code with the two extra fields required by
capped facial progress.  `interfacePresent` is deliberately distinct from
graph support, since a literal isolated occurrence is present but inactive. -/
structure BoundedCappedSupportedPortResidualCode (Interface Port : Type*)
    extends BoundedSupportedPortResidualCode Interface Port where
  interfacePresent : Interface → Bool
  componentCap : Interface → Fin 6

private def boundedCappedSupportedPortResidualCodeEquiv
    (Interface Port : Type*) :
    BoundedCappedSupportedPortResidualCode Interface Port ≃
      BoundedSupportedPortResidualCode Interface Port ×
        (Interface → Bool) × (Interface → Fin 6) where
  toFun code :=
    ⟨code.toBoundedSupportedPortResidualCode, code.interfacePresent,
      code.componentCap⟩
  invFun data :=
    { toBoundedSupportedPortResidualCode := data.1
      interfacePresent := data.2.1
      componentCap := data.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance boundedCappedSupportedPortResidualCodeDecidableEq
    {Interface Port : Type*} :
    DecidableEq (BoundedCappedSupportedPortResidualCode Interface Port) :=
  Classical.decEq _

noncomputable instance boundedCappedSupportedPortResidualCodeFintype
    {Interface Port : Type*} [Fintype Interface] [Fintype Port] :
    Fintype (BoundedCappedSupportedPortResidualCode Interface Port) := by
  letI : Fintype (Interface → Bool) := Fintype.ofFinite _
  letI : Fintype (Interface → Fin 6) := Fintype.ofFinite _
  exact Fintype.ofEquiv _
    (boundedCappedSupportedPortResidualCodeEquiv Interface Port).symm

/-- Canonically embed a finite type in a fixed slot carrier. -/
noncomputable def boundedFiniteSlot
    {Interface : Type*} [Fintype Interface] {bound : Nat}
    (hcard : Fintype.card Interface ≤ bound) : Interface → Fin bound :=
  fun interface => Fin.castLE hcard (Fintype.equivFin Interface interface)

/-- Decode a fixed slot when it belongs to the canonical initial segment. -/
noncomputable def boundedFiniteSlot?
    {Interface : Type*} [Fintype Interface] {bound : Nat}
    (_hcard : Fintype.card Interface ≤ bound) : Fin bound → Option Interface :=
  fun slot =>
    if hslot : slot.val < Fintype.card Interface then
      some ((Fintype.equivFin Interface).symm ⟨slot.val, hslot⟩)
    else none

@[simp] theorem boundedFiniteSlot?_slot
    {Interface : Type*} [Fintype Interface] {bound : Nat}
    (hcard : Fintype.card Interface ≤ bound) (interface : Interface) :
    boundedFiniteSlot? hcard (boundedFiniteSlot hcard interface) =
      some interface := by
  simp [boundedFiniteSlot?, boundedFiniteSlot]

/-- Decoding a fixed slot yields a given interface value exactly at that
value's canonical slot.  Thus the padding decoder is injective on its live
initial segment, not merely a left inverse there. -/
theorem boundedFiniteSlot?_eq_some_iff
    {Interface : Type*} [Fintype Interface] {bound : Nat}
    (hcard : Fintype.card Interface ≤ bound) (slot : Fin bound)
    (interface : Interface) :
    boundedFiniteSlot? hcard slot = some interface ↔
      slot = boundedFiniteSlot hcard interface := by
  constructor
  · intro hdecode
    unfold boundedFiniteSlot? at hdecode
    split at hdecode
    · rename_i hslot
      have heq :
          (Fintype.equivFin Interface).symm ⟨slot.val, hslot⟩ = interface :=
        Option.some.inj hdecode
      apply Fin.ext
      have := congrArg (fun value => (Fintype.equivFin Interface value).val) heq
      simpa [boundedFiniteSlot] using this
    · simp at hdecode
  · rintro rfl
    exact boundedFiniteSlot?_slot hcard interface

/-- Pad capped residual data onto a fixed carrier.  Missing slots carry no
support, no presence, no attachment, and cap zero. -/
def padCappedSupportedPortResidualCode
    {Interface Stable Port : Type*}
    (decode : Stable → Option Interface)
    (code : BoundedCappedSupportedPortResidualCode Interface Port) :
    BoundedCappedSupportedPortResidualCode Stable Port where
  toBoundedSupportedPortResidualCode :=
    padSupportedPortResidualCode decode
      code.toBoundedSupportedPortResidualCode
  interfacePresent := fun stable =>
    match decode stable with
    | some interface => code.interfacePresent interface
    | none => false
  componentCap := fun stable =>
    match decode stable with
    | some interface => code.componentCap interface
    | none => ⟨0, by omega⟩

@[simp] theorem padCappedSupportedPortResidualCode_present_of_decode
    {Interface Stable Port : Type*}
    (decode : Stable → Option Interface)
    (code : BoundedCappedSupportedPortResidualCode Interface Port)
    (stable : Stable) (interface : Interface)
    (hdecode : decode stable = some interface) :
    (padCappedSupportedPortResidualCode decode code).interfacePresent stable =
      code.interfacePresent interface := by
  simp [padCappedSupportedPortResidualCode, hdecode]

@[simp] theorem padCappedSupportedPortResidualCode_cap_of_decode
    {Interface Stable Port : Type*}
    (decode : Stable → Option Interface)
    (code : BoundedCappedSupportedPortResidualCode Interface Port)
    (stable : Stable) (interface : Interface)
    (hdecode : decode stable = some interface) :
    (padCappedSupportedPortResidualCode decode code).componentCap stable =
      code.componentCap interface := by
  simp [padCappedSupportedPortResidualCode, hdecode]

/-- The full literal regional component of one dart occurrence.  Filtering by
regional presence retains an isolated singleton while excluding an absent
coordinate despite reflexive reachability. -/
noncomputable def faceRegionalDartComponentSupport
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (region : Finset E) (start : RS.D) :
    Finset RS.D := by
  classical
  exact Finset.univ.filter fun dart =>
    RS.edgeOf dart ∈ region ∧
      (faceRegionalDartGraph RS region).Reachable start dart

@[simp] theorem mem_faceRegionalDartComponentSupport_iff
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (region : Finset E) (start dart : RS.D) :
    dart ∈ faceRegionalDartComponentSupport RS region start ↔
      RS.edgeOf dart ∈ region ∧
        (faceRegionalDartGraph RS region).Reachable start dart := by
  classical
  simp [faceRegionalDartComponentSupport]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableFaceCappedStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- Exact capped predecessor face data on the dependent literal occurrence
carrier. -/
abbrev SourceCorridorSerialBoundaryRebaseCappedFaceCodeAt
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
    (hnext : offset.val + 1 < blockLength - 3) :=
  BoundedCappedSupportedPortResidualCode
    (SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
      hcubic hrotation htwoSided hunique offset hnext)
    (SourceCorridorSerialBoundaryRebaseFacePortAt realization hcubic hrotation
      htwoSided hunique offset)

/-- Extract the exact predecessor face state on the literal occurrence
carrier. -/
noncomputable def sourceCorridorSerialBoundaryRebaseCappedFaceCodeAt
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
    SourceCorridorSerialBoundaryRebaseCappedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext := by
  classical
  let RS := embedded.cellulation.rotation.toRotationSystem
  let region :=
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges
  exact {
    toBoundedSupportedPortResidualCode :=
      sourceCorridorSerialBoundaryRebaseSupportedFaceCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext
    interfacePresent := fun occurrence =>
      decide (RS.edgeOf occurrence.1 ∈ region)
    componentCap := fun occurrence =>
      ⟨min (faceRegionalDartComponentSupport RS region occurrence.1).card 5,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ }

/-- Fixed sixteen-slot capped facial state.  Its port carrier is the actual
finite predecessor-fragment coordinate type already stored by the bounded
profile. -/
abbrev BoundedSerialBoundaryRebaseStableCappedFaceCode (Port : Type*) :=
  BoundedCappedSupportedPortResidualCode (Fin 16) Port

private theorem sourceCorridorSerialBoundaryRebaseFaceOccurrence_card_le_sixteen
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
    Fintype.card
      (SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
        hcubic hrotation htwoSided hunique offset hnext) ≤ 16 := by
  simpa [Nat.card_eq_fintype_card] using
    sourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt_card_le_sixteen
      realization hcubic hrotation htwoSided hunique offset hnext

/-- Canonical fixed slot of one literal face occurrence. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt
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
    SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
        hcubic hrotation htwoSided hunique offset hnext → Fin 16 :=
  boundedFiniteSlot
    (sourceCorridorSerialBoundaryRebaseFaceOccurrence_card_le_sixteen
      realization hcubic hrotation htwoSided hunique offset hnext)

/-- Partial decoder of a fixed occurrence slot. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFaceOccurrenceAtSlot?
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
    Fin 16 → Option
      (SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
        hcubic hrotation htwoSided hunique offset hnext) :=
  boundedFiniteSlot?
    (sourceCorridorSerialBoundaryRebaseFaceOccurrence_card_le_sixteen
      realization hcubic hrotation htwoSided hunique offset hnext)

@[simp] theorem sourceCorridorSerialBoundaryRebaseFaceOccurrenceAtSlot?_slot
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
    (occurrence :
      SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
        hcubic hrotation htwoSided hunique offset hnext) :
    sourceCorridorSerialBoundaryRebaseFaceOccurrenceAtSlot? realization hcubic
        hrotation htwoSided hunique offset hnext
        (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
          hcubic hrotation htwoSided hunique offset hnext occurrence) =
      some occurrence := by
  apply boundedFiniteSlot?_slot

/-- Transport the exact literal capped face state onto sixteen fixed slots. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt
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
    BoundedSerialBoundaryRebaseStableCappedFaceCode
      (SourceCorridorSerialBoundaryRebaseFacePortAt realization hcubic
        hrotation htwoSided hunique offset) :=
  padCappedSupportedPortResidualCode
    (sourceCorridorSerialBoundaryRebaseFaceOccurrenceAtSlot? realization
      hcubic hrotation htwoSided hunique offset hnext)
    (sourceCorridorSerialBoundaryRebaseCappedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext)

/-- Every actual occurrence round-trips through the stable state, including
support, presence, component attachments, and cap. -/
theorem sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt_occurrence
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
    (occurrence :
      SourceCorridorSerialBoundaryRebaseFaceSwitchDartOccurrenceAt realization
        hcubic hrotation htwoSided hunique offset hnext) :
    let stable :=
      sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext
    let dependent :=
      sourceCorridorSerialBoundaryRebaseCappedFaceCodeAt realization hcubic
        hrotation htwoSided hunique offset hnext
    let slot := sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt
      realization hcubic hrotation htwoSided hunique offset hnext occurrence
    stable.interfaceActive slot = dependent.interfaceActive occurrence ∧
      stable.interfacePresent slot = dependent.interfacePresent occurrence ∧
      stable.componentCap slot = dependent.componentCap occurrence ∧
      (∀ port, stable.attaches slot port = dependent.attaches occurrence port) ∧
      (∀ other,
        stable.residualConnected slot
            (sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt realization
              hcubic hrotation htwoSided hunique offset hnext other) =
          dependent.residualConnected occurrence other) := by
  let decode :=
    sourceCorridorSerialBoundaryRebaseFaceOccurrenceAtSlot? realization
      hcubic hrotation htwoSided hunique offset hnext
  let dependent :=
    sourceCorridorSerialBoundaryRebaseCappedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext
  let slot := sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt
    realization hcubic hrotation htwoSided hunique offset hnext occurrence
  have hdecode : decode slot = some occurrence := by
    exact sourceCorridorSerialBoundaryRebaseFaceOccurrenceAtSlot?_slot
      realization hcubic hrotation htwoSided hunique offset hnext occurrence
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact padSupportedPortResidualCode_interfaceActive_of_decode
      decode dependent.toBoundedSupportedPortResidualCode slot occurrence hdecode
  · exact padCappedSupportedPortResidualCode_present_of_decode
      decode dependent slot occurrence hdecode
  · exact padCappedSupportedPortResidualCode_cap_of_decode
      decode dependent slot occurrence hdecode
  · intro port
    exact padSupportedPortResidualCode_attaches_of_decode
      decode dependent.toBoundedSupportedPortResidualCode slot occurrence port hdecode
  · intro other
    let otherSlot := sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt
      realization hcubic hrotation htwoSided hunique offset hnext other
    have hother : decode otherSlot = some other := by
      exact sourceCorridorSerialBoundaryRebaseFaceOccurrenceAtSlot?_slot
        realization hcubic hrotation htwoSided hunique offset hnext other
    exact padSupportedPortResidualCode_residualConnected_of_decode
      decode dependent.toBoundedSupportedPortResidualCode slot otherSlot occurrence other
        hdecode hother

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
