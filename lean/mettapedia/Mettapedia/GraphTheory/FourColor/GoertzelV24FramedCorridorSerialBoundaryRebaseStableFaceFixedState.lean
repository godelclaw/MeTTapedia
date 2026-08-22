import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialBoundaryRebaseStableFaceCappedStepDecoder

/-!
# A fully fixed capped facial predecessor state

The stable facial state already uses sixteen fixed dart-occurrence slots, but
its persistent-port type was the dependent predecessor fragment carrier.  A
two-edge cut has at most four occurrence-sensitive boundary fragments.  This
file pads those ports onto `Fin 4`, producing one graph-free finite type shared
by every literal serial rebase.

The four-slot bound is the general proved bound for the exact serial carrier.
No sharper three-fragment identification is assumed here.  Unused port slots
are inactive and attach to nothing.

This fixes the state carrier.  It does not yet compute the successor state,
measure its reachable closure, or derive a threshold.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction
open SimpleGraph
open SimpleGraphDartRotation

/-- Pad only the persistent-port carrier of a capped residual state.  The
interface carrier and all interface-indexed fields are retained literally. -/
def padCappedSupportedPortResidualCodePorts
    {Interface Port StablePort : Type*}
    (decodePort : StablePort → Option Port)
    (code : BoundedCappedSupportedPortResidualCode Interface Port) :
    BoundedCappedSupportedPortResidualCode Interface StablePort where
  toBoundedSupportedPortResidualCode := {
    toBoundedPortResidualCode := {
      attaches := fun interface stablePort =>
        match decodePort stablePort with
        | some port => code.attaches interface port
        | none => false
      residualConnected := code.residualConnected }
    interfaceActive := code.interfaceActive
    portActive := fun stablePort =>
      match decodePort stablePort with
      | some port => code.portActive port
      | none => false }
  interfacePresent := code.interfacePresent
  componentCap := code.componentCap

@[simp] theorem padCappedSupportedPortResidualCodePorts_attaches_of_decode
    {Interface Port StablePort : Type*}
    (decodePort : StablePort → Option Port)
    (code : BoundedCappedSupportedPortResidualCode Interface Port)
    (interface : Interface) (stablePort : StablePort) (port : Port)
    (hdecode : decodePort stablePort = some port) :
    (padCappedSupportedPortResidualCodePorts decodePort code).attaches
        interface stablePort = code.attaches interface port := by
  simp [padCappedSupportedPortResidualCodePorts, hdecode]

@[simp] theorem padCappedSupportedPortResidualCodePorts_residualConnected
    {Interface Port StablePort : Type*}
    (decodePort : StablePort → Option Port)
    (code : BoundedCappedSupportedPortResidualCode Interface Port)
    (left right : Interface) :
    (padCappedSupportedPortResidualCodePorts decodePort code).residualConnected
        left right = code.residualConnected left right := by
  rfl

@[simp] theorem padCappedSupportedPortResidualCodePorts_interfaceActive
    {Interface Port StablePort : Type*}
    (decodePort : StablePort → Option Port)
    (code : BoundedCappedSupportedPortResidualCode Interface Port)
    (interface : Interface) :
    (padCappedSupportedPortResidualCodePorts decodePort code).interfaceActive
        interface = code.interfaceActive interface := by
  rfl

@[simp] theorem padCappedSupportedPortResidualCodePorts_interfacePresent
    {Interface Port StablePort : Type*}
    (decodePort : StablePort → Option Port)
    (code : BoundedCappedSupportedPortResidualCode Interface Port)
    (interface : Interface) :
    (padCappedSupportedPortResidualCodePorts decodePort code).interfacePresent
        interface = code.interfacePresent interface := by
  rfl

@[simp] theorem padCappedSupportedPortResidualCodePorts_componentCap
    {Interface Port StablePort : Type*}
    (decodePort : StablePort → Option Port)
    (code : BoundedCappedSupportedPortResidualCode Interface Port)
    (interface : Interface) :
    (padCappedSupportedPortResidualCodePorts decodePort code).componentCap
        interface = code.componentCap interface := by
  rfl

/-- Canonical port padding preserves the residual-or-equal-port component
relation exactly.  A padded slot cannot witness an attachment unless it
decodes to a real port. -/
theorem supportedPortResidualFactoredReachability_padPorts_boundedFiniteSlot
    {Interface Port : Type*} [Fintype Port] {bound : Nat}
    (hcard : Fintype.card Port ≤ bound)
    (code : BoundedCappedSupportedPortResidualCode Interface Port)
    (left right : Interface) :
    SupportedPortResidualFactoredReachability
        (padCappedSupportedPortResidualCodePorts
          (boundedFiniteSlot? hcard) code).toBoundedSupportedPortResidualCode
        (fun leftPort rightPort : Fin bound => leftPort = rightPort)
        left right ↔
      SupportedPortResidualFactoredReachability
        code.toBoundedSupportedPortResidualCode
        (fun leftPort rightPort : Port => leftPort = rightPort)
        left right := by
  classical
  simp only [SupportedPortResidualFactoredReachability,
    PortResidualFactoredReachability]
  constructor
  · rintro (hresidual | ⟨leftSlot, rightSlot, hleft, hslots, hright⟩)
    · exact Or.inl hresidual
    · subst rightSlot
      cases hdecode : boundedFiniteSlot? hcard leftSlot with
      | none =>
          simp [padCappedSupportedPortResidualCodePorts, hdecode] at hleft
      | some port =>
          exact Or.inr ⟨port, port,
            by simpa [padCappedSupportedPortResidualCodePorts, hdecode] using hleft,
            rfl,
            by simpa [padCappedSupportedPortResidualCodePorts, hdecode] using hright⟩
  · rintro (hresidual | ⟨leftPort, rightPort, hleft, hports, hright⟩)
    · exact Or.inl hresidual
    · subst rightPort
      refine Or.inr ⟨boundedFiniteSlot hcard leftPort,
        boundedFiniteSlot hcard leftPort, ?_, rfl, ?_⟩
      · simpa [padCappedSupportedPortResidualCodePorts] using hleft
      · simpa [padCappedSupportedPortResidualCodePorts] using hright

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialBoundaryRebaseStableFaceFixedStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

/-- The exact predecessor fragment carrier of a literal two-edge serial cut
has at most four elements. -/
private theorem sourceCorridorSerialBoundaryRebaseFacePort_card_le_four
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
    (offset : Fin (blockLength - 3)) :
    Fintype.card
      (SourceCorridorSerialBoundaryRebaseFacePortAt realization hcubic
        hrotation htwoSided hunique offset) ≤ 4 := by
  simp only [SourceCorridorSerialBoundaryRebaseFacePortAt,
    SerialCutFragmentIndex, Fintype.card_fin]
  change Fintype.card (BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing))
    (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
      htwoSided hunique offset).regionEdges) ≤ 4
  calc
    _ ≤ 2 * 2 := regionalBoundaryGraphCutData_fragmentCount_le_two_mul
      embedded.cellulation.rotation.toRotationSystem
      (sourceCorridorSerialPrefixCutDataAt realization hcubic hrotation
        htwoSided hunique offset).regionEdges
      ((sourceSlabInterfaceAt realization hcubic hrotation htwoSided hunique
        offset).nextLocalLayerPrefixCrossing)
    _ = 4 := by omega

/-- Canonical four-slot name of one predecessor face port. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFacePortSlotAt
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
    (offset : Fin (blockLength - 3)) :
    SourceCorridorSerialBoundaryRebaseFacePortAt realization hcubic hrotation
        htwoSided hunique offset → Fin 4 :=
  boundedFiniteSlot
    (sourceCorridorSerialBoundaryRebaseFacePort_card_le_four realization hcubic
      hrotation htwoSided hunique offset)

/-- Partial decoder of a fixed predecessor face-port slot. -/
noncomputable def sourceCorridorSerialBoundaryRebaseFacePortAtSlot?
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
    (offset : Fin (blockLength - 3)) :
    Fin 4 → Option
      (SourceCorridorSerialBoundaryRebaseFacePortAt realization hcubic
        hrotation htwoSided hunique offset) :=
  boundedFiniteSlot?
    (sourceCorridorSerialBoundaryRebaseFacePort_card_le_four realization hcubic
      hrotation htwoSided hunique offset)

@[simp] theorem sourceCorridorSerialBoundaryRebaseFacePortAtSlot?_slot
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
    (port : SourceCorridorSerialBoundaryRebaseFacePortAt realization hcubic
      hrotation htwoSided hunique offset) :
    sourceCorridorSerialBoundaryRebaseFacePortAtSlot? realization hcubic
        hrotation htwoSided hunique offset
        (sourceCorridorSerialBoundaryRebaseFacePortSlotAt realization hcubic
          hrotation htwoSided hunique offset port) = some port := by
  apply boundedFiniteSlot?_slot

/-- One common finite type for every capped facial predecessor state in the
literal serial word. -/
abbrev BoundedSerialBoundaryRebaseStableFixedCappedFaceCode :=
  BoundedCappedSupportedPortResidualCode (Fin 16) (Fin 4)

/-- Extract the fully fixed predecessor facial state of one literal rebase. -/
noncomputable def sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceCodeAt
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
    BoundedSerialBoundaryRebaseStableFixedCappedFaceCode :=
  padCappedSupportedPortResidualCodePorts
    (sourceCorridorSerialBoundaryRebaseFacePortAtSlot? realization hcubic
      hrotation htwoSided hunique offset)
    (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization hcubic
      hrotation htwoSided hunique offset hnext)

/-- Every actual occurrence and predecessor port round-trips through the
fully fixed state. -/
theorem sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceCodeAt_occurrence_port
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
        hcubic hrotation htwoSided hunique offset hnext)
    (port : SourceCorridorSerialBoundaryRebaseFacePortAt realization hcubic
      hrotation htwoSided hunique offset) :
    let fixed :=
      sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext
    let stable :=
      sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext
    let occurrenceSlot := sourceCorridorSerialBoundaryRebaseFaceOccurrenceSlotAt
      realization hcubic hrotation htwoSided hunique offset hnext occurrence
    let portSlot := sourceCorridorSerialBoundaryRebaseFacePortSlotAt realization
      hcubic hrotation htwoSided hunique offset port
    fixed.interfaceActive occurrenceSlot = stable.interfaceActive occurrenceSlot ∧
      fixed.interfacePresent occurrenceSlot = stable.interfacePresent occurrenceSlot ∧
      fixed.componentCap occurrenceSlot = stable.componentCap occurrenceSlot ∧
      fixed.attaches occurrenceSlot portSlot = stable.attaches occurrenceSlot port ∧
      (∀ other,
        fixed.residualConnected occurrenceSlot other =
          stable.residualConnected occurrenceSlot other) := by
  dsimp only
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · apply padCappedSupportedPortResidualCodePorts_attaches_of_decode
    exact sourceCorridorSerialBoundaryRebaseFacePortAtSlot?_slot realization
      hcubic hrotation htwoSided hunique offset port
  · intro other
    rfl

/-- Padding the predecessor fragment coordinates onto four slots preserves
the exact facial component relation on all sixteen occurrence slots. -/
theorem sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceCodeAt_factored_iff
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
    (left right : Fin 16) :
    SupportedPortResidualFactoredReachability
        (sourceCorridorSerialBoundaryRebaseStableFixedCappedFaceCodeAt
          realization hcubic hrotation htwoSided hunique offset hnext
            ).toBoundedSupportedPortResidualCode
        (fun leftPort rightPort : Fin 4 => leftPort = rightPort) left right ↔
      SupportedPortResidualFactoredReachability
        (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization
          hcubic hrotation htwoSided hunique offset hnext
            ).toBoundedSupportedPortResidualCode
        (fun leftPort rightPort => leftPort = rightPort) left right := by
  exact
    supportedPortResidualFactoredReachability_padPorts_boundedFiniteSlot
      (sourceCorridorSerialBoundaryRebaseFacePort_card_le_four realization
        hcubic hrotation htwoSided hunique offset)
      (sourceCorridorSerialBoundaryRebaseStableCappedFaceCodeAt realization
        hcubic hrotation htwoSided hunique offset hnext) left right

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
