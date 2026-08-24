import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierBoolGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter

/-!
# Boolean reflection of the literal Cell component steps

The proof-facing one-Cell letter closes two finite unions of component
relations: one for tracked two-colour paths and one for face darts.  Its local
graph families were proposition-valued.  This file replaces only those local
queries by exact Boolean adjacency tables and exposes the complete one-step
relations as `Bool`.

The reflection theorems are iff statements.  Thus the executable step neither
adds nor drops a tracked or facial connection.  Iterating these steps into a
reachable closure remains a later unit.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFiniteStepReflection

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24CorridorProfile
open GoertzelV24SimpleGraphPortResidualFactorContraction
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction

/-- Executable form of the residual-or-port factorization. -/
def SupportedPortResidualFactoredReachabilityBool
    {Interface Port : Type*} [DecidableEq Port]
    (ports : List Port)
    (code : BoundedSupportedPortResidualCode Interface Port)
    (portConnected : Port → Port → Bool)
    (left right : Interface) : Bool :=
  code.residualConnected left right ||
    ports.any fun leftPort =>
      ports.any fun rightPort =>
        code.attaches left leftPort && portConnected leftPort rightPort &&
          code.attaches right rightPort

@[simp]
theorem supportedPortResidualFactoredReachabilityBool_eq_true_iff
    {Interface Port : Type*} [DecidableEq Port]
    (ports : List Port) (hports : ∀ port, port ∈ ports)
    (code : BoundedSupportedPortResidualCode Interface Port)
    (portConnected : Port → Port → Bool)
    (left right : Interface) :
    SupportedPortResidualFactoredReachabilityBool ports code portConnected
        left right = true ↔
    SupportedPortResidualFactoredReachability code
        (fun leftPort rightPort => portConnected leftPort rightPort = true)
        left right := by
  simp only [SupportedPortResidualFactoredReachabilityBool,
    SupportedPortResidualFactoredReachability,
    PortResidualFactoredReachability, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true]
  constructor
  · rintro (hresidual | ⟨leftPort, _hleftMem, rightPort, _hrightMem,
      ⟨hleft, hconnected⟩, hright⟩)
    · exact Or.inl hresidual
    · exact Or.inr ⟨leftPort, rightPort, hleft, hconnected, hright⟩
  · rintro (hresidual | ⟨leftPort, rightPort, hleft, hconnected, hright⟩)
    · exact Or.inl hresidual
    · exact Or.inr ⟨leftPort, hports leftPort, rightPort,
        hports rightPort, ⟨hleft, hconnected⟩, hright⟩

/-- Canonical executable enumeration of the two crossing ports and one
terminal port of the Cell input profile. -/
def sourceLocalLayerSerialTrackedInputPorts : List (CorridorPort 2 1) :=
  (List.finRange 2).map Sum.inl ++ (List.finRange 1).map Sum.inr

theorem mem_sourceLocalLayerSerialTrackedInputPorts
    (port : CorridorPort 2 1) :
    port ∈ sourceLocalLayerSerialTrackedInputPorts := by
  cases port with
  | inl port => simp [sourceLocalLayerSerialTrackedInputPorts]
  | inr port => simp [sourceLocalLayerSerialTrackedInputPorts]

/-- Executable tracked-component step on the reflected common carrier. -/
def SourceLocalLayerSerialTrackedFiniteComponentStepBool
    (state : SourceLocalLayerSerialTrackedPrefixAttachmentState)
    (input : BoundedCorridorCutProfile 2 1 4)
    (code : BoundedCarrierBoolGraphFamilyCode 21 5
      (TrackedColorPair × Bool))
    (pair : TrackedColorPair)
    (left right : Fin code.vertexCount.val) : Bool :=
  SupportedPortResidualFactoredReachabilityBool
      sourceLocalLayerSerialTrackedInputPorts (state pair)
      (fun leftPort rightPort =>
        input.profile.strandConnected pair leftPort rightPort)
        (Fin.castLE (Nat.le_of_lt_succ code.vertexCount.isLt) left)
        (Fin.castLE (Nat.le_of_lt_succ code.vertexCount.isLt) right) ||
    code.reachable (pair, false) left right ||
    code.reachable (pair, true) left right

/-- Executable facial-component step on the reflected common carrier. -/
def SourceLocalLayerSerialFaceFiniteComponentStepBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) : Bool :=
  SupportedPortResidualFactoredReachabilityBool
      (List.finRange 4)
      state.toBoundedSupportedPortResidualCode
      (fun leftPort rightPort : Fin 4 => decide (leftPort = rightPort))
        (Fin.castLE (Nat.le_of_lt_succ code.vertexCount.isLt) left)
        (Fin.castLE (Nat.le_of_lt_succ code.vertexCount.isLt) right) ||
    code.reachable false left right ||
    code.reachable true left right

/-- Reflecting a proof-facing tracked graph code makes the Boolean one-step
query exactly its original proposition-valued component step. -/
theorem trackedFiniteComponentStepBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialTrackedPrefixAttachmentState)
    (input : BoundedCorridorCutProfile 2 1 4)
    (code : BoundedCarrierGraphFamilyCode 21 5
      (TrackedColorPair × Bool))
    (pair : TrackedColorPair)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerSerialTrackedFiniteComponentStepBool state input
        (ofGraphFamilyCode code) pair left right = true ↔
      SourceLocalLayerSerialTrackedFiniteComponentStep state input code pair
        left right := by
  unfold SourceLocalLayerSerialTrackedFiniteComponentStepBool
  simp only [Bool.or_eq_true, ofGraphFamilyCode_reachable_eq_true_iff]
  rw [supportedPortResidualFactoredReachabilityBool_eq_true_iff _
    mem_sourceLocalLayerSerialTrackedInputPorts]
  simp only [
    SourceLocalLayerSerialTrackedFiniteComponentStep,
    sourceLocalLayerSerialTrackedFiniteStableSlot]
  unfold sourceLocalLayerSerialTrackedPrefixFactoredReachability
  tauto

/-- Reflecting a proof-facing facial graph code makes the Boolean one-step
query exactly its original proposition-valued component step. -/
theorem faceFiniteComponentStepBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerSerialFaceFiniteComponentStepBool state
        (ofGraphFamilyCode code) left right = true ↔
      SourceLocalLayerSerialFaceFiniteComponentStep state code left right := by
  unfold SourceLocalLayerSerialFaceFiniteComponentStepBool
  simp only [Bool.or_eq_true, ofGraphFamilyCode_reachable_eq_true_iff]
  rw [supportedPortResidualFactoredReachabilityBool_eq_true_iff _
    (by intro port; simp)]
  simp only [decide_eq_true_eq,
    SourceLocalLayerSerialFaceFiniteComponentStep,
    sourceLocalLayerSerialFaceFiniteStableSlot]
  tauto

end GoertzelV24ClosedWebLocalLayerSerialCellFiniteStepReflection

end Mettapedia.GraphTheory.FourColor
