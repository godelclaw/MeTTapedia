import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundedCarrierBoolGraphFamilyCode
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24FiniteBoolRelationClosure

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
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellTrackedPrefixAttachmentState
open GoertzelV24CorridorProfile
open GoertzelV24FiniteBoolRelationClosure
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

/-- Exact directed closure of the executable tracked-component step. -/
def SourceLocalLayerSerialTrackedFiniteComponentClosureBool
    (state : SourceLocalLayerSerialTrackedPrefixAttachmentState)
    (input : BoundedCorridorCutProfile 2 1 4)
    (code : BoundedCarrierBoolGraphFamilyCode 21 5
      (TrackedColorPair × Bool))
    (pair : TrackedColorPair)
    (left right : Fin code.vertexCount.val) : Bool :=
  boolRelationReachable
    (SourceLocalLayerSerialTrackedFiniteComponentStepBool state input code pair)
    left right

/-- Exact directed closure of the executable facial-component step. -/
def SourceLocalLayerSerialFaceFiniteComponentClosureBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) : Bool :=
  boolRelationReachable
    (SourceLocalLayerSerialFaceFiniteComponentStepBool state code) left right

/-- Embed a live coordinate of a Boolean carrier in its fixed-slot ABI. -/
def BoundedCarrierBoolLiveSlot
    {bound pointCount : Nat} {Family : Type*}
    (code : BoundedCarrierBoolGraphFamilyCode bound pointCount Family)
    (coordinate : Fin code.vertexCount.val) : Fin bound :=
  Fin.castLE (Nat.le_of_lt_succ code.vertexCount.isLt) coordinate

/-- Executable fixed-slot tracked closure used by the finite support letter. -/
def SourceLocalLayerSerialTrackedFiniteConnectedBool
    (state : SourceLocalLayerSerialTrackedPrefixAttachmentState)
    (input : BoundedCorridorCutProfile 2 1 4)
    (code : BoundedCarrierBoolGraphFamilyCode 21 5
      (TrackedColorPair × Bool))
    (pair : TrackedColorPair) (left right : Fin 21) : Bool :=
  decide (∃ leftCoordinate rightCoordinate : Fin code.vertexCount.val,
    BoundedCarrierBoolLiveSlot code leftCoordinate = left ∧
      BoundedCarrierBoolLiveSlot code rightCoordinate = right ∧
        SourceLocalLayerSerialTrackedFiniteComponentClosureBool state input
          code pair leftCoordinate rightCoordinate = true)

/-- Executable fixed-slot facial closure used by the finite support letter. -/
def SourceLocalLayerSerialFaceFiniteConnectedBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (left right : Fin 24) : Bool :=
  decide (∃ leftCoordinate rightCoordinate : Fin code.vertexCount.val,
    BoundedCarrierBoolLiveSlot code leftCoordinate = left ∧
      BoundedCarrierBoolLiveSlot code rightCoordinate = right ∧
        SourceLocalLayerSerialFaceFiniteComponentClosureBool state code
          leftCoordinate rightCoordinate = true)

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

/-- Boolean saturation of a reflected tracked code is exactly the original
proof-facing reflexive-transitive closure. -/
@[simp]
theorem trackedFiniteComponentClosureBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialTrackedPrefixAttachmentState)
    (input : BoundedCorridorCutProfile 2 1 4)
    (code : BoundedCarrierGraphFamilyCode 21 5
      (TrackedColorPair × Bool))
    (pair : TrackedColorPair)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerSerialTrackedFiniteComponentClosureBool state input
        (ofGraphFamilyCode code) pair left right = true ↔
      Relation.ReflTransGen
        (SourceLocalLayerSerialTrackedFiniteComponentStep state input code pair)
        left right := by
  rw [SourceLocalLayerSerialTrackedFiniteComponentClosureBool,
    boolRelationReachable_eq_true_iff]
  constructor
  · exact Relation.ReflTransGen.mono fun first second hstep =>
      (trackedFiniteComponentStepBool_ofGraphFamilyCode_eq_true_iff
        state input code pair first second).1 hstep
  · exact Relation.ReflTransGen.mono fun first second hstep =>
      (trackedFiniteComponentStepBool_ofGraphFamilyCode_eq_true_iff
        state input code pair first second).2 hstep

/-- Boolean saturation of a reflected facial code is exactly the original
proof-facing reflexive-transitive closure. -/
@[simp]
theorem faceFiniteComponentClosureBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerSerialFaceFiniteComponentClosureBool state
        (ofGraphFamilyCode code) left right = true ↔
      Relation.ReflTransGen
        (SourceLocalLayerSerialFaceFiniteComponentStep state code)
        left right := by
  rw [SourceLocalLayerSerialFaceFiniteComponentClosureBool,
    boolRelationReachable_eq_true_iff]
  constructor
  · exact Relation.ReflTransGen.mono fun first second hstep =>
      (faceFiniteComponentStepBool_ofGraphFamilyCode_eq_true_iff
        state code first second).1 hstep
  · exact Relation.ReflTransGen.mono fun first second hstep =>
      (faceFiniteComponentStepBool_ofGraphFamilyCode_eq_true_iff
        state code first second).2 hstep

/-- The fixed-slot tracked query is executable without changing the support
letter's proposition-valued meaning. -/
@[simp]
theorem trackedFiniteConnectedBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialTrackedPrefixAttachmentState)
    (input : BoundedCorridorCutProfile 2 1 4)
    (code : BoundedCarrierGraphFamilyCode 21 5
      (TrackedColorPair × Bool))
    (pair : TrackedColorPair) (left right : Fin 21) :
    SourceLocalLayerSerialTrackedFiniteConnectedBool state input
        (ofGraphFamilyCode code) pair left right = true ↔
      SourceLocalLayerSerialTrackedFiniteConnected state input code pair
        left right := by
  simp only [SourceLocalLayerSerialTrackedFiniteConnectedBool,
    decide_eq_true_eq,
    trackedFiniteComponentClosureBool_ofGraphFamilyCode_eq_true_iff,
    SourceLocalLayerSerialTrackedFiniteConnected,
    BoundedCarrierBoolLiveSlot, BoundedCarrierLiveSlot]
  constructor <;>
    rintro ⟨leftCoordinate, rightCoordinate, hleft, hright, hclosure⟩ <;>
    exact ⟨leftCoordinate, rightCoordinate, by simpa using hleft,
      by simpa using hright, hclosure⟩

/-- The fixed-slot facial query is executable without changing the support
letter's proposition-valued meaning. -/
@[simp]
theorem faceFiniteConnectedBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin 24) :
    SourceLocalLayerSerialFaceFiniteConnectedBool state
        (ofGraphFamilyCode code) left right = true ↔
      SourceLocalLayerSerialFaceFiniteConnected state code left right := by
  simp only [SourceLocalLayerSerialFaceFiniteConnectedBool,
    decide_eq_true_eq,
    faceFiniteComponentClosureBool_ofGraphFamilyCode_eq_true_iff,
    SourceLocalLayerSerialFaceFiniteConnected,
    BoundedCarrierBoolLiveSlot, BoundedCarrierLiveSlot]
  constructor <;>
    rintro ⟨leftCoordinate, rightCoordinate, hleft, hright, hclosure⟩ <;>
    exact ⟨leftCoordinate, rightCoordinate, by simpa using hleft,
      by simpa using hright, hclosure⟩

end GoertzelV24ClosedWebLocalLayerSerialCellFiniteStepReflection

end Mettapedia.GraphTheory.FourColor
