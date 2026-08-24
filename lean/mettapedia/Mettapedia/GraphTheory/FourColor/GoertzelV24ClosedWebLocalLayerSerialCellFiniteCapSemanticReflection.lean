import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteStepReflection

/-!
# Boolean reflection of the literal Cell face-cap laws

The finite face-cap decoder uses two proof-facing semantic certificates.  One
says that the predecessor attachment table is an equivalence relation whose
presence and cap fields are constant on components.  The other says that the
stored equality table is an equivalence relation on the genuinely new edges of
one output component.

This module reflects both certificates to exact Boolean checks on the fixed
twenty-four-slot interface.  It does not yet count canonical representatives
or define the complete Boolean support letter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFiniteCapSemanticReflection

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteEdgeState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteClosure
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFiniteNewEdgeRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFaceFinitePredecessorRepresentatives
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteStepReflection
open GoertzelV24SimpleGraphSupportedPortResidualFactorContraction

/-- Executable predecessor-component connectivity on the live finite carrier. -/
def SourceLocalLayerSerialFaceFinitePredecessorConnectedBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) : Bool :=
  SupportedPortResidualFactoredReachabilityBool
    (List.finRange 4)
    state.toBoundedSupportedPortResidualCode
    (fun leftPort rightPort : Fin 4 => decide (leftPort = rightPort))
    (BoundedCarrierBoolLiveSlot code left)
    (BoundedCarrierBoolLiveSlot code right)

/-- The Boolean predecessor query is exact on a reflected proof-facing code. -/
@[simp]
theorem predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (left right : Fin code.vertexCount.val) :
    SourceLocalLayerSerialFaceFinitePredecessorConnectedBool state
        (ofGraphFamilyCode code) left right = true ↔
      SourceLocalLayerSerialFaceFinitePredecessorConnected state code left
        right := by
  rw [SourceLocalLayerSerialFaceFinitePredecessorConnectedBool,
    supportedPortResidualFactoredReachabilityBool_eq_true_iff]
  · simp only [decide_eq_true_eq,
      SourceLocalLayerSerialFaceFinitePredecessorConnected,
      BoundedCarrierBoolLiveSlot,
      sourceLocalLayerSerialFaceFiniteStableSlot]
    exact Iff.rfl
  · intro port
    exact List.mem_finRange port

/-- Executable check of every law used by the predecessor-component cap sum. -/
def SourceLocalLayerSerialFaceFinitePredecessorSemanticBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool) : Bool :=
  decide
    ((∀ coordinate,
        SourceLocalLayerSerialFaceFinitePredecessorConnectedBool state code
          coordinate coordinate = true) ∧
      (∀ left right,
        SourceLocalLayerSerialFaceFinitePredecessorConnectedBool state code
            left right = true →
          SourceLocalLayerSerialFaceFinitePredecessorConnectedBool state code
            right left = true) ∧
      (∀ left middle right,
        SourceLocalLayerSerialFaceFinitePredecessorConnectedBool state code
            left middle = true →
        SourceLocalLayerSerialFaceFinitePredecessorConnectedBool state code
            middle right = true →
          SourceLocalLayerSerialFaceFinitePredecessorConnectedBool state code
            left right = true) ∧
      (∀ left right,
        SourceLocalLayerSerialFaceFinitePredecessorConnectedBool state code
            left right = true →
          state.interfacePresent (BoundedCarrierBoolLiveSlot code left) =
            state.interfacePresent (BoundedCarrierBoolLiveSlot code right)) ∧
      (∀ left right,
        SourceLocalLayerSerialFaceFinitePredecessorConnectedBool state code
            left right = true →
          state.componentCap (BoundedCarrierBoolLiveSlot code left) =
            state.componentCap (BoundedCarrierBoolLiveSlot code right)))

/-- The executable predecessor-law check is exactly the proof-facing semantic
certificate on reflected graph codes. -/
@[simp]
theorem predecessorSemanticBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool) :
    SourceLocalLayerSerialFaceFinitePredecessorSemanticBool state
        (ofGraphFamilyCode code) = true ↔
      SourceLocalLayerSerialFaceFinitePredecessorSemantic state code := by
  rw [SourceLocalLayerSerialFaceFinitePredecessorSemanticBool,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hrefl, hsymm, htrans, hpresent, hcap⟩
    exact {
      connected_refl := fun coordinate =>
        (predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
          coordinate coordinate).1 (hrefl coordinate)
      connected_symm := fun {left right} hconnected =>
        (predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
          right left).1
          (hsymm left right
            ((predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
              left right).2 hconnected))
      connected_trans := fun {left middle right} hleft hright =>
        (predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
          left right).1
          (htrans left middle right
            ((predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
              left middle).2 hleft)
            ((predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
              middle right).2 hright))
      present_constant := fun {left right} hconnected => by
        simpa [BoundedCarrierBoolLiveSlot,
          sourceLocalLayerSerialFaceFiniteStableSlot] using
          hpresent left right
            ((predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
              left right).2 hconnected)
      cap_constant := fun {left right} hconnected => by
        simpa [BoundedCarrierBoolLiveSlot,
          sourceLocalLayerSerialFaceFiniteStableSlot] using
          hcap left right
            ((predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
              left right).2 hconnected) }
  · intro semantic
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro coordinate
      exact (predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
        coordinate coordinate).2 (semantic.connected_refl coordinate)
    · intro left right hconnected
      exact (predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
        right left).2
          (semantic.connected_symm
            ((predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
              left right).1 hconnected))
    · intro left middle right hleft hright
      exact (predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
        left right).2
          (semantic.connected_trans
            ((predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
              left middle).1 hleft)
            ((predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
              middle right).1 hright))
    · intro left right hconnected
      simpa [BoundedCarrierBoolLiveSlot,
        sourceLocalLayerSerialFaceFiniteStableSlot] using
        semantic.present_constant
          ((predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
            left right).1 hconnected)
    · intro left right hconnected
      simpa [BoundedCarrierBoolLiveSlot,
        sourceLocalLayerSerialFaceFiniteStableSlot] using
        semantic.cap_constant
          ((predecessorConnectedBool_ofGraphFamilyCode_eq_true_iff state code
            left right).1 hconnected)

/-- Executable test that a live coordinate contributes a genuinely new Cell
edge to the selected output face component. -/
def SourceLocalLayerSerialFaceFiniteNewEdgeContributesBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output coordinate : Fin code.vertexCount.val) : Bool :=
  edgeState.cellPresent (BoundedCarrierBoolLiveSlot code coordinate) &&
    !state.interfacePresent (BoundedCarrierBoolLiveSlot code coordinate) &&
      SourceLocalLayerSerialFaceFiniteComponentClosureBool state code output
        coordinate

/-- The Boolean contribution test is exact on reflected proof-facing codes. -/
@[simp]
theorem newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output coordinate : Fin code.vertexCount.val) :
    SourceLocalLayerSerialFaceFiniteNewEdgeContributesBool state
        (ofGraphFamilyCode code) edgeState output coordinate = true ↔
      SourceLocalLayerSerialFaceFiniteNewEdgeContributes state code edgeState
        output coordinate := by
  simp [SourceLocalLayerSerialFaceFiniteNewEdgeContributesBool,
    faceFiniteComponentClosureBool_ofGraphFamilyCode_eq_true_iff,
    SourceLocalLayerSerialFaceFiniteNewEdgeContributes,
    BoundedCarrierBoolLiveSlot, sourceLocalLayerSerialFaceFiniteStableSlot]
  tauto

/-- Executable check of the primal-edge equality laws on the contributing
coordinates of one output component. -/
def SourceLocalLayerSerialFaceFiniteNewEdgeSemanticBool
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val) : Bool :=
  decide
    ((∀ coordinate,
        SourceLocalLayerSerialFaceFiniteNewEdgeContributesBool state code
            edgeState output coordinate = true →
          edgeState.samePrimalEdge
            (BoundedCarrierBoolLiveSlot code coordinate)
            (BoundedCarrierBoolLiveSlot code coordinate) = true) ∧
      (∀ left right,
        SourceLocalLayerSerialFaceFiniteNewEdgeContributesBool state code
            edgeState output left = true →
        SourceLocalLayerSerialFaceFiniteNewEdgeContributesBool state code
            edgeState output right = true →
        edgeState.samePrimalEdge
            (BoundedCarrierBoolLiveSlot code left)
            (BoundedCarrierBoolLiveSlot code right) = true →
          edgeState.samePrimalEdge
            (BoundedCarrierBoolLiveSlot code right)
            (BoundedCarrierBoolLiveSlot code left) = true) ∧
      (∀ left middle right,
        SourceLocalLayerSerialFaceFiniteNewEdgeContributesBool state code
            edgeState output left = true →
        SourceLocalLayerSerialFaceFiniteNewEdgeContributesBool state code
            edgeState output middle = true →
        SourceLocalLayerSerialFaceFiniteNewEdgeContributesBool state code
            edgeState output right = true →
        edgeState.samePrimalEdge
            (BoundedCarrierBoolLiveSlot code left)
            (BoundedCarrierBoolLiveSlot code middle) = true →
        edgeState.samePrimalEdge
            (BoundedCarrierBoolLiveSlot code middle)
            (BoundedCarrierBoolLiveSlot code right) = true →
          edgeState.samePrimalEdge
            (BoundedCarrierBoolLiveSlot code left)
            (BoundedCarrierBoolLiveSlot code right) = true))

/-- The executable new-edge-law check is exactly the proof-facing semantic
certificate on reflected graph codes. -/
@[simp]
theorem newEdgeSemanticBool_ofGraphFamilyCode_eq_true_iff
    (state : SourceLocalLayerSerialFacePrefixAttachmentState)
    (code : BoundedCarrierGraphFamilyCode 24 0 Bool)
    (edgeState : SourceLocalLayerSerialFaceFiniteEdgeState)
    (output : Fin code.vertexCount.val) :
    SourceLocalLayerSerialFaceFiniteNewEdgeSemanticBool state
        (ofGraphFamilyCode code) edgeState output = true ↔
      SourceLocalLayerSerialFaceFiniteNewEdgeSemantic state code edgeState
        output := by
  rw [SourceLocalLayerSerialFaceFiniteNewEdgeSemanticBool, decide_eq_true_eq]
  constructor
  · rintro ⟨hrefl, hsymm, htrans⟩
    exact {
      same_refl := fun coordinate hcoordinate => by
        simpa [BoundedCarrierBoolLiveSlot,
          sourceLocalLayerSerialFaceFiniteStableSlot] using
          hrefl coordinate
            ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
              edgeState output coordinate).2 hcoordinate)
      same_symm := fun {left right} hleft hright hsame => by
        simpa [BoundedCarrierBoolLiveSlot,
          sourceLocalLayerSerialFaceFiniteStableSlot] using
          hsymm left right
            ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
              edgeState output left).2 hleft)
            ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
              edgeState output right).2 hright) hsame
      same_trans := fun {left middle right} hleft hmiddle hright hlm hmr => by
        simpa [BoundedCarrierBoolLiveSlot,
          sourceLocalLayerSerialFaceFiniteStableSlot] using
          htrans left middle right
            ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
              edgeState output left).2 hleft)
            ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
              edgeState output middle).2 hmiddle)
            ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
              edgeState output right).2 hright) hlm hmr }
  · intro semantic
    refine ⟨?_, ?_, ?_⟩
    · intro coordinate hcoordinate
      simpa [BoundedCarrierBoolLiveSlot,
        sourceLocalLayerSerialFaceFiniteStableSlot] using
        semantic.same_refl coordinate
          ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
            edgeState output coordinate).1 hcoordinate)
    · intro left right hleft hright hsame
      simpa [BoundedCarrierBoolLiveSlot,
        sourceLocalLayerSerialFaceFiniteStableSlot] using
        semantic.same_symm
          ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
            edgeState output left).1 hleft)
          ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
            edgeState output right).1 hright) hsame
    · intro left middle right hleft hmiddle hright hlm hmr
      simpa [BoundedCarrierBoolLiveSlot,
        sourceLocalLayerSerialFaceFiniteStableSlot] using
        semantic.same_trans
          ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
            edgeState output left).1 hleft)
          ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
            edgeState output middle).1 hmiddle)
          ((newEdgeContributesBool_ofGraphFamilyCode_eq_true_iff state code
            edgeState output right).1 hright) hlm hmr

end GoertzelV24ClosedWebLocalLayerSerialCellFiniteCapSemanticReflection

end Mettapedia.GraphTheory.FourColor
