import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolOutput
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteStepReflection

/-!
# A fully Boolean receipt for one literal boundary rebase

The existing finite output receipt stores Boolean profile observations, but it
also retains its proof-facing facial graph family.  That field is useful for
adequacy proofs and unsuitable as the carrier of a native finite evaluator.

This file reflects the embedded facial family to a Boolean adjacency table and
packages it with the already finite tracked and facial observations.  Its
decoder is proved equal to the earlier five-field decoder, and hence to the
actual next terminal-aware source profile.  The receipt is still output data;
the complete predecessor-to-successor support predicate is the next unit.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolReceipt

open GoertzelV24BoundedCarrierBoolGraphFamilyCode
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolOutput
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteBoolRelationClosure
open SimpleGraphDartRotation

/-- Native Boolean form of the finite successor-face receipt. -/
structure SourceLocalLayerBoundaryRebaseFiniteBoolFaceReceipt where
  collarCode : BoundedCarrierBoolGraphFamilyCode 24 0 Bool
  fragmentOccupied : Fin 4 → Bool
  fragmentCoordinate : Fin 4 → Option (Fin collarCode.vertexCount.val)
  faceContinues : Fin 4 → Fin 4 → Bool
  fragmentContainsPort : Fin 4 → CorridorPort 2 1 → Bool
  faceLengthCap : Fin 4 → Fin 6

noncomputable instance :
    DecidableEq SourceLocalLayerBoundaryRebaseFiniteBoolFaceReceipt :=
  Classical.decEq _

private abbrev sourceLocalLayerBoundaryRebaseFiniteBoolFaceReceiptCode :=
  Σ code : BoundedCarrierBoolGraphFamilyCode 24 0 Bool,
    (Fin 4 → Bool) ×
      (Fin 4 → Option (Fin code.vertexCount.val)) ×
        (Fin 4 → Fin 4 → Bool) ×
          (Fin 4 → CorridorPort 2 1 → Bool) × (Fin 4 → Fin 6)

private def sourceLocalLayerBoundaryRebaseFiniteBoolFaceReceiptEquiv :
    SourceLocalLayerBoundaryRebaseFiniteBoolFaceReceipt ≃
      sourceLocalLayerBoundaryRebaseFiniteBoolFaceReceiptCode where
  toFun receipt :=
    ⟨receipt.collarCode, receipt.fragmentOccupied,
      receipt.fragmentCoordinate, receipt.faceContinues,
      receipt.fragmentContainsPort, receipt.faceLengthCap⟩
  invFun data :=
    { collarCode := data.1
      fragmentOccupied := data.2.1
      fragmentCoordinate := data.2.2.1
      faceContinues := data.2.2.2.1
      fragmentContainsPort := data.2.2.2.2.1
      faceLengthCap := data.2.2.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

deriving noncomputable instance Fintype for
  sourceLocalLayerBoundaryRebaseFiniteBoolFaceReceiptCode

noncomputable instance :
    Fintype SourceLocalLayerBoundaryRebaseFiniteBoolFaceReceipt :=
  Fintype.ofEquiv _
    sourceLocalLayerBoundaryRebaseFiniteBoolFaceReceiptEquiv.symm

/-- Reflect the one remaining proposition-valued family of a face receipt. -/
noncomputable def ofFiniteFaceReceipt
    (receipt : SourceLocalLayerBoundaryRebaseFiniteFaceReceipt) :
    SourceLocalLayerBoundaryRebaseFiniteBoolFaceReceipt where
  collarCode := ofGraphFamilyCode receipt.collarCode
  fragmentOccupied := receipt.fragmentOccupied
  fragmentCoordinate := receipt.fragmentCoordinate
  faceContinues := receipt.faceContinues
  fragmentContainsPort := receipt.fragmentContainsPort
  faceLengthCap := receipt.faceLengthCap

/-- Complete native-Boolean output data for one boundary rebase. -/
structure SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode where
  outputCount : Fin 5
  tracked : SourceLocalLayerBoundaryRebaseTrackedState
  facial : SourceLocalLayerBoundaryRebaseFiniteBoolFaceReceipt

noncomputable instance :
    DecidableEq SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode :=
  Classical.decEq _

private def sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeEquiv :
    SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode ≃
      Fin 5 × SourceLocalLayerBoundaryRebaseTrackedState ×
        SourceLocalLayerBoundaryRebaseFiniteBoolFaceReceipt where
  toFun code := ⟨code.outputCount, code.tracked, code.facial⟩
  invFun code := ⟨code.1, code.2.1, code.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    Fintype SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode :=
  Fintype.ofEquiv _
    sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeEquiv.symm

/-- Reflect the complete earlier output letter. -/
noncomputable def ofFiniteOutputLetterCode
    (code : SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode) :
    SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode where
  outputCount := code.outputCount
  tracked := code.receipt.tracked
  facial := ofFiniteFaceReceipt code.receipt.facial

/-- Fixed facial slot occupied by one dependent output row. -/
def SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode.outputFaceSlot
    (code : SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode) :
    Fin code.outputCount.val → Fin 4 :=
  Fin.castLE (Nat.le_of_lt_succ code.outputCount.isLt)

/-- Decode all five successor-profile coordinates from native Boolean data. -/
def SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode.outputProfile
    (code : SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode) :
    BoundedCorridorCutProfile 2 1 4 :=
  {
    faceFragmentCount := code.outputCount
    profile := {
      edgeColor := fun crossing =>
        code.tracked.roleColor
          (sourceLocalLayerBoundaryRebaseSuccessorPortRole (.inl crossing))
      strandConnected := fun pair left right =>
        SourceLocalLayerBoundaryRebaseTrackedConnectedBool code.tracked pair
          (sourceLocalLayerBoundaryRebaseSuccessorPortRole left)
          (sourceLocalLayerBoundaryRebaseSuccessorPortRole right)
      faceContinues := fun left right =>
        code.facial.faceContinues
          (code.outputFaceSlot left) (code.outputFaceSlot right)
      fragmentContainsPort := fun fragment port =>
        code.facial.fragmentContainsPort
          (code.outputFaceSlot fragment) port
      faceLengthCap := fun fragment =>
        code.facial.faceLengthCap (code.outputFaceSlot fragment) }
  }

/-- Reflection removes the proof-facing graph family without changing the
decoded five-field profile. -/
@[simp]
theorem outputProfile_ofFiniteOutputLetterCode
    (code : SourceLocalLayerBoundaryRebaseFiniteOutputLetterCode) :
    (ofFiniteOutputLetterCode code).outputProfile =
      sourceLocalLayerBoundaryRebaseFiniteOutputProfileBool code := by
  rfl

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFiniteBoolReceiptEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Canonical fully Boolean receipt extracted from one literal source rebase. -/
noncomputable def sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCode :=
  ofFiniteOutputLetterCode
    (sourceLocalLayerBoundaryRebaseFiniteOutputLetterCodeAt corridor hunique
      offset hnext)

/-- The fully Boolean receipt decodes exactly to the profile consumed by the
next literal Cell. -/
theorem sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt_outputProfile_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt corridor hunique
      offset hnext).outputProfile =
      sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) := by
  rw [sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt,
    outputProfile_ofFiniteOutputLetterCode]
  exact sourceLocalLayerBoundaryRebaseFiniteOutputProfileBoolAt_eq corridor
    hunique offset hnext

/-- On an actual source rebase, the reflected facial closure recognizes the
successor regional-fragment partition exactly. -/
theorem sourceLocalLayerBoundaryRebaseFiniteBoolFaceReceiptAt_fragmentClosure_iff_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : SourceLocalLayerBoundaryRebaseSuccessorFaceFragmentAt corridor
      hunique offset hnext) :
    SourceLocalLayerBoundaryRebaseFaceFiniteClosureBool
        (sourceLocalLayerBoundaryRebaseFiniteBoolOutputLetterCodeAt corridor
          hunique offset hnext).facial.collarCode
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt
          corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt
          corridor hunique offset hnext right) = true ↔
      left = right := by
  change
    SourceLocalLayerBoundaryRebaseFaceFiniteClosureBool
        (ofGraphFamilyCode
          (sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt corridor hunique
            offset hnext).collarCode)
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt
          corridor hunique offset hnext left)
        (sourceLocalLayerBoundaryRebaseSuccessorFaceFragmentCoordinateAt
          corridor hunique offset hnext right) = true ↔
      left = right
  rw [faceFiniteClosureBool_ofGraphFamilyCode_eq_true_iff]
  exact sourceLocalLayerBoundaryRebaseFiniteFaceReceiptAt_fragmentClosure_iff_eq
    corridor hunique offset hnext left right

end


end GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolReceipt

end Mettapedia.GraphTheory.FourColor
