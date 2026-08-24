import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFiniteBoolSupportLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter

/-!
# One executable Cell--rebase transition receipt

The source corridor alternates two different finite morphisms.  A literal
Cell sends a terminal-aware profile to a zero-terminal profile; the following
boundary rebase sends that profile to the next terminal-aware profile.  This
file pairs those endpoint receipts, checks their middle profile exactly, and
exposes the resulting terminal-aware-to-terminal-aware witnessed transition
as a Boolean relation.

Every actual consecutive Cell--rebase pair is supported.  The construction
retains the complete indexed literal letters and all five profile fields.  It
does not quotient Cells by orientation, assert that arbitrary codes have
positive manuscript count, or compute the reachable closure.  In particular,
one receipt is not the complete support relation of its physical Cell: that
relation must range over every positive entry of the Cell's `Count` matrix.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialFiniteBoolStepLetter

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteBoolSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
open GoertzelV24CorridorProfile
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoPentagonCapOpening
open SimpleGraphDartRotation

/-- A complete finite source step: one literal Cell followed by its distinct
boundary rebase. -/
structure SourceLocalLayerSerialFiniteBoolStepLetter where
  cell : SourceLocalLayerSerialCellFiniteBoolSupportLetter
  rebase : SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter

noncomputable instance :
    DecidableEq SourceLocalLayerSerialFiniteBoolStepLetter :=
  Classical.decEq _

private def sourceLocalLayerSerialFiniteBoolStepLetterEquiv :
    SourceLocalLayerSerialFiniteBoolStepLetter ≃
      SourceLocalLayerSerialCellFiniteBoolSupportLetter ×
        SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter where
  toFun letter := ⟨letter.cell, letter.rebase⟩
  invFun data := ⟨data.1, data.2⟩
  left_inv letter := by cases letter; rfl
  right_inv data := rfl

noncomputable instance :
    Fintype SourceLocalLayerSerialFiniteBoolStepLetter :=
  Fintype.ofEquiv _ sourceLocalLayerSerialFiniteBoolStepLetterEquiv.symm

/-- The terminal-aware input profile of a complete Cell--rebase step. -/
def SourceLocalLayerSerialFiniteBoolStepLetter.input
    (letter : SourceLocalLayerSerialFiniteBoolStepLetter) :
    BoundedCorridorCutProfile 2 1 4 :=
  letter.cell.input

/-- The terminal-aware output profile of a complete Cell--rebase step. -/
def SourceLocalLayerSerialFiniteBoolStepLetter.output
    (letter : SourceLocalLayerSerialFiniteBoolStepLetter) :
    BoundedCorridorCutProfile 2 1 4 :=
  letter.rebase.output

/-- Executable support of a complete source step.  Both constituent letters
must be supported and their zero-terminal middle profiles must agree exactly.
-/
def SourceLocalLayerSerialFiniteBoolStepSupportsBool
    (letter : SourceLocalLayerSerialFiniteBoolStepLetter) : Bool :=
  SourceLocalLayerSerialCellFiniteSupportsBool letter.cell &&
    SourceLocalLayerBoundaryRebaseFiniteSupportsBool letter.rebase &&
    decide (letter.cell.output = letter.rebase.input)

/-- The exact singleton transition carried by one finite Cell--rebase receipt.
It is a witness which the later complete support relation must contain, not
that whole relation. -/
def SourceLocalLayerSerialFiniteBoolStepRelation
    (letter : SourceLocalLayerSerialFiniteBoolStepLetter)
    (input output : BoundedCorridorCutProfile 2 1 4) : Bool :=
  SourceLocalLayerSerialFiniteBoolStepSupportsBool letter &&
    decide (input = letter.input ∧ output = letter.output)

theorem finiteBoolStepRelation_eq_true_iff
    (letter : SourceLocalLayerSerialFiniteBoolStepLetter)
    (input output : BoundedCorridorCutProfile 2 1 4) :
    SourceLocalLayerSerialFiniteBoolStepRelation letter input output = true ↔
      SourceLocalLayerSerialFiniteBoolStepSupportsBool letter = true ∧
        input = letter.input ∧ output = letter.output := by
  simp [SourceLocalLayerSerialFiniteBoolStepRelation]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

local instance openedGraphDecidableRel
    (caps : OrientedFacialPentagonCapPair (G := G) graphData) :
    DecidableRel
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.Adj :=
  Classical.decRel _

/-- Extract the complete finite step at one actual source offset which has a
successor offset. -/
noncomputable def sourceLocalLayerSerialFiniteBoolStepLetterAt
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerSerialFiniteBoolStepLetter where
  cell :=
    ofFiniteSupportLetter
      (sourceLocalLayerSerialCellFiniteSupportLetterAt graphData minimal caps
        coloring web corridor hunique offset)
  rebase :=
    sourceLocalLayerBoundaryRebaseFiniteBoolSupportLetterAt corridor hunique
      offset hnext

/-- Every actual consecutive Cell--rebase pair satisfies the complete Boolean
step predicate. -/
theorem sourceLocalLayerSerialFiniteBoolStepLetterAt_supports
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerSerialFiniteBoolStepSupportsBool
      (sourceLocalLayerSerialFiniteBoolStepLetterAt graphData minimal caps
        coloring web corridor hunique offset hnext) = true := by
  rw [SourceLocalLayerSerialFiniteBoolStepSupportsBool, Bool.and_eq_true,
    Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact
      (finiteSupportsBool_ofFiniteSupportLetter_eq_true_iff _).2
        (sourceLocalLayerSerialCellFiniteSupportLetterAt_supports graphData
          minimal caps coloring web corridor hunique offset)
  · exact
      sourceLocalLayerBoundaryRebaseFiniteBoolSupportLetterAt_supports corridor
        hunique offset hnext
  · rw [decide_eq_true_eq]
    rfl

/-- The actual step starts at the literal terminal-aware profile of its source
offset. -/
theorem sourceLocalLayerSerialFiniteBoolStepLetterAt_input_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerSerialFiniteBoolStepLetterAt graphData minimal caps coloring
      web corridor hunique offset hnext).input =
      sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        offset := by
  rfl

/-- The actual step ends at the literal terminal-aware profile of the successor
offset. -/
theorem sourceLocalLayerSerialFiniteBoolStepLetterAt_output_eq
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (sourceLocalLayerSerialFiniteBoolStepLetterAt graphData minimal caps coloring
      web corridor hunique offset hnext).output =
      sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext) := by
  rfl

/-- The exact Boolean relation of an actual step accepts its two literal
terminal-aware endpoints. -/
theorem sourceLocalLayerSerialFiniteBoolStepRelationAt_eq_true
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (caps : OrientedFacialPentagonCapPair graphData)
    (coloring :
      caps.toFacialPentagonCapPair.toPentagonCapPair.openGraph.EdgeColoring Color)
    (web : GoertzelV24ClosedWebAtGoodWord.Instance
      caps.toFacialPentagonCapPair.toPentagonCapPair.boundaryData coloring)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerSerialFiniteBoolStepRelation
      (sourceLocalLayerSerialFiniteBoolStepLetterAt graphData minimal caps
        coloring web corridor hunique offset hnext)
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        offset)
      (sourceLocalLayerSerialTerminalInputBoundedProfileAt corridor hunique
        (sourceLocalLayerNextOffset offset hnext)) = true := by
  rw [finiteBoolStepRelation_eq_true_iff]
  refine ⟨sourceLocalLayerSerialFiniteBoolStepLetterAt_supports graphData minimal
    caps coloring web corridor hunique offset hnext, ?_⟩
  exact ⟨
    (sourceLocalLayerSerialFiniteBoolStepLetterAt_input_eq graphData minimal caps
      coloring web corridor hunique offset hnext).symm,
    (sourceLocalLayerSerialFiniteBoolStepLetterAt_output_eq graphData minimal caps
      coloring web corridor hunique offset hnext).symm⟩

end

end GoertzelV24ClosedWebLocalLayerSerialFiniteBoolStepLetter

end Mettapedia.GraphTheory.FourColor
