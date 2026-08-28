import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellFiniteSupportLetter
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedBoundaryRebaseFiniteReceipt

/-!
# Exact finite transition of a selected Cell followed by boundary rebase

The source serial word alternates a literal Cell with a change of boundary
presentation.  This file composes the two finite receipts at their literal
zero-terminal endpoint.  A source witness consists of an arbitrary positive
cumulative-prefix colour function, a positive literal Cell colouring, and
agreement on their actual terminal-aware overlap.

The combined letter is supported precisely when the Cell receipt is supported,
the rebase consumes the Cell's exact output record, and the rebase receipt is
supported.  Thus the intermediate profile is record equality, not merely
agreement of its displayed boundary colours.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedCellRebaseFiniteTransition

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFiniteBoolSupportLetter
open GoertzelV24ClosedWebLocalLayerSerialCellFiniteSupportLetter
open GoertzelV24ClosedWebPointwiseSelectedCellFiniteSupportLetter
open GoertzelV24HexCorridorSkeleton

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedCellRebaseFiniteTransitionEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- An arbitrary finite colour function whose every value is a Tait colour.
It is the source-level positivity carried by a cumulative-prefix witness. -/
abbrev PointwiseSelectedPositiveColorFunction (Edge : Type*) :=
  {color : Edge → Color // ∀ edge, color edge ≠ 0}

noncomputable instance pointwiseSelectedPositiveColorFunctionFintype
    (Edge : Type*) [Fintype Edge] :
    Fintype (PointwiseSelectedPositiveColorFunction Edge) :=
  Fintype.ofFinite _

/-- Positivity of the cumulative prefix and literal Cell makes their
right-biased splice positive on all four roles read by the rebase. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (prefixColor : G.edgeSet → Color)
    (hprefix : ∀ edge, prefixColor edge ≠ 0)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt formation
        corridor hinterior offset)
    (role :
      GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation.SourceLocalLayerBoundaryRebaseRole) :
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt formation corridor
        hinterior offset prefixColor
        (pointwiseSelectedSourceLocalLayerCellLiteralColorAt formation corridor
          hinterior offset cellColoring)
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext role) ≠ 0 := by
  by_cases hedge :
      pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation corridor
          hinterior offset hnext role ∈
        pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset
  · rw [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_cell_of_mem
      formation corridor hinterior offset prefixColor
        (pointwiseSelectedSourceLocalLayerCellLiteralColorAt formation corridor
          hinterior offset cellColoring) hedge]
    exact pointwiseSelectedSourceLocalLayerCellLiteralColorAt_ne_zero_of_mem
      formation corridor hinterior offset cellColoring hedge
  · simp only [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt,
      if_neg hedge]
    exact hprefix _

/-- One finite heterogeneous letter: a selected literal Cell receipt followed
by a selected boundary-rebase receipt. -/
structure PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetter where
  cell : SourceLocalLayerSerialCellFiniteSupportLetter
  rebase : SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter

noncomputable instance :
    DecidableEq PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetter :=
  Classical.decEq _

noncomputable instance :
    Fintype PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetter :=
  Fintype.ofEquiv
    (SourceLocalLayerSerialCellFiniteSupportLetter ×
      SourceLocalLayerBoundaryRebaseFiniteBoolSupportLetter)
    { toFun := fun data => ⟨data.1, data.2⟩
      invFun := fun letter => (letter.cell, letter.rebase)
      left_inv := by intro data; cases data; rfl
      right_inv := by intro letter; cases letter; rfl }

/-- Proof-facing support relation for a complete Cell--rebase letter. -/
def PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteSupports
    (letter : PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetter) :
    Prop :=
  SourceLocalLayerSerialCellFiniteSupports letter.cell ∧
    letter.rebase.input = letter.cell.output ∧
    SourceLocalLayerBoundaryRebaseFiniteSupportsBool letter.rebase = true

/-- Executable reflection of complete Cell--rebase support. -/
noncomputable def PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteSupportsBool
    (letter : PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetter) :
    Bool := by
  classical
  exact decide
    (PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteSupports letter)

theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteSupportsBool_eq_true_iff
    (letter : PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetter) :
    PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteSupportsBool letter =
        true ↔
      PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteSupports letter := by
  simp [PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteSupportsBool]

/-- The finite rooted profile transition exposed by one supported combined
letter.  Both endpoints are terminal-aware profiles. -/
def PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetter.Transition
    (letter : PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetter)
    (source target : BoundedCorridorCutProfile 2 1 4) : Prop :=
  PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteSupports letter ∧
    letter.cell.input = source ∧
    letter.rebase.output = target

/-- Existential finite transition relation over the complete finite alphabet. -/
def PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteTransition
    (source target : BoundedCorridorCutProfile 2 1 4) : Prop :=
  ∃ letter : PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetter,
    letter.Transition source target

/-- Canonical combined finite letter extracted from an arbitrary positive
cumulative prefix and one positive literal selected Cell. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : PointwiseSelectedPositiveColorFunction G.edgeSet)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset) :
    PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetter := by
  let cell :=
    pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt web
      corridor hinterior offset hcell prefixColor.1 (fun step =>
        prefixColor.2
          (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
            corridor hinterior offset step)) cellColoring
  let cellColor := pointwiseSelectedSourceLocalLayerCellLiteralColorAt
    web.toFormation corridor hinterior offset cellColoring
  let spliced := pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
    web.toFormation corridor hinterior offset prefixColor.1 cellColor
  let hrole : ∀ role,
      spliced (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt
        web.toFormation corridor hinterior offset hnext role) ≠ 0 :=
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      web.toFormation corridor hinterior offset hnext prefixColor.1
        prefixColor.2 cellColoring
  exact {
    cell := cell
    rebase :=
      pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedSupportLetterForColorAt
        web.toFormation corridor hinterior offset hnext cell.output spliced
          hrole }

/-- The two extracted finite factors meet at literal record equality. -/
@[simp]
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt_sharedEndpoint
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : PointwiseSelectedPositiveColorFunction G.edgeSet)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset) :
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt web
      corridor hinterior offset hnext hcell prefixColor cellColoring).rebase.input =
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt web
        corridor hinterior offset hnext hcell prefixColor cellColoring).cell.output := by
  simp only [pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt,
    pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedSupportLetterForColorAt]

/-- Soundness of extraction: every compatible positive source witness produces
a supported finite Cell--rebase letter. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt_supports
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : PointwiseSelectedPositiveColorFunction G.edgeSet)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        web.toFormation corridor hinterior offset prefixColor.1
        (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
          corridor hinterior offset cellColoring)) :
    PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteSupports
      (pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt web
        corridor hinterior offset hnext hcell prefixColor cellColoring) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt_supports
        web corridor hinterior offset hcell prefixColor.1 (fun step =>
          prefixColor.2
            (pointwiseSelectedSourceLocalLayerLeftCrossingAt web.toFormation
              corridor hinterior offset step)) cellColoring hcompatible
  · exact
      pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt_sharedEndpoint
        web corridor hinterior offset hnext hcell prefixColor cellColoring
  · exact
      pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedSupportLetterForColorAt_supports
        web.toFormation corridor hinterior offset hnext _ _ _

/-- Every compatible positive source witness executes from its exact
terminal-aware input profile to its exact selected successor profile. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt_transition
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      web.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt web.toFormation
      corridor hinterior offset).card ≤ 6)
    (prefixColor : PointwiseSelectedPositiveColorFunction G.edgeSet)
    (cellColoring :
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt
        web.toFormation corridor hinterior offset)
    (hcompatible :
      PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
        web.toFormation corridor hinterior offset prefixColor.1
        (pointwiseSelectedSourceLocalLayerCellLiteralColorAt web.toFormation
          corridor hinterior offset cellColoring)) :
    let letter := pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt
      web corridor hinterior offset hnext hcell prefixColor cellColoring
    letter.Transition letter.cell.input letter.rebase.output := by
  dsimp only
  exact ⟨
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt_supports web
      corridor hinterior offset hnext hcell prefixColor cellColoring hcompatible,
    rfl, rfl⟩

end

end GoertzelV24ClosedWebPointwiseSelectedCellRebaseFiniteTransition

end Mettapedia.GraphTheory.FourColor
