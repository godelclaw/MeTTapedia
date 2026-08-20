import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutCompletedStep

/-!
# Source-crosscut completion rooted by literal boundary data

Addendum XXVII splices an annular tangle with degree-one boundary stubs.  The
ambient carrier is therefore not globally cubic.  This module computes the
removed-side full-profile diagonal directly from the complementary open region
rooted by `SourceCrosscutBoundaryData.removedDart` and derives the same reverse
completion and strict reduction interfaces without a global degree premise.

The diagonal fiber is generated from literal open Tait colorings and the full
five-coordinate profiles computed on both source interfaces.  It is not a
boundary-word-only replacement for the source transfer state.

This is a downstream consumer of the physical geometry tracked under
Lean-flag L1.  It does not construct the separated crosscuts, prove the finite
profile audit, reconstruct the packed closed-web output, or close L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24CorridorTransferMatrix
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OpenRegionColorGluing
open GoertzelV24OpenRegionRotation
open GoertzelV24OpenRegionTaitInheritance
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification
open GoertzelV24SpliceUnification.OrderedCutSpliceData
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- Read an ambient regional edge from the complementary open coloring rooted
by the literal source-boundary dart. -/
noncomputable def sourceCrosscutBoundaryRootedLiteralColorOnVertexSide
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
        Color) :
    G.edgeSet → Color :=
  fun edge =>
    if hedge : edge ∈ vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ then
      dartColor data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component)
        (pair.sourceCrosscutComplementRootOfBoundary data boundary) coloring
        (Sum.inl ⟨vertexSideDart data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ edge hedge, by
            simpa using vertexSideDart_mem_inside data.toRotationSystem
              (pair.componentSide boundary.component)ᶜ edge hedge⟩)
    else 0

/-- Every regional edge receives a nonzero color from a complementary literal
open Tait coloring. -/
theorem sourceCrosscutBoundaryRootedLiteralColorOnVertexSide_ne_zero
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
        Color)
    (hcoloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).IsTaitEdgeColoring
        coloring)
    {edge : G.edgeSet}
    (hedge : edge ∈ vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ) :
    pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide data boundary
      coloring edge ≠ 0 := by
  rw [sourceCrosscutBoundaryRootedLiteralColorOnVertexSide]
  simp only [dif_pos hedge]
  exact dartColor_ne_zero data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceCrosscutComplementRootOfBoundary data boundary)
    coloring hcoloring _

/-- The full left source-interface profile computed from a complementary
literal open Tait coloring. -/
noncomputable def sourceCrosscutBoundaryRootedLiteralOpenLeftProfile
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
        Color)
    (hcoloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).IsTaitEdgeColoring
        coloring) :
    pair.SourceCrosscutComplementInterfaceProfile data boundary := by
  let hregion : (pair.sourceCrosscutComplementLeftCutData data boundary).regionEdges ⊆
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ := by
    intro edge hedge
    exact hedge
  let hports := pair.sourceCrosscutComplementLeftCutData_portsInRegion data boundary
  exact (pair.sourceCrosscutComplementLeftCutData data boundary).regionalProfile
    (pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide
      data boundary coloring)
    (fun crossing =>
      pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide_ne_zero
        data boundary coloring hcoloring (hregion (hports (.inl crossing))))

/-- The aligned right source-interface profile computed from the same
complementary literal open Tait coloring. -/
noncomputable def sourceCrosscutBoundaryRootedLiteralOpenRightProfile
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
        Color)
    (hcoloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).IsTaitEdgeColoring
        coloring) :
    pair.SourceCrosscutComplementInterfaceProfile data boundary := by
  let hregion : (pair.sourceCrosscutComplementRightCutData data boundary).regionEdges ⊆
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ := by
    intro edge hedge
    exact hedge
  let hports := pair.sourceCrosscutComplementRightCutData_portsInRegion data boundary
  exact (pair.sourceCrosscutComplementRightCutData data boundary).regionalProfile
    (pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide
      data boundary coloring)
    (fun crossing =>
      pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide_ne_zero
        data boundary coloring hcoloring (hregion (hports (.inl crossing))))

/-- Literal complementary Tait colorings on the source-boundary-rooted open
region. -/
abbrev SourceCrosscutBoundaryRootedLiteralOpenTaitColoring
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :=
  { coloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
        Color //
    (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).IsTaitEdgeColoring
      coloring }

/-- The generated finite fiber at one pair of complete removed-side profiles. -/
noncomputable def sourceCrosscutBoundaryRootedProfilePairFiber
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    Finset (pair.SourceCrosscutBoundaryRootedLiteralOpenTaitColoring data boundary) := by
  classical
  exact Finset.univ.filter fun coloring =>
    pair.sourceCrosscutBoundaryRootedLiteralOpenLeftProfile data boundary
        coloring.1 coloring.2 = left ∧
      pair.sourceCrosscutBoundaryRootedLiteralOpenRightProfile data boundary
        coloring.1 coloring.2 = right

/-- The generated removed-side full-profile `Count` matrix rooted by the
source boundary datum. -/
noncomputable def sourceCrosscutBoundaryRootedProfileCount
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    TransferMatrix (pair.SourceCrosscutComplementInterfaceProfile data boundary) :=
  fun left right =>
    (pair.sourceCrosscutBoundaryRootedProfilePairFiber
      data boundary left right).card

@[simp]
theorem sourceCrosscutBoundaryRootedProfileCount_apply
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    pair.sourceCrosscutBoundaryRootedProfileCount data boundary left right =
      (pair.sourceCrosscutBoundaryRootedProfilePairFiber
        data boundary left right).card :=
  rfl

theorem mem_sourceCrosscutBoundaryRootedProfilePairFiber_iff
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary)
    (coloring : pair.SourceCrosscutBoundaryRootedLiteralOpenTaitColoring
      data boundary) :
    coloring ∈ pair.sourceCrosscutBoundaryRootedProfilePairFiber
        data boundary left right ↔
      pair.sourceCrosscutBoundaryRootedLiteralOpenLeftProfile data boundary
          coloring.1 coloring.2 = left ∧
        pair.sourceCrosscutBoundaryRootedLiteralOpenRightProfile data boundary
          coloring.1 coloring.2 = right := by
  classical
  simp [sourceCrosscutBoundaryRootedProfilePairFiber]

/-- Positivity of a generated profile entry is exactly existence of a literal
complementary Tait coloring realizing both profiles. -/
theorem sourceCrosscutBoundaryRootedProfileCount_pos_iff
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (left right : pair.SourceCrosscutComplementInterfaceProfile data boundary) :
    0 < pair.sourceCrosscutBoundaryRootedProfileCount data boundary left right ↔
      ∃ coloring : pair.SourceCrosscutBoundaryRootedLiteralOpenTaitColoring
          data boundary,
        pair.sourceCrosscutBoundaryRootedLiteralOpenLeftProfile data boundary
            coloring.1 coloring.2 = left ∧
          pair.sourceCrosscutBoundaryRootedLiteralOpenRightProfile data boundary
            coloring.1 coloring.2 = right := by
  rw [pair.sourceCrosscutBoundaryRootedProfileCount_apply]
  constructor
  · intro hpositive
    obtain ⟨coloring, hmember⟩ := Finset.card_pos.mp hpositive
    exact ⟨coloring,
      (pair.mem_sourceCrosscutBoundaryRootedProfilePairFiber_iff
        data boundary left right coloring).1 hmember⟩
  · rintro ⟨coloring, hleft, hright⟩
    apply Finset.card_pos.mpr
    exact ⟨coloring,
      (pair.mem_sourceCrosscutBoundaryRootedProfilePairFiber_iff
        data boundary left right coloring).2 ⟨hleft, hright⟩⟩

/-- The source-boundary-rooted profile reader chooses the opposite dart on a
literal crossing edge, exactly as the complementary boundary word does. -/
theorem sourceCrosscutBoundaryRootedLiteralColorOnVertexSide_eq_boundaryWord
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
        Color)
    (index : pair.SourceCrosscutBoundaryIndex) :
    pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide data boundary
        coloring
        (data.toRotationSystem.edgeOf
          (pair.sourceCrosscutBoundaryDartAt data boundary index).1.1) =
      pair.sourceCrosscutOutsideBoundaryWordOfBoundary data boundary coloring index := by
  let inside := pair.componentSide boundary.component
  let outside := insideᶜ
  let exposed := pair.sourceCrosscutBoundaryDartAt data boundary index
  let edge := data.toRotationSystem.edgeOf exposed.1.1
  have hcrossing : edge ∈ vertexSetCrossingEdges data.toRotationSystem outside := by
    rw [mem_vertexSetCrossingEdges_iff]
    apply (edgeCrossesVertexSet_compl data.toRotationSystem inside edge).2
    rw [← mem_vertexSetCrossingEdges_iff]
    dsimp [edge, exposed, inside]
    exact boundaryDart_edge_mem_vertexSetCrossingEdges data.toRotationSystem
      (pair.componentSide boundary.component)
      (pair.sourceCrosscutBoundaryDartAt data boundary index)
  have hregion : edge ∈ vertexSetRegionEdges data.toRotationSystem outside :=
    vertexSetCrossingEdges_subset_regionEdges data.toRotationSystem outside hcrossing
  rw [sourceCrosscutBoundaryRootedLiteralColorOnVertexSide, dif_pos hregion]
  change dartColor data.toRotationSystem
        (fun vertex => vertex ∉ inside)
        (pair.sourceCrosscutComplementRootOfBoundary data boundary) coloring
        (Sum.inl ⟨vertexSideDart data.toRotationSystem outside edge hregion, by
          simpa [outside] using
            vertexSideDart_mem_inside data.toRotationSystem outside edge hregion⟩) =
      openOldDartColor data.toRotationSystem
        (fun vertex => vertex ∉ inside)
        (pair.sourceCrosscutComplementRootOfBoundary data boundary) coloring
        (data.toRotationSystem.alpha exposed.1.1) exposed.2
  have hsideEdge :
      data.toRotationSystem.edgeOf
        (vertexSideDart data.toRotationSystem outside edge hregion) = edge :=
    vertexSideDart_edgeOf data.toRotationSystem outside edge hregion
  rcases data.toRotationSystem.edge_fiber_two_cases
      (d := vertexSideDart data.toRotationSystem outside edge hregion)
      (y := data.toRotationSystem.alpha exposed.1.1) hsideEdge (by
        simp [edge]) with hsame | hopposite
  · unfold dartColor openOldDartColor
    congr 3
    apply Subtype.ext
    exact hsame.symm
  · exfalso
    have hins : data.toRotationSystem.vertOf exposed.1.1 ∈ inside := by
      change data.toRotationSystem.vertOf
        (pair.sourceCrosscutBoundaryDartAt data boundary index).1.1 ∈
        pair.componentSide boundary.component
      exact (pair.sourceCrosscutBoundaryDartAt data boundary index).1.2
    have hnotOutside : data.toRotationSystem.vertOf exposed.1.1 ∉ outside := by
      simpa [outside] using hins
    apply hnotOutside
    have hsame : exposed.1.1 =
        vertexSideDart data.toRotationSystem outside edge hregion := by
      have halpha := congrArg data.toRotationSystem.alpha hopposite
      simpa only [data.toRotationSystem.alpha_involutive] using halpha
    rw [hsame]
    exact vertexSideDart_mem_inside data.toRotationSystem outside edge hregion

/-- The full left profile's color coordinate is the literal complementary
left boundary word. -/
theorem sourceCrosscutBoundaryRootedLeftProfile_colorWord_eq_boundaryWord
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
        Color)
    (hcoloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).IsTaitEdgeColoring
        coloring) :
    pair.sourceCrosscutComplementInterfaceProfileLeftColorWord data boundary
        (pair.sourceCrosscutBoundaryRootedLiteralOpenLeftProfile data boundary
          coloring hcoloring) =
      fun step => pair.sourceCrosscutOutsideBoundaryWordOfBoundary
        data boundary coloring (.inl step) := by
  funext step
  change ((pair.sourceCrosscutBoundaryRootedLiteralOpenLeftProfile data boundary
      coloring hcoloring).edgeColor step).toColor = _
  calc
    ((pair.sourceCrosscutBoundaryRootedLiteralOpenLeftProfile data boundary
        coloring hcoloring).edgeColor step).toColor =
        pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide data boundary coloring
          ((pair.sourceCrosscutComplementLeftCutData data boundary).crossingEdge step) := by
      unfold sourceCrosscutBoundaryRootedLiteralOpenLeftProfile
      exact GraphCorridorCutData.regionalProfile_edgeColor_toColor _ _ _ step
    _ = pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide data boundary coloring
          (pair.left.crossingEdge hunique step) := by rfl
    _ = pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide data boundary coloring
          (data.toRotationSystem.edgeOf
            (pair.sourceCrosscutBoundaryDartAt data boundary (.inl step)).1.1) := by
      rw [pair.sourceCrosscutBoundaryDartAt_edgeOf data boundary (.inl step)]
      rfl
    _ = pair.sourceCrosscutOutsideBoundaryWordOfBoundary data boundary coloring
          (.inl step) :=
      pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide_eq_boundaryWord
        data boundary coloring (.inl step)

/-- The full aligned right profile's color coordinate is the literal
complementary right boundary word. -/
theorem sourceCrosscutBoundaryRootedRightProfile_colorWord_eq_boundaryWord
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (coloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).EdgeColoring
        Color)
    (hcoloring :
      (pair.sourceCrosscutComplementOpenRegionOfBoundary data boundary).IsTaitEdgeColoring
        coloring) :
    pair.sourceCrosscutComplementInterfaceProfileRightColorWord data boundary
        (pair.sourceCrosscutBoundaryRootedLiteralOpenRightProfile data boundary
          coloring hcoloring) =
      fun step => pair.sourceCrosscutOutsideBoundaryWordOfBoundary
        data boundary coloring (.inr step) := by
  funext rightStep
  let step : Fin pair.left.walk.length := Fin.cast pair.length_eq.symm rightStep
  have hcast : Fin.cast pair.length_eq step = rightStep := by
    apply Fin.ext
    rfl
  change ((pair.sourceCrosscutBoundaryRootedLiteralOpenRightProfile data boundary
      coloring hcoloring).edgeColor step).toColor = _
  calc
    ((pair.sourceCrosscutBoundaryRootedLiteralOpenRightProfile data boundary
        coloring hcoloring).edgeColor step).toColor =
        pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide data boundary coloring
          ((pair.sourceCrosscutComplementRightCutData data boundary).crossingEdge step) := by
      unfold sourceCrosscutBoundaryRootedLiteralOpenRightProfile
      exact GraphCorridorCutData.regionalProfile_edgeColor_toColor _ _ _ step
    _ = pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide data boundary coloring
          (pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)) := by rfl
    _ = pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide data boundary coloring
          (pair.right.crossingEdge hunique rightStep) := by rw [hcast]
    _ = pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide data boundary coloring
          (data.toRotationSystem.edgeOf
            (pair.sourceCrosscutBoundaryDartAt data boundary (.inr rightStep)).1.1) := by
      rw [pair.sourceCrosscutBoundaryDartAt_edgeOf data boundary (.inr rightStep)]
      rfl
    _ = pair.sourceCrosscutOutsideBoundaryWordOfBoundary data boundary coloring
          (.inr rightStep) :=
      pair.sourceCrosscutBoundaryRootedLiteralColorOnVertexSide_eq_boundaryWord
        data boundary coloring (.inr rightStep)

/-- The source-facing one-way full-profile diagonal obligation.  Every seam
word realized by the shortened piece is the color projection of a positive
diagonal entry in the literal complementary five-coordinate profile matrix. -/
def SourceCrosscutBoundaryRootedProfileDiagonalLift
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) : Prop :=
  ∀ word : Fin pair.left.walk.length → Color,
    0 < pair.sourceCrosscutLiteralOpenSeamColorCount data boundary word →
      ∃ profile : pair.SourceCrosscutComplementInterfaceProfile data boundary,
        pair.sourceCrosscutComplementInterfaceProfileLeftColorWord
            data boundary profile = word ∧
          0 < pair.sourceCrosscutBoundaryRootedProfileCount
            data boundary profile profile

/-- A source-boundary-rooted full-profile diagonal lift constructs the exact
reverse completion required by the splice. -/
theorem sourceCrosscutReverseCompletion_ofBoundaryRootedProfileDiagonalLift
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (hlift : pair.SourceCrosscutBoundaryRootedProfileDiagonalLift data boundary) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).ReverseCompletion := by
  intro output houtput
  let word := seamColorWord
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints) output
  have hinsideCount :
      0 < pair.sourceCrosscutLiteralOpenSeamColorCount data boundary word := by
    simpa [word, sourceCrosscutLiteralOpenSeamColorCount] using
      (pair.sourceCrosscutSpliceOutput_literalBoundaryColorCount_pos
        data boundary seamEndpoints output houtput)
  rcases hlift word hinsideCount with ⟨profile, hprofileWord, hprofileCount⟩
  rcases (pair.sourceCrosscutBoundaryRootedProfileCount_pos_iff
      data boundary profile profile).1 hprofileCount with
    ⟨outside, hleftProfile, hrightProfile⟩
  apply pair.exists_sourceCrosscutAmbientTaitColoring_of_openColorings_of_words_eqOfBoundary
    data boundary
    (pair.sourceCrosscutSpliceOutputOpenColoring data boundary seamEndpoints output)
    outside.1
    (pair.sourceCrosscutSpliceOutputOpenColoring_isTait
      data boundary seamEndpoints output houtput)
    outside.2
  funext index
  rcases index with leftStep | rightStep
  · calc
      pair.sourceCrosscutInsideBoundaryWord data boundary
          (pair.sourceCrosscutSpliceOutputOpenColoring
            data boundary seamEndpoints output) (.inl leftStep) =
          word leftStep := by
        exact pair.sourceCrosscutOutputInsideBoundaryWord_left_eq_seamColorWord
          data boundary seamEndpoints output leftStep
      _ = pair.sourceCrosscutComplementInterfaceProfileLeftColorWord
          data boundary profile leftStep := (congrFun hprofileWord leftStep).symm
      _ = pair.sourceCrosscutComplementInterfaceProfileLeftColorWord data boundary
          (pair.sourceCrosscutBoundaryRootedLiteralOpenLeftProfile
            data boundary outside.1 outside.2) leftStep := by rw [hleftProfile]
      _ = pair.sourceCrosscutOutsideBoundaryWordOfBoundary
          data boundary outside.1 (.inl leftStep) :=
        congrFun (pair.sourceCrosscutBoundaryRootedLeftProfile_colorWord_eq_boundaryWord
          data boundary outside.1 outside.2) leftStep
  · let leftStep : Fin pair.left.walk.length := Fin.cast pair.length_eq.symm rightStep
    have hcast : Fin.cast pair.length_eq leftStep = rightStep := by
      apply Fin.ext
      rfl
    calc
      pair.sourceCrosscutInsideBoundaryWord data boundary
          (pair.sourceCrosscutSpliceOutputOpenColoring
            data boundary seamEndpoints output) (.inr rightStep) =
          pair.sourceCrosscutInsideBoundaryWord data boundary
            (pair.sourceCrosscutSpliceOutputOpenColoring
              data boundary seamEndpoints output)
            (.inr (Fin.cast pair.length_eq leftStep)) := by rw [hcast]
      _ = word leftStep := by
        exact pair.sourceCrosscutOutputInsideBoundaryWord_right_eq_seamColorWord
          data boundary seamEndpoints output leftStep
      _ = pair.sourceCrosscutComplementInterfaceProfileLeftColorWord
          data boundary profile leftStep := (congrFun hprofileWord leftStep).symm
      _ = pair.sourceCrosscutComplementInterfaceProfileRightColorWord
          data boundary profile rightStep := by
        rw [pair.sourceCrosscutComplementInterfaceProfileRightColorWord_eq_cast_left]
      _ = pair.sourceCrosscutComplementInterfaceProfileRightColorWord data boundary
          (pair.sourceCrosscutBoundaryRootedLiteralOpenRightProfile
            data boundary outside.1 outside.2) rightStep := by rw [hrightProfile]
      _ = pair.sourceCrosscutOutsideBoundaryWordOfBoundary
          data boundary outside.1 (.inr rightStep) :=
        congrFun (pair.sourceCrosscutBoundaryRootedRightProfile_colorWord_eq_boundaryWord
          data boundary outside.1 outside.2) rightStep

/-- The finite set of seam words supported by positive diagonal entries in
the source-boundary-rooted complementary full-profile matrix. -/
noncomputable def sourceCrosscutBoundaryRootedSeamProfileWords
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) :
    Finset (Fin pair.left.walk.length → Color) := by
  classical
  exact Finset.univ.filter fun word =>
    ∃ profile : pair.SourceCrosscutComplementInterfaceProfile data boundary,
      pair.sourceCrosscutComplementInterfaceProfileLeftColorWord
          data boundary profile = word ∧
        0 < pair.sourceCrosscutBoundaryRootedProfileCount
          data boundary profile profile

@[simp]
theorem mem_sourceCrosscutBoundaryRootedSeamProfileWords_iff
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (word : Fin pair.left.walk.length → Color) :
    word ∈ pair.sourceCrosscutBoundaryRootedSeamProfileWords data boundary ↔
      ∃ profile : pair.SourceCrosscutComplementInterfaceProfile data boundary,
        pair.sourceCrosscutComplementInterfaceProfileLeftColorWord
            data boundary profile = word ∧
          0 < pair.sourceCrosscutBoundaryRootedProfileCount
            data boundary profile profile := by
  classical
  simp [sourceCrosscutBoundaryRootedSeamProfileWords]

/-- The finite source-facing audit: the retained and complementary literal
full-profile diagonals support exactly the same seam words. -/
def SourceCrosscutBoundaryRootedFiniteSeamProfileAuditAgreement
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair) : Prop :=
  pair.sourceCrosscutLiteralOpenSeamProfileWords data boundary =
    pair.sourceCrosscutBoundaryRootedSeamProfileWords data boundary

theorem sourceCrosscutBoundaryRootedProfileDiagonalLift_ofFiniteAudit
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (haudit : pair.SourceCrosscutBoundaryRootedFiniteSeamProfileAuditAgreement
      data boundary) :
    pair.SourceCrosscutBoundaryRootedProfileDiagonalLift data boundary := by
  intro word hword
  have hretained :
      word ∈ pair.sourceCrosscutLiteralOpenSeamProfileWords data boundary :=
    (pair.mem_sourceCrosscutLiteralOpenSeamProfileWords_iff
      data boundary word).2 hword
  have hcomplement :
      word ∈ pair.sourceCrosscutBoundaryRootedSeamProfileWords data boundary := by
    rw [← haudit]
    exact hretained
  exact (pair.mem_sourceCrosscutBoundaryRootedSeamProfileWords_iff
    data boundary word).1 hcomplement

/-- A passed generated full-profile audit supplies a completed source splice
on the actual noncubic annular carrier. -/
noncomputable def sourceCrosscutCompletedStep_ofBoundaryRootedFiniteAudit
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (haudit : pair.SourceCrosscutBoundaryRootedFiniteSeamProfileAuditAgreement
      data boundary) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).CompletedStep :=
  OrderedCutSpliceData.CompletedStep.ofReverseCompletion
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
    (pair.sourceCrosscutReverseCompletion_ofBoundaryRootedProfileDiagonalLift
      data boundary seamEndpoints
      (pair.sourceCrosscutBoundaryRootedProfileDiagonalLift_ofFiniteAudit
        data boundary haudit))

/-- The source-boundary-rooted completed step preserves counterexamples. -/
theorem sourceCrosscutCompletedStep_counterexample_preserved_ofBoundaryRootedFiniteAudit
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (haudit : pair.SourceCrosscutBoundaryRootedFiniteSeamProfileAuditAgreement
      data boundary)
    (hbad : ¬ TaitColorable (RS := data.toRotationSystem)) :
    ¬ TaitColorable
      (pair.sourceCrosscutSpliceData data boundary seamEndpoints).output :=
  completedStep_counterexample_preserved
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
    (pair.sourceCrosscutCompletedStep_ofBoundaryRootedFiniteAudit
      data boundary seamEndpoints haudit) hbad

/-- The same completed source-facing step has the already proved strict size
decrease. -/
theorem sourceCrosscutCompletedStep_outputSize_lt_ofBoundaryRootedFiniteAudit
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (boundary : SourceCrosscutBoundaryData data pair)
    (seamEndpoints : ∀ step,
      data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (pair.left.crossingEdge hunique) boundary.leftCrosses step).1.1.1 ≠
        data.toRotationSystem.vertOf
          (orderedBoundaryDart data.toRotationSystem
            (fun vertex => vertex ∈ pair.componentSide boundary.component)
            (fun index => pair.right.crossingEdge hunique
              (Fin.cast pair.length_eq index))
            (fun index => boundary.rightCrosses
              (Fin.cast pair.length_eq index)) step).1.1.1)
    (haudit : pair.SourceCrosscutBoundaryRootedFiniteSeamProfileAuditAgreement
      data boundary) :
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints).outputSize <
      Fintype.card V :=
  completedStep_strict_size
    (pair.sourceCrosscutSpliceData data boundary seamEndpoints)
    (pair.sourceCrosscutCompletedStep_ofBoundaryRootedFiniteAudit
      data boundary seamEndpoints haudit)

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
