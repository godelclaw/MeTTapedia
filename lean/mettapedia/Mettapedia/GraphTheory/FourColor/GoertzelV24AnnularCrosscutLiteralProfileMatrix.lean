import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLiteralBoundaryCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorTransferMatrix

/-!
# Literal full-profile `Count` matrix for source crosscuts

The compositional source assigns an open corridor piece a nonnegative matrix:
its `(q, q')` entry counts the open Tait colorings restricting to the selected
input and output profiles.  The paired source crosscuts already construct the
two actual transverse interfaces and their common profile carrier.  This file
reads both profiles from a coloring of the literal open component and counts
their fibers.  Thus this is a generated finite `Count` object for the source
geometry, rather than a matrix over an ambient closed coloring or a catalogue.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24CorridorProfile
open GoertzelV24CorridorTransferMatrix
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OpenRegionRotation
open GoertzelV24RotationVertexCutProfile
open GoertzelV24SpliceUnification.OrderedCutSpliceData
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The finite interface-profile carrier used at each of the two aligned
source crosscuts.  Its five coordinates are the existing computed color,
connectivity, and capped-face data. -/
abbrev SourceCrosscutInterfaceProfile
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
  CorridorCutProfile pair.left.walk.length 0
    (pair.sourceCrosscutFaceFragmentCount data boundary)

/-- Read the left source interface from a literal Tait coloring of the open
component.  All profile coordinates are computed over the retained component;
only its actual left crossing-port order is selected here. -/
noncomputable def sourceCrosscutLiteralOpenLeftProfile
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring
      coloring) :
    pair.SourceCrosscutInterfaceProfile data boundary := by
  let hregion : (pair.sourceCrosscutLeftCutData data boundary).regionEdges ⊆
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component) := by
    intro edge hedge
    exact hedge
  let hports := pair.sourceCrosscutLeftCutData_portsInRegion data boundary
  exact (pair.sourceCrosscutLeftCutData data boundary).regionalProfile
    (pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring)
    (fun crossing =>
      pair.sourceCrosscutLiteralColorOnVertexSide_ne_zero data boundary
        coloring hcoloring (hregion (hports (.inl crossing))))

/-- Read the aligned right source interface from the same literal open
coloring.  The right crossing ports are reindexed by the source's proven rung
correspondence, so the result has the same finite carrier as the left one. -/
noncomputable def sourceCrosscutLiteralOpenRightProfile
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring
      coloring) :
    pair.SourceCrosscutInterfaceProfile data boundary := by
  let hregion : (pair.sourceCrosscutRightCutData data boundary).regionEdges ⊆
      vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component) := by
    intro edge hedge
    exact hedge
  let hports := pair.sourceCrosscutRightCutData_portsInRegion data boundary
  exact (pair.sourceCrosscutRightCutData data boundary).regionalProfile
    (pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring)
    (fun crossing =>
      pair.sourceCrosscutLiteralColorOnVertexSide_ne_zero data boundary
        coloring hcoloring (hregion (hports (.inl crossing))))

/-- The right boundary word in the left-hand rung coordinate used by the
source profile matrix. -/
noncomputable def sourceCrosscutLiteralOpenAlignedRightBoundaryWord
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color) :
    Fin pair.left.walk.length → Color :=
  fun step => pair.sourceCrosscutLiteralOpenRightBoundaryWord data boundary coloring
    (Fin.cast pair.length_eq step)

/-- The left full profile really reads the literal left boundary coloring at
each source port. -/
theorem sourceCrosscutLiteralOpenLeftProfile_edgeColor_eq_boundaryWord
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring
      coloring)
    (step : Fin pair.left.walk.length) :
    ((pair.sourceCrosscutLiteralOpenLeftProfile data boundary coloring hcoloring).edgeColor
      step).toColor =
      pair.sourceCrosscutLiteralOpenLeftBoundaryWord data boundary coloring step := by
  change ((pair.sourceCrosscutLiteralOpenLeftProfile data boundary coloring hcoloring).edgeColor
      step).toColor =
      pair.sourceCrosscutInsideBoundaryWord data boundary coloring (.inl step)
  calc
    ((pair.sourceCrosscutLiteralOpenLeftProfile data boundary coloring hcoloring).edgeColor
        step).toColor =
        pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          ((pair.sourceCrosscutLeftCutData data boundary).crossingEdge step) := by
      unfold sourceCrosscutLiteralOpenLeftProfile
      exact GraphCorridorCutData.regionalProfile_edgeColor_toColor _ _ _ step
    _ = pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          (pair.left.crossingEdge hunique step) := by
      rfl
    _ = pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          (data.toRotationSystem.edgeOf
            (pair.sourceCrosscutBoundaryDartAt data boundary (.inl step)).1.1) := by
      rw [pair.sourceCrosscutBoundaryDartAt_edgeOf data boundary (.inl step)]
      rfl
    _ = pair.sourceCrosscutInsideBoundaryWord data boundary coloring (.inl step) :=
      pair.sourceCrosscutLiteralColorOnVertexSide_eq_boundaryDartColor
        data boundary coloring
        (pair.sourceCrosscutBoundaryDartAt data boundary (.inl step))

/-- The aligned right full profile reads the literal right boundary coloring
in the same rung coordinate as the left profile. -/
theorem sourceCrosscutLiteralOpenRightProfile_edgeColor_eq_boundaryWord
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring
      coloring)
    (step : Fin pair.left.walk.length) :
    ((pair.sourceCrosscutLiteralOpenRightProfile data boundary coloring hcoloring).edgeColor
      step).toColor =
      pair.sourceCrosscutLiteralOpenAlignedRightBoundaryWord data boundary coloring step := by
  change ((pair.sourceCrosscutLiteralOpenRightProfile data boundary coloring hcoloring).edgeColor
      step).toColor =
      pair.sourceCrosscutInsideBoundaryWord data boundary coloring
        (.inr (Fin.cast pair.length_eq step))
  calc
    ((pair.sourceCrosscutLiteralOpenRightProfile data boundary coloring hcoloring).edgeColor
        step).toColor =
        pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          ((pair.sourceCrosscutRightCutData data boundary).crossingEdge step) := by
      unfold sourceCrosscutLiteralOpenRightProfile
      exact GraphCorridorCutData.regionalProfile_edgeColor_toColor _ _ _ step
    _ = pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          (pair.right.crossingEdge hunique (Fin.cast pair.length_eq step)) := by
      rfl
    _ = pair.sourceCrosscutLiteralColorOnVertexSide data boundary coloring
          (data.toRotationSystem.edgeOf
            (pair.sourceCrosscutBoundaryDartAt data boundary
              (.inr (Fin.cast pair.length_eq step))).1.1) := by
      rw [pair.sourceCrosscutBoundaryDartAt_edgeOf data boundary
        (.inr (Fin.cast pair.length_eq step))]
      rfl
    _ = pair.sourceCrosscutInsideBoundaryWord data boundary coloring
          (.inr (Fin.cast pair.length_eq step)) :=
      pair.sourceCrosscutLiteralColorOnVertexSide_eq_boundaryDartColor
        data boundary coloring
        (pair.sourceCrosscutBoundaryDartAt data boundary
          (.inr (Fin.cast pair.length_eq step)))

/-- Project the color coordinate of a left interface profile to its literal
source boundary word. -/
noncomputable def sourceCrosscutInterfaceProfileLeftColorWord
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
    (profile : pair.SourceCrosscutInterfaceProfile data boundary) :
    Fin pair.left.walk.length → Color :=
  fun step => (profile.edgeColor step).toColor

/-- Project the color coordinate of an aligned right interface profile back
to the literal right source-boundary order. -/
noncomputable def sourceCrosscutInterfaceProfileRightColorWord
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
    (profile : pair.SourceCrosscutInterfaceProfile data boundary) :
    Fin pair.right.walk.length → Color :=
  fun step => (profile.edgeColor (Fin.cast pair.length_eq.symm step)).toColor

/-- The color projection of the literal left profile is exactly the literal
left boundary word. -/
theorem sourceCrosscutLiteralOpenLeftProfile_colorWord_eq_boundaryWord
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring
      coloring) :
    pair.sourceCrosscutInterfaceProfileLeftColorWord data boundary
      (pair.sourceCrosscutLiteralOpenLeftProfile data boundary coloring hcoloring) =
      pair.sourceCrosscutLiteralOpenLeftBoundaryWord data boundary coloring := by
  funext step
  exact pair.sourceCrosscutLiteralOpenLeftProfile_edgeColor_eq_boundaryWord
    data boundary coloring hcoloring step

/-- The color projection of the literal aligned right profile is exactly the
literal right boundary word. -/
theorem sourceCrosscutLiteralOpenRightProfile_colorWord_eq_boundaryWord
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
    (coloring : (pair.sourceCrosscutOpenRegion data boundary).EdgeColoring Color)
    (hcoloring : (pair.sourceCrosscutOpenRegion data boundary).IsTaitEdgeColoring
      coloring) :
    pair.sourceCrosscutInterfaceProfileRightColorWord data boundary
      (pair.sourceCrosscutLiteralOpenRightProfile data boundary coloring hcoloring) =
      pair.sourceCrosscutLiteralOpenRightBoundaryWord data boundary coloring := by
  funext step
  change ((pair.sourceCrosscutLiteralOpenRightProfile data boundary
    coloring hcoloring).edgeColor (Fin.cast pair.length_eq.symm step)).toColor = _
  change ((pair.sourceCrosscutLiteralOpenRightProfile data boundary
    coloring hcoloring).edgeColor (Fin.cast pair.length_eq.symm step)).toColor =
      pair.sourceCrosscutLiteralOpenAlignedRightBoundaryWord data boundary coloring
        (Fin.cast pair.length_eq.symm step)
  exact pair.sourceCrosscutLiteralOpenRightProfile_edgeColor_eq_boundaryWord
    data boundary coloring hcoloring (Fin.cast pair.length_eq.symm step)

/-- The finite fiber of literal open Tait colorings at a selected pair of
full source-interface profiles. -/
noncomputable def sourceCrosscutLiteralOpenProfilePairFiber
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
    (left right : pair.SourceCrosscutInterfaceProfile data boundary) :
    Finset (pair.SourceCrosscutLiteralOpenTaitColoring data boundary) := by
  classical
  exact Finset.univ.filter fun coloring =>
    pair.sourceCrosscutLiteralOpenLeftProfile data boundary coloring.1 coloring.2 = left ∧
      pair.sourceCrosscutLiteralOpenRightProfile data boundary coloring.1 coloring.2 = right

/-- The source `Count` matrix of the literal crosscut component, indexed by
its two actual finite interface profiles. -/
noncomputable def sourceCrosscutLiteralOpenProfileCount
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
    TransferMatrix (pair.SourceCrosscutInterfaceProfile data boundary) :=
  fun left right =>
    (pair.sourceCrosscutLiteralOpenProfilePairFiber data boundary left right).card

@[simp]
theorem sourceCrosscutLiteralOpenProfileCount_apply
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
    (left right : pair.SourceCrosscutInterfaceProfile data boundary) :
    pair.sourceCrosscutLiteralOpenProfileCount data boundary left right =
      (pair.sourceCrosscutLiteralOpenProfilePairFiber data boundary left right).card :=
  rfl

/-- A literal coloring belongs to a full-profile `Count` fiber exactly when
it realizes the indicated input and output profiles. -/
theorem mem_sourceCrosscutLiteralOpenProfilePairFiber_iff
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
    (left right : pair.SourceCrosscutInterfaceProfile data boundary)
    (coloring : pair.SourceCrosscutLiteralOpenTaitColoring data boundary) :
    coloring ∈ pair.sourceCrosscutLiteralOpenProfilePairFiber data boundary left right ↔
      pair.sourceCrosscutLiteralOpenLeftProfile data boundary coloring.1 coloring.2 = left ∧
        pair.sourceCrosscutLiteralOpenRightProfile data boundary coloring.1 coloring.2 = right := by
  classical
  simp [sourceCrosscutLiteralOpenProfilePairFiber]

/-- Every literal open Tait coloring contributes to the exact matrix entry
selected by its two computed profiles. -/
theorem sourceCrosscutLiteralOpenProfileCount_pos_of_coloring
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
    (coloring : pair.SourceCrosscutLiteralOpenTaitColoring data boundary) :
    0 < pair.sourceCrosscutLiteralOpenProfileCount data boundary
      (pair.sourceCrosscutLiteralOpenLeftProfile data boundary coloring.1 coloring.2)
      (pair.sourceCrosscutLiteralOpenRightProfile data boundary coloring.1 coloring.2) := by
  rw [pair.sourceCrosscutLiteralOpenProfileCount_apply]
  apply Finset.card_pos.mpr
  refine ⟨coloring, ?_⟩
  exact (pair.mem_sourceCrosscutLiteralOpenProfilePairFiber_iff data boundary _ _
    coloring).2 ⟨rfl, rfl⟩

/-- Positivity of a source `Count` entry is exactly the existence of a
literal open Tait coloring with the selected pair of full interface profiles.
This is the support semantics needed before the transfer/pumping arguments
can reason about zero seed counts. -/
theorem sourceCrosscutLiteralOpenProfileCount_pos_iff
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
    (left right : pair.SourceCrosscutInterfaceProfile data boundary) :
    0 < pair.sourceCrosscutLiteralOpenProfileCount data boundary left right ↔
      ∃ coloring : pair.SourceCrosscutLiteralOpenTaitColoring data boundary,
        pair.sourceCrosscutLiteralOpenLeftProfile data boundary coloring.1 coloring.2 = left ∧
          pair.sourceCrosscutLiteralOpenRightProfile data boundary coloring.1 coloring.2 = right := by
  rw [pair.sourceCrosscutLiteralOpenProfileCount_apply]
  constructor
  · intro h
    rcases Finset.card_pos.mp h with ⟨coloring, hmem⟩
    exact ⟨coloring,
      (pair.mem_sourceCrosscutLiteralOpenProfilePairFiber_iff data boundary _ _
        coloring).1 hmem⟩
  · rintro ⟨coloring, hleft, hright⟩
    apply Finset.card_pos.mpr
    refine ⟨coloring, ?_⟩
    exact (pair.mem_sourceCrosscutLiteralOpenProfilePairFiber_iff data boundary _ _
      coloring).2 ⟨hleft, hright⟩

/-- The ordinary boundary-color `Count` support is exactly the projection of
the literal full-profile matrix support.  This is the first concrete
factorization step demanded by the source: every realized color-word pair has
some computed connectivity/face refinement, and every positive full-profile
entry realizes its displayed boundary colors. -/
theorem sourceCrosscutLiteralBoundaryColorCount_pos_iff_exists_profilePair
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
    (leftWord : Fin pair.left.walk.length → Color)
    (rightWord : Fin pair.right.walk.length → Color) :
    0 < pair.sourceCrosscutLiteralOpenBoundaryColorCount data boundary leftWord rightWord ↔
      ∃ leftProfile rightProfile : pair.SourceCrosscutInterfaceProfile data boundary,
        pair.sourceCrosscutInterfaceProfileLeftColorWord data boundary leftProfile = leftWord ∧
          pair.sourceCrosscutInterfaceProfileRightColorWord data boundary rightProfile =
            rightWord ∧
          0 < pair.sourceCrosscutLiteralOpenProfileCount data boundary
            leftProfile rightProfile := by
  constructor
  · rw [pair.sourceCrosscutLiteralOpenBoundaryColorCount_apply]
    intro hpositive
    rcases Finset.card_pos.mp hpositive with ⟨coloring, hmember⟩
    rcases (pair.mem_sourceCrosscutLiteralOpenTaitColoringFiber_iff data boundary
      leftWord rightWord coloring).1 hmember with ⟨hcoloring, hleft, hright⟩
    refine ⟨pair.sourceCrosscutLiteralOpenLeftProfile data boundary coloring hcoloring,
      pair.sourceCrosscutLiteralOpenRightProfile data boundary coloring hcoloring, ?_, ?_, ?_⟩
    · calc
        pair.sourceCrosscutInterfaceProfileLeftColorWord data boundary
            (pair.sourceCrosscutLiteralOpenLeftProfile data boundary coloring hcoloring) =
            pair.sourceCrosscutLiteralOpenLeftBoundaryWord data boundary coloring :=
          pair.sourceCrosscutLiteralOpenLeftProfile_colorWord_eq_boundaryWord
            data boundary coloring hcoloring
        _ = leftWord := hleft
    · calc
        pair.sourceCrosscutInterfaceProfileRightColorWord data boundary
            (pair.sourceCrosscutLiteralOpenRightProfile data boundary coloring hcoloring) =
            pair.sourceCrosscutLiteralOpenRightBoundaryWord data boundary coloring :=
          pair.sourceCrosscutLiteralOpenRightProfile_colorWord_eq_boundaryWord
            data boundary coloring hcoloring
        _ = rightWord := hright
    · exact pair.sourceCrosscutLiteralOpenProfileCount_pos_of_coloring
        data boundary ⟨coloring, hcoloring⟩
  · rintro ⟨leftProfile, rightProfile, hleftWord, hrightWord, hpositive⟩
    rw [pair.sourceCrosscutLiteralOpenBoundaryColorCount_apply]
    rcases (pair.sourceCrosscutLiteralOpenProfileCount_pos_iff data boundary
      leftProfile rightProfile).1 hpositive with ⟨coloring, hleft, hright⟩
    apply Finset.card_pos.mpr
    refine ⟨coloring.1, ?_⟩
    apply (pair.mem_sourceCrosscutLiteralOpenTaitColoringFiber_iff data boundary
      leftWord rightWord coloring.1).2
    refine ⟨coloring.2, ?_, ?_⟩
    · calc
        pair.sourceCrosscutLiteralOpenLeftBoundaryWord data boundary coloring.1 =
            pair.sourceCrosscutInterfaceProfileLeftColorWord data boundary
              (pair.sourceCrosscutLiteralOpenLeftProfile data boundary
                coloring.1 coloring.2) :=
          (pair.sourceCrosscutLiteralOpenLeftProfile_colorWord_eq_boundaryWord
            data boundary coloring.1 coloring.2).symm
        _ = pair.sourceCrosscutInterfaceProfileLeftColorWord data boundary leftProfile := by
          rw [hleft]
        _ = leftWord := hleftWord
    · calc
        pair.sourceCrosscutLiteralOpenRightBoundaryWord data boundary coloring.1 =
            pair.sourceCrosscutInterfaceProfileRightColorWord data boundary
              (pair.sourceCrosscutLiteralOpenRightProfile data boundary
                coloring.1 coloring.2) :=
          (pair.sourceCrosscutLiteralOpenRightProfile_colorWord_eq_boundaryWord
            data boundary coloring.1 coloring.2).symm
        _ = pair.sourceCrosscutInterfaceProfileRightColorWord data boundary rightProfile := by
          rw [hright]
        _ = rightWord := hrightWord

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
