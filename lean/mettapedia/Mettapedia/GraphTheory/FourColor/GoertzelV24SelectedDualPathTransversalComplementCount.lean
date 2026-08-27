import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualPathTransversalSpliceBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutComplementProfileOfBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorProfileRestriction

/-!
# Literal Count on the complement of a selected transversal pair

A selected dual transversal records the actual primal edge crossed at every
dual step.  Consequently its open-tangle `Count` must not be routed through
the older globally-unique face-intersection carrier.  This module constructs
the same five-coordinate profile and finite colouring count directly from the
selected ordered boundary.

Only the source-facing presentation changes.  The profile payload is the
established `CorridorCutProfile`, so the graph-free Cell and rebase transition
continues to consume exactly the same finite data.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SelectedDualPathTransversal

open GoertzelV24AnnularCrosscutOpenRegionalProfile
open GoertzelV24CorridorProfile
open GoertzelV24CorridorProfileRestriction
open GoertzelV24CorridorTransferMatrix
open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24OpenRegionRotation
open GoertzelV24OpenRegionTaitInheritance
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace SeparatedAlignedSelectedDualTransversals

local instance selectedComplementCountEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The two selected transversals, in left-then-right order, enumerate the
same cut when it is viewed from the removed side. -/
noncomputable def sourceSelectedComplementPort
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair) :
    Fin pair.left.crosscut.walk.length ⊕
        Fin pair.right.crosscut.walk.length ≃
      VertexSetCrossingEdge data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ := by
  let port : Fin pair.left.crosscut.walk.length ⊕
        Fin pair.right.crosscut.walk.length →
      VertexSetCrossingEdge data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ := fun source => by
    let edge : G.edgeSet := match source with
      | .inl step => pair.left.crossingEdge step
      | .inr step => pair.right.crossingEdge step
    have hedgeCut : edge ∈ pair.primalCutEdges data := by
      cases source with
      | inl step =>
          exact Finset.mem_union_left _
            ((pair.left.mem_crossingEdges_iff _).2 ⟨step, rfl⟩)
      | inr step =>
          exact Finset.mem_union_right _
            ((pair.right.mem_crossingEdges_iff _).2 ⟨step, rfl⟩)
    have hedgeKept : edge ∈ vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component) := by
      rw [pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
        data boundary.component boundary.component_boundary]
      exact hedgeCut
    refine ⟨edge, ?_⟩
    rw [mem_vertexSetCrossingEdges_iff]
    apply (edgeCrossesVertexSet_compl data.toRotationSystem
      (pair.componentSide boundary.component) edge).2
    rw [← mem_vertexSetCrossingEdges_iff]
    exact hedgeKept
  apply Equiv.ofBijective port
  constructor
  · intro first second heq
    have hedges : (port first).1 = (port second).1 := congrArg Subtype.val heq
    cases first with
    | inl left =>
        cases second with
        | inl right =>
            have : left = right := boundary.leftInjective hedges
            simp [this]
        | inr right =>
            exfalso
            have hedges' : pair.left.crossingEdge left =
                pair.right.crossingEdge right := by
              simpa [port] using hedges
            have hleft : pair.left.crossingEdge left ∈
                pair.left.crossingEdges :=
              (pair.left.mem_crossingEdges_iff _).2 ⟨left, rfl⟩
            have hright : pair.left.crossingEdge left ∈
                pair.right.crossingEdges := by
              rw [hedges']
              exact (pair.right.mem_crossingEdges_iff _).2 ⟨right, rfl⟩
            exact (Finset.disjoint_left.1 pair.crossing_disjoint hleft hright).elim
    | inr left =>
        cases second with
        | inl right =>
            exfalso
            have hedges' : pair.right.crossingEdge left =
                pair.left.crossingEdge right := by
              simpa [port] using hedges
            have hright : pair.right.crossingEdge left ∈
                pair.right.crossingEdges :=
              (pair.right.mem_crossingEdges_iff _).2 ⟨left, rfl⟩
            have hleft : pair.right.crossingEdge left ∈
                pair.left.crossingEdges := by
              rw [hedges']
              exact (pair.left.mem_crossingEdges_iff _).2 ⟨right, rfl⟩
            exact (Finset.disjoint_left.1 pair.crossing_disjoint hleft hright).elim
        | inr right =>
            have : left = right := boundary.rightInjective hedges
            simp [this]
  · intro crossing
    have hedgeKept : crossing.1 ∈ vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component) := by
      rw [mem_vertexSetCrossingEdges_iff]
      apply (edgeCrossesVertexSet_compl data.toRotationSystem
        (pair.componentSide boundary.component) crossing.1).1
      rw [← mem_vertexSetCrossingEdges_iff]
      exact crossing.2
    have hedgeCut : crossing.1 ∈ pair.primalCutEdges data := by
      rw [← pair.vertexSetCrossingEdges_componentSide_eq_primalCutEdges
        data boundary.component boundary.component_boundary]
      exact hedgeKept
    rcases Finset.mem_union.1 hedgeCut with hleft | hright
    · rcases (pair.left.mem_crossingEdges_iff crossing.1).1 hleft with
        ⟨step, hstep⟩
      refine ⟨Sum.inl step, ?_⟩
      exact Subtype.ext hstep
    · rcases (pair.right.mem_crossingEdges_iff crossing.1).1 hright with
        ⟨step, hstep⟩
      refine ⟨Sum.inr step, ?_⟩
      exact Subtype.ext hstep

@[simp] theorem sourceSelectedComplementPort_left
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (step : Fin pair.left.crosscut.walk.length) :
    (pair.sourceSelectedComplementPort data boundary (Sum.inl step)).1 =
      pair.left.crossingEdge step :=
  rfl

@[simp] theorem sourceSelectedComplementPort_right
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (step : Fin pair.right.crosscut.walk.length) :
    (pair.sourceSelectedComplementPort data boundary (Sum.inr step)).1 =
      pair.right.crossingEdge step :=
  rfl

/-- Source order on the removed-side boundary. -/
noncomputable def sourceSelectedComplementBoundaryIndexing
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair) :
    VertexSetCrossingIndexing data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ := by
  let hcard : Fintype.card (VertexSetCrossingEdge data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ) =
      pair.left.crosscut.walk.length + pair.right.crosscut.walk.length := by
    simpa using (Fintype.card_congr
      (pair.sourceSelectedComplementPort data boundary)).symm
  exact (finCongr hcard).trans
    ((finSumFinEquiv).symm.trans
      (pair.sourceSelectedComplementPort data boundary))

/-- The graph-derived combined profile carrier of the removed Cell. -/
noncomputable def sourceSelectedComplementBoundaryProfileData
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair) :=
  vertexSetBoundaryGraphCutDataWithIndexing data.toRotationSystem
    (pair.componentSide boundary.component)ᶜ
    (pair.sourceSelectedComplementBoundaryIndexing data boundary)

theorem sourceSelectedComplementBoundaryProfileData_portsInRegion
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair) :
    (pair.sourceSelectedComplementBoundaryProfileData data boundary).PortsInRegion :=
  vertexSetBoundaryGraphCutDataWithIndexing_portsInRegion
    data.toRotationSystem (pair.componentSide boundary.component)ᶜ
      (pair.sourceSelectedComplementBoundaryIndexing data boundary)

/-- The first and second selected transversal blocks inside the combined
four-port profile. -/
noncomputable def sourceSelectedComplementLeftCombinedIndex
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair) :
    Fin pair.left.crosscut.walk.length →
      Fin (Fintype.card (VertexSetCrossingEdge data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)) :=
  fun step => (pair.sourceSelectedComplementBoundaryIndexing data boundary).symm
    (pair.sourceSelectedComplementPort data boundary (Sum.inl step))

noncomputable def sourceSelectedComplementRightCombinedIndex
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair) :
    Fin pair.left.crosscut.walk.length →
      Fin (Fintype.card (VertexSetCrossingEdge data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)) :=
  fun step => (pair.sourceSelectedComplementBoundaryIndexing data boundary).symm
    (pair.sourceSelectedComplementPort data boundary
      (Sum.inr (Fin.cast pair.length_eq step)))

@[simp] theorem sourceSelectedComplementBoundaryProfileData_crossingEdge_left
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (step : Fin pair.left.crosscut.walk.length) :
    (pair.sourceSelectedComplementBoundaryProfileData data boundary).crossingEdge
        (pair.sourceSelectedComplementLeftCombinedIndex data boundary step) =
      pair.left.crossingEdge step := by
  simp [sourceSelectedComplementBoundaryProfileData,
    sourceSelectedComplementLeftCombinedIndex,
    vertexSetBoundaryGraphCutDataWithIndexing,
    vertexSetCrossingEdgeAtWithIndexing]

@[simp] theorem sourceSelectedComplementBoundaryProfileData_crossingEdge_right
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (step : Fin pair.left.crosscut.walk.length) :
    (pair.sourceSelectedComplementBoundaryProfileData data boundary).crossingEdge
        (pair.sourceSelectedComplementRightCombinedIndex data boundary step) =
      pair.right.crossingEdge (Fin.cast pair.length_eq step) := by
  simp [sourceSelectedComplementBoundaryProfileData,
    sourceSelectedComplementRightCombinedIndex,
    vertexSetBoundaryGraphCutDataWithIndexing,
    vertexSetCrossingEdgeAtWithIndexing]

/-- Root and literal open rotation system of the selected complement. -/
noncomputable def sourceSelectedComplementRoot
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair) :
    Dart data.toRotationSystem
      (fun vertex => vertex ∉ pair.componentSide boundary.component) :=
  Sum.inl ⟨boundary.removedDart, by
    intro hkept
    apply boundary.removed_not_kept
    rw [← boundary.removedDart_vertOf]
    exact hkept⟩

noncomputable def sourceSelectedComplementOpenRegion
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair) :=
  rotationSystem data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceSelectedComplementRoot data boundary)

/-- Read an ambient edge colour from a colouring of the selected open Cell. -/
noncomputable def sourceSelectedComplementColor
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (coloring : (pair.sourceSelectedComplementOpenRegion data boundary).EdgeColoring
      Color) : G.edgeSet → Color :=
  fun edge =>
    if hedge : edge ∈ vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ then
      dartColor data.toRotationSystem
        (fun vertex => vertex ∉ pair.componentSide boundary.component)
        (pair.sourceSelectedComplementRoot data boundary) coloring
        (Sum.inl ⟨vertexSideDart data.toRotationSystem
          (pair.componentSide boundary.component)ᶜ edge hedge, by
            simpa using vertexSideDart_mem_inside data.toRotationSystem
              (pair.componentSide boundary.component)ᶜ edge hedge⟩)
    else 0

theorem sourceSelectedComplementColor_ne_zero
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (coloring : (pair.sourceSelectedComplementOpenRegion data boundary).EdgeColoring
      Color)
    (hcoloring : (pair.sourceSelectedComplementOpenRegion data boundary)
      |>.IsTaitEdgeColoring coloring)
    {edge : G.edgeSet}
    (hedge : edge ∈ vertexSetRegionEdges data.toRotationSystem
      (pair.componentSide boundary.component)ᶜ) :
    pair.sourceSelectedComplementColor data boundary coloring edge ≠ 0 := by
  rw [sourceSelectedComplementColor]
  simp only [dif_pos hedge]
  exact dartColor_ne_zero data.toRotationSystem
    (fun vertex => vertex ∉ pair.componentSide boundary.component)
    (pair.sourceSelectedComplementRoot data boundary) coloring hcoloring _

/-- Literal selected-Cell colourings and their one combined five-field
profile. -/
abbrev SourceSelectedComplementLiteralOpenTaitColoring
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair) :=
  { coloring : (pair.sourceSelectedComplementOpenRegion data boundary)
      |>.EdgeColoring Color //
    (pair.sourceSelectedComplementOpenRegion data boundary)
      |>.IsTaitEdgeColoring coloring }

noncomputable def sourceSelectedComplementLiteralOpenProfile
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (coloring : (pair.sourceSelectedComplementOpenRegion data boundary).EdgeColoring
      Color)
    (hcoloring : (pair.sourceSelectedComplementOpenRegion data boundary)
      |>.IsTaitEdgeColoring coloring) :=
  let cutData := pair.sourceSelectedComplementBoundaryProfileData data boundary
  let hports := pair.sourceSelectedComplementBoundaryProfileData_portsInRegion
    data boundary
  cutData.regionalProfile
    (pair.sourceSelectedComplementColor data boundary coloring)
    (fun crossing => pair.sourceSelectedComplementColor_ne_zero data boundary
      coloring hcoloring (hports (.inl crossing)))

abbrev SourceSelectedComplementInterfaceProfile
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair) :=
  CorridorCutProfile pair.left.crosscut.walk.length 0
    (Fintype.card (BoundaryRegionalFragment data.toRotationSystem
      (vertexSetCrossingEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)
      (vertexSetRegionEdges data.toRotationSystem
        (pair.componentSide boundary.component)ᶜ)))

noncomputable def sourceSelectedComplementLiteralOpenLeftProfile
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (coloring : (pair.sourceSelectedComplementOpenRegion data boundary).EdgeColoring
      Color)
    (hcoloring : (pair.sourceSelectedComplementOpenRegion data boundary)
      |>.IsTaitEdgeColoring coloring) :
    pair.SourceSelectedComplementInterfaceProfile data boundary :=
  CorridorCutProfile.restrictCrossings
    (pair.sourceSelectedComplementLiteralOpenProfile data boundary coloring
      hcoloring)
    (pair.sourceSelectedComplementLeftCombinedIndex data boundary)

noncomputable def sourceSelectedComplementLiteralOpenRightProfile
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (coloring : (pair.sourceSelectedComplementOpenRegion data boundary).EdgeColoring
      Color)
    (hcoloring : (pair.sourceSelectedComplementOpenRegion data boundary)
      |>.IsTaitEdgeColoring coloring) :
    pair.SourceSelectedComplementInterfaceProfile data boundary :=
  CorridorCutProfile.restrictCrossings
    (pair.sourceSelectedComplementLiteralOpenProfile data boundary coloring
      hcoloring)
    (pair.sourceSelectedComplementRightCombinedIndex data boundary)

/-- Finite fibre and exact `Count` of selected-Cell colourings. -/
noncomputable def sourceSelectedComplementLiteralOpenProfilePairFiber
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (left right : pair.SourceSelectedComplementInterfaceProfile data boundary) :
    Finset (pair.SourceSelectedComplementLiteralOpenTaitColoring data boundary) := by
  classical
  exact Finset.univ.filter fun coloring =>
    pair.sourceSelectedComplementLiteralOpenLeftProfile data boundary
        coloring.1 coloring.2 = left ∧
      pair.sourceSelectedComplementLiteralOpenRightProfile data boundary
        coloring.1 coloring.2 = right

noncomputable def sourceSelectedComplementLiteralOpenProfileCount
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair) :
    TransferMatrix (pair.SourceSelectedComplementInterfaceProfile data boundary) :=
  fun left right =>
    (pair.sourceSelectedComplementLiteralOpenProfilePairFiber data boundary
      left right).card

/-- Positivity is neither approximated nor postulated: it is exactly one
literal selected-Cell colouring realizing both restricted profiles. -/
theorem sourceSelectedComplementLiteralOpenProfileCount_pos_iff
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSelectedDualTransversals
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) start finish)
    (boundary : SourceSelectedBoundaryData data pair)
    (left right : pair.SourceSelectedComplementInterfaceProfile data boundary) :
    0 < pair.sourceSelectedComplementLiteralOpenProfileCount data boundary
        left right ↔
      ∃ coloring :
          pair.SourceSelectedComplementLiteralOpenTaitColoring data boundary,
        pair.sourceSelectedComplementLiteralOpenLeftProfile data boundary
            coloring.1 coloring.2 = left ∧
          pair.sourceSelectedComplementLiteralOpenRightProfile data boundary
            coloring.1 coloring.2 = right := by
  constructor
  · intro hpositive
    rcases Finset.card_pos.mp hpositive with ⟨coloring, hmember⟩
    exact ⟨coloring, (Finset.mem_filter.mp hmember).2⟩
  · rintro ⟨coloring, hleft, hright⟩
    apply Finset.card_pos.mpr
    exact ⟨coloring, Finset.mem_filter.mpr
      ⟨Finset.mem_univ coloring, hleft, hright⟩⟩

end SeparatedAlignedSelectedDualTransversals

end

end GoertzelV24SelectedDualPathTransversal

end Mettapedia.GraphTheory.FourColor
