import Mettapedia.GraphTheory.FourColor.GoertzelV24FourEdgeCutComplementCoordinates

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FourEdgeCutGluing

open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FourDefectBoundary
open GoertzelV24FourEdgeCutBoundaryData
open GoertzelV24FourEdgeCutClosureColor
open GoertzelV24FourEdgeCutComplementCoordinates
open GoertzelV24FourEdgeCutNoncrossingInterfaces
open GoertzelV24FourEdgeCutRetainedBridge
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24ThreeEdgeCutMinimality
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- An ambient dart whose endpoints both survive on the retained side
determines an edge of the retained induced graph. -/
def retainedInternalEdge
    (cut : SmallCyclicEdgeCut G) (dart : G.Dart)
    (hfst : ¬ cut.side dart.fst) (hsnd : ¬ cut.side dart.snd) :
    (retainedCutGraph G cut).edgeSet :=
  ⟨s(⟨dart.fst, hfst⟩, ⟨dart.snd, hsnd⟩), dart.adj⟩

@[simp]
theorem retainedInternalEdge_symm
    (cut : SmallCyclicEdgeCut G) (dart : G.Dart)
    (hfst : ¬ cut.side dart.fst) (hsnd : ¬ cut.side dart.snd) :
    retainedInternalEdge cut dart.symm hsnd hfst =
      retainedInternalEdge cut dart hfst hsnd := by
  apply Subtype.ext
  exact Sym2.eq_swap

@[simp]
theorem retainedCutEdgeToAmbientEdge_retainedInternalEdge
    (cut : SmallCyclicEdgeCut G) (dart : G.Dart)
    (hfst : ¬ cut.side dart.fst) (hsnd : ¬ cut.side dart.snd) :
    retainedCutEdgeToAmbientEdge cut
        (retainedInternalEdge cut dart hfst hsnd) =
      (⟨dart.edge, dart.edge_mem⟩ : G.edgeSet) := by
  apply Subtype.ext
  rfl

theorem retainedInternalEdge_mem_incidentEdgeFinset_fst
    (cut : SmallCyclicEdgeCut G) (dart : G.Dart)
    (hfst : ¬ cut.side dart.fst) (hsnd : ¬ cut.side dart.snd) :
    retainedInternalEdge cut dart hfst hsnd ∈
      incidentEdgeFinset (retainedCutGraph G cut) ⟨dart.fst, hfst⟩ := by
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact Sym2.mem_iff.mpr (Or.inl rfl)

/-- In a simple graph, an oriented edge is determined by its underlying
edge together with its initial vertex. -/
theorem dart_eq_of_fst_eq_of_edge_eq
    (first second : G.Dart) (hfst : first.fst = second.fst)
    (hedge : first.edge = second.edge) : first = second := by
  rcases (SimpleGraph.dart_edge_eq_iff first second).1 hedge with
    hsame | hopposite
  · exact hsame
  · exfalso
    apply second.snd_ne_fst
    calc
      second.snd = second.symm.fst := rfl
      _ = first.fst := congrArg (fun dart : G.Dart ↦ dart.fst) hopposite.symm
      _ = second.fst := hfst

theorem retainedInternalEdge_ne_of_dart_ne_of_fst_eq
    (cut : SmallCyclicEdgeCut G) (first second : G.Dart)
    (hfirstFst : ¬ cut.side first.fst)
    (hfirstSnd : ¬ cut.side first.snd)
    (hsecondFst : ¬ cut.side second.fst)
    (hsecondSnd : ¬ cut.side second.snd)
    (hfst : first.fst = second.fst) (hne : first ≠ second) :
    retainedInternalEdge cut first hfirstFst hfirstSnd ≠
      retainedInternalEdge cut second hsecondFst hsecondSnd := by
  intro hedges
  apply hne
  apply dart_eq_of_fst_eq_of_edge_eq first second hfst
  have hambient := congrArg (retainedCutEdgeToAmbientEdge cut) hedges
  exact congrArg Subtype.val hambient

theorem retainedInternalEdges_lineGraph_adj_of_fst_eq_of_ne
    (cut : SmallCyclicEdgeCut G) (first second : G.Dart)
    (hfirstFst : ¬ cut.side first.fst)
    (hfirstSnd : ¬ cut.side first.snd)
    (hsecondFst : ¬ cut.side second.fst)
    (hsecondSnd : ¬ cut.side second.snd)
    (hfst : first.fst = second.fst) (hne : first ≠ second) :
    (retainedCutGraph G cut).lineGraph.Adj
      (retainedInternalEdge cut first hfirstFst hfirstSnd)
      (retainedInternalEdge cut second hsecondFst hsecondSnd) := by
  apply SimpleGraph.lineGraph_adj_iff_exists.2
  refine ⟨retainedInternalEdge_ne_of_dart_ne_of_fst_eq
    cut first second hfirstFst hfirstSnd hsecondFst hsecondSnd hfst hne,
    ⟨first.fst, hfirstFst⟩, ?_, ?_⟩
  · exact Sym2.mem_iff.mpr (Or.inl rfl)
  · exact Sym2.mem_iff.mpr (Or.inl (Subtype.ext hfst))

/-- A dart directed from the retained side into the selected side is an
actual boundary dart in the common cyclic boundary carrier. -/
def retainedBoundaryDart
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (dart : G.Dart) (hfst : ¬ cut.side dart.fst)
    (hsnd : cut.side dart.snd) :
    BoundaryDart graphData.toRotationSystem
      (deletedRegionKeep (cyclicCutVertexSide cut)) :=
  ⟨⟨dart, by
      simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff] using hfst⟩,
    by
      simpa [deletedRegionKeep, mem_cyclicCutVertexSide_iff] using hsnd⟩

/-- The unique common cyclic coordinate of a retained-to-selected
crossing dart. -/
def retainedBoundaryPort
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (dart : G.Dart) (hfst : ¬ cut.side dart.fst)
    (hsnd : cut.side dart.snd) : Fin 4 :=
  cyclicData.boundaryOrder.symm
    (retainedBoundaryDart graphData cut dart hfst hsnd)

@[simp]
theorem boundaryOrder_retainedBoundaryPort
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (dart : G.Dart) (hfst : ¬ cut.side dart.fst)
    (hsnd : cut.side dart.snd) :
    cyclicData.boundaryOrder
        (retainedBoundaryPort graphData cut cyclicData dart hfst hsnd) =
      retainedBoundaryDart graphData cut dart hfst hsnd := by
  exact cyclicData.boundaryOrder.apply_symm_apply _

/-- The retained defect vertex at a crossing dart's coordinate is its
initial endpoint. -/
theorem commonRetainedBoundaryData_defectVertex_retainedBoundaryPort
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (dart : G.Dart) (hfst : ¬ cut.side dart.fst)
    (hsnd : cut.side dart.snd) :
    (commonRetainedBoundaryData graphData cut cyclicData).defectVertex
        (retainedBoundaryPort graphData cut cyclicData dart hfst hsnd) =
      ⟨dart.fst, hfst⟩ := by
  apply Subtype.ext
  change graphData.toRotationSystem.vertOf
      (cyclicData.boundaryOrder
        (retainedBoundaryPort graphData cut cyclicData dart hfst hsnd)).1.1 =
    dart.fst
  rw [boundaryOrder_retainedBoundaryPort]
  rfl

/-- An internal dart based at the same retained vertex as a crossing dart
is incident to that crossing port in the induced side graph. -/
theorem retainedInternalEdge_mem_incident_at_retainedBoundaryPort
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (internal crossing : G.Dart)
    (hinternalFst : ¬ cut.side internal.fst)
    (hinternalSnd : ¬ cut.side internal.snd)
    (hcrossingFst : ¬ cut.side crossing.fst)
    (hcrossingSnd : cut.side crossing.snd)
    (hfst : internal.fst = crossing.fst) :
    retainedInternalEdge cut internal hinternalFst hinternalSnd ∈
      incidentEdgeFinset (retainedCutGraph G cut)
        ((commonRetainedBoundaryData graphData cut cyclicData).defectVertex
          (retainedBoundaryPort graphData cut cyclicData crossing
            hcrossingFst hcrossingSnd)) := by
  rw [commonRetainedBoundaryData_defectVertex_retainedBoundaryPort]
  simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact Sym2.mem_iff.mpr (Or.inl (Subtype.ext hfst.symm))

/-- On the complementary side the reflected coordinate `-port` has the
opposite endpoint of the same crossing dart as its defect vertex. -/
theorem complement_commonRetainedBoundaryData_defectVertex_neg_port
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (dart : G.Dart) (hfst : ¬ cut.side dart.fst)
    (hsnd : cut.side dart.snd) :
    (commonRetainedBoundaryData graphData cut.compl
        (complementCyclicFourBoundaryData cyclicData)).defectVertex
        (-(retainedBoundaryPort graphData cut cyclicData dart hfst hsnd)) =
      ⟨dart.snd, by simpa [SmallCyclicEdgeCut.compl] using hsnd⟩ := by
  apply Subtype.ext
  change graphData.toRotationSystem.vertOf
      ((complementCyclicFourBoundaryData cyclicData).boundaryOrder
        (-(retainedBoundaryPort graphData cut cyclicData dart hfst hsnd))).1.1 =
    dart.snd
  rw [complementCyclicFourBoundaryData_boundaryOrder]
  simp only [neg_neg]
  rw [boundaryOrder_retainedBoundaryPort]
  rfl

/-- A crossing dart based on the selected side has reflected coordinate
`-port` in the complementary boundary system. -/
theorem complement_retainedBoundaryPort_eq_neg
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (dart : G.Dart) (hfst : cut.side dart.fst)
    (hsnd : ¬ cut.side dart.snd) :
    retainedBoundaryPort graphData cut.compl
        (complementCyclicFourBoundaryData cyclicData) dart
        (by simpa [SmallCyclicEdgeCut.compl] using hfst)
        (by simpa [SmallCyclicEdgeCut.compl] using hsnd) =
      -(retainedBoundaryPort graphData cut cyclicData
        dart.symm hsnd hfst) := by
  apply (complementCyclicFourBoundaryData cyclicData).boundaryOrder.injective
  apply Subtype.ext
  apply Subtype.ext
  rw [boundaryOrder_retainedBoundaryPort,
    complementCyclicFourBoundaryData_boundaryOrder]
  simp only [neg_neg]
  rw [boundaryOrder_retainedBoundaryPort]
  rfl

/-- Distinct retained-to-selected crossing darts cannot start at the same
defect vertex. This is the dart-level form of distinctness of the four
exact-cut ports. -/
theorem retained_crossing_dart_eq_of_fst_eq
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (hdata : (commonRetainedBoundaryData graphData cut cyclicData).WellFormed)
    (first second : G.Dart)
    (hfirstFst : ¬ cut.side first.fst)
    (hfirstSnd : cut.side first.snd)
    (hsecondFst : ¬ cut.side second.fst)
    (hsecondSnd : cut.side second.snd)
    (hfst : first.fst = second.fst) : first = second := by
  let firstPort := retainedBoundaryPort graphData cut cyclicData
    first hfirstFst hfirstSnd
  let secondPort := retainedBoundaryPort graphData cut cyclicData
    second hsecondFst hsecondSnd
  have hports : firstPort = secondPort := by
    apply hdata.1
    rw [commonRetainedBoundaryData_defectVertex_retainedBoundaryPort,
      commonRetainedBoundaryData_defectVertex_retainedBoundaryPort]
    exact Subtype.ext hfst
  have hboundary :
      retainedBoundaryDart graphData cut first hfirstFst hfirstSnd =
        retainedBoundaryDart graphData cut second hsecondFst hsecondSnd := by
    apply cyclicData.boundaryOrder.symm.injective
    exact hports
  exact congrArg (fun boundary ↦ boundary.1.1) hboundary

/-- Read an ambient dart from the Tait coloring on the side containing its
initial vertex. Internal colors on the retained side are globally relabeled.
A crossing dart receives the relabeled missing color at its uniquely
oriented retained-side port. -/
def gluedDartColor
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color) (dart : G.Dart) : Color := by
  classical
  exact if hfst : cut.side dart.fst then
    if hsnd : cut.side dart.snd then
      selectedColoring
        (retainedInternalEdge cut.compl dart
          (by simpa [SmallCyclicEdgeCut.compl] using hfst)
          (by simpa [SmallCyclicEdgeCut.compl] using hsnd))
    else
      let port := retainedBoundaryPort graphData cut cyclicData
        dart.symm hsnd hfst
      colorEquiv
        ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
          retainedColoring port)
  else
    if hsnd : cut.side dart.snd then
      let port := retainedBoundaryPort graphData cut cyclicData
        dart hfst hsnd
      colorEquiv
        ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
          retainedColoring port)
    else
      colorEquiv (retainedColoring
        (retainedInternalEdge cut dart hfst hsnd))

@[simp]
theorem gluedDartColor_selected_internal
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color) (dart : G.Dart)
    (hfst : cut.side dart.fst) (hsnd : cut.side dart.snd) :
    gluedDartColor graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv dart =
      selectedColoring
        (retainedInternalEdge cut.compl dart
          (by simpa [SmallCyclicEdgeCut.compl] using hfst)
          (by simpa [SmallCyclicEdgeCut.compl] using hsnd)) := by
  simp [gluedDartColor, hfst, hsnd]

@[simp]
theorem gluedDartColor_selected_crossing
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color) (dart : G.Dart)
    (hfst : cut.side dart.fst) (hsnd : ¬ cut.side dart.snd) :
    gluedDartColor graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv dart =
      colorEquiv
        ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
          retainedColoring
          (retainedBoundaryPort graphData cut cyclicData
            dart.symm hsnd hfst)) := by
  simp [gluedDartColor, hfst, hsnd]

@[simp]
theorem gluedDartColor_retained_crossing
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color) (dart : G.Dart)
    (hfst : ¬ cut.side dart.fst) (hsnd : cut.side dart.snd) :
    gluedDartColor graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv dart =
      colorEquiv
        ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
          retainedColoring
          (retainedBoundaryPort graphData cut cyclicData
            dart hfst hsnd)) := by
  simp [gluedDartColor, hfst, hsnd]

@[simp]
theorem gluedDartColor_retained_internal
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color) (dart : G.Dart)
    (hfst : ¬ cut.side dart.fst) (hsnd : ¬ cut.side dart.snd) :
    gluedDartColor graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv dart =
      colorEquiv (retainedColoring
        (retainedInternalEdge cut dart hfst hsnd)) := by
  simp [gluedDartColor, hfst, hsnd]

/-- The canonical retained orientation of a crossing edge makes the
piecewise dart color invariant under edge reversal. -/
theorem gluedDartColor_symm
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color) (dart : G.Dart) :
    gluedDartColor graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv dart.symm =
      gluedDartColor graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv dart := by
  by_cases hfst : cut.side dart.fst <;>
    by_cases hsnd : cut.side dart.snd
  · rw [gluedDartColor_selected_internal _ _ _ _ _ _ _ hsnd hfst,
      gluedDartColor_selected_internal _ _ _ _ _ _ _ hfst hsnd,
      retainedInternalEdge_symm]
  · rw [gluedDartColor_retained_crossing _ _ _ _ _ _ _ hsnd hfst,
      gluedDartColor_selected_crossing _ _ _ _ _ _ _ hfst hsnd]
  · rw [gluedDartColor_selected_crossing _ _ _ _ _ _ _ hsnd hfst,
      gluedDartColor_retained_crossing _ _ _ _ _ _ _ hfst hsnd]
    simp
  · rw [gluedDartColor_retained_internal _ _ _ _ _ _ _ hsnd hfst,
      gluedDartColor_retained_internal _ _ _ _ _ _ _ hfst hsnd,
      retainedInternalEdge_symm]

/-- Rotation-system edge reversal is graph-dart reversal, so the preceding
invariance is exactly the descent condition. -/
theorem gluedDartColor_alpha
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color) (dart : G.Dart) :
    gluedDartColor graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv
        (graphData.toRotationSystem.alpha dart) =
      gluedDartColor graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv dart := by
  exact gluedDartColor_symm graphData cut cyclicData retainedColoring
    selectedColoring colorEquiv dart

/-- At a selected-side crossing dart, boundary alignment identifies the
canonical retained missing color with the selected side's missing color at
the reflected port. -/
theorem gluedDartColor_selected_crossing_eq_selected_colorWord
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color)
    (halign : ∀ port : Fin 4,
      colorEquiv
          ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
            retainedColoring port) =
        (commonRetainedBoundaryData graphData cut.compl
            (complementCyclicFourBoundaryData cyclicData)).colorWord
          selectedColoring (-port))
    (dart : G.Dart) (hfst : cut.side dart.fst)
    (hsnd : ¬ cut.side dart.snd) :
    gluedDartColor graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv dart =
      (commonRetainedBoundaryData graphData cut.compl
          (complementCyclicFourBoundaryData cyclicData)).colorWord
        selectedColoring
        (-(retainedBoundaryPort graphData cut cyclicData
          dart.symm hsnd hfst)) := by
  rw [gluedDartColor_selected_crossing]
  exact halign _

/-- At every ambient vertex, two distinct darts receive distinct colors.
Internal/internal pairs inherit properness from one induced side;
internal/crossing pairs use the missing-color equation; and two crossing
darts are excluded by injectivity of the four defect ports. -/
theorem gluedDartColor_proper
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color)
    (hretainedData :
      (commonRetainedBoundaryData graphData cut cyclicData).WellFormed)
    (hselectedData :
      (commonRetainedBoundaryData graphData cut.compl
        (complementCyclicFourBoundaryData cyclicData)).WellFormed)
    (hretainedTait :
      IsTaitEdgeColoring (retainedCutGraph G cut) retainedColoring)
    (hselectedTait :
      IsTaitEdgeColoring (retainedCutGraph G cut.compl) selectedColoring)
    (halign : ∀ port : Fin 4,
      colorEquiv
          ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
            retainedColoring port) =
        (commonRetainedBoundaryData graphData cut.compl
            (complementCyclicFourBoundaryData cyclicData)).colorWord
          selectedColoring (-port))
    {first second : G.Dart} (hfst : first.fst = second.fst)
    (hne : first ≠ second) :
    gluedDartColor graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv first ≠
      gluedDartColor graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv second := by
  by_cases hfirstBase : cut.side first.fst
  · have hsecondBase : cut.side second.fst := by
      rw [← hfst]
      exact hfirstBase
    by_cases hfirstTerminal : cut.side first.snd
    · by_cases hsecondTerminal : cut.side second.snd
      · rw [gluedDartColor_selected_internal _ _ _ _ _ _ _
          hfirstBase hfirstTerminal,
        gluedDartColor_selected_internal _ _ _ _ _ _ _
          hsecondBase hsecondTerminal]
        apply selectedColoring.valid
        exact retainedInternalEdges_lineGraph_adj_of_fst_eq_of_ne
          cut.compl first second
          (by simpa [SmallCyclicEdgeCut.compl] using hfirstBase)
          (by simpa [SmallCyclicEdgeCut.compl] using hfirstTerminal)
          (by simpa [SmallCyclicEdgeCut.compl] using hsecondBase)
          (by simpa [SmallCyclicEdgeCut.compl] using hsecondTerminal)
          hfst hne
      · rw [gluedDartColor_selected_internal _ _ _ _ _ _ _
          hfirstBase hfirstTerminal,
        gluedDartColor_selected_crossing_eq_selected_colorWord
          graphData cut cyclicData retainedColoring selectedColoring
          colorEquiv halign second hsecondBase hsecondTerminal]
        let complementData := complementCyclicFourBoundaryData cyclicData
        let port := retainedBoundaryPort graphData cut cyclicData
          second.symm hsecondTerminal hsecondBase
        let complementPort := retainedBoundaryPort graphData cut.compl
          complementData second
          (by simpa [SmallCyclicEdgeCut.compl] using hsecondBase)
          (by simpa [SmallCyclicEdgeCut.compl] using hsecondTerminal)
        have hport : complementPort = -port := by
          exact complement_retainedBoundaryPort_eq_neg
            graphData cut cyclicData second hsecondBase hsecondTerminal
        have hincident :=
          retainedInternalEdge_mem_incident_at_retainedBoundaryPort
            graphData cut.compl complementData first second
            (by simpa [SmallCyclicEdgeCut.compl] using hfirstBase)
            (by simpa [SmallCyclicEdgeCut.compl] using hfirstTerminal)
            (by simpa [SmallCyclicEdgeCut.compl] using hsecondBase)
            (by simpa [SmallCyclicEdgeCut.compl] using hsecondTerminal)
            hfst
        have hmissing :=
          DegreeTwoBoundaryData.colorWord_ne_incidentColor
            (commonRetainedBoundaryData graphData cut.compl complementData)
              hselectedData selectedColoring
              hselectedTait complementPort
              (retainedInternalEdge cut.compl first
                (by simpa [SmallCyclicEdgeCut.compl] using hfirstBase)
                (by simpa [SmallCyclicEdgeCut.compl] using hfirstTerminal))
              hincident
        exact (hport ▸ hmissing).symm
    · by_cases hsecondTerminal : cut.side second.snd
      · rw [gluedDartColor_selected_crossing_eq_selected_colorWord
          graphData cut cyclicData retainedColoring selectedColoring
          colorEquiv halign first hfirstBase hfirstTerminal,
        gluedDartColor_selected_internal _ _ _ _ _ _ _
          hsecondBase hsecondTerminal]
        let complementData := complementCyclicFourBoundaryData cyclicData
        let port := retainedBoundaryPort graphData cut cyclicData
          first.symm hfirstTerminal hfirstBase
        let complementPort := retainedBoundaryPort graphData cut.compl
          complementData first
          (by simpa [SmallCyclicEdgeCut.compl] using hfirstBase)
          (by simpa [SmallCyclicEdgeCut.compl] using hfirstTerminal)
        have hport : complementPort = -port := by
          exact complement_retainedBoundaryPort_eq_neg
            graphData cut cyclicData first hfirstBase hfirstTerminal
        have hincident :=
          retainedInternalEdge_mem_incident_at_retainedBoundaryPort
            graphData cut.compl complementData second first
            (by simpa [SmallCyclicEdgeCut.compl] using hsecondBase)
            (by simpa [SmallCyclicEdgeCut.compl] using hsecondTerminal)
            (by simpa [SmallCyclicEdgeCut.compl] using hfirstBase)
            (by simpa [SmallCyclicEdgeCut.compl] using hfirstTerminal)
            hfst.symm
        have hmissing :=
          DegreeTwoBoundaryData.colorWord_ne_incidentColor
            (commonRetainedBoundaryData graphData cut.compl complementData)
              hselectedData selectedColoring
              hselectedTait complementPort
              (retainedInternalEdge cut.compl second
                (by simpa [SmallCyclicEdgeCut.compl] using hsecondBase)
                (by simpa [SmallCyclicEdgeCut.compl] using hsecondTerminal))
              hincident
        exact hport ▸ hmissing
      · exfalso
        apply hne
        exact retained_crossing_dart_eq_of_fst_eq
          graphData cut.compl
          (complementCyclicFourBoundaryData cyclicData) hselectedData
          first second
          (by simpa [SmallCyclicEdgeCut.compl] using hfirstBase)
          (by simpa [SmallCyclicEdgeCut.compl] using hfirstTerminal)
          (by simpa [SmallCyclicEdgeCut.compl] using hsecondBase)
          (by simpa [SmallCyclicEdgeCut.compl] using hsecondTerminal)
          hfst
  · have hsecondBase : ¬ cut.side second.fst := by
      rw [← hfst]
      exact hfirstBase
    by_cases hfirstTerminal : cut.side first.snd
    · by_cases hsecondTerminal : cut.side second.snd
      · exfalso
        apply hne
        exact retained_crossing_dart_eq_of_fst_eq graphData cut cyclicData
          hretainedData first second hfirstBase hfirstTerminal
          hsecondBase hsecondTerminal hfst
      · rw [gluedDartColor_retained_crossing _ _ _ _ _ _ _
          hfirstBase hfirstTerminal,
        gluedDartColor_retained_internal _ _ _ _ _ _ _
          hsecondBase hsecondTerminal]
        apply colorEquiv.injective.ne
        let port := retainedBoundaryPort graphData cut cyclicData
          first hfirstBase hfirstTerminal
        have hincident :=
          retainedInternalEdge_mem_incident_at_retainedBoundaryPort
            graphData cut cyclicData second first hsecondBase
            hsecondTerminal hfirstBase hfirstTerminal hfst.symm
        exact DegreeTwoBoundaryData.colorWord_ne_incidentColor
          (commonRetainedBoundaryData graphData cut cyclicData)
            hretainedData retainedColoring
            hretainedTait port
            (retainedInternalEdge cut second hsecondBase hsecondTerminal)
            hincident
    · by_cases hsecondTerminal : cut.side second.snd
      · rw [gluedDartColor_retained_internal _ _ _ _ _ _ _
          hfirstBase hfirstTerminal,
        gluedDartColor_retained_crossing _ _ _ _ _ _ _
          hsecondBase hsecondTerminal]
        apply colorEquiv.injective.ne
        let port := retainedBoundaryPort graphData cut cyclicData
          second hsecondBase hsecondTerminal
        have hincident :=
          retainedInternalEdge_mem_incident_at_retainedBoundaryPort
            graphData cut cyclicData first second hfirstBase
            hfirstTerminal hsecondBase hsecondTerminal hfst
        exact (DegreeTwoBoundaryData.colorWord_ne_incidentColor
          (commonRetainedBoundaryData graphData cut cyclicData)
            hretainedData retainedColoring
            hretainedTait port
            (retainedInternalEdge cut first hfirstBase hfirstTerminal)
            hincident).symm
      · rw [gluedDartColor_retained_internal _ _ _ _ _ _ _
          hfirstBase hfirstTerminal,
        gluedDartColor_retained_internal _ _ _ _ _ _ _
          hsecondBase hsecondTerminal]
        apply colorEquiv.injective.ne
        apply retainedColoring.valid
        exact retainedInternalEdges_lineGraph_adj_of_fst_eq_of_ne
          cut first second hfirstBase hfirstTerminal hsecondBase
            hsecondTerminal hfst hne

/-- A color equivalence fixing zero preserves nonzeroness. -/
theorem colorEquiv_apply_ne_zero
    (colorEquiv : Color ≃ Color) (hzero : colorEquiv 0 = 0)
    {color : Color} (hcolor : color ≠ 0) : colorEquiv color ≠ 0 := by
  intro hmap
  apply hcolor
  apply colorEquiv.injective
  simpa [hzero] using hmap

/-- Every piecewise dart color is nonzero when both induced-side
colorings are Tait and the global relabeling fixes zero. -/
theorem gluedDartColor_ne_zero
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color)
    (hzero : colorEquiv 0 = 0)
    (hretainedData :
      (commonRetainedBoundaryData graphData cut cyclicData).WellFormed)
    (hretainedTait :
      IsTaitEdgeColoring (retainedCutGraph G cut) retainedColoring)
    (hselectedTait :
      IsTaitEdgeColoring (retainedCutGraph G cut.compl) selectedColoring)
    (dart : G.Dart) :
    gluedDartColor graphData cut cyclicData retainedColoring
      selectedColoring colorEquiv dart ≠ 0 := by
  by_cases hfst : cut.side dart.fst
  · by_cases hsnd : cut.side dart.snd
    · rw [gluedDartColor_selected_internal _ _ _ _ _ _ _ hfst hsnd]
      exact hselectedTait _
    · rw [gluedDartColor_selected_crossing _ _ _ _ _ _ _ hfst hsnd]
      apply colorEquiv_apply_ne_zero colorEquiv hzero
      exact DegreeTwoBoundaryData.colorWord_ne_zero
        (commonRetainedBoundaryData graphData cut cyclicData)
          hretainedData retainedColoring _
  · by_cases hsnd : cut.side dart.snd
    · rw [gluedDartColor_retained_crossing _ _ _ _ _ _ _ hfst hsnd]
      apply colorEquiv_apply_ne_zero colorEquiv hzero
      exact DegreeTwoBoundaryData.colorWord_ne_zero
        (commonRetainedBoundaryData graphData cut cyclicData)
          hretainedData retainedColoring _
    · rw [gluedDartColor_retained_internal _ _ _ _ _ _ _ hfst hsnd]
      exact colorEquiv_apply_ne_zero colorEquiv hzero (hretainedTait _)

/-- Descend the alpha-invariant, locally proper dart colors to a proper
edge coloring of the ambient graph-backed rotation system. -/
def gluedColoring
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color)
    (hretainedData :
      (commonRetainedBoundaryData graphData cut cyclicData).WellFormed)
    (hselectedData :
      (commonRetainedBoundaryData graphData cut.compl
        (complementCyclicFourBoundaryData cyclicData)).WellFormed)
    (hretainedTait :
      IsTaitEdgeColoring (retainedCutGraph G cut) retainedColoring)
    (hselectedTait :
      IsTaitEdgeColoring (retainedCutGraph G cut.compl) selectedColoring)
    (halign : ∀ port : Fin 4,
      colorEquiv
          ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
            retainedColoring port) =
        (commonRetainedBoundaryData graphData cut.compl
            (complementCyclicFourBoundaryData cyclicData)).colorWord
          selectedColoring (-port)) :
    graphData.toRotationSystem.EdgeColoring Color :=
  graphData.toRotationSystem.dartDescendedColoring
    (gluedDartColor graphData cut cyclicData retainedColoring
      selectedColoring colorEquiv)
    (gluedDartColor_alpha graphData cut cyclicData retainedColoring
      selectedColoring colorEquiv)
    (by
      intro first second hfst hne
      exact gluedDartColor_proper graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv hretainedData hselectedData
        hretainedTait hselectedTait halign hfst hne)

/-- The descended coloring is a Tait coloring of the ambient rotation
system. -/
theorem gluedColoring_isTait
    (graphData : Data G) (cut : SmallCyclicEdgeCut G)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut))
    (retainedColoring : (retainedCutGraph G cut).EdgeColoring Color)
    (selectedColoring :
      (retainedCutGraph G cut.compl).EdgeColoring Color)
    (colorEquiv : Color ≃ Color)
    (hzero : colorEquiv 0 = 0)
    (hretainedData :
      (commonRetainedBoundaryData graphData cut cyclicData).WellFormed)
    (hselectedData :
      (commonRetainedBoundaryData graphData cut.compl
        (complementCyclicFourBoundaryData cyclicData)).WellFormed)
    (hretainedTait :
      IsTaitEdgeColoring (retainedCutGraph G cut) retainedColoring)
    (hselectedTait :
      IsTaitEdgeColoring (retainedCutGraph G cut.compl) selectedColoring)
    (halign : ∀ port : Fin 4,
      colorEquiv
          ((commonRetainedBoundaryData graphData cut cyclicData).colorWord
            retainedColoring port) =
        (commonRetainedBoundaryData graphData cut.compl
            (complementCyclicFourBoundaryData cyclicData)).colorWord
          selectedColoring (-port)) :
    graphData.toRotationSystem.IsTaitEdgeColoring
      (gluedColoring graphData cut cyclicData retainedColoring
        selectedColoring colorEquiv hretainedData hselectedData
        hretainedTait hselectedTait halign) := by
  apply graphData.toRotationSystem.dartDescendedColoring_isTait
  intro dart
  exact gluedDartColor_ne_zero graphData cut cyclicData retainedColoring
    selectedColoring colorEquiv hzero hretainedData hretainedTait
    hselectedTait dart

/-- An exact cyclic four-edge cut carrying its canonical planar boundary
coordinates contradicts graph-backed vertex minimality. The overlap theorem
colors both induced sides compatibly, and the preceding descent glues them
to an ambient Tait coloring. -/
theorem false_of_exactCyclicFourEdgeCut_of_cyclicBoundaryData
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4)
    (cyclicData : CyclicFourBoundaryData graphData.toRotationSystem
      (cyclicCutVertexSide cut)) : False := by
  let hcubicGraph : ∀ vertex : V,
      (incidentEdgeFinset G vertex).card = 3 := fun vertex ↦ by
    rw [GoertzelV24DeletedEdgeTrail.incidentEdgeFinset_card_eq_degree]
    exact (graphData.toRotationSystem_isCubic_iff.mp
      minimal.spherical.cubic) vertex
  let hcyclic :=
    cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample
      graphData minimal
  let complementData := complementCyclicFourBoundaryData cyclicData
  have hretainedData :
      (commonRetainedBoundaryData graphData cut cyclicData).WellFormed :=
    commonRetainedBoundaryData_wellFormed graphData hcubicGraph hcyclic
      cut hcard cyclicData
  have hselectedData :
      (commonRetainedBoundaryData graphData cut.compl
        complementData).WellFormed :=
    commonRetainedBoundaryData_wellFormed graphData hcubicGraph hcyclic
      cut.compl (by simpa using hcard) complementData
  rcases exists_aligned_complementary_retainedCutColorings
      graphData minimal cut hcard cyclicData with
    ⟨retainedColoring, selectedColoring, colorEquiv,
      hretainedTait, hselectedTait, hzero, halign⟩
  apply minimal.notColorable
  exact ⟨gluedColoring graphData cut cyclicData retainedColoring
      selectedColoring colorEquiv hretainedData hselectedData
      hretainedTait hselectedTait halign,
    gluedColoring_isTait graphData cut cyclicData retainedColoring
      selectedColoring colorEquiv hzero hretainedData hselectedData
      hretainedTait hselectedTait halign⟩

/-- Exact cyclic four-edge cuts are impossible in a graph-backed
vertex-minimal Tait counterexample. Spherical planarity first supplies the
common cyclic boundary coordinates required by the compositional overlap
and gluing argument. -/
theorem false_of_exactCyclicFourEdgeCut
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) (hcard : cut.edgeCut.card = 4) : False := by
  have hconnected : G.Connected := by
    rw [← GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
      G graphData]
    exact minimal.primalConnected
  let hcyclic :=
    cyclicEdgeConnectivityAtLeast_four_of_vertexMinimalTaitCounterexample
      graphData minimal
  rcases exists_cyclicFourBoundaryData_of_exactCyclicFourCut
      graphData minimal.spherical minimal.facesTwoSided hconnected
      minimal.vertexRotationCyclic hcyclic cut hcard with
    ⟨cyclicData⟩
  exact false_of_exactCyclicFourEdgeCut_of_cyclicBoundaryData
    graphData minimal cut hcard cyclicData

/-- The four-edge rung of the cyclic-connectivity ladder is discharged. -/
theorem no_smallCyclicEdgeCut_card_eq_four_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cut : SmallCyclicEdgeCut G) : cut.edgeCut.card ≠ 4 := by
  intro hcard
  exact false_of_exactCyclicFourEdgeCut graphData minimal cut hcard

/-- Every graph-backed vertex-minimal Tait counterexample is cyclically
five-edge-connected: the two- and three-edge reductions supply the lower
rungs, while the compositional four-pole overlap excludes the last cut. -/
theorem cyclicallyFiveEdgeConnected_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData) :
    CyclicallyFiveEdgeConnected G := by
  exact cyclicallyFiveEdgeConnected_of_no_four_cyclicEdgeCut
    graphData minimal
    (no_smallCyclicEdgeCut_card_eq_four_of_vertexMinimalTaitCounterexample
      graphData minimal)

end

end GoertzelV24FourEdgeCutGluing

end Mettapedia.GraphTheory.FourColor
