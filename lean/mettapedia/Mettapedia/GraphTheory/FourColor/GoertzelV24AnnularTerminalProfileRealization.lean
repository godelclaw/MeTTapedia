import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mettapedia.GraphTheory.FourColor.GoertzelV24SourceTerminalCapCount

/-!
# Realizing the annular Seed profile in the cumulative carrier

The source Menu-B census records connected components of the selected-color
vertex graph, whereas the cumulative corridor profile records connectivity in
the selected-color edge graph.  This module proves that the two presentations
agree on the five cap-foot edges: connectedness of incident boundary edges in
the line graph is equivalent to connectedness of their cap stubs in the
selected vertex graph.

The whole annulus therefore supplies a literal graph-derived cumulative source
profile with exactly the counted terminal view.  The manuscript's global color
normalization is performed on the actual Tait coloring and is proved to
preserve the full connection table.  Consequently positivity of the corrected
Seed count needs no separate profile-realization hypothesis.

This is a boundary-semantic bridge.  It does not claim that the whole-annulus
profile has already been reached by the literal one-Cell serial transition;
that remaining statement is geometric coverage of the serial prefix.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem reachable_of_mem_common_edge
    (edge : G.edgeSet) {left right : V}
    (hleft : left ∈ (edge : Sym2 V))
    (hright : right ∈ (edge : Sym2 V)) :
    G.Reachable left right := by
  by_cases heq : left = right
  · subst right
    exact .refl left
  · apply Adj.reachable
    rw [adj_iff_exists_edge]
    exact ⟨heq, edge, edge.2, hleft, hright⟩

theorem lineGraph_reachable_of_common_vertex
    (left right : G.edgeSet) {vertex : V}
    (hleft : vertex ∈ (left : Sym2 V))
    (hright : vertex ∈ (right : Sym2 V)) :
    G.lineGraph.Reachable left right := by
  by_cases heq : left = right
  · subst right
    exact .refl left
  · exact (lineGraph_adj_iff_exists.mpr
      ⟨heq, vertex, hleft, hright⟩).reachable

theorem reachable_of_lineGraph_reachable_of_mem
    {first last : G.edgeSet}
    (hedges : G.lineGraph.Reachable first last)
    {start finish : V}
    (hstart : start ∈ (first : Sym2 V))
    (hfinish : finish ∈ (last : Sym2 V)) :
    G.Reachable start finish := by
  rw [reachable_iff_reflTransGen] at hedges
  induction hedges using Relation.ReflTransGen.head_induction_on generalizing start with
  | refl =>
    exact reachable_of_mem_common_edge last hstart hfinish
  | head hadj _ ih =>
    rcases lineGraph_adj_iff_exists.mp hadj with
      ⟨_, vertex, hcurrent, hnext⟩
    exact (reachable_of_mem_common_edge _ hstart hcurrent).trans
      (ih hnext)

theorem lineGraph_reachable_of_reachable_of_mem
    {start finish : V}
    (hvertices : G.Reachable start finish)
    {first last : G.edgeSet}
    (hstart : start ∈ (first : Sym2 V))
    (hfinish : finish ∈ (last : Sym2 V)) :
    G.lineGraph.Reachable first last := by
  rw [reachable_iff_reflTransGen] at hvertices
  induction hvertices using Relation.ReflTransGen.head_induction_on generalizing first with
  | refl =>
    exact lineGraph_reachable_of_common_vertex first last hstart hfinish
  | @head middle next hadj _ ih =>
    let stepEdge : G.edgeSet :=
      ⟨s(middle, next), (mem_edgeSet G).2 hadj⟩
    have hmiddle : middle ∈ (stepEdge : Sym2 V) := by
      simp [stepEdge]
    have hnext : next ∈ (stepEdge : Sym2 V) := by
      simp [stepEdge]
    exact (lineGraph_reachable_of_common_vertex first stepEdge hstart hmiddle).trans
      (ih hnext)

theorem lineGraph_reachable_iff_reachable_of_mem
    {first last : G.edgeSet} {start finish : V}
    (hstart : start ∈ (first : Sym2 V))
    (hfinish : finish ∈ (last : Sym2 V)) :
    G.lineGraph.Reachable first last ↔ G.Reachable start finish :=
  ⟨fun h => reachable_of_lineGraph_reachable_of_mem h hstart hfinish,
    fun h => lineGraph_reachable_of_reachable_of_mem h hstart hfinish⟩

theorem induce_support_reachable_iff
    (first second : G.support) :
    (G.induce G.support).Reachable first second ↔
      G.Reachable first.1 second.1 := by
  constructor
  · intro hreachable
    exact hreachable.map
      (SimpleGraph.Embedding.induce G.support).toHom
  · rintro ⟨walk⟩
    by_cases hnil : walk.Nil
    · have heq : first = second := Subtype.ext hnil.eq
      subst second
      exact .refl first
    · refine ⟨walk.induce G.support ?_⟩
      intro vertex hvertex
      exact SimpleGraph.mem_support_of_mem_walk_support walk hnil hvertex

theorem induce_reachable_iff_of_support_subset_set
    (carrier : Set V)
    (hsupport : G.support ⊆ carrier)
    (first second : carrier) :
    (G.induce carrier).Reachable first second ↔
      G.Reachable first.1 second.1 := by
  constructor
  · intro hreachable
    exact hreachable.map
      (SimpleGraph.Embedding.induce carrier).toHom
  · rintro ⟨walk⟩
    by_cases hnil : walk.Nil
    · have heq : first = second := Subtype.ext hnil.eq
      subst second
      exact .refl first
    · refine ⟨walk.induce carrier ?_⟩
      intro vertex hvertex
      exact hsupport
        (SimpleGraph.mem_support_of_mem_walk_support walk hnil hvertex)

end SimpleGraph

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularTerminalProfileRealization

open SimpleGraph
open GoertzelV24AnnularFrontierMenu
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebSelectedEdgeStructure
open GoertzelV24CorridorProfile
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24SourceCorridorProfile
open GoertzelV24SourceTerminalCapCount
open GoertzelV24SourceTerminalCapView
open GoertzelV24SourceTerminalCapGauge

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Consumer-facing form of the generic line-graph/vertex-graph reachability
equivalence used at the annular boundary. -/
theorem boundaryLineGraph_reachable_iff_vertexReachable
    {first last : G.edgeSet} {start finish : V}
    (hstart : start ∈ (first : Sym2 V))
    (hfinish : finish ∈ (last : Sym2 V)) :
    G.lineGraph.Reachable first last ↔ G.Reachable start finish :=
  SimpleGraph.lineGraph_reachable_iff_reachable_of_mem hstart hfinish

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem mem_colorPairGraph_edgeSet_iff
    (C : G.EdgeColoring Color) (first second : Color)
    (edge : G.edgeSet) :
    edge.1 ∈ (colorPairGraph C first second).edgeSet ↔
      IsTrackedColor first second (C edge) := by
  rcases edge with ⟨edge, hedge⟩
  induction edge using Sym2.inductionOn with
  | _ left right =>
      rw [SimpleGraph.mem_edgeSet,
        colorPairGraph_adj_iff]
      constructor
      · rintro ⟨_, hcolor⟩
        exact hcolor
      · intro hcolor
        exact ⟨(SimpleGraph.mem_edgeSet G).1 hedge, hcolor⟩

noncomputable def selectedAmbientEdgeEquivColorPairEdge
    (C : G.EdgeColoring Color) (first second : Color) :
    C.bicoloredSet first second ≃
      (colorPairGraph C first second).edgeSet where
  toFun edge :=
    ⟨edge.1.1,
      (mem_colorPairGraph_edgeSet_iff C first second edge.1).2 edge.2⟩
  invFun edge := by
    let ambient : G.edgeSet :=
      ⟨edge.1, SimpleGraph.edgeSet_mono
        (colorPairGraph_le C first second) edge.2⟩
    exact ⟨ambient,
      (mem_colorPairGraph_edgeSet_iff C first second ambient).1 edge.2⟩
  left_inv edge := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv edge := by
    apply Subtype.ext
    rfl

noncomputable def bicoloredSubgraphIsoColorPairLineGraph
    (C : G.EdgeColoring Color) (first second : Color) :
    C.bicoloredSubgraph first second ≃g
      (colorPairGraph C first second).lineGraph where
  toEquiv := selectedAmbientEdgeEquivColorPairEdge C first second
  map_rel_iff' := by
    intro left right
    change (colorPairGraph C first second).lineGraph.Adj
        (selectedAmbientEdgeEquivColorPairEdge C first second left)
        (selectedAmbientEdgeEquivColorPairEdge C first second right) ↔
      G.lineGraph.Adj left.1 right.1
    constructor
    · intro htarget
      rcases SimpleGraph.lineGraph_adj_iff_exists.mp htarget with
        ⟨hne, vertex, hleft, hright⟩
      apply SimpleGraph.lineGraph_adj_iff_exists.mpr
      refine ⟨?_, vertex, ?_, ?_⟩
      · intro heq
        apply hne
        exact Subtype.ext
          (congrArg (fun edge : G.edgeSet => edge.1) heq)
      · simpa [selectedAmbientEdgeEquivColorPairEdge] using hleft
      · simpa [selectedAmbientEdgeEquivColorPairEdge] using hright
    · intro hsource
      rcases SimpleGraph.lineGraph_adj_iff_exists.mp hsource with
        ⟨hne, vertex, hleft, hright⟩
      apply SimpleGraph.lineGraph_adj_iff_exists.mpr
      refine ⟨?_, vertex, ?_, ?_⟩
      · intro heq
        apply hne
        exact Subtype.ext
          (congrArg (fun edge : (colorPairGraph C first second).edgeSet =>
            edge.1) heq)
      · simpa [selectedAmbientEdgeEquivColorPairEdge] using hleft
      · simpa [selectedAmbientEdgeEquivColorPairEdge] using hright

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem bicoloredSubgraph_reachable_iff_colorPairLineGraph
    (C : G.EdgeColoring Color) (first second : Color)
    (left right : C.bicoloredSet first second) :
    (C.bicoloredSubgraph first second).Reachable left right ↔
      (colorPairGraph C first second).lineGraph.Reachable
        (selectedAmbientEdgeEquivColorPairEdge C first second left)
        (selectedAmbientEdgeEquivColorPairEdge C first second right) := by
  exact (SimpleGraph.Iso.reachable_iff
    (φ := bicoloredSubgraphIsoColorPairLineGraph C first second)).symm

noncomputable def activeBoundaryEdge
    {outerCount : Nat}
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (first second : Color)
    (inner : AnnularFrontierActivePairPort data C first second) :
    C.bicoloredSet first second :=
  ⟨data.innerBoundaryEdge inner.1, by
    have hactive := (Finset.mem_filter.mp inner.2).2
    change C (data.innerBoundaryEdge inner.1) = first ∨
      C (data.innerBoundaryEdge inner.1) = second
    simpa only [AnnularBoundaryData.innerBoundaryWord,
      cap5BoundaryWordOfEdges] using hactive⟩

theorem activePairComponents_eq_iff_bicoloredReachable
    {outerCount : Nat}
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (first second : Color)
    (left right : AnnularFrontierActivePairPort data C first second) :
    annularFrontierActivePairPortComponent data hdata C first second left =
        annularFrontierActivePairPortComponent data hdata C first second right ↔
      (C.bicoloredSubgraph first second).Reachable
        (activeBoundaryEdge data C first second left)
        (activeBoundaryEdge data C first second right) := by
  change
    (colorPairSupportGraph C first second).connectedComponentMk
        ⟨data.innerStub left.1,
          innerStub_mem_colorPairGraph_support_of_mem_activeSupport
            data hdata C first second left.1 left.2⟩ =
      (colorPairSupportGraph C first second).connectedComponentMk
        ⟨data.innerStub right.1,
          innerStub_mem_colorPairGraph_support_of_mem_activeSupport
            data hdata C first second right.1 right.2⟩ ↔ _
  rw [ConnectedComponent.eq]
  change
    ((colorPairGraph C first second).induce
        (colorPairGraph C first second).support).Reachable _ _ ↔ _
  rw [SimpleGraph.induce_support_reachable_iff,
    bicoloredSubgraph_reachable_iff_colorPairLineGraph]
  apply Iff.symm
  apply SimpleGraph.lineGraph_reachable_iff_reachable_of_mem
  · simpa [selectedAmbientEdgeEquivColorPairEdge, activeBoundaryEdge,
      incidentEdgeFinset] using hdata.innerBoundaryEdge_incident left.1
  · simpa [selectedAmbientEdgeEquivColorPairEdge, activeBoundaryEdge,
      incidentEdgeFinset] using hdata.innerBoundaryEdge_incident right.1

theorem trackedEdgeGraph_support_subset_bicoloredSet
    (graphData : SimpleGraphDartRotation.Data G)
    (C : G.EdgeColoring Color) (first second : Color) :
    (graphData.toRotationSystem.trackedEdgeGraph
      (fun edge => C edge) first second).support ⊆
        C.bicoloredSet first second := by
  intro edge hedge
  rcases (SimpleGraph.mem_support _).1 hedge with ⟨other, hadj⟩
  exact hadj.2.1

theorem trackedEdgeGraph_induce_eq_bicoloredSubgraph
    (graphData : SimpleGraphDartRotation.Data G)
    (C : G.EdgeColoring Color) (first second : Color) :
    (graphData.toRotationSystem.trackedEdgeGraph
      (fun edge => C edge) first second).induce
        (C.bicoloredSet first second) =
      C.bicoloredSubgraph first second := by
  ext left right
  change
    (graphData.toRotationSystem.edgeAdjacencyGraph.Adj left.1 right.1 ∧
        IsTrackedColor first second (C left.1) ∧
        IsTrackedColor first second (C right.1)) ↔
      G.lineGraph.Adj left.1 right.1
  rw [GoertzelV24SimpleGraphTaitBridge.toRotationSystem_edgeAdjacencyGraph_eq_lineGraph]
  simp only [IsTrackedColor]
  exact and_iff_left ⟨left.2, right.2⟩

theorem trackedEdgeGraph_reachable_iff_bicoloredSubgraph
    (graphData : SimpleGraphDartRotation.Data G)
    (C : G.EdgeColoring Color) (first second : Color)
    (left right : C.bicoloredSet first second) :
    (graphData.toRotationSystem.trackedEdgeGraph
      (fun edge => C edge) first second).Reachable left.1 right.1 ↔
      (C.bicoloredSubgraph first second).Reachable left right := by
  rw [← SimpleGraph.induce_reachable_iff_of_support_subset_set
      (carrier := C.bicoloredSet first second)
      (trackedEdgeGraph_support_subset_bicoloredSet
        graphData C first second),
    trackedEdgeGraph_induce_eq_bicoloredSubgraph]

noncomputable def wholeAnnulusTerminalCutData
    {outerCount : Nat}
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AnnularBoundaryData G outerCount) :
    GraphCorridorCutData graphData.toRotationSystem 0 5 0 where
  regionEdges := Finset.univ
  crossingEdge := Fin.elim0
  terminalEdge := data.innerBoundaryEdge
  fragmentFace := Fin.elim0
  fragmentEdges := Fin.elim0

theorem wholeAnnulusTerminalCutData_portsInRegion
    {outerCount : Nat}
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AnnularBoundaryData G outerCount) :
    (wholeAnnulusTerminalCutData graphData data).PortsInRegion := by
  intro port
  cases port with
  | inl crossing => exact Fin.elim0 crossing
  | inr terminal => simp [wholeAnnulusTerminalCutData,
      GraphCorridorCutData.portEdge]

theorem wholeAnnulusTerminalCutData_crossing_nonzero
    {outerCount : Nat}
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AnnularBoundaryData G outerCount)
    (C : G.edgeSet → Color) :
    ∀ crossing,
      C ((wholeAnnulusTerminalCutData graphData data).crossingEdge crossing) ≠ 0 := by
  intro crossing
  exact Fin.elim0 crossing

theorem regionalTrackedEdgeGraph_univ_reachable_iff_bicoloredSubgraph
    (graphData : SimpleGraphDartRotation.Data G)
    (C : G.EdgeColoring Color) (first second : Color)
    (left right : C.bicoloredSet first second) :
    (regionalTrackedEdgeGraph graphData.toRotationSystem Finset.univ
      (fun edge => C edge) first second).Reachable left.1 right.1 ↔
      (C.bicoloredSubgraph first second).Reachable left right := by
  have hgraph :
      regionalTrackedEdgeGraph graphData.toRotationSystem Finset.univ
          (fun edge => C edge) first second =
        graphData.toRotationSystem.trackedEdgeGraph
          (fun edge => C edge) first second := by
    ext edge other
    simp [regionalTrackedEdgeGraph]
  rw [hgraph]
  exact trackedEdgeGraph_reachable_iff_bicoloredSubgraph
    graphData C first second left right

theorem connectionTable_eq_regionalTrackedConnectivity
    {outerCount : Nat}
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (first second : Color)
    (pair : TrackedColorPair)
    (hcolors : trackedColorPairColors pair = (first, second))
    (left right : Fin 5) :
    annularFrontierMenuConnectionTable data hdata C first second left right =
      regionalTrackedConnectivity graphData.toRotationSystem Finset.univ
        (fun edge => C edge) pair
        (data.innerBoundaryEdge left) (data.innerBoundaryEdge right) := by
  apply Bool.eq_iff_iff.mpr
  rw [annularFrontierMenuConnectionTable_eq_true_iff,
    regionalTrackedConnectivity_eq_true_iff, hcolors]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hleft, hright, hcomponents⟩
    have hleftColor : IsTrackedColor first second
        (C (data.innerBoundaryEdge left)) := by
      simpa [cap5ActiveSupport, AnnularBoundaryData.innerBoundaryWord,
        cap5BoundaryWordOfEdges, IsTrackedColor] using hleft
    have hrightColor : IsTrackedColor first second
        (C (data.innerBoundaryEdge right)) := by
      simpa [cap5ActiveSupport, AnnularBoundaryData.innerBoundaryWord,
        cap5BoundaryWordOfEdges, IsTrackedColor] using hright
    have hbicolored :
        (C.bicoloredSubgraph first second).Reachable
          (activeBoundaryEdge data C first second ⟨left, hleft⟩)
          (activeBoundaryEdge data C first second ⟨right, hright⟩) :=
      (activePairComponents_eq_iff_bicoloredReachable
        data hdata C first second ⟨left, hleft⟩
          ⟨right, hright⟩).1 hcomponents
    have hregional :=
      (regionalTrackedEdgeGraph_univ_reachable_iff_bicoloredSubgraph
        graphData C first second
          ⟨data.innerBoundaryEdge left, hleftColor⟩
          ⟨data.innerBoundaryEdge right, hrightColor⟩).2
        (by simpa [activeBoundaryEdge] using hbicolored)
    exact ⟨hleftColor, hrightColor, hregional⟩
  · rintro ⟨hleftColor, hrightColor, hregional⟩
    have hleft : left ∈ cap5ActiveSupport first second
        (data.innerBoundaryWord C) := by
      simpa [cap5ActiveSupport, AnnularBoundaryData.innerBoundaryWord,
        cap5BoundaryWordOfEdges, IsTrackedColor] using hleftColor
    have hright : right ∈ cap5ActiveSupport first second
        (data.innerBoundaryWord C) := by
      simpa [cap5ActiveSupport, AnnularBoundaryData.innerBoundaryWord,
        cap5BoundaryWordOfEdges, IsTrackedColor] using hrightColor
    have hbicolored :=
      (regionalTrackedEdgeGraph_univ_reachable_iff_bicoloredSubgraph
        graphData C first second
          ⟨data.innerBoundaryEdge left, hleftColor⟩
          ⟨data.innerBoundaryEdge right, hrightColor⟩).1 hregional
    refine ⟨hleft, hright, ?_⟩
    apply (activePairComponents_eq_iff_bicoloredReachable
      data hdata C first second ⟨left, hleft⟩ ⟨right, hright⟩).2
    simpa [activeBoundaryEdge] using hbicolored

theorem sourcePair_connectionTable_eq_regionalTrackedConnectivity
    {outerCount : Nat}
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color)
    (pair : SourceTrackedColorPair) (left right : Fin 5) :
    annularFrontierMenuConnectionTable data hdata C
        (sourceTrackedColorPairColors red blue purple pair).1
        (sourceTrackedColorPairColors red blue purple pair).2 left right =
      regionalTrackedConnectivity graphData.toRotationSystem Finset.univ
        (fun edge => C edge) pair.toTrackedColorPair
        (data.innerBoundaryEdge left) (data.innerBoundaryEdge right) := by
  cases pair
  · exact connectionTable_eq_regionalTrackedConnectivity
      graphData data hdata C red blue .ab rfl left right
  · exact connectionTable_eq_regionalTrackedConnectivity
      graphData data hdata C red purple .ac rfl left right

noncomputable def wholeAnnulusSourceProfile
    {outerCount : Nat}
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) : SourceCorridorCutProfile 0 5 0 :=
  toSourceProfile
    ((wholeAnnulusTerminalCutData graphData data).regionalProfile
      (fun edge => C edge)
      (wholeAnnulusTerminalCutData_crossing_nonzero graphData data C))

/-- The source's vertex-component profile and the cumulative corridor's
tracked-edge profile have literally the same five-terminal cap view in the
standard color gauge. -/
theorem terminalCapViewOfUniformProfile_standard_eq_wholeAnnulusSourceProfile
    {outerCount : Nat}
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    terminalCapViewOfUniformProfileAt
        (annularFrontierMenuUniformProfile data hdata C)
        red blue purple =
      terminalCapViewOfSourceProfile
        (wholeAnnulusSourceProfile graphData data C) := by
  apply SourceTerminalCapView.ext
  · funext terminal
    change data.innerBoundaryWord C terminal =
      (terminalCapViewOfSourceProfile
        (toSourceProfile
          ((wholeAnnulusTerminalCutData graphData data).regionalProfile
            (fun edge => C edge)
            (wholeAnnulusTerminalCutData_crossing_nonzero
              graphData data C)))).word terminal
    rw [terminalCapView_word_toSourceProfile_regionalProfile
      (wholeAnnulusTerminalCutData graphData data)
      (wholeAnnulusTerminalCutData_portsInRegion graphData data)
      (fun edge => C edge)
      (wholeAnnulusTerminalCutData_crossing_nonzero graphData data C)
      (fun terminal => hC (data.innerBoundaryEdge terminal)) terminal]
    rfl
  · funext pair left right
    change annularFrontierMenuConnectionTable data hdata C
        (sourceTrackedColorPairColors red blue purple pair).1
          (sourceTrackedColorPairColors red blue purple pair).2 left right =
      (terminalCapViewOfSourceProfile
        (toSourceProfile
          ((wholeAnnulusTerminalCutData graphData data).regionalProfile
            (fun edge => C edge)
            (wholeAnnulusTerminalCutData_crossing_nonzero
              graphData data C)))).strand pair left right
    rw [terminalCapView_strand_toSourceProfile_regionalProfile]
    exact sourcePair_connectionTable_eq_regionalTrackedConnectivity
      graphData data hdata C pair left right

noncomputable def relabelEdgeColoring
    (C : G.EdgeColoring Color) (relabel : Color ≃ Color) :
    G.EdgeColoring Color :=
  SimpleGraph.Coloring.mk (fun edge => relabel (C edge)) (by
    intro left right hadj heq
    exact C.valid hadj (relabel.injective heq))

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem relabelEdgeColoring_apply
    (C : G.EdgeColoring Color) (relabel : Color ≃ Color)
    (edge : G.edgeSet) :
    relabelEdgeColoring C relabel edge = relabel (C edge) :=
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem isTaitEdgeColoring_relabelEdgeColoring
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (relabel : Color ≃ Color) (hzero : relabel 0 = 0) :
    IsTaitEdgeColoring G (relabelEdgeColoring C relabel) := by
  intro edge hzeroColor
  apply hC edge
  exact relabel.injective (hzeroColor.trans hzero.symm)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem mem_activeSupport_relabelEdgeColoring_iff
    {outerCount : Nat}
    (data : AnnularBoundaryData G outerCount)
    (C : G.EdgeColoring Color) (relabel : Color ≃ Color)
    (first second : Color) (position : Fin 5) :
    position ∈ cap5ActiveSupport (relabel first) (relabel second)
        (data.innerBoundaryWord (relabelEdgeColoring C relabel)) ↔
      position ∈ cap5ActiveSupport first second
        (data.innerBoundaryWord C) := by
  simp only [cap5ActiveSupport, Finset.mem_filter, Finset.mem_univ,
    true_and, AnnularBoundaryData.innerBoundaryWord,
    cap5BoundaryWordOfEdges, relabelEdgeColoring_apply]
  constructor
  · rintro (hfirst | hsecond)
    · exact Or.inl (relabel.injective hfirst)
    · exact Or.inr (relabel.injective hsecond)
  · rintro (hfirst | hsecond)
    · exact Or.inl (congrArg relabel hfirst)
    · exact Or.inr (congrArg relabel hsecond)

noncomputable def relabelBicoloredSetEquiv
    (C : G.EdgeColoring Color) (relabel : Color ≃ Color)
    (first second : Color) :
    (relabelEdgeColoring C relabel).bicoloredSet
        (relabel first) (relabel second) ≃
      C.bicoloredSet first second where
  toFun edge := ⟨edge.1, by
    rcases edge.2 with hfirst | hsecond
    · exact Or.inl (relabel.injective hfirst)
    · exact Or.inr (relabel.injective hsecond)⟩
  invFun edge := ⟨edge.1, by
    rcases edge.2 with hfirst | hsecond
    · exact Or.inl (congrArg relabel hfirst)
    · exact Or.inr (congrArg relabel hsecond)⟩
  left_inv edge := Subtype.ext rfl
  right_inv edge := Subtype.ext rfl

noncomputable def relabelBicoloredSubgraphIso
    (C : G.EdgeColoring Color) (relabel : Color ≃ Color)
    (first second : Color) :
    (relabelEdgeColoring C relabel).bicoloredSubgraph
        (relabel first) (relabel second) ≃g
      C.bicoloredSubgraph first second where
  toEquiv := relabelBicoloredSetEquiv C relabel first second
  map_rel_iff' := by
    intro left right
    rfl

theorem connectionTable_eq_true_iff_bicoloredBoundaryReachable
    {outerCount : Nat}
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (first second : Color)
    (left right : Fin 5) :
    annularFrontierMenuConnectionTable data hdata C
        first second left right = true ↔
      ∃ hleft : left ∈ cap5ActiveSupport first second
          (data.innerBoundaryWord C),
        ∃ hright : right ∈ cap5ActiveSupport first second
            (data.innerBoundaryWord C),
          (C.bicoloredSubgraph first second).Reachable
            (activeBoundaryEdge data C first second ⟨left, hleft⟩)
            (activeBoundaryEdge data C first second ⟨right, hright⟩) := by
  rw [annularFrontierMenuConnectionTable_eq_true_iff]
  constructor
  · rintro ⟨hleft, hright, hcomponents⟩
    exact ⟨hleft, hright,
      (activePairComponents_eq_iff_bicoloredReachable
        data hdata C first second ⟨left, hleft⟩
          ⟨right, hright⟩).1 hcomponents⟩
  · rintro ⟨hleft, hright, hreachable⟩
    exact ⟨hleft, hright,
      (activePairComponents_eq_iff_bicoloredReachable
        data hdata C first second ⟨left, hleft⟩
          ⟨right, hright⟩).2 hreachable⟩

theorem connectionTable_relabelEdgeColoring
    {outerCount : Nat}
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (relabel : Color ≃ Color)
    (first second : Color) (left right : Fin 5) :
    annularFrontierMenuConnectionTable data hdata
        (relabelEdgeColoring C relabel)
        (relabel first) (relabel second) left right =
      annularFrontierMenuConnectionTable data hdata C
        first second left right := by
  apply Bool.eq_iff_iff.mpr
  rw [connectionTable_eq_true_iff_bicoloredBoundaryReachable,
    connectionTable_eq_true_iff_bicoloredBoundaryReachable]
  constructor
  · rintro ⟨hleftRelabeled, hrightRelabeled, hreachable⟩
    have hleft := (mem_activeSupport_relabelEdgeColoring_iff
      data C relabel first second left).1 hleftRelabeled
    have hright := (mem_activeSupport_relabelEdgeColoring_iff
      data C relabel first second right).1 hrightRelabeled
    refine ⟨hleft, hright, ?_⟩
    have himage :=
      (SimpleGraph.Iso.reachable_iff
        (φ := relabelBicoloredSubgraphIso C relabel first second)).2
        hreachable
    simpa [relabelBicoloredSubgraphIso, relabelBicoloredSetEquiv,
      activeBoundaryEdge] using himage
  · rintro ⟨hleft, hright, hreachable⟩
    have hleftRelabeled := (mem_activeSupport_relabelEdgeColoring_iff
      data C relabel first second left).2 hleft
    have hrightRelabeled := (mem_activeSupport_relabelEdgeColoring_iff
      data C relabel first second right).2 hright
    refine ⟨hleftRelabeled, hrightRelabeled, ?_⟩
    have himage :=
      (SimpleGraph.Iso.reachable_iff
        (φ := (relabelBicoloredSubgraphIso C relabel first second).symm)).2
        hreachable
    simpa [relabelBicoloredSubgraphIso, relabelBicoloredSetEquiv,
      activeBoundaryEdge] using himage

theorem normalizedUniformCapView_eq_relabelledUniformCapView
    {outerCount : Nat}
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma) :
    normalizedCapView
        (terminalCapViewOfUniformProfileAt
          (annularFrontierMenuUniformProfile data hdata C)
          alpha beta gamma) hcolors =
      terminalCapViewOfUniformProfileAt
        (annularFrontierMenuUniformProfile data hdata
          (relabelEdgeColoring C (normalizeColorEquiv hcolors)))
        red blue purple := by
  apply SourceTerminalCapView.ext
  · funext terminal
    rfl
  · funext pair left right
    cases pair
    · simpa [normalizedCapView, relabelWord,
        terminalCapViewOfUniformProfileAt,
        annularFrontierMenuUniformProfile,
        sourceTrackedColorPairColors] using
        (connectionTable_relabelEdgeColoring data hdata C
          (normalizeColorEquiv hcolors) alpha beta left right).symm
    · simpa [normalizedCapView, relabelWord,
        terminalCapViewOfUniformProfileAt,
        annularFrontierMenuUniformProfile,
        sourceTrackedColorPairColors] using
        (connectionTable_relabelEdgeColoring data hdata C
          (normalizeColorEquiv hcolors) alpha gamma left right).symm

/-- After the manuscript's global color normalization, every realized
uniform profile is literally the five-terminal view of a graph-derived
cumulative profile on the whole annulus. -/
theorem normalizedUniformCapView_eq_wholeAnnulusSourceProfile
    {outerCount : Nat}
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    {alpha beta gamma : Color}
    (hcolors : IsTaitColorTriple alpha beta gamma) :
    normalizedCapView
        (terminalCapViewOfUniformProfileAt
          (annularFrontierMenuUniformProfile data hdata C)
          alpha beta gamma) hcolors =
      terminalCapViewOfSourceProfile
        (wholeAnnulusSourceProfile graphData data
          (relabelEdgeColoring C (normalizeColorEquiv hcolors))) := by
  rw [normalizedUniformCapView_eq_relabelledUniformCapView]
  exact terminalCapViewOfUniformProfile_standard_eq_wholeAnnulusSourceProfile
    graphData data hdata
      (relabelEdgeColoring C (normalizeColorEquiv hcolors))
      (isTaitEdgeColoring_relabelEdgeColoring C hC
        (normalizeColorEquiv hcolors) (normalizeColorEquiv_zero hcolors))

/-- The corrected Seed count is positive exactly when an actual Tait coloring,
normalized as in the manuscript, yields an accepted graph-derived cumulative
profile on the whole annulus.  Thus the counted uniform-profile semantics and
the cumulative finite-state semantics meet without an extra realization
hypothesis. -/
theorem capComposedSeedCount_pos_iff_exists_realizedSourceProfile
    {outerCount : Nat}
    (graphData : SimpleGraphDartRotation.Data G)
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (word : CAP5BoundaryWord) :
    0 < GoertzelV24AnnularFrontierCapComposedProfileCount.capComposedSeedCount
        data hdata word ↔
      ∃ C : G.EdgeColoring Color,
        IsTaitEdgeColoring G C ∧ data.innerBoundaryWord C = word ∧
          ∃ (alpha beta gamma : Color)
              (htriple : AnnularFrontierMajorityTriple
                (data.innerBoundaryWord C) alpha beta gamma),
            (terminalCapViewOfSourceProfile
              (wholeAnnulusSourceProfile graphData data
                (relabelEdgeColoring C
                  (normalizeColorEquiv htriple.1)))).standardGaugeCapComposedMenuBState := by
  rw [capComposedSeedCount_pos_iff_exists_normalized_sourceView]
  constructor
  · rintro ⟨profile, hword, hpositive, alpha, beta, gamma,
        htriple, haccepted⟩
    rcases (annularFrontierMenuUniformProfileCount_pos_iff
      data hdata profile).1 hpositive with ⟨C, hC, hprofile⟩
    have hwordC : data.innerBoundaryWord C = word := by
      rw [← annularFrontierMenuUniformProfile_word data hdata C,
        hprofile]
      exact hword
    have htripleC : AnnularFrontierMajorityTriple
        (data.innerBoundaryWord C) alpha beta gamma := by
      rw [← annularFrontierMenuUniformProfile_word data hdata C,
        hprofile]
      exact htriple
    refine ⟨C, hC, hwordC, alpha, beta, gamma, htripleC, ?_⟩
    rw [← normalizedUniformCapView_eq_wholeAnnulusSourceProfile
      graphData data hdata C hC htripleC.1]
    simpa [hprofile] using haccepted
  · rintro ⟨C, hC, hword, alpha, beta, gamma, htriple, haccepted⟩
    refine ⟨annularFrontierMenuUniformProfile data hdata C, ?_, ?_,
      alpha, beta, gamma, ?_, ?_⟩
    · simpa only [annularFrontierMenuUniformProfile_word] using hword
    · exact (annularFrontierMenuUniformProfileCount_pos_iff
        data hdata (annularFrontierMenuUniformProfile data hdata C)).2
          ⟨C, hC, rfl⟩
    · simpa only [annularFrontierMenuUniformProfile_word] using htriple
    · rw [normalizedUniformCapView_eq_wholeAnnulusSourceProfile
        graphData data hdata C hC htriple.1]
      exact haccepted

end GoertzelV24AnnularTerminalProfileRealization

end Mettapedia.GraphTheory.FourColor
