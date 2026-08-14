import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapOpenHoleOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutNormalization

/-!
# Connectivity of the retained side of a facial pentagon cap

The one-cap hole-orbit calculation needs the complement of the five cap
vertices to be connected.  This file derives that fact from the actual
minimal-counterexample connectivity already proved by the two-edge-cut
normalization.

The finite argument is exact.  Every connected component of the retained
induced graph must meet the cap through one of its five named spokes.  If it
met through at most two spokes, deleting a distinct pair covering those
spokes would disconnect the ambient graph, contrary to vertex minimality.
Two distinct retained components would therefore consume at least six
disjoint spoke indices, impossible in `Fin 5`.

No planar separation principle and no configuration catalogue is used.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapRetainedConnectivity

open SimpleGraph
open SimpleGraphDartRotation
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24DeletedRegionSlitGraph
open GoertzelV24FacialPentagonCap
open GoertzelV24PentagonCapOpening
open GoertzelV24PentagonCapOpeningComparison
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24TwoEdgeCutNormalization

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace PentagonCap

/-- The literal graph induced by the vertices retained after deleting the
five cap vertices. -/
def retainedGraph (cap : PentagonCap G) :
    SimpleGraph {vertex : V // vertex ∉ cap.vertexSupport} :=
  G.induce {vertex | vertex ∉ cap.vertexSupport}

/-- A retained ambient vertex belongs to a selected connected component of
the retained induced graph. -/
def retainedComponentSide (cap : PentagonCap G)
    (component : (retainedGraph cap).ConnectedComponent) (vertex : V) : Prop :=
  ∃ hvertex : vertex ∉ cap.vertexSupport,
    (⟨vertex, hvertex⟩ : {vertex : V // vertex ∉ cap.vertexSupport}) ∈
      component.supp

/-- The named spokes whose retained endpoints lie in one retained component. -/
def componentSpokeIndices (cap : PentagonCap G)
    (component : (retainedGraph cap).ConnectedComponent) : Finset (Fin 5) :=
  by
    classical
    exact Finset.univ.filter fun step =>
      retainedComponentSide cap component (cap.spokeOuter step)

@[simp]
theorem mem_componentSpokeIndices_iff (cap : PentagonCap G)
    (component : (retainedGraph cap).ConnectedComponent) (step : Fin 5) :
    step ∈ componentSpokeIndices cap component ↔
      retainedComponentSide cap component (cap.spokeOuter step) := by
  simp [componentSpokeIndices]

/-- A cap vertex is never on a retained-component side. -/
theorem not_retainedComponentSide_vertex (cap : PentagonCap G)
    (component : (retainedGraph cap).ConnectedComponent) (step : Fin 5) :
    ¬ retainedComponentSide cap component (cap.vertex step) := by
  rintro ⟨hvertex, _⟩
  exact hvertex ((cap.mem_vertexSupport_iff _).mpr ⟨step, rfl⟩)

/-- Ambient adjacency between two retained vertices is adjacency in the
retained induced graph. -/
theorem retainedGraph_adj_of_adj (cap : PentagonCap G)
    {first second : V}
    (hfirst : first ∉ cap.vertexSupport)
    (hsecond : second ∉ cap.vertexSupport)
    (hadj : G.Adj first second) :
    (retainedGraph cap).Adj
      (⟨first, hfirst⟩ : {vertex : V // vertex ∉ cap.vertexSupport})
      (⟨second, hsecond⟩ : {vertex : V // vertex ∉ cap.vertexSupport}) :=
  hadj

/-- Every ambient edge crossing a retained component is one of the named cap
spokes, and its retained endpoint supplies an index belonging to that
component. -/
theorem exists_spokeIndex_of_edgeCrosses_retainedComponent
    (cap : PentagonCap G)
    (component : (retainedGraph cap).ConnectedComponent)
    (edge : G.edgeSet)
    (hcross : EdgeCrossesVertexSide G
      (retainedComponentSide cap component) edge) :
    ∃ step ∈ componentSpokeIndices cap component,
      edge = cap.spokeEdge step := by
  rcases hcross with
    ⟨inside, outside, hinsideEdge, houtsideEdge, hinside, houtside⟩
  rcases hinside with ⟨hinsideRetained, hinsideComponent⟩
  have houtsideCap : outside ∈ cap.vertexSupport := by
    by_contra houtsideRetained
    have hadj : G.Adj inside outside := by
      have hne : inside ≠ outside := by
        intro heq
        exact houtside (heq ▸ ⟨hinsideRetained, hinsideComponent⟩)
      have hedgeValue : edge.1 = s(inside, outside) :=
        sym2_eq_mk_of_mem_of_mem_of_ne hinsideEdge houtsideEdge hne
      exact (SimpleGraph.mem_edgeSet G).mp (by simpa [hedgeValue] using edge.2)
    have hretainedAdj := retainedGraph_adj_of_adj cap
      hinsideRetained houtsideRetained hadj
    have houtsideComponent :
        (⟨outside, houtsideRetained⟩ :
          {vertex : V // vertex ∉ cap.vertexSupport}) ∈ component.supp :=
      (component.mem_supp_congr_adj hretainedAdj).mp hinsideComponent
    exact houtside ⟨houtsideRetained, houtsideComponent⟩
  let dart : G.Dart :=
    ⟨(inside, outside), by
      have hne : inside ≠ outside := by
        intro heq
        exact hinsideRetained (heq ▸ houtsideCap)
      have hedgeValue : edge.1 = s(inside, outside) :=
        sym2_eq_mk_of_mem_of_mem_of_ne hinsideEdge houtsideEdge hne
      exact (SimpleGraph.mem_edgeSet G).mp (by simpa [hedgeValue] using edge.2)⟩
  let port : DeletedRegionBoundaryPort G cap.vertexSupport :=
    { dart := dart
      retained := hinsideRetained
      removed := houtsideCap }
  rcases
      GoertzelV24PentagonCapOpeningComparison.PentagonCap.boundaryPort_eq_spokeBoundaryPort
        cap port with
    ⟨step, hport⟩
  have hinsideEq : inside = cap.spokeOuter step := by
    have := congrArg
      (fun boundary : DeletedRegionBoundaryPort G cap.vertexSupport =>
        boundary.dart.fst) hport
    simpa [port, dart] using this
  have houtsideEq : outside = cap.vertex step := by
    have := congrArg
      (fun boundary : DeletedRegionBoundaryPort G cap.vertexSupport =>
        boundary.dart.snd) hport
    simpa [port, dart] using this
  have hedgeValue : edge.1 = (cap.spokeEdge step).1 := by
    have hne : inside ≠ outside := by
      intro heq
      exact hinsideRetained (heq ▸ houtsideCap)
    calc
      edge.1 = s(inside, outside) :=
        sym2_eq_mk_of_mem_of_mem_of_ne hinsideEdge houtsideEdge hne
      _ = s(cap.spokeOuter step, cap.vertex step) := by
        rw [hinsideEq, houtsideEq]
      _ = s(cap.vertex step, cap.spokeOuter step) := Sym2.eq_swap
      _ = (cap.spokeEdge step).1 := (cap.spokeEdge_eq step).symm
  refine ⟨step, ?_, Subtype.ext hedgeValue⟩
  rw [mem_componentSpokeIndices_iff]
  exact ⟨cap.spokeOuter_not_mem_vertexSupport step, by simpa [hinsideEq] using hinsideComponent⟩

/-- Every retained component meets at least one named cap spoke.  This uses
ambient connectedness only after the exact crossing-to-spoke classification
above has been established. -/
theorem componentSpokeIndices_nonempty (cap : PentagonCap G)
    (hconnected : G.Connected)
    (component : (retainedGraph cap).ConnectedComponent) :
    (componentSpokeIndices cap component).Nonempty := by
  rcases component.nonempty_supp with ⟨inside, hinside⟩
  have hinsideSide : retainedComponentSide cap component inside.1 :=
    ⟨inside.2, hinside⟩
  have houtsideSide :
      ¬ retainedComponentSide cap component (cap.vertex 0) :=
    not_retainedComponentSide_vertex cap component 0
  rcases hconnected inside.1 (cap.vertex 0) with ⟨walk⟩
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      (retainedComponentSide cap component) walk hinsideSide houtsideSide with
    ⟨edge, _hedgeWalk, hcross⟩
  rcases exists_spokeIndex_of_edgeCrosses_retainedComponent
      cap component edge hcross with ⟨step, hstep, _⟩
  exact ⟨step, hstep⟩

/-- Distinct retained components consume disjoint sets of named spokes. -/
theorem componentSpokeIndices_disjoint (cap : PentagonCap G)
    {first second : (retainedGraph cap).ConnectedComponent}
    (hne : first ≠ second) :
    Disjoint (componentSpokeIndices cap first)
      (componentSpokeIndices cap second) := by
  rw [Finset.disjoint_left]
  intro step hfirst hsecond
  rw [mem_componentSpokeIndices_iff] at hfirst hsecond
  rcases hfirst with ⟨hretainedFirst, hfirstComponent⟩
  rcases hsecond with ⟨hretainedSecond, hsecondComponent⟩
  apply hne
  apply SimpleGraph.ConnectedComponent.eq_of_common_vertex hfirstComponent
  simpa only [Subtype.ext_iff] using hsecondComponent

/-- A nonempty component-spoke set of cardinality at most two is covered by
a pair of distinct ambient edges.  In the singleton case a cap-cycle edge is
used only as harmless padding; cap incidence proves it differs from every
spoke. -/
theorem exists_distinct_edgePair_cover_componentSpokes_of_card_le_two
    (cap : PentagonCap G)
    (component : (retainedGraph cap).ConnectedComponent)
    (hnonempty : (componentSpokeIndices cap component).Nonempty)
    (hcard : (componentSpokeIndices cap component).card ≤ 2) :
    ∃ first second : G.edgeSet,
      first ≠ second ∧
        ∀ step ∈ componentSpokeIndices cap component,
          cap.spokeEdge step = first ∨ cap.spokeEdge step = second := by
  have hpositive : 0 < (componentSpokeIndices cap component).card :=
    Finset.card_pos.mpr hnonempty
  have hcases :
      (componentSpokeIndices cap component).card = 1 ∨
        (componentSpokeIndices cap component).card = 2 := by
    omega
  rcases hcases with hone | htwo
  · rcases Finset.card_eq_one.mp hone with ⟨only, hindices⟩
    refine ⟨cap.spokeEdge only, cap.cycleEdge 0, ?_, ?_⟩
    · exact (cap.cycle_spoke_ne 0 only).symm
    · intro step hstep
      rw [hindices] at hstep
      have : step = only := by simpa using hstep
      subst step
      exact Or.inl rfl
  · rcases Finset.card_eq_two.mp htwo with
      ⟨firstStep, secondStep, hsteps, hindices⟩
    refine ⟨cap.spokeEdge firstStep, cap.spokeEdge secondStep, ?_, ?_⟩
    · intro hedges
      exact hsteps (cap.spokeEdge.injective hedges)
    · intro step hstep
      rw [hindices] at hstep
      simp only [Finset.mem_insert, Finset.mem_singleton] at hstep
      rcases hstep with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- A distinct edge pair covering all spokes of one retained component
disconnects that component from the cap. -/
theorem not_connected_deleteEdges_pair_of_componentSpoke_cover
    (cap : PentagonCap G)
    (component : (retainedGraph cap).ConnectedComponent)
    (first second : G.edgeSet)
    (hcover : ∀ step ∈ componentSpokeIndices cap component,
      cap.spokeEdge step = first ∨ cap.spokeEdge step = second) :
    ¬ (G.deleteEdges
      ({first.1, second.1} : Set (Sym2 V))).Connected := by
  intro hdeleteConnected
  rcases component.nonempty_supp with ⟨inside, hinsideComponent⟩
  have hinsideSide : retainedComponentSide cap component inside.1 :=
    ⟨inside.2, hinsideComponent⟩
  have houtsideSide :
      ¬ retainedComponentSide cap component (cap.vertex 0) :=
    not_retainedComponentSide_vertex cap component 0
  rcases hdeleteConnected inside.1 (cap.vertex 0) with ⟨deletedWalk⟩
  let ambientWalk : G.Walk inside.1 (cap.vertex 0) :=
    deletedWalk.mapLe
      (G.deleteEdges_le ({first.1, second.1} : Set (Sym2 V)))
  have hambientEdges : ambientWalk.edges = deletedWalk.edges :=
    deletedWalk.edges_mapLe_eq_edges
      (G.deleteEdges_le ({first.1, second.1} : Set (Sym2 V)))
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      (retainedComponentSide cap component) ambientWalk
      hinsideSide houtsideSide with
    ⟨crossing, hcrossingWalk, hcrossing⟩
  rcases exists_spokeIndex_of_edgeCrosses_retainedComponent
      cap component crossing hcrossing with
    ⟨step, hstep, hcrossingEq⟩
  rcases hcover step hstep with hfirst | hsecond
  · have hcrossingFirst : crossing = first := hcrossingEq.trans hfirst
    have havoidsFirst : first.1 ∉ ambientWalk.edges := by
      intro hmem
      have hdeleted := deletedWalk.edges_subset_edgeSet
        (by simpa [hambientEdges] using hmem)
      simp at hdeleted
    exact havoidsFirst (by simpa [hcrossingFirst] using hcrossingWalk)
  · have hcrossingSecond : crossing = second := hcrossingEq.trans hsecond
    have havoidsSecond : second.1 ∉ ambientWalk.edges := by
      intro hmem
      have hdeleted := deletedWalk.edges_subset_edgeSet
        (by simpa [hambientEdges] using hmem)
      simp at hdeleted
    exact havoidsSecond (by simpa [hcrossingSecond] using hcrossingWalk)

/-- In a graph-backed vertex-minimal Tait counterexample, every retained
component owns at least three of the five cap spokes. -/
theorem three_le_card_componentSpokeIndices_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cap : PentagonCap G)
    (component : (retainedGraph cap).ConnectedComponent) :
    3 ≤ (componentSpokeIndices cap component).card := by
  by_contra hnotThree
  have hcard : (componentSpokeIndices cap component).card ≤ 2 := by
    omega
  have hconnected : G.Connected := by
    rw [←
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
        G graphData]
    exact minimal.primalConnected
  have hnonempty := componentSpokeIndices_nonempty cap hconnected component
  rcases exists_distinct_edgePair_cover_componentSpokes_of_card_le_two
      cap component hnonempty hcard with
    ⟨first, second, hne, hcover⟩
  exact
    (not_connected_deleteEdges_pair_of_componentSpoke_cover
      cap component first second hcover)
      (deleteEdges_pair_connected_of_vertexMinimalTaitCounterexample
        graphData minimal first second hne)

/-- The five cap spokes cannot support two distinct retained components:
minimality forces each component to own at least three disjoint indices. -/
theorem retainedGraph_connected_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cap : PentagonCap G) :
    (retainedGraph cap).Connected := by
  let retainedVertex : {vertex : V // vertex ∉ cap.vertexSupport} :=
    ⟨cap.spokeOuter 0, cap.spokeOuter_not_mem_vertexSupport 0⟩
  letI : Nonempty {vertex : V // vertex ∉ cap.vertexSupport} :=
    ⟨retainedVertex⟩
  by_contra hnotConnected
  have hnotPreconnected : ¬ (retainedGraph cap).Preconnected := by
    intro hpreconnected
    exact hnotConnected ⟨hpreconnected⟩
  rw [SimpleGraph.Preconnected] at hnotPreconnected
  push Not at hnotPreconnected
  rcases hnotPreconnected with ⟨firstVertex, secondVertex, hnotReachable⟩
  let firstComponent :=
    (retainedGraph cap).connectedComponentMk firstVertex
  let secondComponent :=
    (retainedGraph cap).connectedComponentMk secondVertex
  have hcomponentsNe : firstComponent ≠ secondComponent := by
    intro heq
    exact hnotReachable (SimpleGraph.ConnectedComponent.exact heq)
  have hfirstThree :
      3 ≤ (componentSpokeIndices cap firstComponent).card :=
    three_le_card_componentSpokeIndices_of_vertexMinimalTaitCounterexample
      graphData minimal cap firstComponent
  have hsecondThree :
      3 ≤ (componentSpokeIndices cap secondComponent).card :=
    three_le_card_componentSpokeIndices_of_vertexMinimalTaitCounterexample
      graphData minimal cap secondComponent
  have hdisjoint :
      Disjoint (componentSpokeIndices cap firstComponent)
        (componentSpokeIndices cap secondComponent) :=
    componentSpokeIndices_disjoint cap hcomponentsNe
  have hsubset :
      componentSpokeIndices cap firstComponent ∪
          componentSpokeIndices cap secondComponent ⊆
        (Finset.univ : Finset (Fin 5)) := by
    intro step _
    exact Finset.mem_univ step
  have hcardLe :
      (componentSpokeIndices cap firstComponent ∪
        componentSpokeIndices cap secondComponent).card ≤ 5 := by
    have := Finset.card_le_card hsubset
    simpa using this
  rw [Finset.card_union_of_disjoint hdisjoint] at hcardLe
  omega

/-- Source-facing form of retained-complement connectivity, in exactly the
predicate used by the one-cap opened-hole orbit theorem. -/
theorem retainedComplement_connected_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (cap : PentagonCap G) :
    (G.induce {vertex | deletedRegionKeep cap.vertexSupport vertex}).Connected := by
  exact retainedGraph_connected_of_vertexMinimalTaitCounterexample
    graphData minimal cap

/-- In a graph-backed vertex-minimal Tait counterexample, all five fresh
stubs of an oriented facial pentagon cap lie on one literal opened face orbit.
This discharges the retained-connectivity premise of the one-cap C-2 theorem
from minimality rather than carrying it into source formation. -/
theorem openedHoleFace_stub_eq_of_vertexMinimalTaitCounterexample
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (walk : FacialPentagonCapBoundaryWalk graphData)
    (first second : Fin 5) :
    GoertzelV24FaceOrbitIncidence.dartOrbitFace
        (GoertzelV24OpenRegionRotation.rotationSystem
          graphData.toRotationSystem
          (GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.keep
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
          (Sum.inl (GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.openBoundaryDart graphData
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap 0).1))
        (Sum.inr (GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.openBoundaryDart graphData
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap first)) =
      GoertzelV24FaceOrbitIncidence.dartOrbitFace
        (GoertzelV24OpenRegionRotation.rotationSystem
          graphData.toRotationSystem
          (GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.keep
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
          (Sum.inl (GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.openBoundaryDart graphData
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap 0).1))
        (Sum.inr (GoertzelV24FacialPentagonCapOpenBoundary.PentagonCap.openBoundaryDart graphData
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap second)) := by
  have hconnected : G.Connected := by
    rw [←
      GoertzelV24SimpleGraphFaceDualConnectedness.rotationPrimalGraph_toRotationSystem_eq
        G graphData]
    exact minimal.primalConnected
  exact
    GoertzelV24FacialPentagonCapOpenHoleOrbit.openedHoleFace_stub_eq
      walk minimal.spherical minimal.facesTwoSided hconnected
        minimal.spherical.cubic minimal.vertexRotationCyclic
        (retainedComplement_connected_of_vertexMinimalTaitCounterexample
          graphData minimal
            walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap)
        first second

end PentagonCap

end

end GoertzelV24FacialPentagonCapRetainedConnectivity

end Mettapedia.GraphTheory.FourColor
