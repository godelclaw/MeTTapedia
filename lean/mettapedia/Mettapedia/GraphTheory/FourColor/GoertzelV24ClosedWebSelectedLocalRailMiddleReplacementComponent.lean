import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebHoleBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFiniteCutRadialEscape
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicSmallBoundaryCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceWalk
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualCycleBond

/-!
# Boundary-free components of the middle-replacement separator

Every non-centre middle-replacement residue now supplies a literal selected
primal separator of cardinality three or four.  This module chooses a genuine
deletion component away from the distinguished outer-hole dart and proves
that all ten boundary stubs lie outside it.  The local cubic degree count then
shows that the component either contains a cycle or has at most two vertices.

The two-vertex allowance is essential for a four-edge separator: a cubic tree
with four outgoing edges may be one vertex or one edge.  This is a component
classification, not yet a rotor/digon/square reduction, an elimination of the
two centre cases, a rolling transition, or a separated-crosscut constructor.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebComponentCensus
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24ClosedWebInnerTouching
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebTotalClosure
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedLocalDualCycleBond
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceWalk
open GoertzelV24SelectedDualCycleSeparator
open GoertzelV24SelectedDualCycleBond
open SimpleGraph
open SimpleGraphDartRotation
open Instance.LocalLayerFormation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

local instance middleReplacementComponentEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

namespace MiddleReplacementShortDualCycle

variable {face : AmbientFace
  (Finset.univ : Finset (OrbitFace web.annular.RS))}

/-- The concrete source rung retained by the short-cycle construction is one
of the selected primal crossings. -/
@[simp] theorem anchorEdge_mem_crossingEdges
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    cycle.anchorEdge ∈ cycle.selectedCycle.crossingEdges := by
  exact (cycle.selectedCycle.mem_crossingEdges_iff cycle.anchorEdge).2
    ⟨cycle.anchor, cycle.selectedCycle_crossingEdge_anchor⟩

/-- The separator theorem on the finite crossing-edge support consumed by the
deletion-component API. -/
theorem not_connected_deleteEdges_crossingEdges
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    ¬ (G.deleteEdges (edgeFinsetValueSet
      cycle.selectedCycle.crossingEdges)).Connected := by
  rw [← cycle.selectedCycle.primalCut_eq_edgeFinsetValueSet_crossingEdges]
  exact cycle.not_connected_deleteEdges_primalCut

/-- Choose a deletion component on the side opposite the distinguished
outer-hole dart. -/
theorem exists_component_away_from_outerRoot
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    ∃ component :
        (G.deleteEdges (edgeFinsetValueSet
          cycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ component.supp := by
  exact exists_component_not_mem_root_of_not_connected
    cycle.selectedCycle.crossingEdges web.annular.RS.outer.fst
    cycle.not_connected_deleteEdges_crossingEdges

/-- Local facial two-sidedness propagates any nonempty component boundary
around the selected short cycle.  Thus the computed boundary is exactly the
three or four literally selected crossings, without global two-sidedness or
unique shared-edge assumptions. -/
theorem componentCrossingEdges_eq_crossingEdges
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    componentCrossingEdges cycle.selectedCycle.crossingEdges component =
      cycle.selectedCycle.crossingEdges := by
  classical
  let removed := cycle.selectedCycle.crossingEdges
  let deleted := G.deleteEdges (edgeFinsetValueSet removed)
  let outside := deleted.connectedComponentMk web.annular.RS.outer.fst
  have hrootOutside : web.annular.RS.outer.fst ∈ outside.supp := rfl
  have hdistinct : component ≠ outside := by
    intro heq
    exact hroot (heq ▸ hrootOutside)
  have hcomponentNonempty :
      (componentCrossingEdges removed component).Nonempty :=
    componentCrossingEdges_nonempty_of_distinct
      web.annular.cellulation.connected removed component outside hdistinct
  have hcomponentBoundary :
      componentCrossingEdges removed component =
        localCrossingEdgeFinset G
          (fun vertex => vertex ∈ component.supp) := by
    ext edge
    dsimp [removed]
    simp only [mem_componentCrossingEdges_iff,
      mem_localCrossingEdgeFinset_iff]
  have hsubset : localCrossingEdgeFinset G
        (fun vertex => vertex ∈ component.supp) ⊆ removed := by
    rw [← hcomponentBoundary]
    exact componentCrossingEdges_subset_removed removed component
  have hnonempty : (localCrossingEdgeFinset G
      (fun vertex => vertex ∈ component.supp)).Nonempty := by
    rw [← hcomponentBoundary]
    exact hcomponentNonempty
  have hboundary :=
    crossingEdgeFinset_eq_crossingEdges_of_isCycle_of_subset_of_supportTwoSided
      web.annular.cellulation.rotation cycle.selectedCycle
      (fun vertex => vertex ∈ component.supp) hsubset hnonempty
      (by
        intro current hcurrent dart hdart
        apply dartOrbitFace_ne_alpha_of_mem_interiorFaces web dart
        rw [hdart]
        exact cycle.support_internal current hcurrent)
  rw [hcomponentBoundary]
  exact hboundary

/-- A component away from the distinguished outer dart is away from every
vertex on the complete outer-hole face. -/
theorem outerHole_vertex_not_mem_component
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (dart : G.Dart)
    (hdart : dartOrbitFace web.annular.RS dart =
      web.annular.cellulation.outerHole) :
    dart.fst ∉ component.supp := by
  rcases exists_rootedFaceWalk web.annular.cellulation.rotation
      web.annular.RS.outer with ⟨walk, hwalkDarts, hwalkBoundary⟩
  have hdartSupport : dart.fst ∈ walk.support := by
    apply walk.dart_fst_mem_support_of_mem_darts
    rw [hwalkDarts]
    exact (mem_faceOrbitDarts_iff web.annular.cellulation.rotation
      web.annular.RS.outer dart).2
      (hdart.trans web.annular.outer_dart_on_outerHole.symm)
  have hwalkAvoid : ∀ edge : G.edgeSet,
      (edge : Sym2 V) ∈ walk.edges →
        edge.1 ∉ edgeFinsetValueSet
          cycle.selectedCycle.crossingEdges := by
    intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      cycle.selectedCycle.crossingEdges edge.1).1 hvalue with
      ⟨crossing, hcrossing, hcrossingValue⟩
    have hedgeBoundary := hwalkBoundary edge hedge
    rw [web.annular.outer_dart_on_outerHole] at hedgeBoundary
    have hedgeCrossing : edge ∈ cycle.selectedCycle.crossingEdges := by
      simpa [Subtype.ext hcrossingValue] using hcrossing
    exact (Finset.disjoint_left.mp
      cycle.crossingEdges_disjoint_outerHoleBoundary)
        hedgeCrossing hedgeBoundary
  have hside := component_side_iff_of_mem_walk_support_of_avoiding_removed
    cycle.selectedCycle.crossingEdges component walk hwalkAvoid hdartSupport
  intro hdartComponent
  exact hroot (hside.mpr hdartComponent)

/-- Every named outer degree-one stub lies outside the selected component. -/
theorem outerStub_not_mem_component
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (outer : Fin 5) :
    data.outerStub outer ∉ component.supp := by
  simpa using cycle.outerHole_vertex_not_mem_component component hroot
    (outerBoundaryDart data web.boundary_wellFormed outer)
    (outerBoundaryDart_on_outerHole web.annular web.boundary_wellFormed outer)

/-- Fewer than five selected crossings miss one literal radial path. -/
theorem exists_radialPath_avoiding_crossingEdges
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    ∃ endpoint : InnerEnd data coloring,
      ∀ edge : G.edgeSet,
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            (everyColorPairComponentInnerTouching_of_totallyClosed
              data web.boundary_wellFormed web.connected coloring web.tait
                web.totallyClosed)
            endpoint)).edges →
          edge ∉ cycle.selectedCycle.crossingEdges := by
  apply exists_radialPathOfInnerEnd_avoiding_finiteCut (web := web)
  rcases cycle.crossingEdges_card_eq_three_or_four with hthree | hfour
  · omega
  · omega

/-- A component away from the outer hole is also away from every vertex on
the inner-hole face. -/
theorem innerHole_vertex_not_mem_component
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (dart : G.Dart)
    (hdart : dartOrbitFace web.annular.RS dart =
      web.annular.cellulation.innerHole) :
    dart.fst ∉ component.supp := by
  obtain ⟨endpoint, havoids⟩ := cycle.exists_radialPath_avoiding_crossingEdges
  let hinnerTouching : EveryColorPairComponentInnerTouching data coloring :=
    everyColorPairComponentInnerTouching_of_totallyClosed
      data web.boundary_wellFormed web.connected coloring web.tait web.totallyClosed
  let radial := radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
    hinnerTouching endpoint
  have hradialAvoid : ∀ edge : G.edgeSet,
      (edge : Sym2 V) ∈ (ambientRadialPath radial).edges →
        edge.1 ∉ edgeFinsetValueSet
          cycle.selectedCycle.crossingEdges := by
    intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      cycle.selectedCycle.crossingEdges edge.1).1 hvalue with
      ⟨crossing, hcrossing, hcrossingValue⟩
    apply havoids crossing
    · rw [hcrossingValue]
      exact hedge
    · exact hcrossing
  have hradialSide := component_side_iff_of_walk_avoiding_removed
    cycle.selectedCycle.crossingEdges component
      (ambientRadialPath radial) hradialAvoid
  have hselectedInner : data.innerStub radial.inner ∉ component.supp := by
    intro hinner
    have hstart : radial.start.1 ∈ component.supp := by
      rw [radial.start_eq_innerStub]
      exact hinner
    have hfinish : radial.finish.1 ∈ component.supp := hradialSide.mp hstart
    apply cycle.outerStub_not_mem_component component hroot radial.outer
    rw [← radial.finish_eq_outerStub]
    exact hfinish
  let innerRoot := innerBoundaryDart data web.boundary_wellFormed radial.inner
  have hinnerRootFace : dartOrbitFace web.annular.RS innerRoot =
      web.annular.cellulation.innerHole := by
    simpa [innerRoot] using innerBoundaryDart_on_innerHole
      web.annular web.boundary_wellFormed radial.inner
  rcases exists_rootedFaceWalk web.annular.cellulation.rotation innerRoot with
    ⟨walk, hwalkDarts, hwalkBoundary⟩
  have hdartSupport : dart.fst ∈ walk.support := by
    apply walk.dart_fst_mem_support_of_mem_darts
    rw [hwalkDarts]
    exact (mem_faceOrbitDarts_iff web.annular.cellulation.rotation
      innerRoot dart).2 (hdart.trans hinnerRootFace.symm)
  have hwalkAvoid : ∀ edge : G.edgeSet,
      (edge : Sym2 V) ∈ walk.edges →
        edge.1 ∉ edgeFinsetValueSet
          cycle.selectedCycle.crossingEdges := by
    intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      cycle.selectedCycle.crossingEdges edge.1).1 hvalue with
      ⟨crossing, hcrossing, hcrossingValue⟩
    have hedgeBoundary := hwalkBoundary edge hedge
    rw [hinnerRootFace] at hedgeBoundary
    have hedgeCrossing : edge ∈ cycle.selectedCycle.crossingEdges := by
      simpa [Subtype.ext hcrossingValue] using hcrossing
    exact (Finset.disjoint_left.mp
      cycle.crossingEdges_disjoint_innerHoleBoundary)
        hedgeCrossing hedgeBoundary
  have hside := component_side_iff_of_mem_walk_support_of_avoiding_removed
    cycle.selectedCycle.crossingEdges component walk hwalkAvoid hdartSupport
  intro hdartComponent
  apply hselectedInner
  have hinnerRootComponent : innerRoot.fst ∈ component.supp :=
    hside.mpr hdartComponent
  simpa [innerRoot] using hinnerRootComponent

/-- Every named inner degree-one stub lies outside the selected component. -/
theorem innerStub_not_mem_component
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (inner : Fin 5) :
    data.innerStub inner ∉ component.supp := by
  simpa using cycle.innerHole_vertex_not_mem_component component hroot
    (innerBoundaryDart data web.boundary_wellFormed inner)
    (innerBoundaryDart_on_innerHole web.annular web.boundary_wellFormed inner)

/-- The boundary-free selected component is locally cubic.  With at most four
outgoing selected crossings, an acyclic component has at most two vertices. -/
theorem hasCycleOnSide_or_component_card_le_two
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
      Nat.card {vertex : V // vertex ∈ component.supp} ≤ 2 := by
  classical
  let side : V → Prop := fun vertex => vertex ∈ component.supp
  let exception : V → Prop := fun _ => False
  letI componentFintype : Fintype {vertex : V // side vertex} :=
    Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
  have hdegreeThree :
      ∀ vertex, side vertex → ¬ exception vertex → G.degree vertex = 3 := by
    intro vertex hvertex _
    have hcubic := web.boundary_wellFormed.cubic_elsewhere vertex
      (by
        intro inner heq
        subst vertex
        exact (cycle.innerStub_not_mem_component component hroot inner) hvertex)
      (by
        intro outer heq
        subst vertex
        exact (cycle.outerStub_not_mem_component component hroot outer) hvertex)
    convert
      (GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
        (G := G) vertex).symm.trans hcubic using 1
  rcases hasCycleOnSide_or_card_le_two_mul_exception_add_removed_sub_two
      side exception
      (by intro _ _ hfalse; exact False.elim hfalse)
      hdegreeThree
      (connected_induce_component cycle.selectedCycle.crossingEdges component)
      cycle.selectedCycle.crossingEdges
      (by
        intro dart
        apply edge_mem_removed_of_crosses_component
          cycle.selectedCycle.crossingEdges component
        exact ⟨dart.1.fst, dart.1.snd,
          (by change dart.1.fst ∈ s(dart.1.fst, dart.1.snd); simp),
          (by change dart.1.snd ∈ s(dart.1.fst, dart.1.snd); simp),
          dart.2.1, dart.2.2⟩) with hcycle | hcard
  · exact .inl hcycle
  · right
    rw [Nat.card_eq_fintype_card]
    have hsideCardEq :
        Fintype.card {vertex : V // side vertex} =
          Fintype.card {vertex : V // vertex ∈ component.supp} :=
      Fintype.card_congr (Equiv.refl _)
    simp only [exception, Finset.filter_false, Finset.card_empty,
      Nat.mul_zero, zero_add] at hcard
    rw [← hsideCardEq]
    rcases cycle.crossingEdges_card_eq_three_or_four with hthree | hfour
    · omega
    · omega

/-- The bounded acyclic branch is exactly one vertex or exactly one edge's
two endpoints; nonemptiness of a deletion component excludes cardinality
zero. -/
theorem hasCycleOnSide_or_component_card_eq_one_or_two
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
      Nat.card {vertex : V // vertex ∈ component.supp} = 1 ∨
      Nat.card {vertex : V // vertex ∈ component.supp} = 2 := by
  rcases cycle.hasCycleOnSide_or_component_card_le_two component hroot with
    hcycle | hcard
  · exact .inl hcycle
  · right
    letI : Nonempty {vertex : V // vertex ∈ component.supp} :=
      ⟨⟨component.nonempty_supp.choose,
        component.nonempty_supp.choose_spec⟩⟩
    have hpositive :
        0 < Nat.card {vertex : V // vertex ∈ component.supp} := Nat.card_pos
    omega

/-- In the acyclic branch the exact selected boundary has cardinality two
more than the locally cubic deletion component.  Thus the three- and
four-edge cases cannot be interchanged: a selected triangle surrounds one
vertex, while a selected quadrilateral surrounds two. -/
theorem component_card_add_two_eq_crossingEdges_card_of_not_hasCycleOnSide
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hnoCycle :
      ¬ HasCycleOnSide G (fun vertex => vertex ∈ component.supp)) :
    Nat.card {vertex : V // vertex ∈ component.supp} + 2 =
      cycle.selectedCycle.crossingEdges.card := by
  classical
  let side : V → Prop := fun vertex => vertex ∈ component.supp
  let sideFintype : Fintype {vertex : V // side vertex} :=
    Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
  letI sideSubtypeFintype : Fintype {vertex : V // side vertex} :=
    sideFintype
  letI sideSetFintype : Fintype ↑({vertex | side vertex} : Set V) :=
    sideFintype
  have hdegree : ∀ vertex, side vertex → G.degree vertex = 3 := by
    intro vertex hvertex
    have hcubic := web.boundary_wellFormed.cubic_elsewhere vertex
      (by
        intro inner heq
        subst vertex
        exact (cycle.innerStub_not_mem_component component hroot inner) hvertex)
      (by
        intro outer heq
        subst vertex
        exact (cycle.outerStub_not_mem_component component hroot outer) hvertex)
    convert
      (GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
        (G := G) vertex).symm.trans hcubic using 1
  have hacyclic : (G.induce {vertex | side vertex}).IsAcyclic := by
    intro vertex walk hwalk
    apply hnoCycle
    let inclusion :=
      (SimpleGraph.Embedding.induce (G := G) {vertex | side vertex}).toHom
    refine ⟨vertex.1, vertex.2, walk.map inclusion, ?_, ?_⟩
    · exact hwalk.map (fun _ _ heq => Subtype.ext heq)
    · intro other hother
      have hother' : other ∈ walk.support.map inclusion := by
        exact SimpleGraph.Walk.support_map inclusion walk ▸ hother
      rcases List.mem_map.mp hother' with ⟨source, _hsource, hsource⟩
      rw [← hsource]
      exact source.2
  have htree : (G.induce {vertex | side vertex}).IsTree :=
    ⟨connected_induce_component cycle.selectedCycle.crossingEdges component,
      hacyclic⟩
  have htreeCard := htree.card_edgeFinset
  have hpartition := Fintype.card_congr
    (sideDartEquivInternalSumCrossing G side)
  rw [Fintype.card_sum] at hpartition
  have hsideCard := card_sideDart_eq_three_mul_of_local side hdegree
  have hinternalCard := card_internalSideDart_eq_twice_card_edges
    (G := G) side
  have hlocalBoundary :
      localCrossingEdgeFinset G side =
        cycle.selectedCycle.crossingEdges := by
    calc
      localCrossingEdgeFinset G side =
          componentCrossingEdges cycle.selectedCycle.crossingEdges component := by
        ext edge
        simp only [side, mem_localCrossingEdgeFinset_iff,
          mem_componentCrossingEdges_iff]
      _ = cycle.selectedCycle.crossingEdges :=
        cycle.componentCrossingEdges_eq_crossingEdges component hroot
  have hcrossingCard :
      Fintype.card (CrossingSideDart G side) =
        cycle.selectedCycle.crossingEdges.card := by
    rw [← card_localCrossingEdgeFinset_eq_crossingSideDart,
      hlocalBoundary]
  have hsameSideCard :
      Fintype.card ↑({vertex | side vertex} : Set V) =
        Fintype.card {vertex : V // side vertex} := by
    rfl
  have hnatCard :
      Nat.card {vertex : V // side vertex} =
        Fintype.card {vertex : V // side vertex} := Nat.card_eq_fintype_card
  change Nat.card {vertex : V // side vertex} + 2 = _
  omega

/-- Exact finite classification of the non-cyclic branch: the selected
three-edge boundary encloses one vertex, and the selected four-edge boundary
encloses two. -/
theorem hasCycleOnSide_or_component_star_or_bond
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
      (Nat.card {vertex : V // vertex ∈ component.supp} = 1 ∧
        cycle.selectedCycle.crossingEdges.card = 3) ∨
      (Nat.card {vertex : V // vertex ∈ component.supp} = 2 ∧
        cycle.selectedCycle.crossingEdges.card = 4) := by
  by_cases hcycle :
      HasCycleOnSide G (fun vertex => vertex ∈ component.supp)
  · exact .inl hcycle
  · right
    have hexact :=
      cycle.component_card_add_two_eq_crossingEdges_card_of_not_hasCycleOnSide
        component hroot hcycle
    rcases cycle.hasCycleOnSide_or_component_card_eq_one_or_two component hroot with
      hcycle' | hone | htwo
    · exact False.elim (hcycle hcycle')
    · exact .inl ⟨hone, by omega⟩
    · exact .inr ⟨htwo, by omega⟩

/-- A singleton acyclic component is a literal star centre: every selected
crossing is incident to its unique vertex. -/
theorem exists_vertex_mem_all_crossingEdges_of_component_card_eq_one
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hcard : Nat.card {vertex : V // vertex ∈ component.supp} = 1) :
    ∃ vertex : V, vertex ∈ component.supp ∧
      ∀ edge ∈ cycle.selectedCycle.crossingEdges, vertex ∈ edge.1 := by
  classical
  letI componentFintype :
      Fintype {vertex : V // vertex ∈ component.supp} :=
    Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
  have hcardFintype :
      Fintype.card {vertex : V // vertex ∈ component.supp} = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  let vertex : V := component.nonempty_supp.choose
  have hvertex : vertex ∈ component.supp := component.nonempty_supp.choose_spec
  have hunique : ∀ first second :
      {candidate : V // candidate ∈ component.supp}, first = second := by
    rcases Fintype.card_eq_one_iff.mp hcardFintype with ⟨witness, hall⟩
    intro first second
    exact (hall first).trans (hall second).symm
  refine ⟨vertex, hvertex, ?_⟩
  intro edge hedge
  have hboundary : edge ∈ componentCrossingEdges
      cycle.selectedCycle.crossingEdges component := by
    rw [cycle.componentCrossingEdges_eq_crossingEdges component hroot]
    exact hedge
  rcases (mem_componentCrossingEdges_iff
      cycle.selectedCycle.crossingEdges component edge).1 hboundary with
    ⟨inside, outside, hinsideEdge, _houtsideEdge, hinside, _houtside⟩
  have heq : inside = vertex := congrArg Subtype.val
    (hunique ⟨inside, hinside⟩ ⟨vertex, hvertex⟩)
  simpa only [heq] using hinsideEdge

/-- An exact selected triangle either encloses a cyclic side or a literal
single star centre incident to every selected crossing.  The two-vertex bond
branch is impossible because its selected boundary has four edges. -/
theorem hasCycleOnSide_or_exists_vertex_mem_all_crossingEdges_of_card_eq_three
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hthree : cycle.selectedCycle.crossingEdges.card = 3) :
    HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
      ∃ vertex : V, vertex ∈ component.supp ∧
        ∀ edge ∈ cycle.selectedCycle.crossingEdges, vertex ∈ edge.1 := by
  rcases cycle.hasCycleOnSide_or_component_star_or_bond component hroot with
    hcycle | hstar | hbond
  · exact .inl hcycle
  · exact .inr
      (cycle.exists_vertex_mem_all_crossingEdges_of_component_card_eq_one
        component hroot hstar.1)
  · omega

/-- Choose the component away from the outer root for an exact selected
triangle and classify it as cyclic or a literal single star centre. -/
theorem exists_component_cycle_or_star_of_length_eq_three
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (hlength : cycle.walk.length = 3) :
    ∃ component :
        (G.deleteEdges (edgeFinsetValueSet
          cycle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ component.supp ∧
        (HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
          ∃ vertex : V, vertex ∈ component.supp ∧
            ∀ edge ∈ cycle.selectedCycle.crossingEdges,
              vertex ∈ edge.1) := by
  rcases cycle.exists_component_away_from_outerRoot with ⟨component, hroot⟩
  refine ⟨component, hroot, ?_⟩
  apply cycle.hasCycleOnSide_or_exists_vertex_mem_all_crossingEdges_of_card_eq_three
    component hroot
  rw [cycle.crossingEdges_card_eq_length]
  exact hlength

/-- A two-vertex deletion component consists of a unique adjacent pair in
the ambient graph. -/
theorem exists_adjacent_pair_of_component_card_eq_two
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hcard : Nat.card {vertex : V // vertex ∈ component.supp} = 2) :
    ∃ first second : V,
      first ≠ second ∧ component.supp = {first, second} ∧
        G.Adj first second := by
  classical
  have hsuppCard : component.supp.ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  rcases Set.ncard_eq_two.mp hsuppCard with
    ⟨first, second, hfirstSecond, hsupp⟩
  have hfirstMem : first ∈ component.supp := by
    rw [hsupp]
    simp
  have hsecondMem : second ∈ component.supp := by
    rw [hsupp]
    simp
  let firstVertex : component.supp := ⟨first, hfirstMem⟩
  let secondVertex : component.supp := ⟨second, hsecondMem⟩
  have hverticesNe : firstVertex ≠ secondVertex := by
    intro heq
    exact hfirstSecond (congrArg Subtype.val heq)
  have hconnected := connected_induce_component
    cycle.selectedCycle.crossingEdges component
  rcases hconnected.exists_isPath firstVertex secondVertex with
    ⟨path, hpath⟩
  letI componentFintype : Fintype component.supp :=
    Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
  have hsubtypeCard : Fintype.card component.supp = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hlengthLt : path.length < 2 := by
    simpa [hsubtypeCard] using hpath.length_lt
  have hlengthPositive : 0 < path.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hverticesNe (path.eq_of_length_eq_zero hzero)
  have hlength : path.length = 1 := by omega
  have hadj : (G.induce component.supp).Adj firstVertex secondVertex :=
    path.adj_of_length_eq_one hlength
  exact ⟨first, second, hfirstSecond, hsupp, hadj⟩

/-- In the two-vertex branch every selected crossing is attached to one of
the two endpoints of the component's unique internal bond. -/
theorem exists_adjacent_pair_covering_crossingEdges_of_component_card_eq_two
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hcard : Nat.card {vertex : V // vertex ∈ component.supp} = 2) :
    ∃ first second : V,
      first ≠ second ∧ component.supp = {first, second} ∧
        G.Adj first second ∧
        ∀ edge ∈ cycle.selectedCycle.crossingEdges,
          first ∈ edge.1 ∨ second ∈ edge.1 := by
  classical
  obtain ⟨first, second, hne, hsupp, hadj⟩ :=
    cycle.exists_adjacent_pair_of_component_card_eq_two component hcard
  refine ⟨first, second, hne, hsupp, hadj, ?_⟩
  intro edge hedge
  have hboundary : edge ∈ componentCrossingEdges
      cycle.selectedCycle.crossingEdges component := by
    rw [cycle.componentCrossingEdges_eq_crossingEdges component hroot]
    exact hedge
  rcases (mem_componentCrossingEdges_iff
      cycle.selectedCycle.crossingEdges component edge).1 hboundary with
    ⟨inside, outside, hinsideEdge, _houtsideEdge, hinside, _houtside⟩
  have hinsidePair : inside = first ∨ inside = second := by
    rw [hsupp] at hinside
    simpa using hinside
  rcases hinsidePair with rfl | rfl
  · exact .inl hinsideEdge
  · exact .inr hinsideEdge

/-- In the singleton branch the unique star centre is incident to the literal
source rung retained by the short-cycle constructor. -/
theorem exists_vertex_mem_anchorEdge_of_component_card_eq_one
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hcard : Nat.card {vertex : V // vertex ∈ component.supp} = 1) :
    ∃ vertex : V, vertex ∈ component.supp ∧ vertex ∈ cycle.anchorEdge.1 := by
  obtain ⟨vertex, hvertex, hall⟩ :=
    cycle.exists_vertex_mem_all_crossingEdges_of_component_card_eq_one
      component hroot hcard
  exact ⟨vertex, hvertex, hall cycle.anchorEdge cycle.anchorEdge_mem_crossingEdges⟩

/-- In the two-vertex branch at least one endpoint of the unique internal bond
is incident to the literal source rung retained by the short-cycle
constructor. -/
theorem exists_adjacent_pair_meeting_anchorEdge_of_component_card_eq_two
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hcard : Nat.card {vertex : V // vertex ∈ component.supp} = 2) :
    ∃ first second : V,
      first ≠ second ∧ component.supp = {first, second} ∧
        G.Adj first second ∧
        (first ∈ cycle.anchorEdge.1 ∨ second ∈ cycle.anchorEdge.1) := by
  obtain ⟨first, second, hne, hsupp, hadj, hall⟩ :=
    cycle.exists_adjacent_pair_covering_crossingEdges_of_component_card_eq_two
      component hroot hcard
  exact ⟨first, second, hne, hsupp, hadj,
    hall cycle.anchorEdge cycle.anchorEdge_mem_crossingEdges⟩

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
