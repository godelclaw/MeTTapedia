import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebHoleBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFiniteCutRadialEscape
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalCommonNeighborIncidence
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicSmallBoundaryCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceWalk

/-!
# The outer-remote component of a selected append triangle

The adjacent selected-rail obstruction now has an exact finite three-edge
deletion support.  This module chooses a genuine deletion component away from
the distinguished outer-hole dart and proves that every outer interface stub
is also outside that component.  The proof follows the literal outer face
orbit and uses the selected crossing-edge hole-safety theorem.

This is an L1 component classification, not the completed crosscut
construction.  It excludes all ten boundary stubs, proves the local
cyclic-or-singleton degree dichotomy, saturates the boundary in the singleton
case, and then eliminates that case using the literal outgoing-rung anchor and
the pointwise local incidence theorem.  The surviving component therefore
contains a cycle.  The module does not manufacture a complementary-side cycle
or transport closed minimality to the opened carrier; those remain the honest
cyclic-branch formation obligation.
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
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceWalk
open GoertzelV24SelectedDualCycleSeparator
open SimpleGraph
open SimpleGraphDartRotation
open Instance.LocalLayerFormation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance selectedAppendComponentEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance.SelectedLocalLayerFormation

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

namespace SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle

variable
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}
    {successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement}

/-- The separator theorem re-presented on the finite crossing-edge support
consumed by the deletion-component API. -/
theorem not_connected_deleteEdges_crossingEdges
    (triangle : AdjacentDualTriangle successor) :
    ¬ (G.deleteEdges (edgeFinsetValueSet
      triangle.selectedCycle.crossingEdges)).Connected := by
  rw [← triangle.selectedCycle.primalCut_eq_edgeFinsetValueSet_crossingEdges]
  exact triangle.not_connected_deleteEdges_primalCut

/-- There is a literal deletion component on the side opposite the
distinguished outer-hole dart. -/
theorem exists_component_away_from_outerRoot
    (triangle : AdjacentDualTriangle successor) :
    ∃ component :
        (G.deleteEdges (edgeFinsetValueSet
          triangle.selectedCycle.crossingEdges)).ConnectedComponent,
      web.annular.RS.outer.fst ∉ component.supp := by
  exact exists_component_not_mem_root_of_not_connected
    triangle.selectedCycle.crossingEdges web.annular.RS.outer.fst
    triangle.not_connected_deleteEdges_crossingEdges

/-- Any component away from the distinguished outer dart is away from every
dart on the whole outer-hole face. -/
theorem outerHole_vertex_not_mem_component
    (triangle : AdjacentDualTriangle successor)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        triangle.selectedCycle.crossingEdges)).ConnectedComponent)
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
          triangle.selectedCycle.crossingEdges := by
    intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      triangle.selectedCycle.crossingEdges edge.1).1 hvalue with
      ⟨crossing, hcrossing, hcrossingValue⟩
    have hedgeBoundary := hwalkBoundary edge hedge
    rw [web.annular.outer_dart_on_outerHole] at hedgeBoundary
    have hedgeCrossing : edge ∈ triangle.selectedCycle.crossingEdges := by
      simpa [Subtype.ext hcrossingValue] using hcrossing
    exact (Finset.disjoint_left.mp
      triangle.crossingEdges_disjoint_outerHoleBoundary)
        hedgeCrossing hedgeBoundary
  have hside := component_side_iff_of_mem_walk_support_of_avoiding_removed
    triangle.selectedCycle.crossingEdges component walk hwalkAvoid hdartSupport
  intro hdartComponent
  exact hroot (hside.mpr hdartComponent)

/-- In particular every named outer degree-one stub lies outside the selected
outer-remote component. -/
theorem outerStub_not_mem_component
    (triangle : AdjacentDualTriangle successor)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        triangle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (outer : Fin 5) :
    data.outerStub outer ∉ component.supp := by
  simpa using triangle.outerHole_vertex_not_mem_component component hroot
    (outerBoundaryDart data web.boundary_wellFormed outer)
    (outerBoundaryDart_on_outerHole web.annular web.boundary_wellFormed outer)

/-- The source's finite radial-escape count applies directly to the selected
triangle: its three crossing edges cannot meet all twenty oriented inner
incidences. -/
theorem exists_radialPath_avoiding_crossingEdges
    (triangle : AdjacentDualTriangle successor) :
    ∃ endpoint : InnerEnd data coloring,
      ∀ edge : G.edgeSet,
        edge.1 ∈ (ambientRadialPath
          (radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
            (everyColorPairComponentInnerTouching_of_totallyClosed
              data web.boundary_wellFormed web.connected coloring web.tait
                web.totallyClosed)
            endpoint)).edges →
          edge ∉ triangle.selectedCycle.crossingEdges := by
  apply exists_radialPathOfInnerEnd_avoiding_finiteCut (web := web)
  rw [triangle.crossingEdges_card_eq_three]
  omega

/-- Any component away from the outer hole is also away from every vertex on
the inner-hole face.  A counted radial escape first puts one inner stub on the
outer side; the complete rooted inner-face walk then propagates that side to
the requested dart. -/
theorem innerHole_vertex_not_mem_component
    (triangle : AdjacentDualTriangle successor)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        triangle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (dart : G.Dart)
    (hdart : dartOrbitFace web.annular.RS dart =
      web.annular.cellulation.innerHole) :
    dart.fst ∉ component.supp := by
  obtain ⟨endpoint, havoids⟩ :=
    triangle.exists_radialPath_avoiding_crossingEdges
  let hinnerTouching : EveryColorPairComponentInnerTouching data coloring :=
    everyColorPairComponentInnerTouching_of_totallyClosed
      data web.boundary_wellFormed web.connected coloring web.tait web.totallyClosed
  let radial := radialPathOfInnerEnd data web.boundary_wellFormed coloring web.tait
    hinnerTouching endpoint
  have hradialAvoid : ∀ edge : G.edgeSet,
      (edge : Sym2 V) ∈ (ambientRadialPath radial).edges →
        edge.1 ∉ edgeFinsetValueSet
          triangle.selectedCycle.crossingEdges := by
    intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      triangle.selectedCycle.crossingEdges edge.1).1 hvalue with
      ⟨crossing, hcrossing, hcrossingValue⟩
    apply havoids crossing
    · rw [hcrossingValue]
      exact hedge
    · exact hcrossing
  have hradialSide := component_side_iff_of_walk_avoiding_removed
    triangle.selectedCycle.crossingEdges component
      (ambientRadialPath radial) hradialAvoid
  have hselectedInner : data.innerStub radial.inner ∉ component.supp := by
    intro hinner
    have hstart : radial.start.1 ∈ component.supp := by
      rw [radial.start_eq_innerStub]
      exact hinner
    have hfinish : radial.finish.1 ∈ component.supp := hradialSide.mp hstart
    apply triangle.outerStub_not_mem_component component hroot radial.outer
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
          triangle.selectedCycle.crossingEdges := by
    intro edge hedge hvalue
    rcases (mem_edgeFinsetValueSet_iff
      triangle.selectedCycle.crossingEdges edge.1).1 hvalue with
      ⟨crossing, hcrossing, hcrossingValue⟩
    have hedgeBoundary := hwalkBoundary edge hedge
    rw [hinnerRootFace] at hedgeBoundary
    have hedgeCrossing : edge ∈ triangle.selectedCycle.crossingEdges := by
      simpa [Subtype.ext hcrossingValue] using hcrossing
    exact (Finset.disjoint_left.mp
      triangle.crossingEdges_disjoint_innerHoleBoundary)
        hedgeCrossing hedgeBoundary
  have hside := component_side_iff_of_mem_walk_support_of_avoiding_removed
    triangle.selectedCycle.crossingEdges component walk hwalkAvoid hdartSupport
  intro hdartComponent
  apply hselectedInner
  have hinnerRootComponent : innerRoot.fst ∈ component.supp :=
    hside.mpr hdartComponent
  simpa [innerRoot] using hinnerRootComponent

/-- In particular every named inner degree-one stub lies outside the selected
outer-remote component. -/
theorem innerStub_not_mem_component
    (triangle : AdjacentDualTriangle successor)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        triangle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (inner : Fin 5) :
    data.innerStub inner ∉ component.supp := by
  simpa using triangle.innerHole_vertex_not_mem_component component hroot
    (innerBoundaryDart data web.boundary_wellFormed inner)
    (innerBoundaryDart_on_innerHole web.annular web.boundary_wellFormed inner)

/-- The exact local degree count on a boundary-free deletion component.  The
selected component is connected in the ambient graph, all of its vertices are
cubic because all ten degree-one stubs are excluded, and every outgoing dart
uses one of the three deleted edges.  Hence the component either contains a
cycle or consists of exactly one vertex. -/
theorem hasCycleOnSide_or_component_card_eq_one
    (triangle : AdjacentDualTriangle successor)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        triangle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
      Fintype.card {vertex : V // vertex ∈ component.supp} = 1 := by
  classical
  letI componentFintype : Fintype {vertex : V // vertex ∈ component.supp} :=
    Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
  apply
    hasCycleOnSide_or_card_eq_one_of_local_cubic_of_connected_induce_of_crossing_le_three
      (fun vertex => vertex ∈ component.supp)
  · intro vertex hvertex
    have hcubic := web.boundary_wellFormed.cubic_elsewhere vertex
      (by
        intro inner heq
        subst vertex
        exact (triangle.innerStub_not_mem_component component hroot inner) hvertex)
      (by
        intro outer heq
        subst vertex
        exact (triangle.outerStub_not_mem_component component hroot outer) hvertex)
    convert
      (GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
        (G := G) vertex).symm.trans hcubic using 1
    apply GoertzelV24CubicSmallBoundaryCycle.degree_instance_independent
  · exact component.nonempty_supp
  · exact connected_induce_component
      triangle.selectedCycle.crossingEdges component
  · rw [triangle.crossingEdges_card_eq_three]
  · intro dart
    apply edge_mem_removed_of_crosses_component
      triangle.selectedCycle.crossingEdges component
    exact ⟨dart.1.fst, dart.1.snd,
      (by
        change dart.1.fst ∈ s(dart.1.fst, dart.1.snd)
        simp),
      (by
        change dart.1.snd ∈ s(dart.1.fst, dart.1.snd)
        simp),
      dart.2.1, dart.2.2⟩

/-- A singleton selected deletion component sees all three selected
crossings.  Its unique vertex is locally cubic because the component avoids
the ten boundary stubs.  Thus its three outgoing darts inject into the
computed component boundary; that boundary is already a subset of the three
selected crossings, so both finite sets have cardinality three and coincide.
-/
theorem componentCrossingEdges_eq_crossingEdges_of_component_card_eq_one
    (triangle : AdjacentDualTriangle successor)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        triangle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hcard : Fintype.card {vertex : V // vertex ∈ component.supp} = 1) :
    componentCrossingEdges triangle.selectedCycle.crossingEdges component =
      triangle.selectedCycle.crossingEdges := by
  classical
  let side : V → Prop := fun vertex => vertex ∈ component.supp
  letI componentFintype : Fintype {vertex : V // side vertex} :=
    Fintype.ofInjective (fun vertex => vertex.1) Subtype.val_injective
  have hunique : ∀ first second : {vertex : V // side vertex}, first = second := by
    rcases Fintype.card_eq_one_iff.mp hcard with ⟨witness, hall⟩
    intro first second
    exact (hall first).trans (hall second).symm
  have hdegree : ∀ vertex, side vertex → G.degree vertex = 3 := by
    intro vertex hvertex
    have hcubic := web.boundary_wellFormed.cubic_elsewhere vertex
      (by
        intro inner heq
        subst vertex
        exact (triangle.innerStub_not_mem_component component hroot inner) hvertex)
      (by
        intro outer heq
        subst vertex
        exact (triangle.outerStub_not_mem_component component hroot outer) hvertex)
    convert
      (GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
        (G := G) vertex).symm.trans hcubic using 1
    apply GoertzelV24CubicSmallBoundaryCycle.degree_instance_independent
  letI internalEmpty : IsEmpty (InternalSideDart G side) :=
    ⟨fun dart => dart.1.adj.ne (congrArg Subtype.val
      (hunique ⟨dart.1.fst, dart.2.1⟩ ⟨dart.1.snd, dart.2.2⟩))⟩
  have hsideCard := card_sideDart_eq_three_mul_of_local side hdegree
  have hpartition := Fintype.card_congr
    (sideDartEquivInternalSumCrossing G side)
  have hinternalCard : Fintype.card (InternalSideDart G side) = 0 :=
    Fintype.card_eq_zero
  rw [Fintype.card_sum, hinternalCard] at hpartition
  have hsideOne : Fintype.card {vertex : V // side vertex} = 1 := hcard
  have hcrossingCard : Fintype.card (CrossingSideDart G side) = 3 := by
    omega
  let toBoundary : CrossingSideDart G side →
      {edge // edge ∈ componentCrossingEdges
        triangle.selectedCycle.crossingEdges component} := fun dart =>
    ⟨⟨dart.1.edge, dart.1.edge_mem⟩,
      (mem_componentCrossingEdges_iff
        triangle.selectedCycle.crossingEdges component _).2
        ⟨dart.1.fst, dart.1.snd,
          (by change dart.1.fst ∈ s(dart.1.fst, dart.1.snd); simp),
          (by change dart.1.snd ∈ s(dart.1.fst, dart.1.snd); simp),
          dart.2.1, dart.2.2⟩⟩
  have htoBoundaryInjective : Function.Injective toBoundary := by
    intro first second heq
    apply crossingSideDart_edge_injective side
    exact congrArg Subtype.val heq
  have hboundaryLower : 3 ≤
      (componentCrossingEdges
        triangle.selectedCycle.crossingEdges component).card := by
    rw [← hcrossingCard]
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective toBoundary htoBoundaryInjective
  have hboundaryUpper :
      (componentCrossingEdges
        triangle.selectedCycle.crossingEdges component).card ≤ 3 := by
    calc
      _ ≤ triangle.selectedCycle.crossingEdges.card :=
        card_componentCrossingEdges_le_removed
          triangle.selectedCycle.crossingEdges component
      _ = 3 := triangle.crossingEdges_card_eq_three
  apply Finset.eq_of_subset_of_card_le
    (componentCrossingEdges_subset_removed
      triangle.selectedCycle.crossingEdges component)
  rw [triangle.crossingEdges_card_eq_three]
  exact hboundaryLower

/-- The singleton component has one ambient vertex incident to every selected
triangle crossing.  This is the incidence form consumed by the local rail
append repair. -/
theorem exists_vertex_mem_all_crossingEdges_of_component_card_eq_one
    (triangle : AdjacentDualTriangle successor)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        triangle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hcard : Fintype.card {vertex : V // vertex ∈ component.supp} = 1) :
    ∃ vertex : V, ∀ edge ∈ triangle.selectedCycle.crossingEdges,
      vertex ∈ edge.1 := by
  classical
  let vertex : V := component.nonempty_supp.choose
  have hvertex : vertex ∈ component.supp := component.nonempty_supp.choose_spec
  have hunique : ∀ first second : {candidate : V // candidate ∈ component.supp},
      first = second := by
    rcases Fintype.card_eq_one_iff.mp hcard with ⟨witness, hall⟩
    intro first second
    exact (hall first).trans (hall second).symm
  refine ⟨vertex, ?_⟩
  intro edge hedge
  have hboundary : edge ∈ componentCrossingEdges
      triangle.selectedCycle.crossingEdges component := by
    rw [triangle.componentCrossingEdges_eq_crossingEdges_of_component_card_eq_one
      component hroot hcard]
    exact hedge
  rcases (mem_componentCrossingEdges_iff
      triangle.selectedCycle.crossingEdges component edge).1 hboundary with
    ⟨inside, outside, hinsideEdge, _houtsideEdge, hinside, _houtside⟩
  have heq : inside = vertex := congrArg Subtype.val
    (hunique ⟨inside, hinside⟩ ⟨vertex, hvertex⟩)
  simpa only [heq] using hinsideEdge

/-- The selected obstruction component cannot be a singleton.  Boundary
saturation gives one vertex incident to both the literal outgoing rung and
the selected crossing from the third face back to the left centre.  The
pointwise local cubic incidence theorem then classifies the third face as one
of the two named flanks, contradicting the obstruction witness. -/
theorem component_card_ne_one
    (triangle : AdjacentDualTriangle successor)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        triangle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    Fintype.card {vertex : V // vertex ∈ component.supp} ≠ 1 := by
  intro hcard
  obtain ⟨vertex, hvertex⟩ :=
    triangle.exists_vertex_mem_all_crossingEdges_of_component_card_eq_one
      component hroot hcard
  let targetEdge := triangle.selectedCycle.crossingEdge triangle.lastStep
  have htargetSelected : targetEdge ∈
      triangle.selectedCycle.crossingEdges := by
    exact (SelectedDualCycle.mem_crossingEdges_iff
      triangle.selectedCycle targetEdge).2 ⟨triangle.lastStep, rfl⟩
  have houtgoingSelected : rungs.edge leftInterior.outgoing ∈
      triangle.selectedCycle.crossingEdges := by
    exact (SelectedDualCycle.mem_crossingEdges_iff
      triangle.selectedCycle (rungs.edge leftInterior.outgoing)).2
        ⟨triangle.firstStep, triangle.selectedCycle_crossingEdge_zero⟩
  have htargetCenter : targetEdge ∈ orbitFaceBoundary web.annular.RS
      ((corridor.toCleanOrbitHexCorridorSkeleton
        |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center).1 := by
    simpa [targetEdge] using
      triangle.selectedCycle.crossingEdge_mem_rightFace triangle.lastStep
  have htargetThird : targetEdge ∈
      orbitFaceBoundary web.annular.RS triangle.third.1 := by
    simpa [targetEdge] using
      triangle.selectedCycle.crossingEdge_mem_leftFace triangle.lastStep
  have hvertexOutgoing : vertex ∈ web.annular.RS.endpoints
      (web.annular.RS.edgeOf (faceCycleDart web.annular.RS
        leftPlacement.root leftPlacement.outgoingPosition)) := by
    apply (GoertzelV24RotationVertexCutProfile.mem_simpleGraphRotationSystem_endpoints_iff
      web.annular.cellulation.rotation _ vertex).2
    change vertex ∈ (faceCycleEdge web.annular.RS leftPlacement.root
      leftPlacement.outgoingPosition : G.edgeSet).1
    rw [leftPlacement.outgoing_edge]
    exact hvertex _ houtgoingSelected
  have hvertexTarget : vertex ∈ web.annular.RS.endpoints targetEdge := by
    apply (GoertzelV24RotationVertexCutProfile.mem_simpleGraphRotationSystem_endpoints_iff
      web.annular.cellulation.rotation targetEdge vertex).2
    exact hvertex _ htargetSelected
  have hincidence : successor.CommonNeighborVertexIncidenceAt triangle.third
      triangle.leftCenter_adj_third triangle.rightCenter_adj_third :=
    ⟨targetEdge, htargetCenter, htargetThird, vertex,
      hvertexOutgoing, hvertexTarget⟩
  rcases successor.face_eq_before_or_after_of_commonNeighborVertexIncidenceAt
      triangle.third triangle.leftCenter_adj_third
        triangle.rightCenter_adj_third hincidence with hbefore | hafter
  · exact triangle.third_ne_before hbefore
  · exact triangle.third_ne_after hafter

/-- Therefore the selected outer-remote component of every obstruction
triangle lies on the cyclic branch of the local degree classification.  This
does not yet provide a complementary-side cycle or transport closed
minimality to the opened carrier. -/
theorem hasCycleOnSide
    (triangle : AdjacentDualTriangle successor)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        triangle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    HasCycleOnSide G (fun vertex => vertex ∈ component.supp) := by
  rcases triangle.hasCycleOnSide_or_component_card_eq_one component hroot with
    hcycle | hcard
  · exact hcycle
  · exact False.elim (triangle.component_card_ne_one component hroot hcard)

end SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
