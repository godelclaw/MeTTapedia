import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebHoleBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebFiniteCutRadialEscape
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24CubicSmallBoundaryCycle
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceWalk

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
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceWalk
open GoertzelV24SelectedDualCycleSeparator
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

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
