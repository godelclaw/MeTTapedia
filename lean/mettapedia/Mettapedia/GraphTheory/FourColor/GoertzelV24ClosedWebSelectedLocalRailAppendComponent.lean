import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebHoleBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppendSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceWalk

/-!
# The outer-remote component of a selected append triangle

The adjacent selected-rail obstruction now has an exact finite three-edge
deletion support.  This module chooses a genuine deletion component away from
the distinguished outer-hole dart and proves that every outer interface stub
is also outside that component.  The proof follows the literal outer face
orbit and uses the selected crossing-edge hole-safety theorem.

This is an L1 component classification, not yet the cubic degree count.  It
does not put the five inner stubs on the outer side, prove boundary saturation,
or promote the separator to a cyclic three-edge cut.  Those are separate
source-local obligations and are not assumed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebHoleBoundaryOrder
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceWalk
open GoertzelV24SelectedDualCycleSeparator
open SimpleGraph
open SimpleGraphDartRotation

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

end SeparatedSelectedSourceLocalRailSuccessor.AdjacentDualTriangle

end Instance.SelectedLocalLayerFormation

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
