import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementComponent

/-!
# L1: exact bond carried by an acyclic replacement square

A four-step middle-replacement dual cycle has four selected primal crossing
edges.  The locally cubic component count therefore rules out the singleton
star branch: away from the two annular boundaries, an acyclic side is exactly
two adjacent vertices, and those vertices meet every selected crossing.

This identifies the complete graph-level residue of the square branch.  It
does not identify the facial-dual four-cycle with a primal facial square,
invoke the source's square reduction, reroute the rail pair, attach end caps,
or close Fable flag L1.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteDeletionCyclicCut

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring}

private abbrev SelectedFace :=
  AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS))

namespace MiddleReplacementShortDualCycle

variable {face : SelectedFace (web := web)}

/-- The complete two-vertex realization of an acyclic four-edge replacement
separator. -/
structure SquareBondRealization
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent) where
  first : V
  second : V
  first_ne_second : first ≠ second
  component_supp : component.supp = {first, second}
  adjacent : G.Adj first second
  covers_crossingEdges : ∀ edge ∈ cycle.selectedCycle.crossingEdges,
    first ∈ edge.1 ∨ second ∈ edge.1

/-- The retained literal source rung is incident to one endpoint of the
two-vertex bond. -/
theorem SquareBondRealization.anchorEdge_meets_endpoint
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component) :
    bond.first ∈ cycle.anchorEdge.1 ∨ bond.second ∈ cycle.anchorEdge.1 := by
  exact bond.covers_crossingEdges cycle.anchorEdge
    cycle.anchorEdge_mem_crossingEdges

/-- **L1 square residue classification.** A literal four-step replacement
cycle has either a cyclic component on the selected remote side or a
constructed two-vertex bond carrying all four crossings. -/
theorem hasCycleOnSide_or_squareBond
    (cycle : MiddleReplacementShortDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp)
    (hlength : cycle.walk.length = 4) :
    HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
      Nonempty (SquareBondRealization cycle component) := by
  rcases cycle.hasCycleOnSide_or_component_star_or_bond component hroot with
    hcycle | hstar | hbond
  · exact .inl hcycle
  · have hcrossing : cycle.selectedCycle.crossingEdges.card = 4 := by
      rw [cycle.crossingEdges_card_eq_length, hlength]
    exact False.elim (by omega)
  · obtain ⟨first, second, hne, hsupp, hadj, hcover⟩ :=
      cycle.exists_adjacent_pair_covering_crossingEdges_of_component_card_eq_two
        component hroot hbond.1
    exact .inr ⟨{
      first := first
      second := second
      first_ne_second := hne
      component_supp := hsupp
      adjacent := hadj
      covers_crossingEdges := hcover
    }⟩

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
