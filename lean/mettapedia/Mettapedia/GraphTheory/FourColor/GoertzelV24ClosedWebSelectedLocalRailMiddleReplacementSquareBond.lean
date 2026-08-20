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
open GoertzelV24FramedLocalDualCycleBond

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

/-- The literal edge internal to the two-vertex square-bond side. -/
def SquareBondRealization.internalEdge
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component) : G.edgeSet :=
  ⟨s(bond.first, bond.second), (SimpleGraph.mem_edgeSet G).2 bond.adjacent⟩

/-- The selected four-edge boundary is exactly the local side boundary of
the realized adjacent pair. -/
theorem SquareBondRealization.crossingEdges_eq_localBoundary
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    cycle.selectedCycle.crossingEdges =
      localCrossingEdgeFinset G
        (fun vertex => vertex ∈ ({bond.first, bond.second} : Set V)) := by
  rw [← cycle.componentCrossingEdges_eq_crossingEdges component hroot]
  ext edge
  simp only [mem_componentCrossingEdges_iff,
    mem_localCrossingEdgeFinset_iff, bond.component_supp]

/-- The internal bond edge is not one of the four selected crossings. -/
theorem SquareBondRealization.internalEdge_not_mem_crossingEdges
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    bond.internalEdge ∉ cycle.selectedCycle.crossingEdges := by
  rw [bond.crossingEdges_eq_localBoundary hroot]
  intro hcrossing
  rcases (mem_localCrossingEdgeFinset_iff
      (fun vertex => vertex ∈ ({bond.first, bond.second} : Set V))
      bond.internalEdge).1 hcrossing with
    ⟨inside, outside, _hinsideEdge, houtsideEdge,
      _hinsideSide, houtsideSide⟩
  apply houtsideSide
  simpa [SquareBondRealization.internalEdge, Sym2.mem_iff] using houtsideEdge

/-- At the first endpoint, the four selected crossings are exactly the
incident edges other than the internal bond. -/
theorem SquareBondRealization.filter_incident_first_eq_erase_internalEdge
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    (incidentEdgeFinset G bond.first).filter
        (fun edge => edge ∈ cycle.selectedCycle.crossingEdges) =
      (incidentEdgeFinset G bond.first).erase bond.internalEdge := by
  classical
  rw [bond.crossingEdges_eq_localBoundary hroot]
  ext edge
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hincident, hcrossing⟩
    refine ⟨?_, hincident⟩
    intro hedge
    subst edge
    exact bond.internalEdge_not_mem_crossingEdges hroot (by
      rw [bond.crossingEdges_eq_localBoundary hroot]
      exact hcrossing)
  · rintro ⟨hedgeNe, hincident⟩
    refine ⟨hincident, ?_⟩
    have hfirstEdge : bond.first ∈ (edge.1 : Sym2 V) := by
      simpa [incidentEdgeFinset] using hincident
    rcases Sym2.mem_iff_exists.1 hfirstEdge with ⟨other, hedgeValue⟩
    have hfirstOther : G.Adj bond.first other := by
      rw [← SimpleGraph.mem_edgeSet G, ← hedgeValue]
      exact edge.2
    have hotherNeFirst : other ≠ bond.first := hfirstOther.ne.symm
    have hotherNeSecond : other ≠ bond.second := by
      intro hother
      subst other
      apply hedgeNe
      apply Subtype.ext
      simpa [SquareBondRealization.internalEdge] using hedgeValue
    apply (mem_localCrossingEdgeFinset_iff
      (fun vertex => vertex ∈ ({bond.first, bond.second} : Set V)) edge).2
    refine ⟨bond.first, other, hfirstEdge, ?_, by simp, ?_⟩
    · rw [hedgeValue]
      simp
    · simp [hotherNeFirst, hotherNeSecond]

/-- Local cubicity makes exactly two selected crossings incident to the first
endpoint of the square bond. -/
theorem SquareBondRealization.first_crossingEdges_card_eq_two
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    ((incidentEdgeFinset G bond.first).filter
      (fun edge => edge ∈ cycle.selectedCycle.crossingEdges)).card = 2 := by
  classical
  rw [bond.filter_incident_first_eq_erase_internalEdge hroot]
  have hfirstMem : bond.first ∈ component.supp := by
    rw [bond.component_supp]
    simp
  have hcubic := web.boundary_wellFormed.cubic_elsewhere bond.first
    (by
      intro inner heq
      apply cycle.innerStub_not_mem_component component hroot inner
      rw [← heq]
      exact hfirstMem)
    (by
      intro outer heq
      apply cycle.outerStub_not_mem_component component hroot outer
      rw [← heq]
      exact hfirstMem)
  have hinternal : bond.internalEdge ∈ incidentEdgeFinset G bond.first := by
    simp [SquareBondRealization.internalEdge, incidentEdgeFinset, Sym2.mem_iff]
  rw [Finset.card_erase_of_mem hinternal, hcubic]

/-- Local cubicity makes exactly two selected crossings incident to the second
endpoint of the square bond. -/
theorem SquareBondRealization.second_crossingEdges_card_eq_two
    {cycle : MiddleReplacementShortDualCycle (web := web) face}
    {component :
      (G.deleteEdges (edgeFinsetValueSet
        cycle.selectedCycle.crossingEdges)).ConnectedComponent}
    (bond : SquareBondRealization cycle component)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    ((incidentEdgeFinset G bond.second).filter
      (fun edge => edge ∈ cycle.selectedCycle.crossingEdges)).card = 2 := by
  let swapped : SquareBondRealization cycle component := {
    first := bond.second
    second := bond.first
    first_ne_second := bond.first_ne_second.symm
    component_supp := by simpa [Set.pair_comm] using bond.component_supp
    adjacent := bond.adjacent.symm
    covers_crossingEdges := by
      intro edge hedge
      rcases bond.covers_crossingEdges edge hedge with hfirst | hsecond
      · exact .inr hfirst
      · exact .inl hsecond
  }
  simpa [swapped, SquareBondRealization.internalEdge, Sym2.eq_swap] using
    swapped.first_crossingEdges_card_eq_two hroot

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

namespace MiddleReplacementSquareDualCycle

variable {face : SelectedFace (web := web)}

/-- Feed a typed distance-two square residue directly into the exact
cyclic-side-or-two-vertex-bond classification.  The four-step equality is
carried by the packet rather than being reconstructed by each consumer. -/
theorem hasCycleOnSide_or_squareBond
    (square : MiddleReplacementSquareDualCycle (web := web) face)
    (component :
      (G.deleteEdges (edgeFinsetValueSet
        square.cycle.selectedCycle.crossingEdges)).ConnectedComponent)
    (hroot : web.annular.RS.outer.fst ∉ component.supp) :
    HasCycleOnSide G (fun vertex => vertex ∈ component.supp) ∨
      Nonempty
        (MiddleReplacementShortDualCycle.SquareBondRealization
          square.cycle component) :=
  square.cycle.hasCycleOnSide_or_squareBond component hroot
    square.length_eq_four

end MiddleReplacementSquareDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
