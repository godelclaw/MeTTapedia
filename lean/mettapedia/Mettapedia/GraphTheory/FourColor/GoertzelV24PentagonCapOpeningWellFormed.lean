import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpening
import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpeningComparison
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedBoundaryCounts

/-!
# Well-formed inner boundary from a cubic pentagon-cap opening

The manuscript-side cap opening has five degree-one boundary stubs.  This
file proves the corresponding literal fact for the toolchain presentation:
if the closed graph is cubic, deleting the cap cycle leaves every non-cap
vertex cubic and gives a well-formed five-stub boundary with no invented outer
interface.

This is only the inner half of the Cell-3 formation.  It does not select a cap
in the source map, construct an outer boundary or annular embedding, or form
crosscuts.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PentagonCapOpeningWellFormed

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedBoundaryCounts
open GoertzelV24PentagonCapOpening
open GoertzelV24PentagonCapOpeningComparison

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace PentagonCap

local instance openGraphDecidableRel (cap : PentagonCap G) :
    DecidableRel cap.openGraph.Adj :=
  Classical.decRel _

local instance openGraphEdgeSetFintype (cap : PentagonCap G) :
    Fintype cap.openGraph.edgeSet :=
  cap.openGraph.fintypeEdgeSet

/-- Removing cap-cycle edges leaves the neighborhood of every vertex outside
the cap unchanged. -/
theorem openGraph_neighborFinset_eq_of_not_mem_vertexSupport
    (cap : PentagonCap G) {vertex : V}
    (hvertex : vertex ∉ cap.vertexSupport) :
    cap.openGraph.neighborFinset vertex = G.neighborFinset vertex := by
  ext neighbor
  simp only [SimpleGraph.mem_neighborFinset]
  change (G.deleteEdges (edgeFinsetValueSet cap.cycleSupport)).Adj vertex neighbor ↔
    G.Adj vertex neighbor
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · exact And.left
  · intro hadj
    refine ⟨hadj, ?_⟩
    intro hremoved
    rcases (mem_edgeFinsetValueSet_iff cap.cycleSupport _).mp hremoved with
      ⟨edge, hedge, hedgeValue⟩
    rcases Finset.mem_map.mp hedge with ⟨cycle, -, hcycle⟩
    have hcycleValue : (cap.cycleEdge cycle).1 = s(vertex, neighbor) := by
      calc
        (cap.cycleEdge cycle).1 = edge.1 := congrArg Subtype.val hcycle
        _ = s(vertex, neighbor) := hedgeValue
    have hvertexOnCycle : vertex ∈ (cap.cycleEdge cycle).1 := by
      rw [hcycleValue]
      simp
    rcases cap.cycleEdge_endpoint_eq_vertex cycle vertex hvertexOnCycle with
      ⟨step, hstep⟩
    apply hvertex
    exact (cap.mem_vertexSupport_iff vertex).2 ⟨step, hstep⟩

/-- Away from its five boundary stubs, a cap opening preserves the cubic
degree of the closed source graph. -/
theorem openGraph_incidentEdgeFinset_card_eq_three_of_not_mem_vertexSupport
    (cap : PentagonCap G) (hregular : G.IsRegularOfDegree 3)
    {vertex : V} (hvertex : vertex ∉ cap.vertexSupport) :
    (incidentEdgeFinset cap.openGraph vertex).card = 3 := by
  calc
    (incidentEdgeFinset cap.openGraph vertex).card =
        cap.openGraph.degree vertex :=
      incidentEdgeFinset_card_eq_degree (G := cap.openGraph) vertex
    _ = 3 := by
      change (cap.openGraph.neighborFinset vertex).card = 3
      rw [openGraph_neighborFinset_eq_of_not_mem_vertexSupport cap hvertex]
      exact hregular vertex

/-- The toolchain cap vertex has exactly its named outward-spoke neighbour in
the opened graph. -/
theorem openGraph_neighborFinset_capVertex_eq_singleton
    (cap : PentagonCap G) (step : Fin 5) :
    cap.openGraph.neighborFinset (cap.vertex step) = {cap.spokeOuter step} := by
  ext vertex
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  constructor
  · intro hadj
    by_cases hcap : vertex ∈ cap.vertexSupport
    · rcases (cap.mem_vertexSupport_iff vertex).1 hcap with ⟨other, hother⟩
      subst vertex
      exact False.elim
        (_root_.Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpeningComparison.PentagonCap.not_openGraph_adj_capVertices
          cap other step (cap.openGraph.adj_symm hadj))
    · exact _root_.Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpeningComparison.PentagonCap.eq_spokeOuter_of_openGraph_adj_vertex
          cap step ⟨vertex, hcap⟩ (cap.openGraph.adj_symm hadj)
  · intro hvertex
    subst vertex
    exact cap.openGraph.adj_symm
      (_root_.Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpeningComparison.PentagonCap.openGraph_adj_spokeOuter_vertex
        cap step)

/-- Every toolchain cap vertex becomes a degree-one inner stub. -/
theorem openGraph_degree_capVertex_eq_one
    (cap : PentagonCap G) (step : Fin 5) :
    cap.openGraph.degree (cap.vertex step) = 1 := by
  change (cap.openGraph.neighborFinset (cap.vertex step)).card = 1
  rw [openGraph_neighborFinset_capVertex_eq_singleton cap step]
  simp

/-- In a cubic closed source graph, opening just the cap creates exactly the
five degree-one vertices of the cap interface.  Thus the outer boundary of a
Cell--3 annulus cannot be silently manufactured by this local operation: it
must already be present in the frontier tangle that is opened at the cap. -/
theorem openGraph_degree_eq_one_iff_mem_vertexSupport
    (cap : PentagonCap G) (hregular : G.IsRegularOfDegree 3)
    (vertex : V) :
    cap.openGraph.degree vertex = 1 ↔ vertex ∈ cap.vertexSupport := by
  constructor
  · intro hone
    by_contra houtside
    have hthree : cap.openGraph.degree vertex = 3 := by
      rw [← incidentEdgeFinset_card_eq_degree (G := cap.openGraph) vertex]
      exact openGraph_incidentEdgeFinset_card_eq_three_of_not_mem_vertexSupport
        cap hregular houtside
    omega
  · intro hmem
    rcases (cap.mem_vertexSupport_iff vertex).mp hmem with ⟨step, hstep⟩
    rw [← hstep]
    exact openGraph_degree_capVertex_eq_one cap step

/-- A well-formed annular boundary datum whose inner interface is the literal
opened cap has no outer stubs at all.  This rules out the false construction
that would turn a closed cubic graph into the source annulus merely by opening
its pentagon; the source's free outer interface is separate input data. -/
theorem outerCount_eq_zero_of_innerStub_eq_capVertex
    {outerCount : Nat} (cap : PentagonCap G)
    (hregular : G.IsRegularOfDegree 3)
    (data : AnnularBoundaryData cap.openGraph outerCount)
    (hdata : data.WellFormed)
    (hinner : ∀ step : Fin 5, data.innerStub step = cap.vertex step) :
    outerCount = 0 := by
  by_contra hnonzero
  have hpositive : 0 < outerCount := Nat.pos_of_ne_zero hnonzero
  let outer : Fin outerCount := ⟨0, hpositive⟩
  have hone : cap.openGraph.degree (data.outerStub outer) = 1 := by
    calc
      cap.openGraph.degree (data.outerStub outer) =
          (incidentEdgeFinset cap.openGraph (data.outerStub outer)).card :=
        (incidentEdgeFinset_card_eq_degree (G := cap.openGraph)
          (data.outerStub outer)).symm
      _ = 1 := hdata.outer_stub_degree_one outer
  have hcap : data.outerStub outer ∈ cap.vertexSupport :=
    (openGraph_degree_eq_one_iff_mem_vertexSupport cap hregular
      (data.outerStub outer)).mp hone
  rcases (cap.mem_vertexSupport_iff _).mp hcap with ⟨step, hstep⟩
  exact (hdata.inner_outer_stub_disjoint step outer)
    ((hinner step).trans hstep)

/-- **Source-opening inner boundary.** A cubic closed graph together with a
literal pentagon cap produces the complete five-stub well-formed boundary
datum of the opened cap.  The `Fin 0` outer interface records deliberately
that no annular outer boundary has been constructed at this stage. -/
theorem innerBoundaryData_wellFormed_of_isRegularOfDegree_three
    (cap : PentagonCap G) (hregular : G.IsRegularOfDegree 3) :
    (cap.innerBoundaryData).WellFormed := by
  refine {
    inner_outer_stub_disjoint := ?_,
    inner_outer_edge_disjoint := ?_,
    innerBoundaryEdge_incident := ?_,
    outerBoundaryEdge_incident := ?_,
    inner_stub_degree_one := ?_,
    outer_stub_degree_one := ?_,
    cubic_elsewhere := ?_ }
  · intro _ outer
    exact Fin.elim0 outer
  · intro _ outer
    exact Fin.elim0 outer
  · intro inner
    change cap.openSpokeEdge inner ∈
      incidentEdgeFinset cap.openGraph (cap.vertex inner)
    simp only [incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    change cap.vertex inner ∈ (cap.openSpokeEdge inner).1
    simpa [cap.openSpokeEdge_val, cap.spokeEdge_eq inner] using
      cap.spokeEdge_incident inner
  · intro outer
    exact Fin.elim0 outer
  · intro inner
    calc
      (incidentEdgeFinset cap.openGraph
          ((cap.innerBoundaryData).innerStub inner)).card =
          cap.openGraph.degree (cap.vertex inner) := by
        exact incidentEdgeFinset_card_eq_degree (G := cap.openGraph)
          (cap.vertex inner)
      _ = 1 := openGraph_degree_capVertex_eq_one cap inner
  · intro outer
    exact Fin.elim0 outer
  · intro vertex hinner _
    have houtside : vertex ∉ cap.vertexSupport := by
      intro hmem
      rcases (cap.mem_vertexSupport_iff vertex).1 hmem with ⟨step, hstep⟩
      exact hinner step hstep.symm
    exact openGraph_incidentEdgeFinset_card_eq_three_of_not_mem_vertexSupport cap
      hregular houtside

end PentagonCap

end

end GoertzelV24PentagonCapOpeningWellFormed

end Mettapedia.GraphTheory.FourColor
