import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpeningWellFormed

/-!
# Addendum V frontier-tangle cap opening

Addendum V starts with a frontier tangle `X` that already has an ordered
outer interface, and removes one interior pentagon cap to obtain the annular
tangle `X'`.  This differs essentially from opening one cap in a closed cubic
graph: the latter has no outer interface.

This module gives the graph-level carrier construction for the source
operation.  It records an outer-only frontier boundary, states precisely that
the cap is interior to that boundary, preserves the outer stubs and their
edges through the cap opening, and constructs the existing
`AnnularBoundaryData` carrier.  The construction does not assert an annular
cellulation, select the frontier tangle from a minimal counterexample, or
construct the L1 crosscuts.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FrontierPentagonCapOpening

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24FramedBoundaryCounts
open GoertzelV24PentagonCapOpening
open GoertzelV24PentagonCapOpeningWellFormed

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The ordered free outer interface already present on Addendum V's frontier
tangle `X`.  The inner interface is created only after opening the cap. -/
structure FrontierBoundaryData (G : SimpleGraph V) (outerCount : Nat) where
  outerStub : Fin outerCount ↪ V
  outerBoundaryEdge : Fin outerCount ↪ G.edgeSet

namespace FrontierBoundaryData

variable {outerCount : Nat}

/-- Graph-level validity of the frontier tangle before its interior cap is
opened: the named outer stubs have degree one and every other vertex is
cubic. -/
structure WellFormed (frontier : FrontierBoundaryData G outerCount) : Prop where
  outerBoundaryEdge_incident :
    ∀ outer,
      frontier.outerBoundaryEdge outer ∈
        incidentEdgeFinset G (frontier.outerStub outer)
  outer_stub_degree_one :
    ∀ outer,
      (incidentEdgeFinset G (frontier.outerStub outer)).card = 1
  cubic_elsewhere :
    ∀ vertex,
      (∀ outer, vertex ≠ frontier.outerStub outer) →
        (incidentEdgeFinset G vertex).card = 3

/-- The five cap vertices do not meet the old outer stubs, and none of the
five cap spokes is already an outer boundary edge.  These are exactly the
graph-level separation conditions needed to say that the chosen cap is
interior to the frontier tangle. -/
structure InteriorPentagonCap
    (frontier : FrontierBoundaryData G outerCount) (cap : PentagonCap G) : Prop where
  capVertex_ne_outerStub :
    ∀ capStep outer, cap.vertex capStep ≠ frontier.outerStub outer
  spokeEdge_ne_outerBoundaryEdge :
    ∀ capStep outer, cap.spokeEdge capStep ≠ frontier.outerBoundaryEdge outer

variable (frontier : FrontierBoundaryData G outerCount)
  (cap : PentagonCap G) (hinterior : frontier.InteriorPentagonCap cap)

local instance openGraphDecidableRel : DecidableRel cap.openGraph.Adj :=
  Classical.decRel _

local instance openGraphEdgeSetFintype : Fintype cap.openGraph.edgeSet :=
  cap.openGraph.fintypeEdgeSet

include hinterior

/-- No old outer boundary edge is one of the deleted cap-cycle edges.  This
is derived from endpoint incidence and cap-vertex/outer-stub separation; it
is not an additional field of `InteriorPentagonCap`. -/
theorem outerBoundaryEdge_not_mem_removed (hfrontier : frontier.WellFormed)
    (outer : Fin outerCount) :
    (frontier.outerBoundaryEdge outer).1 ∉
      edgeFinsetValueSet cap.cycleSupport := by
  intro hremoved
  rcases (mem_edgeFinsetValueSet_iff cap.cycleSupport _).mp hremoved with
    ⟨edge, hedge, hedgeValue⟩
  rcases Finset.mem_map.mp hedge with ⟨cycle, -, hcycle⟩
  have hcycleValue : (cap.cycleEdge cycle).1 =
      (frontier.outerBoundaryEdge outer).1 := by
    calc
      (cap.cycleEdge cycle).1 = edge.1 := congrArg Subtype.val hcycle
      _ = (frontier.outerBoundaryEdge outer).1 := hedgeValue
  have houterOnCycle : frontier.outerStub outer ∈
      (cap.cycleEdge cycle).1 := by
    rw [hcycleValue]
    exact (Finset.mem_filter.mp
      (hfrontier.outerBoundaryEdge_incident outer)).2
  rcases cap.cycleEdge_endpoint_eq_vertex cycle (frontier.outerStub outer)
      houterOnCycle with ⟨capStep, hcapStep⟩
  exact InteriorPentagonCap.capVertex_ne_outerStub hinterior capStep outer hcapStep

/-- An old outer boundary edge survives the cap opening. -/
def openOuterBoundaryEdge (hfrontier : frontier.WellFormed)
    (outer : Fin outerCount) : cap.openGraph.edgeSet :=
  ⟨(frontier.outerBoundaryEdge outer).1,
    (cap.mem_openGraph_edgeSet_iff _ (frontier.outerBoundaryEdge outer).2).mpr
      (outerBoundaryEdge_not_mem_removed (frontier := frontier) (cap := cap)
        (hinterior := hinterior) hfrontier outer)⟩

@[simp] theorem openOuterBoundaryEdge_val (hfrontier : frontier.WellFormed)
    (outer : Fin outerCount) :
    (openOuterBoundaryEdge (frontier := frontier) (cap := cap)
      (hinterior := hinterior) hfrontier outer).1 =
      (frontier.outerBoundaryEdge outer).1 :=
  rfl

/-- The surviving outer edges retain their source ordering and remain
duplicate-free. -/
def openOuterBoundaryEdgeEmbedding (hfrontier : frontier.WellFormed) :
    Fin outerCount ↪ cap.openGraph.edgeSet :=
  ⟨openOuterBoundaryEdge (frontier := frontier) (cap := cap)
      (hinterior := hinterior) hfrontier, by
    intro first second heq
    apply frontier.outerBoundaryEdge.injective
    apply Subtype.ext
    simpa only [openOuterBoundaryEdge_val] using congrArg Subtype.val heq⟩

/-- The exact Addendum V boundary carrier after opening the interior cap:
five new inner stubs and the old ordered outer interface. -/
def openingBoundaryData (hfrontier : frontier.WellFormed) :
    AnnularBoundaryData cap.openGraph outerCount where
  innerStub := cap.vertex
  outerStub := frontier.outerStub
  innerBoundaryEdge := cap.openSpokeEmbedding
  outerBoundaryEdge :=
    openOuterBoundaryEdgeEmbedding (frontier := frontier) (cap := cap)
      (hinterior := hinterior) hfrontier

/-- The old outer boundary edge remains incident with its old stub after the
cap cycle is deleted. -/
theorem openOuterBoundaryEdge_incident (hfrontier : frontier.WellFormed)
    (outer : Fin outerCount) :
    openOuterBoundaryEdge (frontier := frontier) (cap := cap)
      (hinterior := hinterior) hfrontier outer ∈
      incidentEdgeFinset cap.openGraph (frontier.outerStub outer) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact (Finset.mem_filter.mp
    (hfrontier.outerBoundaryEdge_incident outer)).2

/-- The opened graph has no new edge at an old outer stub, and its unique old
boundary edge survives; hence the stub remains degree one. -/
theorem openGraph_incidentEdgeFinset_outerStub_eq_singleton
    (hfrontier : frontier.WellFormed) (outer : Fin outerCount) :
    incidentEdgeFinset cap.openGraph (frontier.outerStub outer) =
      {openOuterBoundaryEdge (frontier := frontier) (cap := cap)
        (hinterior := hinterior) hfrontier outer} := by
  ext openEdge
  simp only [Finset.mem_singleton]
  constructor
  · intro hopen
    let ambientEdge : G.edgeSet :=
      ⟨openEdge.1, cap.openGraph_edgeSet_subset openEdge.2⟩
    have hambient : ambientEdge ∈
        incidentEdgeFinset G (frontier.outerStub outer) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hopen).2⟩
    have hsingleton : incidentEdgeFinset G (frontier.outerStub outer) =
        {frontier.outerBoundaryEdge outer} := by
      rcases Finset.card_eq_one.mp (hfrontier.outer_stub_degree_one outer) with
        ⟨edge, hedge⟩
      have hnamed : frontier.outerBoundaryEdge outer = edge := by
        simpa [hedge] using hfrontier.outerBoundaryEdge_incident outer
      simpa [hnamed] using hedge
    rw [hsingleton] at hambient
    have heq : ambientEdge = frontier.outerBoundaryEdge outer := by
      simpa using hambient
    apply Subtype.ext
    simpa only [openOuterBoundaryEdge_val] using congrArg Subtype.val heq
  · intro heq
    subst openEdge
    exact openOuterBoundaryEdge_incident (frontier := frontier) (cap := cap)
      (hinterior := hinterior) hfrontier outer

/-- Old outer stubs keep degree one in the opened frontier. -/
theorem openGraph_outer_stub_degree_one (hfrontier : frontier.WellFormed)
    (outer : Fin outerCount) :
    (incidentEdgeFinset cap.openGraph (frontier.outerStub outer)).card = 1 := by
  rw [openGraph_incidentEdgeFinset_outerStub_eq_singleton
    (frontier := frontier) (cap := cap) (hinterior := hinterior)
    hfrontier outer]
  simp

/-- Away from the opened cap and old outer stubs, the frontier's cubic local
degree is unchanged. -/
theorem openGraph_cubic_elsewhere (hfrontier : frontier.WellFormed)
    (vertex : V) (hinner : ∀ inner, vertex ≠ cap.vertex inner)
    (houter : ∀ outer, vertex ≠ frontier.outerStub outer) :
    (incidentEdgeFinset cap.openGraph vertex).card = 3 := by
  have hnotCap : vertex ∉ cap.vertexSupport := by
    intro hmem
    rcases (cap.mem_vertexSupport_iff vertex).mp hmem with ⟨step, hstep⟩
    exact hinner step hstep.symm
  calc
    (incidentEdgeFinset cap.openGraph vertex).card = cap.openGraph.degree vertex :=
      incidentEdgeFinset_card_eq_degree (G := cap.openGraph) vertex
    _ = G.degree vertex := by
      change (cap.openGraph.neighborFinset vertex).card =
        (G.neighborFinset vertex).card
      rw [PentagonCap.openGraph_neighborFinset_eq_of_not_mem_vertexSupport
        cap hnotCap]
    _ = (incidentEdgeFinset G vertex).card :=
      (incidentEdgeFinset_card_eq_degree (G := G) vertex).symm
    _ = 3 := hfrontier.cubic_elsewhere vertex houter

/-- **Addendum V carrier formation.** Opening an interior pentagon of a
well-formed frontier tangle produces the established well-formed annular
boundary carrier, preserving the complete ordered outer interface. -/
theorem openingBoundaryData_wellFormed (hfrontier : frontier.WellFormed) :
    (openingBoundaryData (frontier := frontier) (cap := cap)
      (hinterior := hinterior) hfrontier).WellFormed := by
  refine {
    inner_outer_stub_disjoint := ?_,
    inner_outer_edge_disjoint := ?_,
    innerBoundaryEdge_incident := ?_,
    outerBoundaryEdge_incident := ?_,
    inner_stub_degree_one := ?_,
    outer_stub_degree_one := ?_,
    cubic_elsewhere := ?_ }
  · exact InteriorPentagonCap.capVertex_ne_outerStub hinterior
  · intro inner outer heq
    apply InteriorPentagonCap.spokeEdge_ne_outerBoundaryEdge hinterior inner outer
    change cap.openSpokeEdge inner =
      openOuterBoundaryEdge (frontier := frontier) (cap := cap)
        (hinterior := hinterior) hfrontier outer at heq
    apply Subtype.ext
    simpa only [PentagonCap.openSpokeEdge_val, openOuterBoundaryEdge_val] using
      congrArg Subtype.val heq
  · intro inner
    change cap.openSpokeEdge inner ∈
      incidentEdgeFinset cap.openGraph (cap.vertex inner)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [cap.openSpokeEdge_val] using cap.spokeEdge_incident inner
  · exact openOuterBoundaryEdge_incident (frontier := frontier) (cap := cap)
      (hinterior := hinterior) hfrontier
  · intro inner
    change (incidentEdgeFinset cap.openGraph (cap.vertex inner)).card = 1
    calc
      (incidentEdgeFinset cap.openGraph (cap.vertex inner)).card =
          cap.openGraph.degree (cap.vertex inner) :=
        incidentEdgeFinset_card_eq_degree (G := cap.openGraph) (cap.vertex inner)
      _ = 1 :=
        GoertzelV24PentagonCapOpeningWellFormed.PentagonCap.openGraph_degree_capVertex_eq_one
          cap inner
  · exact openGraph_outer_stub_degree_one (frontier := frontier) (cap := cap)
      (hinterior := hinterior) hfrontier
  · exact openGraph_cubic_elsewhere (frontier := frontier) (cap := cap)
      (hinterior := hinterior) hfrontier

end FrontierBoundaryData

end

end GoertzelV24FrontierPentagonCapOpening

end Mettapedia.GraphTheory.FourColor
