import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionSlitGraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpening

/-!
# Ordered boundary comparison for the two pentagon openings

The manuscript deletes the five cap vertices and replaces each outward spoke by
a fresh stub.  The supplied toolchain retains those five vertices and deletes
the five cap-cycle edges.  The two descriptions therefore have the same five
ordered boundary positions, but that fact must be made explicit before a graph
isomorphism can transport boundary words or selected-component data.

This file establishes the ordered port map, proves that its five outward
spokes exhaust all manuscript-side boundary ports, and constructs the graph
isomorphism between the two openings.  Its canonical isomorphism sends port
`i` to cap vertex `i` by `rfl`; this definitional compatibility is deliberate,
so replacing it with a merely propositional transport would be a regression.
It deliberately does not identify dependent face-fragment carriers merely
from agreement of the five boundary edges.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PentagonCapOpeningComparison

open SimpleGraph
open GoertzelV24DeletedRegionSlitGraph
open GoertzelV24PentagonCapOpening
open GoertzelV24FiniteDeletionCyclicCut

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetFintype : Fintype G.edgeSet :=
  Fintype.ofFinite _

namespace PentagonCap

/-- Orient the `step`-th cap spoke from its retained endpoint into the cap.
This is the manuscript-side boundary direction. -/
def spokeBoundaryDart (cap : PentagonCap G) (step : Fin 5) : G.Dart :=
  ⟨(cap.spokeOuter step, cap.vertex step), by
    rw [← SimpleGraph.mem_edgeSet]
    simpa [cap.spokeEdge_eq step, Sym2.eq_swap] using (cap.spokeEdge step).2⟩

@[simp] theorem spokeBoundaryDart_fst (cap : PentagonCap G) (step : Fin 5) :
    (spokeBoundaryDart cap step).fst = cap.spokeOuter step :=
  rfl

@[simp] theorem spokeBoundaryDart_snd (cap : PentagonCap G) (step : Fin 5) :
    (spokeBoundaryDart cap step).snd = cap.vertex step :=
  rfl

/-- The `step`-th ordered toolchain stub determines the corresponding fresh
manuscript-side port. -/
def spokeBoundaryPort (cap : PentagonCap G) (step : Fin 5) :
    DeletedRegionBoundaryPort G cap.vertexSupport where
  dart := spokeBoundaryDart cap step
  retained := by
    simpa [spokeBoundaryDart] using cap.spokeOuter_not_mem_vertexSupport step
  removed := by
    exact (cap.mem_vertexSupport_iff _).mpr ⟨step, rfl⟩

@[simp] theorem spokeBoundaryPort_fst (cap : PentagonCap G) (step : Fin 5) :
    (spokeBoundaryPort cap step).dart.fst = cap.spokeOuter step :=
  rfl

@[simp] theorem spokeBoundaryPort_snd (cap : PentagonCap G) (step : Fin 5) :
    (spokeBoundaryPort cap step).dart.snd = cap.vertex step :=
  rfl

/-- The source order is injective on fresh manuscript-side boundary ports. -/
def spokeBoundaryPortEmbedding (cap : PentagonCap G) :
    Fin 5 ↪ DeletedRegionBoundaryPort G cap.vertexSupport :=
  ⟨spokeBoundaryPort cap, by
    intro first second hports
    apply cap.vertex.injective
    have hends := congrArg (fun port : DeletedRegionBoundaryPort G cap.vertexSupport =>
      port.dart.snd) hports
    simpa using hends⟩

/-- Every manuscript-side boundary port has a unique cap index at its deleted
endpoint.  This is the first half of the exactness statement needed for the
opening isomorphism. -/
theorem exists_unique_capIndex_of_boundaryPort (cap : PentagonCap G)
    (port : DeletedRegionBoundaryPort G cap.vertexSupport) :
    ∃! step : Fin 5, cap.vertex step = port.dart.snd := by
  rcases (cap.mem_vertexSupport_iff _).mp port.removed with ⟨step, hstep⟩
  refine ⟨step, hstep, ?_⟩
  intro other hother
  apply cap.vertex.injective
  exact hother.trans hstep.symm

/-- No unrecorded boundary port is created by deleting the cap vertices: every
such port is exactly one of the five ordered outward spokes.  The proof uses
the literal cubic incidence list at the deleted endpoint; the two cycle-edge
cases contradict the fact that a boundary port starts outside the cap. -/
theorem boundaryPort_eq_spokeBoundaryPort (cap : PentagonCap G)
    (port : DeletedRegionBoundaryPort G cap.vertexSupport) :
    ∃ step : Fin 5, port = spokeBoundaryPort cap step := by
  rcases (exists_unique_capIndex_of_boundaryPort cap port).exists with
    ⟨step, hstep⟩
  let portEdge : G.edgeSet := ⟨port.dart.edge, port.dart.edge_mem⟩
  have hincident : portEdge ∈ incidentEdgeFinset G (cap.vertex step) := by
    simp [portEdge, incidentEdgeFinset, SimpleGraph.Dart.edge, ← hstep]
  have hincEq : incidentEdgeFinset G (cap.vertex step) =
      {cap.cycleEdge step, cap.cycleEdge (cap.cycleMate step), cap.spokeEdge step} :=
    cap.incident_eq step
  rw [hincEq] at hincident
  simp only [Finset.mem_insert, Finset.mem_singleton] at hincident
  rcases hincident with hcycle | hcycle | hspoke
  · have hfst : port.dart.fst ∈ (cap.cycleEdge step).1 := by
      rw [← congrArg Subtype.val hcycle]
      simp [portEdge, SimpleGraph.Dart.edge]
    rcases cap.cycleEdge_endpoint_eq_vertex step port.dart.fst hfst with
      ⟨capStep, hcapStep⟩
    exact False.elim (port.retained
      ((cap.mem_vertexSupport_iff _).mpr ⟨capStep, hcapStep⟩))
  · have hfst : port.dart.fst ∈ (cap.cycleEdge (cap.cycleMate step)).1 := by
      rw [← congrArg Subtype.val hcycle]
      simp [portEdge, SimpleGraph.Dart.edge]
    rcases cap.cycleEdge_endpoint_eq_vertex (cap.cycleMate step) port.dart.fst hfst with
      ⟨capStep, hcapStep⟩
    exact False.elim (port.retained
      ((cap.mem_vertexSupport_iff _).mpr ⟨capStep, hcapStep⟩))
  · refine ⟨step, ?_⟩
    have hpairs : s(port.dart.fst, port.dart.snd) =
        s(cap.vertex step, cap.spokeOuter step) := by
      simpa [portEdge, SimpleGraph.Dart.edge, cap.spokeEdge_eq step] using
        congrArg Subtype.val hspoke
    rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
    · exact False.elim (cap.spokeOuter_ne_vertex step step
        (hstraight.2.symm.trans hstep.symm))
    · have hdart : port.dart = spokeBoundaryDart cap step := by
        apply SimpleGraph.Dart.ext
        exact Prod.ext hswapped.1 hswapped.2
      cases port
      cases hdart
      rfl

/-- The five ordered ports exhaust the manuscript-side slit boundary. -/
def spokeBoundaryPortEquiv (cap : PentagonCap G) :
    Fin 5 ≃ DeletedRegionBoundaryPort G cap.vertexSupport :=
  Equiv.ofBijective (spokeBoundaryPort cap)
    ⟨(spokeBoundaryPortEmbedding cap).injective, by
      intro port
      rcases boundaryPort_eq_spokeBoundaryPort cap port with ⟨step, hstep⟩
      exact ⟨step, hstep.symm⟩⟩

/-- The carrier map for the eventual graph isomorphism.  Old manuscript-side
vertices retain their names; a fresh boundary stub takes the name of the cap
vertex which the toolchain retained. -/
def slitToOpenVertexEquiv (cap : PentagonCap G) :
    DeletedRegionSlitVertex G cap.vertexSupport ≃ V :=
  Equiv.ofBijective
    (fun vertex => match vertex with
      | Sum.inl oldVertex => oldVertex.1
      | Sum.inr boundaryPort => boundaryPort.dart.snd)
    ⟨by
      intro first second heq
      rcases first with oldFirst | portFirst <;>
        rcases second with oldSecond | portSecond
      · exact congrArg Sum.inl (Subtype.ext heq)
      · exact False.elim (oldFirst.2 (by simpa [← heq] using portSecond.removed))
      · exact False.elim (oldSecond.2 (by simpa [heq] using portFirst.removed))
      · rcases boundaryPort_eq_spokeBoundaryPort cap portFirst with ⟨firstStep, hfirst⟩
        rcases boundaryPort_eq_spokeBoundaryPort cap portSecond with ⟨secondStep, hsecond⟩
        subst portFirst
        subst portSecond
        have hsteps : firstStep = secondStep := cap.vertex.injective (by
          simpa using heq)
        cases hsteps
        rfl,
      by
        intro vertex
        by_cases hcap : vertex ∈ cap.vertexSupport
        · rcases (cap.mem_vertexSupport_iff vertex).mp hcap with ⟨step, hstep⟩
          refine ⟨Sum.inr (spokeBoundaryPort cap step), ?_⟩
          simpa [hstep]
        · exact ⟨Sum.inl ⟨vertex, hcap⟩, rfl⟩⟩

@[simp] theorem slitToOpenVertexEquiv_old (cap : PentagonCap G)
    (vertex : {vertex // vertex ∉ cap.vertexSupport}) :
    slitToOpenVertexEquiv cap (Sum.inl vertex) = vertex.1 :=
  rfl

@[simp] theorem slitToOpenVertexEquiv_stub (cap : PentagonCap G)
    (port : DeletedRegionBoundaryPort G cap.vertexSupport) :
    slitToOpenVertexEquiv cap (Sum.inr port) = port.dart.snd :=
  rfl

/-- An ambient edge whose two endpoints remain outside the cap survives the
toolchain opening: a removed cap-cycle edge has both endpoints in the cap. -/
theorem openGraph_adj_of_adj_outside (cap : PentagonCap G)
    {first second : V} (hfirst : first ∉ cap.vertexSupport)
    (hsecond : second ∉ cap.vertexSupport) (hadj : G.Adj first second) :
    cap.openGraph.Adj first second := by
  rw [← SimpleGraph.mem_edgeSet]
  apply (cap.mem_openGraph_edgeSet_iff _ (by simpa using hadj)).mpr
  intro hremoved
  rcases (mem_edgeFinsetValueSet_iff cap.cycleSupport _).mp hremoved with
    ⟨edge, hedge, hedgeValue⟩
  rcases Finset.mem_map.mp hedge with ⟨cycle, -, hcycle⟩
  have hcycleValue : (cap.cycleEdge cycle).1 = s(first, second) := by
    calc
      (cap.cycleEdge cycle).1 = edge.1 := congrArg Subtype.val hcycle
      _ = s(first, second) := hedgeValue
  have hfirstCycle : first ∈ (cap.cycleEdge cycle).1 := by
    rw [hcycleValue]
    exact Sym2.mem_iff.mpr (Or.inl rfl)
  rcases cap.cycleEdge_endpoint_eq_vertex cycle first hfirstCycle with
    ⟨capStep, hcapStep⟩
  exact hfirst ((cap.mem_vertexSupport_iff _).mpr ⟨capStep, hcapStep⟩)

/-- The ordered cap spoke survives as an edge from its retained endpoint to
the toolchain stub vertex. -/
theorem openGraph_adj_spokeOuter_vertex (cap : PentagonCap G) (step : Fin 5) :
    cap.openGraph.Adj (cap.spokeOuter step) (cap.vertex step) := by
  have hmem : (cap.spokeEdge step).1 ∈ cap.openGraph.edgeSet :=
    (cap.openSpokeEdge step).2
  simpa [SimpleGraph.mem_edgeSet, cap.spokeEdge_eq step, Sym2.eq_swap] using hmem

/-- The unique surviving neighbour of a retained toolchain cap vertex is its
ordered outward spoke endpoint. -/
theorem eq_spokeOuter_of_openGraph_adj_vertex (cap : PentagonCap G)
    (step : Fin 5) (outside : {vertex // vertex ∉ cap.vertexSupport})
    (hadj : cap.openGraph.Adj outside.1 (cap.vertex step)) :
    outside.1 = cap.spokeOuter step := by
  let openEdge : cap.openGraph.edgeSet :=
    ⟨s(outside.1, cap.vertex step), by simpa using hadj⟩
  have hincident : openEdge ∈
      incidentEdgeFinset cap.openGraph (cap.vertex step) := by
    simp [openEdge, incidentEdgeFinset, Sym2.mem_iff]
  rw [cap.openGraph_incidentEdgeFinset_capVertex_eq_singleton step] at hincident
  have hedge : openEdge = cap.openSpokeEdge step := Finset.mem_singleton.mp hincident
  have hpairs : s(outside.1, cap.vertex step) =
      s(cap.vertex step, cap.spokeOuter step) := by
    calc
      s(outside.1, cap.vertex step) = openEdge.1 := rfl
      _ = (cap.openSpokeEdge step).1 := congrArg Subtype.val hedge
      _ = (cap.spokeEdge step).1 := by
        simp [GoertzelV24PentagonCapOpening.PentagonCap.openSpokeEdge_val]
      _ = s(cap.vertex step, cap.spokeOuter step) := cap.spokeEdge_eq step
  rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
  · exact False.elim (cap.spokeOuter_ne_vertex step step
      (hstraight.2.symm))
  · exact hswapped.1

/-- After deleting the cycle edges, no two toolchain cap vertices are
adjacent. -/
theorem not_openGraph_adj_capVertices (cap : PentagonCap G)
    (first second : Fin 5) :
    ¬ cap.openGraph.Adj (cap.vertex first) (cap.vertex second) := by
  intro hadj
  let openEdge : cap.openGraph.edgeSet :=
    ⟨s(cap.vertex first, cap.vertex second), by simpa using hadj⟩
  have hincident : openEdge ∈
      incidentEdgeFinset cap.openGraph (cap.vertex first) := by
    simp [openEdge, incidentEdgeFinset, Sym2.mem_iff]
  rw [cap.openGraph_incidentEdgeFinset_capVertex_eq_singleton first] at hincident
  have hedge : openEdge = cap.openSpokeEdge first := Finset.mem_singleton.mp hincident
  have hpairs : s(cap.vertex first, cap.vertex second) =
      s(cap.vertex first, cap.spokeOuter first) := by
    calc
      s(cap.vertex first, cap.vertex second) = openEdge.1 := rfl
      _ = (cap.openSpokeEdge first).1 := congrArg Subtype.val hedge
      _ = (cap.spokeEdge first).1 := by
        simp [GoertzelV24PentagonCapOpening.PentagonCap.openSpokeEdge_val]
      _ = s(cap.vertex first, cap.spokeOuter first) := cap.spokeEdge_eq first
  rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
  · exact cap.spokeOuter_ne_vertex first second hstraight.2.symm
  · exact cap.spokeOuter_ne_vertex first first hswapped.1.symm

/-- The literal manuscript opening and the supplied toolchain opening are
isomorphic as graphs.  The isomorphism is deliberately not merely cardinal:
it maps the fresh stub of ordered port `i` to the retained toolchain cap vertex
at the same ordered position `i`. -/
def openingGraphIso (cap : PentagonCap G) :
    (deletedRegionSlitGraph (G := G) cap.vertexSupport).Iso cap.openGraph where
  toEquiv := slitToOpenVertexEquiv cap
  map_rel_iff' := by
    intro first second
    rcases first with oldFirst | portFirst <;>
      rcases second with oldSecond | portSecond
    · change cap.openGraph.Adj oldFirst.1 oldSecond.1 ↔ G.Adj oldFirst.1 oldSecond.1
      constructor
      · intro hopen
        have hmem : s(oldFirst.1, oldSecond.1) ∈ cap.openGraph.edgeSet := by
          simpa [SimpleGraph.mem_edgeSet] using hopen
        have hambient := cap.openGraph_edgeSet_subset hmem
        simpa [SimpleGraph.mem_edgeSet] using hambient
      · exact openGraph_adj_of_adj_outside cap oldFirst.2 oldSecond.2
    · change cap.openGraph.Adj oldFirst.1 portSecond.dart.snd ↔
        oldFirst.1 = portSecond.dart.fst
      constructor
      · intro hopen
        rcases boundaryPort_eq_spokeBoundaryPort cap portSecond with ⟨step, hport⟩
        subst portSecond
        simpa using eq_spokeOuter_of_openGraph_adj_vertex cap step oldFirst hopen
      · intro hslit
        rcases boundaryPort_eq_spokeBoundaryPort cap portSecond with ⟨step, hport⟩
        subst portSecond
        rw [spokeBoundaryPort_fst] at hslit
        simpa [hslit] using openGraph_adj_spokeOuter_vertex cap step
    · change cap.openGraph.Adj portFirst.dart.snd oldSecond.1 ↔
        portFirst.dart.fst = oldSecond.1
      constructor
      · intro hopen
        rcases boundaryPort_eq_spokeBoundaryPort cap portFirst with ⟨step, hport⟩
        subst portFirst
        have hopen' : cap.openGraph.Adj oldSecond.1 (cap.vertex step) :=
          cap.openGraph.adj_symm hopen
        have heq := eq_spokeOuter_of_openGraph_adj_vertex cap step oldSecond hopen'
        simpa using heq.symm
      · intro hslit
        rcases boundaryPort_eq_spokeBoundaryPort cap portFirst with ⟨step, hport⟩
        subst portFirst
        rw [spokeBoundaryPort_fst] at hslit
        have hopen := openGraph_adj_spokeOuter_vertex cap step
        simpa [hslit] using cap.openGraph.adj_symm hopen
    · change cap.openGraph.Adj portFirst.dart.snd portSecond.dart.snd ↔ False
      constructor
      · intro hopen
        rcases boundaryPort_eq_spokeBoundaryPort cap portFirst with ⟨firstStep, hfirst⟩
        rcases boundaryPort_eq_spokeBoundaryPort cap portSecond with ⟨secondStep, hsecond⟩
        subst portFirst
        subst portSecond
        exact (not_openGraph_adj_capVertices cap firstStep secondStep hopen).elim
      · exact False.elim

/-- The graph isomorphism fixes the five source coordinates: the fresh
manuscript-side stub created at `step` maps to the toolchain's cap vertex at
that same `step`.  This is the ordered compatibility needed by boundary-word
and selected-component consumers. -/
theorem openingGraphIso_ordered_stub (cap : PentagonCap G) (step : Fin 5) :
    openingGraphIso cap (Sum.inr (spokeBoundaryPort cap step)) = cap.vertex step :=
  rfl

/-- The ordered comparison at the boundary.  The left side is the fresh stub
created by the manuscript operation; the right side is the cap vertex retained
by the toolchain operation.  Both use the same `Fin 5` coordinate, so a later
opening isomorphism is required to commute with this map rather than merely
permute the five stubs. -/
def orderedStubComparison (cap : PentagonCap G) :
    Fin 5 →
      DeletedRegionBoundaryPort G cap.vertexSupport × V :=
  fun step => (spokeBoundaryPort cap step, cap.vertex step)

theorem orderedStubComparison_preserves_deleted_endpoint
    (cap : PentagonCap G) (step : Fin 5) :
    (orderedStubComparison cap step).1.dart.snd =
      (orderedStubComparison cap step).2 :=
  rfl

end PentagonCap

end

end GoertzelV24PentagonCapOpeningComparison

end Mettapedia.GraphTheory.FourColor
