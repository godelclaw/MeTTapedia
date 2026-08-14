import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionSlitGraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpening

/-!
# Ordered manuscript-side ports for a two-cap opening

The two-cap graph opening retains cap vertices as degree-one stubs.  The
manuscript presentation instead deletes both cap vertex sets and makes fresh
stubs from outward boundary darts.  This module proves the first exact bridge
between the two: the manuscript-side boundary ports of the union are *exactly*
the two ordered five-port families.  In particular, the two-cap opening has no
hidden third interface.

This is still a graph-boundary comparison.  It does not construct an annular
rotation embedding, select the two caps from a minimal counterexample, or
identify dependent face-fragment carriers.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoPentagonCapOpening

open SimpleGraph
open GoertzelV24DeletedRegionSlitGraph
open GoertzelV24FiniteDeletionCyclicCut
open GoertzelV24PentagonCapOpening
open GoertzelV24TwoPentagonCapOpening

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance boundaryGraphEdgeSetFintype : Fintype G.edgeSet :=
  Fintype.ofFinite _

namespace PentagonCapPair

/-- The two cap vertex sets which the manuscript-side presentation deletes. -/
def deletedVertexSupport (caps : PentagonCapPair G) : Finset V :=
  caps.inner.vertexSupport ∪ caps.outer.vertexSupport

/-- The ordered outward dart of the inner cap, pointing from the retained side
into the deleted two-cap region. -/
def innerBoundaryDart (caps : PentagonCapPair G) (step : Fin 5) : G.Dart :=
  ⟨(caps.inner.spokeOuter step, caps.inner.vertex step), by
    rw [← SimpleGraph.mem_edgeSet]
    simpa [caps.inner.spokeEdge_eq step, Sym2.eq_swap] using
      (caps.inner.spokeEdge step).2⟩

/-- The ordered outward dart of the outer cap, pointing from the retained side
into the deleted two-cap region. -/
def outerBoundaryDart (caps : PentagonCapPair G) (step : Fin 5) : G.Dart :=
  ⟨(caps.outer.spokeOuter step, caps.outer.vertex step), by
    rw [← SimpleGraph.mem_edgeSet]
    simpa [caps.outer.spokeEdge_eq step, Sym2.eq_swap] using
      (caps.outer.spokeEdge step).2⟩

@[simp] theorem innerBoundaryDart_fst (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.innerBoundaryDart step).fst = caps.inner.spokeOuter step :=
  rfl

@[simp] theorem innerBoundaryDart_snd (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.innerBoundaryDart step).snd = caps.inner.vertex step :=
  rfl

@[simp] theorem outerBoundaryDart_fst (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.outerBoundaryDart step).fst = caps.outer.spokeOuter step :=
  rfl

@[simp] theorem outerBoundaryDart_snd (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.outerBoundaryDart step).snd = caps.outer.vertex step :=
  rfl

/-- The `step`-th ordered inner port in the manuscript-side two-cap slit. -/
def innerBoundaryPort (caps : PentagonCapPair G) (step : Fin 5) :
    DeletedRegionBoundaryPort G caps.deletedVertexSupport where
  dart := caps.innerBoundaryDart step
  retained := by
    simp only [deletedVertexSupport, Finset.mem_union, not_or]
    exact ⟨caps.inner.spokeOuter_not_mem_vertexSupport step,
      caps.inner_spokeOuter_not_mem_outerSupport step⟩
  removed := by
    apply Finset.mem_union_left
    exact (caps.inner.mem_vertexSupport_iff _).mpr ⟨step, rfl⟩

/-- The `step`-th ordered outer port in the manuscript-side two-cap slit. -/
def outerBoundaryPort (caps : PentagonCapPair G) (step : Fin 5) :
    DeletedRegionBoundaryPort G caps.deletedVertexSupport where
  dart := caps.outerBoundaryDart step
  retained := by
    simp only [deletedVertexSupport, Finset.mem_union, not_or]
    exact ⟨caps.outer_spokeOuter_not_mem_innerSupport step,
      caps.outer.spokeOuter_not_mem_vertexSupport step⟩
  removed := by
    apply Finset.mem_union_right
    exact (caps.outer.mem_vertexSupport_iff _).mpr ⟨step, rfl⟩

@[simp] theorem innerBoundaryPort_fst (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.innerBoundaryPort step).dart.fst = caps.inner.spokeOuter step :=
  rfl

@[simp] theorem innerBoundaryPort_snd (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.innerBoundaryPort step).dart.snd = caps.inner.vertex step :=
  rfl

@[simp] theorem outerBoundaryPort_fst (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.outerBoundaryPort step).dart.fst = caps.outer.spokeOuter step :=
  rfl

@[simp] theorem outerBoundaryPort_snd (caps : PentagonCapPair G) (step : Fin 5) :
    (caps.outerBoundaryPort step).dart.snd = caps.outer.vertex step :=
  rfl

/-- The two ordered port families jointly enumerate every manuscript-side
boundary port of the deleted two-cap vertex region. -/
theorem boundaryPort_eq_inner_or_outer (caps : PentagonCapPair G)
    (port : DeletedRegionBoundaryPort G caps.deletedVertexSupport) :
    (∃ step : Fin 5, port = caps.innerBoundaryPort step) ∨
      ∃ step : Fin 5, port = caps.outerBoundaryPort step := by
  have hremoved : port.dart.snd ∈ caps.inner.vertexSupport ∪ caps.outer.vertexSupport := by
    simpa only [deletedVertexSupport] using port.removed
  rcases Finset.mem_union.mp hremoved with hinner | houter
  · rcases (caps.inner.mem_vertexSupport_iff _).mp hinner with ⟨step, hstep⟩
    let portEdge : G.edgeSet := ⟨port.dart.edge, port.dart.edge_mem⟩
    have hincident : portEdge ∈ incidentEdgeFinset G (caps.inner.vertex step) := by
      simp [portEdge, incidentEdgeFinset, SimpleGraph.Dart.edge, ← hstep]
    rw [caps.inner.incident_eq step] at hincident
    simp only [Finset.mem_insert, Finset.mem_singleton] at hincident
    rcases hincident with hcycle | hcycle | hspoke
    · exfalso
      have hfst : port.dart.fst ∈ (caps.inner.cycleEdge step).1 := by
        rw [← congrArg Subtype.val hcycle]
        simp [portEdge, SimpleGraph.Dart.edge]
      rcases caps.inner.cycleEdge_endpoint_eq_vertex step port.dart.fst hfst with
        ⟨capStep, hcapStep⟩
      apply port.retained
      change port.dart.fst ∈ caps.inner.vertexSupport ∪ caps.outer.vertexSupport
      exact Finset.mem_union_left _
        ((caps.inner.mem_vertexSupport_iff _).mpr ⟨capStep, hcapStep⟩)
    · exfalso
      have hfst : port.dart.fst ∈ (caps.inner.cycleEdge (caps.inner.cycleMate step)).1 := by
        rw [← congrArg Subtype.val hcycle]
        simp [portEdge, SimpleGraph.Dart.edge]
      rcases caps.inner.cycleEdge_endpoint_eq_vertex (caps.inner.cycleMate step)
        port.dart.fst hfst with ⟨capStep, hcapStep⟩
      apply port.retained
      change port.dart.fst ∈ caps.inner.vertexSupport ∪ caps.outer.vertexSupport
      exact Finset.mem_union_left _
        ((caps.inner.mem_vertexSupport_iff _).mpr ⟨capStep, hcapStep⟩)
    · left
      refine ⟨step, ?_⟩
      have hpairs : s(port.dart.fst, port.dart.snd) =
          s(caps.inner.vertex step, caps.inner.spokeOuter step) := by
        simpa [portEdge, SimpleGraph.Dart.edge, caps.inner.spokeEdge_eq step] using
          congrArg Subtype.val hspoke
      rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
      · exact False.elim (caps.inner.spokeOuter_ne_vertex step step
          (hstraight.2.symm.trans hstep.symm))
      · have hdart : port.dart = caps.innerBoundaryDart step := by
          apply SimpleGraph.Dart.ext
          exact Prod.ext hswapped.1 hswapped.2
        cases port
        cases hdart
        rfl
  · rcases (caps.outer.mem_vertexSupport_iff _).mp houter with ⟨step, hstep⟩
    let portEdge : G.edgeSet := ⟨port.dart.edge, port.dart.edge_mem⟩
    have hincident : portEdge ∈ incidentEdgeFinset G (caps.outer.vertex step) := by
      simp [portEdge, incidentEdgeFinset, SimpleGraph.Dart.edge, ← hstep]
    rw [caps.outer.incident_eq step] at hincident
    simp only [Finset.mem_insert, Finset.mem_singleton] at hincident
    rcases hincident with hcycle | hcycle | hspoke
    · exfalso
      have hfst : port.dart.fst ∈ (caps.outer.cycleEdge step).1 := by
        rw [← congrArg Subtype.val hcycle]
        simp [portEdge, SimpleGraph.Dart.edge]
      rcases caps.outer.cycleEdge_endpoint_eq_vertex step port.dart.fst hfst with
        ⟨capStep, hcapStep⟩
      apply port.retained
      change port.dart.fst ∈ caps.inner.vertexSupport ∪ caps.outer.vertexSupport
      exact Finset.mem_union_right _
        ((caps.outer.mem_vertexSupport_iff _).mpr ⟨capStep, hcapStep⟩)
    · exfalso
      have hfst : port.dart.fst ∈ (caps.outer.cycleEdge (caps.outer.cycleMate step)).1 := by
        rw [← congrArg Subtype.val hcycle]
        simp [portEdge, SimpleGraph.Dart.edge]
      rcases caps.outer.cycleEdge_endpoint_eq_vertex (caps.outer.cycleMate step)
        port.dart.fst hfst with ⟨capStep, hcapStep⟩
      apply port.retained
      change port.dart.fst ∈ caps.inner.vertexSupport ∪ caps.outer.vertexSupport
      exact Finset.mem_union_right _
        ((caps.outer.mem_vertexSupport_iff _).mpr ⟨capStep, hcapStep⟩)
    · right
      refine ⟨step, ?_⟩
      have hpairs : s(port.dart.fst, port.dart.snd) =
          s(caps.outer.vertex step, caps.outer.spokeOuter step) := by
        simpa [portEdge, SimpleGraph.Dart.edge, caps.outer.spokeEdge_eq step] using
          congrArg Subtype.val hspoke
      rcases Sym2.eq_iff.mp hpairs with hstraight | hswapped
      · exact False.elim (caps.outer.spokeOuter_ne_vertex step step
          (hstraight.2.symm.trans hstep.symm))
      · have hdart : port.dart = caps.outerBoundaryDart step := by
          apply SimpleGraph.Dart.ext
          exact Prod.ext hswapped.1 hswapped.2
        cases port
        cases hdart
        rfl

/-- The ten source boundary coordinates map to their corresponding literal
manuscript-side ports. -/
def boundaryPortMap (caps : PentagonCapPair G) :
    Fin 5 ⊕ Fin 5 → DeletedRegionBoundaryPort G caps.deletedVertexSupport
  | Sum.inl step => caps.innerBoundaryPort step
  | Sum.inr step => caps.outerBoundaryPort step

theorem boundaryPortMap_injective (caps : PentagonCapPair G) :
    Function.Injective caps.boundaryPortMap := by
  intro first second heq
  rcases first with first | first <;> rcases second with second | second
  · have hsteps : first = second := caps.inner.vertex.injective (by
      have hends := congrArg
        (fun port : DeletedRegionBoundaryPort G caps.deletedVertexSupport => port.dart.snd) heq
      change caps.inner.vertex first = caps.inner.vertex second at hends
      exact hends)
    exact congrArg Sum.inl hsteps
  · exfalso
    have hends := congrArg
      (fun port : DeletedRegionBoundaryPort G caps.deletedVertexSupport => port.dart.snd) heq
    change caps.inner.vertex first = caps.outer.vertex second at hends
    exact caps.inner_vertex_not_mem_outerSupport first
      ((caps.outer.mem_vertexSupport_iff _).mpr ⟨second, hends.symm⟩)
  · exfalso
    have hends := congrArg
      (fun port : DeletedRegionBoundaryPort G caps.deletedVertexSupport => port.dart.snd) heq
    change caps.outer.vertex first = caps.inner.vertex second at hends
    exact caps.inner_vertex_not_mem_outerSupport second
      ((caps.outer.mem_vertexSupport_iff _).mpr ⟨first, hends⟩)
  · have hsteps : first = second := caps.outer.vertex.injective (by
      have hends := congrArg
        (fun port : DeletedRegionBoundaryPort G caps.deletedVertexSupport => port.dart.snd) heq
      change caps.outer.vertex first = caps.outer.vertex second at hends
      exact hends)
    exact congrArg Sum.inr hsteps

/-- Exact ordered enumeration of the two-cap manuscript boundary. -/
def boundaryPortEquiv (caps : PentagonCapPair G) :
    Fin 5 ⊕ Fin 5 ≃ DeletedRegionBoundaryPort G caps.deletedVertexSupport :=
  Equiv.ofBijective caps.boundaryPortMap
    ⟨caps.boundaryPortMap_injective, by
      intro port
      rcases caps.boundaryPort_eq_inner_or_outer port with hinner | houter
      · rcases hinner with ⟨step, hstep⟩
        exact ⟨Sum.inl step, hstep.symm⟩
      · rcases houter with ⟨step, hstep⟩
        exact ⟨Sum.inr step, hstep.symm⟩⟩

@[simp] theorem boundaryPortEquiv_inner (caps : PentagonCapPair G) (step : Fin 5) :
    caps.boundaryPortEquiv (Sum.inl step) = caps.innerBoundaryPort step :=
  rfl

@[simp] theorem boundaryPortEquiv_outer (caps : PentagonCapPair G) (step : Fin 5) :
    caps.boundaryPortEquiv (Sum.inr step) = caps.outerBoundaryPort step :=
  rfl

end PentagonCapPair

end

end GoertzelV24TwoPentagonCapOpening

end Mettapedia.GraphTheory.FourColor
