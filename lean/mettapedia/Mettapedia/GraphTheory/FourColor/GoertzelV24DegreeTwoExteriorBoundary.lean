import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactor
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# A degree-two exterior component has at most two boundary vertices

Let a finite graph be represented through a bounded interface, and delete the
interface vertices.  In a graph of maximum degree two, every connected
component of the strict exterior can meet the deleted interface through at
most two exterior vertices.  These are the two endpoints of the exterior path;
an exterior cycle has none.

The proof is graph-theoretic rather than pictorial.  A connected graph of
maximum degree two has at most two vertices of degree at most one, by the
handshake identity and the connected lower bound on its number of edges.  A
vertex of an exterior component adjacent to the interface loses at least that
one neighbor when the component is induced, so its component degree is at
most one.

For the rolling facial transfer, this is the structural reason that advancing
the interface removes at most two labels from each old exterior component.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DegreeTwoExteriorBoundary

open Finset
open GoertzelV24InterfaceDeletionComponentFactor
open SimpleGraph

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]

/-- In a finite connected graph of maximum degree two, any specified set of
vertices whose degrees are at most one has cardinality at most two. -/
theorem card_boundary_le_two
    (boundary : Finset W) (hconnected : H.Connected)
    (hdegree : ∀ vertex, H.degree vertex ≤ 2)
    (hboundary : ∀ vertex ∈ boundary, H.degree vertex ≤ 1) :
    boundary.card ≤ 2 := by
  have hpointwise : ∀ vertex : W,
      H.degree vertex + (if vertex ∈ boundary then 1 else 0) ≤ 2 := by
    intro vertex
    by_cases hmem : vertex ∈ boundary
    · simp only [if_pos hmem]
      exact Nat.add_le_of_le_sub (by omega) (hboundary vertex hmem)
    · simpa [hmem] using hdegree vertex
  have hsum := Finset.sum_le_sum fun vertex
    (_hvertex : vertex ∈ (Finset.univ : Finset W)) => hpointwise vertex
  have hupper :
      (∑ vertex : W, H.degree vertex) + boundary.card ≤
        2 * Fintype.card W := by
    simpa [Finset.sum_add_distrib, Nat.mul_comm] using hsum
  have hlower : Fintype.card W ≤ H.edgeFinset.card + 1 := by
    simpa [Nat.card_eq_fintype_card, ← H.edgeFinset_card] using
      hconnected.card_vert_le_card_edgeSet_add_one
  have hhandshake :
      (∑ vertex : W, H.degree vertex) = 2 * H.edgeFinset.card :=
    H.sum_degrees_eq_twice_card_edges
  omega

variable {N Interface : Type*} [Fintype N] [DecidableEq N]
  [Fintype Interface]

/-- Vertices of one strict-exterior component that are adjacent in the
original graph to at least one represented interface vertex. -/
noncomputable def exteriorComponentBoundaryVertices
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (component : (exteriorGraph graph interfaceVertex).ConnectedComponent) :
    Finset component := by
  classical
  letI : Fintype component := Fintype.ofFinite component
  exact Finset.univ.filter fun vertex =>
    ∃ slot, graph.Adj (interfaceVertex slot) vertex.1

omit [DecidableEq N] in
@[simp]
theorem mem_exteriorComponentBoundaryVertices_iff
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (component : (exteriorGraph graph interfaceVertex).ConnectedComponent)
    (vertex : component) :
    vertex ∈ exteriorComponentBoundaryVertices graph interfaceVertex component ↔
      ∃ slot, graph.Adj (interfaceVertex slot) vertex.1 := by
  classical
  simp [exteriorComponentBoundaryVertices]

omit [Fintype N] [DecidableEq N] [Fintype Interface] in
/-- Every vertex reachable from a strict-exterior root in the exterior graph
is itself strictly exterior. -/
theorem outsideInterface_of_exteriorGraph_reachable
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    {root vertex : N} (hroot : OutsideInterface interfaceVertex root)
    (hreachable : (exteriorGraph graph interfaceVertex).Reachable root vertex) :
    OutsideInterface interfaceVertex vertex := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreachable
  induction hreachable with
  | refl => exact hroot
  | tail _ hadj _ => exact hadj.2.2

omit [DecidableEq N] in
/-- A boundary vertex of a strict-exterior component has component degree at
most one when the ambient graph has maximum degree two.  One ambient neighbour
is represented by the deleted interface, so it is missing from the induced
component. -/
theorem exteriorComponent_degree_le_one_of_mem_boundary
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (interfaceVertex : Interface → N)
    (component : (exteriorGraph graph interfaceVertex).ConnectedComponent)
    [Fintype component]
    [DecidableRel component.toSimpleGraph.Adj]
    {root : N} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface interfaceVertex root)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2)
    (vertex : component)
    (hboundary : vertex ∈
      exteriorComponentBoundaryVertices graph interfaceVertex component) :
    component.toSimpleGraph.degree vertex ≤ 1 := by
  classical
  let componentGraph := component.toSimpleGraph
  let includeNeighbor :
      componentGraph.neighborSet vertex → graph.neighborSet vertex.1 :=
    fun neighbor =>
      ⟨neighbor.1.1,
        ((component.toSimpleGraph_adj vertex.2 neighbor.1.2).1
          neighbor.2).1⟩
  have hinjective : Function.Injective includeNeighbor := by
    intro first second heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun value : graph.neighborSet vertex.1 => value.1) heq
  have hcomponentOutside : ∀ candidate : component,
      OutsideInterface interfaceVertex candidate.1 := by
    intro candidate
    exact outsideInterface_of_exteriorGraph_reachable graph interfaceVertex
      hrootOutside (component.reachable_of_mem_supp hroot candidate.2)
  rcases (mem_exteriorComponentBoundaryVertices_iff graph interfaceVertex
    component vertex).1 hboundary with ⟨slot, hadj⟩
  let missingNeighbor : graph.neighborSet vertex.1 :=
    ⟨interfaceVertex slot, hadj.symm⟩
  have hmissing : missingNeighbor ∉ Set.range includeNeighbor := by
    rintro ⟨neighbor, heq⟩
    have heqVertex : interfaceVertex slot = neighbor.1.1 :=
      (congrArg
        (fun value : graph.neighborSet vertex.1 => value.1) heq).symm
    exact hcomponentOutside neighbor slot heqVertex.symm
  have hstrict :
      componentGraph.degree vertex < graph.degree vertex.1 := by
    have hcard := Fintype.card_lt_of_injective_of_notMem
      includeNeighbor hinjective hmissing
    rw [componentGraph.card_neighborSet_eq_degree,
      graph.card_neighborSet_eq_degree] at hcard
    exact hcard
  have hambient : graph.degree vertex.1 ≤ 2 := by
    calc
      graph.degree vertex.1 = Fintype.card (graph.neighborSet vertex.1) :=
        (graph.card_neighborSet_eq_degree vertex.1).symm
      _ = (graph.neighborSet vertex.1).ncard :=
        Set.fintypeCard_eq_ncard _
      _ ≤ 2 := hdegree vertex.1
  change componentGraph.degree vertex ≤ 1
  omega

/-- A strict-exterior component of a finite maximum-degree-two graph touches
the interface through at most two of its own vertices. -/
theorem card_exteriorComponentBoundaryVertices_le_two
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (interfaceVertex : Interface → N)
    (component : (exteriorGraph graph interfaceVertex).ConnectedComponent)
    {root : N} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface interfaceVertex root)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2) :
    (exteriorComponentBoundaryVertices graph interfaceVertex component).card ≤
      2 := by
  classical
  let componentGraph := component.toSimpleGraph
  let includeNeighbor (vertex : component) :
      componentGraph.neighborSet vertex → graph.neighborSet vertex.1 :=
    fun neighbor =>
      ⟨neighbor.1.1,
        ((component.toSimpleGraph_adj vertex.2 neighbor.1.2).1
          neighbor.2).1⟩
  have hinjective (vertex : component) :
      Function.Injective (includeNeighbor vertex) := by
    intro first second heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun value : graph.neighborSet vertex.1 => value.1) heq
  have hgraphDegree : ∀ vertex, graph.degree vertex ≤ 2 := by
    intro vertex
    calc
      graph.degree vertex = Fintype.card (graph.neighborSet vertex) :=
        (graph.card_neighborSet_eq_degree vertex).symm
      _ = (graph.neighborSet vertex).ncard :=
        Set.fintypeCard_eq_ncard _
      _ ≤ 2 := hdegree vertex
  have hcomponentDegree : ∀ vertex : component,
      componentGraph.degree vertex ≤ 2 := by
    intro vertex
    have hcard :
        Fintype.card (componentGraph.neighborSet vertex) ≤
          Fintype.card (graph.neighborSet vertex.1) :=
      Fintype.card_le_of_injective _ (hinjective vertex)
    rw [componentGraph.card_neighborSet_eq_degree,
      graph.card_neighborSet_eq_degree] at hcard
    exact hcard.trans (hgraphDegree vertex.1)
  have hcomponentOutside : ∀ vertex : component,
      OutsideInterface interfaceVertex vertex.1 := by
    intro vertex
    exact outsideInterface_of_exteriorGraph_reachable graph interfaceVertex
      hrootOutside (component.reachable_of_mem_supp hroot vertex.2)
  apply card_boundary_le_two
    (H := componentGraph)
    (exteriorComponentBoundaryVertices graph interfaceVertex component)
    component.connected_toSimpleGraph hcomponentDegree
  intro vertex hboundary
  rcases (mem_exteriorComponentBoundaryVertices_iff graph interfaceVertex
    component vertex).1 hboundary with ⟨slot, hadj⟩
  let missingNeighbor : graph.neighborSet vertex.1 :=
    ⟨interfaceVertex slot, hadj.symm⟩
  have hmissing : missingNeighbor ∉ Set.range (includeNeighbor vertex) := by
    rintro ⟨neighbor, heq⟩
    have heqVertex : interfaceVertex slot = neighbor.1.1 :=
      (congrArg
        (fun value : graph.neighborSet vertex.1 => value.1) heq).symm
    exact hcomponentOutside neighbor slot heqVertex.symm
  have hstrict : componentGraph.degree vertex < graph.degree vertex.1 := by
    have hcard := Fintype.card_lt_of_injective_of_notMem
      (includeNeighbor vertex) (hinjective vertex) hmissing
    rw [componentGraph.card_neighborSet_eq_degree,
      graph.card_neighborSet_eq_degree] at hcard
    exact hcard
  have hambient := hgraphDegree vertex.1
  omega

variable {Label : Type*} [DecidableEq Label]

/-- Labels carried by all vertices of one strict-exterior component. -/
noncomputable def exteriorComponentLabelSupport
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (label : N → Label)
    (component : (exteriorGraph graph interfaceVertex).ConnectedComponent) :
    Finset Label := by
  classical
  letI : Fintype component := Fintype.ofFinite component
  exact Finset.univ.image fun vertex : component => label vertex.1

omit [DecidableEq N] [Fintype Interface] in
@[simp]
theorem mem_exteriorComponentLabelSupport_iff
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (label : N → Label)
    (component : (exteriorGraph graph interfaceVertex).ConnectedComponent)
    (value : Label) :
    value ∈ exteriorComponentLabelSupport graph interfaceVertex label
        component ↔
      ∃ vertex : component, label vertex.1 = value := by
  classical
  simp [exteriorComponentLabelSupport]

/-- Labels on the exterior vertices through which one component meets the
represented interface.  Repeated labels are counted only once. -/
noncomputable def exteriorComponentBoundaryLabels
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (label : N → Label)
    (component : (exteriorGraph graph interfaceVertex).ConnectedComponent) :
    Finset Label :=
  (exteriorComponentBoundaryVertices graph interfaceVertex component).image
    fun vertex => label vertex.1

omit [DecidableEq N] in
@[simp]
theorem mem_exteriorComponentBoundaryLabels_iff
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (label : N → Label)
    (component : (exteriorGraph graph interfaceVertex).ConnectedComponent)
    (value : Label) :
    value ∈ exteriorComponentBoundaryLabels graph interfaceVertex label
        component ↔
      ∃ vertex ∈ exteriorComponentBoundaryVertices graph interfaceVertex
          component,
        label vertex.1 = value := by
  classical
  simp [exteriorComponentBoundaryLabels]

omit [DecidableEq N] in
/-- Every boundary label is carried by the component it bounds. -/
theorem exteriorComponentBoundaryLabels_subset_labelSupport
    (graph : SimpleGraph N) (interfaceVertex : Interface → N)
    (label : N → Label)
    (component : (exteriorGraph graph interfaceVertex).ConnectedComponent) :
    exteriorComponentBoundaryLabels graph interfaceVertex label component ⊆
      exteriorComponentLabelSupport graph interfaceVertex label component := by
  intro value hvalue
  rcases (mem_exteriorComponentBoundaryLabels_iff graph interfaceVertex label
    component value).1 hvalue with ⟨vertex, _hboundary, rfl⟩
  exact (mem_exteriorComponentLabelSupport_iff graph interfaceVertex label
    component _).2
    ⟨vertex, rfl⟩

/-- The endpoint theorem descends through any vertex-label map: a regional
component exposes at most two distinct labels at the interface. -/
theorem card_exteriorComponentBoundaryLabels_le_two
    (graph : SimpleGraph N) [DecidableRel graph.Adj]
    (interfaceVertex : Interface → N) (label : N → Label)
    (component : (exteriorGraph graph interfaceVertex).ConnectedComponent)
    {root : N} (hroot : root ∈ component.supp)
    (hrootOutside : OutsideInterface interfaceVertex root)
    (hdegree : ∀ vertex, (graph.neighborSet vertex).ncard ≤ 2) :
    (exteriorComponentBoundaryLabels graph interfaceVertex label component
      ).card ≤ 2 := by
  calc
    (exteriorComponentBoundaryLabels graph interfaceVertex label component
      ).card ≤
        (exteriorComponentBoundaryVertices graph interfaceVertex component
          ).card := Finset.card_image_le
    _ ≤ 2 := card_exteriorComponentBoundaryVertices_le_two graph
      interfaceVertex component hroot hrootOutside hdegree

end GoertzelV24DegreeTwoExteriorBoundary

end Mettapedia.GraphTheory.FourColor
