import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Odd-degree endpoints in one finite graph component

The handshaking lemma applies componentwise: an odd-degree vertex has a
distinct odd-degree partner in the same connected component.  Keeping this
generic fact in a light module lets regional path arguments use it without
importing any collar or closed-web construction.
-/

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]

omit [DecidableEq W] in
/-- Every odd vertex in a finite graph shares its component with a distinct
odd vertex. -/
theorem exists_distinct_reachable_odd_of_odd
    (start : W) (hstartOdd : Odd (H.degree start)) :
    ∃ finish : W, finish ≠ start ∧ Odd (H.degree finish) ∧
      H.Reachable start finish := by
  classical
  let component : H.ConnectedComponent := H.connectedComponentMk start
  letI componentVertexFintype : Fintype component.supp :=
    Subtype.fintype _
  let componentGraph : SimpleGraph component.supp :=
    H.induce component.supp
  have hstartComponent : start ∈ component.supp := by
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  let startInComponent : component.supp :=
    ⟨start, hstartComponent⟩
  have hstartNeighbors : H.neighborSet start ⊆ component.supp := by
    intro neighbor hadjacent
    exact component.mem_supp_of_adj_mem_supp
      hstartComponent hadjacent
  have hstartDegree : componentGraph.degree startInComponent =
      H.degree start := by
    exact SimpleGraph.degree_induce_of_neighborSet_subset
      (G := H) (s := component.supp) (v := startInComponent)
        hstartNeighbors
  have hstartComponentOdd :
      Odd (componentGraph.degree startInComponent) := by
    simpa [hstartDegree] using hstartOdd
  obtain ⟨finishInComponent, hfinishNe, hfinishComponentOdd⟩ :=
    componentGraph.exists_ne_odd_degree_of_exists_odd_degree
      startInComponent hstartComponentOdd
  have hfinishNeighbors : H.neighborSet finishInComponent.1 ⊆
      component.supp := by
    intro neighbor hadjacent
    exact component.mem_supp_of_adj_mem_supp
      finishInComponent.2 hadjacent
  have hfinishDegree : componentGraph.degree finishInComponent =
      H.degree finishInComponent.1 := by
    exact SimpleGraph.degree_induce_of_neighborSet_subset
      (G := H) (s := component.supp) (v := finishInComponent)
        hfinishNeighbors
  have hfinishOdd : Odd (H.degree finishInComponent.1) := by
    simpa [hfinishDegree] using hfinishComponentOdd
  have hfinishDistinct : finishInComponent.1 ≠ start := by
    intro heq
    exact hfinishNe (Subtype.ext heq)
  exact ⟨finishInComponent.1, hfinishDistinct, hfinishOdd,
    component.reachable_of_mem_supp
      hstartComponent finishInComponent.2⟩

omit [DecidableEq W] in
/-- If every odd vertex of a finite support graph is one of its displayed
boundary portals, then an odd portal is connected to a distinct displayed
portal.  The geometric work in applications is the boundary classification;
this lemma only packages the componentwise handshaking consequence. -/
theorem exists_distinct_reachable_mem_of_odd_of_odd_subset
    (start : W) (hstartOdd : Odd (H.degree start)) (boundary : Set W)
    (hoddBoundary : ∀ vertex : W, Odd (H.degree vertex) → vertex ∈ boundary) :
    ∃ finish : W, finish ≠ start ∧ finish ∈ boundary ∧
      H.Reachable start finish := by
  rcases exists_distinct_reachable_odd_of_odd
      (H := H) start hstartOdd with
    ⟨finish, hfinishNe, hfinishOdd, hfinishReachable⟩
  exact ⟨finish, hfinishNe, hoddBoundary finish hfinishOdd,
    hfinishReachable⟩

end Mettapedia.GraphTheory.FourColor
