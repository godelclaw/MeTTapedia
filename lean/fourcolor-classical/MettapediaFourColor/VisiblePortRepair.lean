import MettapediaFourColor.ThreeBlockReconstruction
import Mettapedia.GraphTheory.FourColor.AnchoredBoundaryExample
import Mettapedia.GraphTheory.Kempe.PairHistory

/-!
# A visible boundary change repairs an anchored exterior

For the initial three-run word, switching only port six from colour three
to colour one admits a direct core assignment. This provides an alternative
to preserving that word while preparing a complementary path. The actual
example has no nontrivial boundary-preserving history, but its three-vertex
component effects precisely this repair.
-/

namespace FourColor.VisiblePortRepair

open SimpleGraph Color ThreeBlockCore FiveTriangleCollapseObstruction

def assignment : Fin 18 → Color :=
  ![c1,c3,c2,c3,c1,c0,c1,c0,c2,c0,c2,c3,c2,c3,c1,c1,c1,c0]

theorem assignment_proper : ∀ u v, upper.graph.Adj u v → assignment u ≠ assignment v := by
  decide +kernel

def sourceColouring : upper.graph.Coloring Color :=
  .mk assignment (fun h => assignment_proper _ _ h)

theorem boundary_assignment : ∀ j : Fin 11, sourceColouring (j.castAdd 7) =
    if j = 6 then Equiv.swap c1 c3 (word false false false j)
      else word false false false j := by decide +kernel

/-- The component of port six may be arbitrarily large. Its boundary
observation, rather than its internal size, determines reconstruction. -/
theorem repair_of_isolated_port {W : Type*} {H : SimpleGraph W}
    (C : H.Coloring Color) (ports : Fin 11 → W)
    (boundary : ∀ j, C (ports j) = word false false false j)
    (K : (C.bicoloredSubgraph c1 c3).ConnectedComponent)
    (membership : ∀ j, ports j ∈ C.kempeComponentSet c1 c3 K ↔ j = 6) :
    ∃ D : H.Coloring Color, H.KempeStep C D ∧
      ∀ j : Fin 11, sourceColouring (j.castAdd 7) = D (ports j) := by
  classical
  refine ⟨C.swapOnKempeComponent c1 c3 K, H.kempeStep_swapOnKempeComponent C c1 c3 K, ?_⟩
  intro j
  change _ = if ports j ∈ C.kempeComponentSet c1 c3 K then
    Equiv.swap c1 c3 (C (ports j)) else C (ports j)
  simp only [membership, boundary]
  exact boundary_assignment j

/-- Avoiding the two other boundary runs is enough. Their adjacent port
pairs cannot split across different components. -/
theorem isolated_of_two_exclusions {W : Type*} {H : SimpleGraph W}
    (C : H.Coloring Color) (ports : Fin 11 → W)
    (boundary : ∀ j, C (ports j) = word false false false j)
    (edge01 : H.Adj (ports 0) (ports 1)) (edge34 : H.Adj (ports 3) (ports 4))
    (K : (C.bicoloredSubgraph c1 c3).ConnectedComponent)
    (m6 : ports 6 ∈ C.kempeComponentSet c1 c3 K)
    (n1 : ports 1 ∉ C.kempeComponentSet c1 c3 K)
    (n3 : ports 3 ∉ C.kempeComponentSet c1 c3 K) :
    ∀ j, ports j ∈ C.kempeComponentSet c1 c3 K ↔ j = 6 := by
  have n0 : ports 0 ∉ C.kempeComponentSet c1 c3 K := fun h =>
    n1 (C.mem_kempeComponentSet_of_adj h edge01 (Or.inr (boundary 1)))
  have n4 : ports 4 ∉ C.kempeComponentSet c1 c3 K := fun h =>
    n3 (C.mem_kempeComponentSet_of_adj h edge34.symm (Or.inr (boundary 3)))
  have inactive (j : Fin 11) (h : j = 2 ∨ j = 5 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10) :
      ports j ∉ C.kempeComponentSet c1 c3 K := by
    intro member
    have a := C.mem_bicoloredSet_of_mem_kempeComponentSet member
    rw [boundary] at a
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> contradiction
  intro j
  fin_cases j
  · exact iff_of_false n0 (by decide)
  · exact iff_of_false n1 (by decide)
  · exact iff_of_false (inactive 2 (by simp)) (by decide)
  · exact iff_of_false n3 (by decide)
  · exact iff_of_false n4 (by decide)
  · exact iff_of_false (inactive 5 (by simp)) (by decide)
  · exact iff_of_true m6 rfl
  · exact iff_of_false (inactive 7 (by simp)) (by decide)
  · exact iff_of_false (inactive 8 (by simp)) (by decide)
  · exact iff_of_false (inactive 9 (by simp)) (by decide)
  · exact iff_of_false (inactive 10 (by simp)) (by decide)

open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation ThreeBlockGeometry

/-- The alternative consumes the same exact exterior/core gluing theorem.
No new global colouring theorem or repair table is used. -/
theorem whole_repair_of_isolated_port {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}
    {data : Data G} {s : ThreeBlockGeometry.Patch data} (e : ExteriorReading s H)
    (covers : ∀ v, s.Exterior v → ∃ w, e.embedding w = v)
    (stars : ∀ i : Fin 18, 11 ≤ i.val → ∀ v, G.Adj (s.point i) v →
      ∃ j, s.point j = v ∧ upper.graph.Adj i j)
    (C : H.Coloring Color) (boundary : ∀ j, C (e.ports j) = word false false false j)
    (K : (C.bicoloredSubgraph c1 c3).ConnectedComponent)
    (m6 : e.ports 6 ∈ C.kempeComponentSet c1 c3 K)
    (n1 : e.ports 1 ∉ C.kempeComponentSet c1 c3 K)
    (n3 : e.ports 3 ∉ C.kempeComponentSet c1 c3 K) :
    ∃ D : H.Coloring Color, H.KempeStep C D ∧
      ∃ k : G.Coloring Color, ∀ w, k (e.embedding w) = D w := by
  have membership := isolated_of_two_exclusions C e.ports boundary
    (e.port_adj 0 1 (by decide +kernel)) (e.port_adj 3 4 (by decide +kernel)) K m6 n1 n3
  obtain ⟨D, step, agree⟩ := repair_of_isolated_port C e.ports boundary K membership
  obtain ⟨k, reads, _⟩ := e.reconstruct covers stars D sourceColouring agree
  exact ⟨D,step,k,reads⟩

open Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness

/-- For this boundary word, the two proved repairs leave one precise
connectivity case: port six joins the second one/three run, but not the
first. This residual case is not asserted to be impossible. -/
theorem whole_repair_or_residual {V W : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W}
    {data : Data G} {s : ThreeBlockGeometry.Patch data} (e : ExteriorReading s H)
    (rotation : VertexRotationCyclic data.toRotationSystem)
    (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (connected : G.Connected)
    (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (covers : ∀ v, s.Exterior v → ∃ w, e.embedding w = v)
    (stars : ∀ i : Fin 18, 11 ≤ i.val → ∀ v, G.Adj (s.point i) v →
      ∃ j, s.point j = v ∧ upper.graph.Adj i j)
    (C : H.Coloring Color) (boundary : ∀ j, C (e.ports j) = word false false false j) :
    (∃ D : H.Coloring Color, H.KempeStep C D ∧
      ∃ k : G.Coloring Color, ∀ w, k (e.embedding w) = D w) ∨
    ∃ K : (C.bicoloredSubgraph c1 c3).ConnectedComponent,
      e.ports 6 ∈ C.kempeComponentSet c1 c3 K ∧
      e.ports 3 ∈ C.kempeComponentSet c1 c3 K ∧
      e.ports 1 ∉ C.kempeComponentSet c1 c3 K := by
  classical
  have a6 : C (e.ports 6) = c1 ∨ C (e.ports 6) = c3 := Or.inr (boundary 6)
  let K := (C.bicoloredSubgraph c1 c3).connectedComponentMk ⟨e.ports 6,a6⟩
  have m6 : e.ports 6 ∈ C.kempeComponentSet c1 c3 K := C.mem_kempeComponentSet_self a6
  by_cases m1 : e.ports 1 ∈ C.kempeComponentSet c1 c3 K
  · left
    obtain ⟨a1,k1⟩ := m1
    obtain ⟨a6,k6⟩ := m6
    obtain ⟨q⟩ := ConnectedComponent.exact (k1.trans k6.symm)
    let forget : C.bicoloredSubgraph c1 c3 →g H := ⟨Subtype.val, fun h => h⟩
    apply e.whole_repair_of_path rotation dual connected euler covers stars C boundary (q.map forget)
    intro x hx
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨z,_,rfl⟩ := hx
    exact z.property
  · by_cases m3 : e.ports 3 ∈ C.kempeComponentSet c1 c3 K
    · exact Or.inr ⟨K,m6,m3,m1⟩
    · exact Or.inl (whole_repair_of_isolated_port e covers stars C boundary K m6 m1 m3)

namespace Example

open SimpleGraph.AnchoredBoundaryExample

def palette : Fin 4 → Color := ![c0,c1,c2,c3]

theorem initial_boundary : ∀ j : Fin 11,
    palette (initial (ports.get j)) = word false false false j := by decide +kernel

theorem initial_rejects (k : upper.graph.Coloring Color)
    (agree : ∀ j : Fin 11, k (j.castAdd 7) = palette (initial (ports.get j))) : False := by
  have h := necessary false false false k (fun j => (agree j).trans (initial_boundary j))
  exact h.2 rfl

private theorem active02 : ∀ v : Fin 155,
    (initial v = 0 ∨ initial v = 2) → v ∈ chain 4 := by decide +kernel

/-- There is just one initial zero/two component. Thus an arbitrarily
long phase either changes all active vertices or none of them. -/
theorem phase_global (D : graph.Coloring (Fin 4))
    (history : Relation.ReflTransGen (KempePairHistory.Step 0 2) initial D) :
    (∀ v, D v = initial v) ∨ (∀ v, D v = Equiv.swap 0 2 (initial v)) := by
  have pw := KempePairHistory.pointwise history
  have rootActive : initial (13 : Fin 155) = 0 ∨ initial 13 = 2 := by decide +kernel
  have carries {u v : Fin 155} (hu : initial u = 0 ∨ initial u = 2)
      (hv : initial v = 0 ∨ initial v = 2) :
      v ∈ initial.kempeComponentSet 0 2
        ((initial.bicoloredSubgraph 0 2).connectedComponentMk ⟨u,hu⟩) :=
    initial.mem_component_along_chain 0 2 _ (chain 4) (connected 4) (active 4)
      (active02 u hu) (active02 v hv) (initial.mem_kempeComponentSet_self hu)
  by_cases changed : D 13 ≠ initial 13
  · right
    intro v
    by_cases hv : initial v = 0 ∨ initial v = 2
    · exact (pw v).resolve_left (KempePairHistory.component_changed history changed rootActive
        (carries rootActive hv))
    · rcases pw v with h | h
      · rw [h, Equiv.swap_apply_of_ne_of_ne (fun e => hv (Or.inl e)) (fun e => hv (Or.inr e))]
      · exact h
  · left
    intro v
    by_contra moved
    have eq := (pw v).resolve_left moved
    have hv : initial v = 0 ∨ initial v = 2 :=
      Equiv.eq_or_eq_of_swap_apply_ne_self (fun h => moved (eq.trans h))
    exact changed (KempePairHistory.component_changed history moved hv (carries hv rootActive))

/-- The failed supplier is exact: arbitrary silent preparation followed
by an arbitrarily long zero/two phase still cannot reconstruct this core.
Other final colour pairs are deliberately not excluded. -/
theorem no_silent_then_tail_phase (D E : graph.Coloring (Fin 4))
    (preparation : Relation.ReflTransGen (graph.KempeStepAvoiding boundary) initial D)
    (phase : Relation.ReflTransGen (KempePairHistory.Step 0 2) D E)
    (k : upper.graph.Coloring Color)
    (agree : ∀ j : Fin 11, k (j.castAdd 7) = palette (E (ports.get j))) : False := by
  rw [silent_history_fixed D preparation] at phase
  rcases phase_global E phase with unchanged | swapped
  · exact initial_rejects k (fun j => (agree j).trans (congrArg palette (unchanged _)))
  · have table : ∀ j : Fin 11, palette (Equiv.swap 0 2 (initial (ports.get j))) =
        word true true true j := by decide +kernel
    have bad := necessary true true true k (fun j =>
      (agree j).trans ((congrArg palette (swapped _)).trans (table j)))
    exact bad.2 rfl

theorem repaired_boundary : ∀ j : Fin 11,
    sourceColouring (j.castAdd 7) = palette (repaired (ports.get j)) := by
  have table : ∀ j : Fin 11, sourceColouring (j.castAdd 7) =
      palette (if ports.get j ∈ repairTrace then Equiv.swap 1 3 (initial (ports.get j))
        else initial (ports.get j)) := by decide +kernel
  intro j
  rw [repaired_apply]
  exact table j

/-- The very same exterior has a physical one-switch repair when a port
change is permitted. -/
theorem visible_repair : ∃ D : graph.Coloring (Fin 4), graph.KempeStep initial D ∧
    ∃ k : upper.graph.Coloring Color, ∀ j : Fin 11,
      k (j.castAdd 7) = palette (D (ports.get j)) :=
  ⟨repaired,physical_repair,sourceColouring,repaired_boundary⟩

end Example
end FourColor.VisiblePortRepair
