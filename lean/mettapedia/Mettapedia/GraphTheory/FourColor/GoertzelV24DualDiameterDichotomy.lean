import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# The dual diameter dichotomy

A connected graph of bounded degree and bounded diameter is small.  Contrapositively,
a large connected graph of bounded degree contains a long geodesic.  Applied to the
facial dual of a map whose faces are short, this is the dichotomy the corridor
extraction runs on: either some face is long, or the dual has a long geodesic.

The count is the classical breadth-first layer bound.  Around any root the sphere of
radius zero is a single vertex and the sphere of radius one has at most `B` vertices.
From radius `i ≥ 1` onwards each vertex of the sphere already spends one of its at most
`B` neighbours on a vertex one step closer to the root, so it contributes at most
`B - 1` vertices to the next sphere.  Summing gives

    |V| ≤ 1 + B · ∑_{i<L-1} (B-1)^i

whenever the diameter is at most `L-1`.

Degree here is the underlying *neighbour* count, which is the honest reading for a
facial dual: two faces may share several edges, and the dual then has parallel edges,
but a face of length at most `B` still has at most `B` distinct neighbouring faces.
Loops are excluded because face boundaries are two-sided.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualDiameterDichotomy

open Finset

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The breadth-first sphere of radius `i` about a root. -/
noncomputable def sphere (G : SimpleGraph V) (r : V) (i : ℕ) : Finset V :=
  Finset.univ.filter fun v => G.dist r v = i

@[simp] theorem mem_sphere {r v : V} {i : ℕ} :
    v ∈ sphere G r i ↔ G.dist r v = i := by simp [sphere]

/-- **A vertex at positive distance has a neighbour one step closer.**  This is the
only walk-level fact the layer count needs. -/
theorem exists_adj_dist_eq (hconn : G.Connected) {r v : V} {i : ℕ}
    (h : G.dist r v = i + 1) :
    ∃ u : V, G.Adj u v ∧ G.dist r u = i := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist r v
  rw [h] at hp
  have hnil : ¬ p.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq, hp]
    omega
  refine ⟨p.penultimate, p.adj_penultimate hnil, ?_⟩
  have hdrop : p.dropLast.length = i := by
    have := SimpleGraph.Walk.length_dropLast_add_one hnil
    omega
  have hle : G.dist r p.penultimate ≤ i := by
    have := SimpleGraph.dist_le p.dropLast
    omega
  have hge : i ≤ G.dist r p.penultimate := by
    obtain ⟨p', hp'⟩ := hconn.exists_walk_length_eq_dist r p.penultimate
    have hcon : G.dist r v ≤ (p'.concat (p.adj_penultimate hnil)).length :=
      SimpleGraph.dist_le _
    rw [SimpleGraph.Walk.length_concat, hp', h] at hcon
    omega
  omega

/-- The sphere of radius zero is the root alone. -/
theorem sphere_zero (hconn : G.Connected) (r : V) : sphere G r 0 = {r} := by
  ext v
  simp only [mem_sphere, Finset.mem_singleton]
  constructor
  · intro h
    exact ((hconn.dist_eq_zero_iff).1 h).symm
  · rintro rfl
    exact SimpleGraph.dist_self

/-- Every next-sphere vertex is a neighbour of a current-sphere vertex. -/
theorem sphere_succ_subset [DecidableRel G.Adj] (hconn : G.Connected) (r : V) (i : ℕ) :
    sphere G r (i + 1) ⊆ (sphere G r i).biUnion (fun u => G.neighborFinset u) := by
  intro v hv
  rw [mem_sphere] at hv
  obtain ⟨u, hadj, hu⟩ := exists_adj_dist_eq hconn hv
  exact Finset.mem_biUnion.2 ⟨u, by simpa using hu, by simpa using hadj⟩

/-! ## The breadth-first layer count -/

variable [DecidableRel G.Adj]

/-- Radius one is contained in the root's neighbourhood. -/
theorem sphere_one_subset (hconn : G.Connected) (r : V) :
    sphere G r 1 ⊆ G.neighborFinset r := by
  intro v hv
  rw [mem_sphere] at hv
  obtain ⟨u, hadj, hu⟩ := exists_adj_dist_eq hconn (i := 0) (by simpa using hv)
  have : u = r := by
    have := (hconn.dist_eq_zero_iff).1 hu
    exact this.symm
  subst this
  simpa using hadj

/-- **One neighbour is spent going back.**  A vertex at distance `i+1` has a
neighbour at distance `i`, which is not at distance `i+2`, so at most
`B - 1` of its neighbours advance. -/
theorem card_neighbors_advancing_le (hconn : G.Connected) {B : ℕ}
    (hdeg : ∀ v : V, G.degree v ≤ B) (r : V) (i : ℕ)
    {u : V} (hu : u ∈ sphere G r (i + 1)) :
    (G.neighborFinset u ∩ sphere G r (i + 2)).card ≤ B - 1 := by
  rw [mem_sphere] at hu
  obtain ⟨w, hadj, hw⟩ := exists_adj_dist_eq hconn hu
  have hwmem : w ∈ G.neighborFinset u := by simpa using hadj.symm
  have hwnot : w ∉ sphere G r (i + 2) := by
    rw [mem_sphere, hw]; omega
  have hsub : G.neighborFinset u ∩ sphere G r (i + 2) ⊆ (G.neighborFinset u).erase w := by
    intro x hx
    rw [Finset.mem_inter] at hx
    exact Finset.mem_erase.2 ⟨fun hxw => hwnot (hxw ▸ hx.2), hx.1⟩
  have hcard := Finset.card_le_card hsub
  have herase : ((G.neighborFinset u).erase w).card = G.degree u - 1 := by
    rw [Finset.card_erase_of_mem hwmem, SimpleGraph.card_neighborFinset_eq_degree]
  have hdegu := hdeg u
  omega

/-- Each sphere is covered by the advancing neighbours of the previous one. -/
theorem card_sphere_succ_le_sum (hconn : G.Connected) (r : V) (i : ℕ) :
    (sphere G r (i + 1)).card ≤
      ∑ u ∈ sphere G r i, (G.neighborFinset u ∩ sphere G r (i + 1)).card := by
  have hsub : sphere G r (i + 1) ⊆
      (sphere G r i).biUnion (fun u => G.neighborFinset u ∩ sphere G r (i + 1)) := by
    intro v hv
    obtain ⟨u, hadj, hu⟩ := exists_adj_dist_eq hconn (mem_sphere.1 hv)
    exact Finset.mem_biUnion.2 ⟨u, mem_sphere.2 hu,
      Finset.mem_inter.2 ⟨by simpa using hadj, hv⟩⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)

/-- **The layer recursion.**  From radius one onwards each sphere is at most
`B - 1` times the previous one. -/
theorem card_sphere_succ_le (hconn : G.Connected) {B : ℕ}
    (hdeg : ∀ v : V, G.degree v ≤ B) (r : V) (i : ℕ) :
    (sphere G r (i + 2)).card ≤ (B - 1) * (sphere G r (i + 1)).card := by
  refine le_trans (card_sphere_succ_le_sum hconn r (i + 1)) ?_
  calc ∑ u ∈ sphere G r (i + 1), (G.neighborFinset u ∩ sphere G r (i + 2)).card
      ≤ ∑ _u ∈ sphere G r (i + 1), (B - 1) :=
        Finset.sum_le_sum fun u hu => card_neighbors_advancing_le hconn hdeg r i hu
    _ = (sphere G r (i + 1)).card * (B - 1) := by simp [Finset.sum_const, smul_eq_mul]
    _ = (B - 1) * (sphere G r (i + 1)).card := Nat.mul_comm _ _

/-- **The sphere bound.**  Radius `i+1` holds at most `B(B-1)^i` vertices. -/
theorem card_sphere_le (hconn : G.Connected) {B : ℕ}
    (hdeg : ∀ v : V, G.degree v ≤ B) (r : V) (i : ℕ) :
    (sphere G r (i + 1)).card ≤ B * (B - 1) ^ i := by
  induction i with
  | zero =>
      have := Finset.card_le_card (sphere_one_subset hconn r)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at this
      have := le_trans this (hdeg r)
      simpa using this
  | succ i ih =>
      refine le_trans (card_sphere_succ_le hconn hdeg r i) ?_
      calc (B - 1) * (sphere G r (i + 1)).card
          ≤ (B - 1) * (B * (B - 1) ^ i) := Nat.mul_le_mul_left _ ih
        _ = B * (B - 1) ^ (i + 1) := by ring

/-- The Moore-style threshold: a connected graph of degree at most `B` and
diameter at most `L-1` has at most this many vertices. -/
def mooreBound (B L : ℕ) : ℕ := 1 + B * ∑ i ∈ Finset.range (L - 1), (B - 1) ^ i

/-- **A shallow bounded-degree graph is small.** -/
theorem card_le_mooreBound (hconn : G.Connected) {B L : ℕ}
    (hdeg : ∀ v : V, G.degree v ≤ B) (r : V)
    (hdiam : ∀ v : V, G.dist r v < L) :
    Fintype.card V ≤ mooreBound B L := by
  classical
  have hcover : (Finset.univ : Finset V) ⊆ (Finset.range L).biUnion (sphere G r) := by
    intro v _
    exact Finset.mem_biUnion.2 ⟨G.dist r v, Finset.mem_range.2 (hdiam v), mem_sphere.2 rfl⟩
  have hle : Fintype.card V ≤ ∑ i ∈ Finset.range L, (sphere G r i).card := by
    have := Finset.card_le_card hcover
    simpa using le_trans this Finset.card_biUnion_le
  refine le_trans hle ?_
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [mooreBound]
  · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have hzero : (sphere G r 0).card = 1 := by rw [sphere_zero hconn]; simp
    have hrest : ∑ i ∈ Finset.range L', (sphere G r (i + 1)).card ≤
        ∑ i ∈ Finset.range L', B * (B - 1) ^ i :=
      Finset.sum_le_sum fun i _ => card_sphere_le hconn hdeg r i
    have hmul : ∑ i ∈ Finset.range L', B * (B - 1) ^ i =
        B * ∑ i ∈ Finset.range L', (B - 1) ^ i := by
      rw [Finset.mul_sum]
    simp only [mooreBound, hzero, Nat.add_sub_cancel]
    omega

/-- **The dichotomy.**  A connected bounded-degree graph with more than the
Moore-threshold many vertices has two vertices at distance at least `L`, hence a
geodesic of at least `L` edges. -/
theorem exists_dist_ge_of_mooreBound_lt (hconn : G.Connected) {B L : ℕ}
    (hdeg : ∀ v : V, G.degree v ≤ B) (r : V)
    (hcard : mooreBound B L < Fintype.card V) :
    ∃ v : V, L ≤ G.dist r v := by
  by_contra hno
  push_neg at hno
  exact absurd (card_le_mooreBound hconn hdeg r hno) (by omega)

end GoertzelV24DualDiameterDichotomy

end Mettapedia.GraphTheory.FourColor
