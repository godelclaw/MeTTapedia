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

/-- The breadth-first sphere of radius `i` about a root, inside its own
component. -/
noncomputable def sphere (G : SimpleGraph V) (r : V) (i : ℕ) : Finset V :=
  Finset.univ.filter fun v => G.Reachable r v ∧ G.dist r v = i

@[simp] theorem mem_sphere {r v : V} {i : ℕ} :
    v ∈ sphere G r i ↔ G.Reachable r v ∧ G.dist r v = i := by simp [sphere]

/-- The component of a root. -/
noncomputable def ball (G : SimpleGraph V) (r : V) : Finset V :=
  Finset.univ.filter fun v => G.Reachable r v

@[simp] theorem mem_ball {r v : V} : v ∈ ball G r ↔ G.Reachable r v := by simp [ball]

/-- **A vertex at positive distance has a neighbour one step closer.**  This is the
only walk-level fact the layer count needs. -/
theorem exists_adj_dist_eq {r v : V} (hreach : G.Reachable r v) {i : ℕ}
    (h : G.dist r v = i + 1) :
    ∃ u : V, G.Adj u v ∧ G.Reachable r u ∧ G.dist r u = i := by
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  rw [h] at hp
  have hnil : ¬ p.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq, hp]
    omega
  have hru : G.Reachable r p.penultimate := p.dropLast.reachable
  refine ⟨p.penultimate, p.adj_penultimate hnil, hru, ?_⟩
  have hdrop : p.dropLast.length = i := by
    have := SimpleGraph.Walk.length_dropLast_add_one hnil
    omega
  have hle : G.dist r p.penultimate ≤ i := by
    have := SimpleGraph.dist_le p.dropLast
    omega
  have hge : i ≤ G.dist r p.penultimate := by
    obtain ⟨p', hp'⟩ := hru.exists_walk_length_eq_dist
    have hcon : G.dist r v ≤ (p'.concat (p.adj_penultimate hnil)).length :=
      SimpleGraph.dist_le _
    rw [SimpleGraph.Walk.length_concat, hp', h] at hcon
    omega
  omega

/-- The sphere of radius zero is the root alone. -/
theorem sphere_zero (r : V) : sphere G r 0 = {r} := by
  ext v
  simp only [mem_sphere, Finset.mem_singleton]
  constructor
  · rintro ⟨hre, h⟩
    exact ((hre.dist_eq_zero_iff).1 h).symm
  · rintro rfl
    exact ⟨SimpleGraph.Reachable.refl _, SimpleGraph.dist_self⟩

/-! ## The breadth-first layer count -/

variable [DecidableRel G.Adj]

/-- Radius one is contained in the root's neighbourhood. -/
theorem sphere_one_subset (r : V) : sphere G r 1 ⊆ G.neighborFinset r := by
  intro v hv
  rw [mem_sphere] at hv
  obtain ⟨u, hadj, hru, hu⟩ := exists_adj_dist_eq hv.1 (i := 0) (by simpa using hv.2)
  have hur : r = u := (hru.dist_eq_zero_iff).1 hu
  subst hur
  simpa using hadj

/-- **One neighbour is spent going back.**  A vertex at distance `i+1` has a
neighbour at distance `i`, which is not at distance `i+2`, so at most `B - 1` of
its neighbours advance. -/
theorem card_neighbors_advancing_le {B : ℕ}
    (hdeg : ∀ v : V, G.degree v ≤ B) (r : V) (i : ℕ)
    {u : V} (hu : u ∈ sphere G r (i + 1)) :
    (G.neighborFinset u ∩ sphere G r (i + 2)).card ≤ B - 1 := by
  rw [mem_sphere] at hu
  obtain ⟨w, hadj, -, hw⟩ := exists_adj_dist_eq hu.1 hu.2
  have hwmem : w ∈ G.neighborFinset u := by simpa using hadj.symm
  have hwnot : w ∉ sphere G r (i + 2) := by
    rw [mem_sphere]
    rintro ⟨-, h2⟩
    omega
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
theorem card_sphere_succ_le_sum (r : V) (i : ℕ) :
    (sphere G r (i + 1)).card ≤
      ∑ u ∈ sphere G r i, (G.neighborFinset u ∩ sphere G r (i + 1)).card := by
  have hsub : sphere G r (i + 1) ⊆
      (sphere G r i).biUnion (fun u => G.neighborFinset u ∩ sphere G r (i + 1)) := by
    intro v hv
    have hv' := mem_sphere.1 hv
    obtain ⟨u, hadj, hru, hu⟩ := exists_adj_dist_eq hv'.1 hv'.2
    exact Finset.mem_biUnion.2 ⟨u, mem_sphere.2 ⟨hru, hu⟩,
      Finset.mem_inter.2 ⟨by simpa using hadj, hv⟩⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)

/-- **The layer recursion.** -/
theorem card_sphere_succ_le {B : ℕ}
    (hdeg : ∀ v : V, G.degree v ≤ B) (r : V) (i : ℕ) :
    (sphere G r (i + 2)).card ≤ (B - 1) * (sphere G r (i + 1)).card := by
  refine le_trans (card_sphere_succ_le_sum r (i + 1)) ?_
  calc ∑ u ∈ sphere G r (i + 1), (G.neighborFinset u ∩ sphere G r (i + 2)).card
      ≤ ∑ _u ∈ sphere G r (i + 1), (B - 1) :=
        Finset.sum_le_sum fun u hu => card_neighbors_advancing_le hdeg r i hu
    _ = (sphere G r (i + 1)).card * (B - 1) := by simp [Finset.sum_const, smul_eq_mul]
    _ = (B - 1) * (sphere G r (i + 1)).card := Nat.mul_comm _ _

/-- **The sphere bound.** -/
theorem card_sphere_le {B : ℕ} (hdeg : ∀ v : V, G.degree v ≤ B) (r : V) (i : ℕ) :
    (sphere G r (i + 1)).card ≤ B * (B - 1) ^ i := by
  induction i with
  | zero =>
      have h1 := Finset.card_le_card (sphere_one_subset (G := G) r)
      rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
      simpa using le_trans h1 (hdeg r)
  | succ i ih =>
      refine le_trans (card_sphere_succ_le hdeg r i) ?_
      calc (B - 1) * (sphere G r (i + 1)).card
          ≤ (B - 1) * (B * (B - 1) ^ i) := Nat.mul_le_mul_left _ ih
        _ = B * (B - 1) ^ (i + 1) := by ring

/-- The Moore-style threshold. -/
def mooreBound (B L : ℕ) : ℕ := 1 + B * ∑ i ∈ Finset.range (L - 1), (B - 1) ^ i

/-- **A shallow component of a bounded-degree graph is small.** -/
theorem card_ball_le_mooreBound {B L : ℕ} (hdeg : ∀ v : V, G.degree v ≤ B) (r : V)
    (hdiam : ∀ v : V, G.Reachable r v → G.dist r v < L) :
    (ball G r).card ≤ mooreBound B L := by
  classical
  have hcover : ball G r ⊆ (Finset.range L).biUnion (sphere G r) := by
    intro v hv
    have hre := mem_ball.1 hv
    exact Finset.mem_biUnion.2
      ⟨G.dist r v, Finset.mem_range.2 (hdiam v hre), mem_sphere.2 ⟨hre, rfl⟩⟩
  have hle : (ball G r).card ≤ ∑ i ∈ Finset.range L, (sphere G r i).card :=
    le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
  refine le_trans hle ?_
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [mooreBound]
  · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have hzero : (sphere G r 0).card = 1 := by rw [sphere_zero]; simp
    have hrest : ∑ i ∈ Finset.range L', (sphere G r (i + 1)).card ≤
        ∑ i ∈ Finset.range L', B * (B - 1) ^ i :=
      Finset.sum_le_sum fun i _ => card_sphere_le hdeg r i
    have hmul : ∑ i ∈ Finset.range L', B * (B - 1) ^ i =
        B * ∑ i ∈ Finset.range L', (B - 1) ^ i := by rw [Finset.mul_sum]
    simp only [mooreBound, hzero, Nat.add_sub_cancel]
    omega

/-- **The dichotomy.**  A component with more than the Moore-threshold many
vertices contains a vertex at distance at least `L` from the root, hence a
geodesic of at least `L` edges. -/
theorem exists_dist_ge_of_mooreBound_lt {B L : ℕ} (hdeg : ∀ v : V, G.degree v ≤ B)
    (r : V) (hcard : mooreBound B L < (ball G r).card) :
    ∃ v : V, G.Reachable r v ∧ L ≤ G.dist r v := by
  by_contra hno
  push_neg at hno
  exact absurd (card_ball_le_mooreBound hdeg r hno) (by omega)

/-- On a connected graph the component is everything. -/
theorem ball_eq_univ (hconn : G.Connected) (r : V) : ball G r = Finset.univ := by
  ext v
  simp [mem_ball, hconn r v]

/-- The connected form of the dichotomy. -/
theorem exists_dist_ge_of_connected (hconn : G.Connected) {B L : ℕ}
    (hdeg : ∀ v : V, G.degree v ≤ B) (r : V)
    (hcard : mooreBound B L < Fintype.card V) :
    ∃ v : V, L ≤ G.dist r v := by
  obtain ⟨v, -, hv⟩ := exists_dist_ge_of_mooreBound_lt hdeg r
    (by rwa [ball_eq_univ hconn, Finset.card_univ])
  exact ⟨v, hv⟩

end GoertzelV24DualDiameterDichotomy

end Mettapedia.GraphTheory.FourColor
