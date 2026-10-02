import MettapediaFourColor.NearLinearRuleData
import MettapediaFourColor.LocalCoverageAssembly
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Actual rule occurrences and local discharging

The charge convention is that of arXiv:2603.24880v1, Sections 6, 7 and 9.1:
start with `10 * (6 - degree)`, and count each oriented rule once when its
degree-preserving, orientation-preserving homomorphism exists at the marked
edge. The complete pinned rules are decoded in `NearLinearRuleData`.

Occurrences retain actual vertices, edges, degree bounds and every known
cyclic step. They need not be globally injective. Charge is based on existence
of an occurrence, not on the number of witnesses. No C++ checker is trusted.
The cartwheel enumeration and its completeness are not established here.
-/

namespace FourColor.NearLinearCharge

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData LocalCoverageAssembly
open scoped BigOperators

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (rotation : Data G)

/-- A homomorphic reading of one entire oriented rule in actual graph darts. -/
structure Occurrence (r : Fin 84) where
  vertex : Vertex r → V
  edge : ∀ i j, (graph r).Adj i j → G.Adj (vertex i) (vertex j)
  degree : ∀ i, lower r i ≤ G.degree (vertex i) ∧
    (upper r i = 0 ∨ G.degree (vertex i) ≤ upper r i)
  turn : ∀ i j k (hij : (graph r).Adj i j) (hik : (graph r).Adj i k),
    Turn r i j k → rotation.vertexRotation ⟨(vertex i, vertex j), edge i j hij⟩ =
      ⟨(vertex i, vertex k), edge i k hik⟩

namespace Occurrence
variable {rotation} {r : Fin 84} (x : Occurrence rotation r)

/-- All degree and rotation observations of a rule have radius two about
either marked endpoint. This conclusion allows ambient vertex collisions. -/
theorem vertex_near (b : Vertex r) (hb : b ∈ [sender r, receiver r]) (v : Vertex r) :
    x.vertex v ∈ closedBall G (x.vertex b) 2 := by
  rcases local_paths r b hb v with rfl | h | ⟨w, hw, hwv, _, _⟩
  · exact centre_mem G _ _
  · let p : G.Walk (x.vertex b) (x.vertex v) := .cons (x.edge b v h) .nil
    exact (show G.edist (x.vertex b) (x.vertex v) ≤ 1 by
      simpa [p] using p.edist_le).trans (by decide)
  · let p : G.Walk (x.vertex b) (x.vertex v) :=
      .cons (x.edge b w hw) (.cons (x.edge w v hwv) .nil)
    simpa [closedBall, p] using p.edist_le

/-- A rule application forces an actual degree-five vertex close to both
endpoints. The same vertex witnesses the two radius bounds. -/
theorem five_near : ∃ w : V, G.degree w = 5 ∧
    w ∈ closedBall G (x.vertex (sender r)) 2 ∧
    w ∈ closedBall G (x.vertex (receiver r)) 2 := by
  obtain ⟨v, hlo, hup⟩ := five_witness r
  have hd := x.degree v
  rw [hlo, hup] at hd
  refine ⟨x.vertex v, by omega, ?_, ?_⟩
  · exact x.vertex_near _ (by simp) v
  · exact x.vertex_near _ (by simp) v

theorem sender_degree_le : G.degree (x.vertex (sender r)) ≤ 8 := by
  have hd := (x.degree (sender r)).2
  have hb := sender_bound r
  rcases hd with impossible | hd
  · exact False.elim (hb.1 impossible)
  · exact hd.trans hb.2

end Occurrence

def Applies (r : Fin 84) (u v : V) : Prop :=
  ∃ x : Occurrence rotation r, x.vertex (sender r) = u ∧ x.vertex (receiver r) = v

theorem applies_adj {r : Fin 84} {u v : V} (h : Applies rotation r u v) : G.Adj u v := by
  obtain ⟨x, rfl, rfl⟩ := h
  exact x.edge _ _ (endpoint_edge r)

theorem applies_five_near {r : Fin 84} {u v : V} (h : Applies rotation r u v) :
    ∃ w, G.degree w = 5 ∧ w ∈ closedBall G u 2 ∧ w ∈ closedBall G v 2 := by
  obtain ⟨x, rfl, rfl⟩ := h
  exact x.five_near

noncomputable section

/-- Sum of the amounts of the applicable oriented rules, one per source rule. -/
def sent (u v : V) : ℤ := by
  classical
  exact ∑ r : Fin 84, if Applies rotation r u v then (amount r : ℤ) else 0

theorem sent_nonneg (u v : V) : 0 ≤ sent rotation u v := by
  classical
  apply Finset.sum_nonneg
  intro r _
  split_ifs <;> positivity

theorem sent_eq_zero_of_not_adj {u v : V} (h : ¬ G.Adj u v) : sent rotation u v = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro r _
  simp only [ite_eq_right (fun hr => h (applies_adj rotation hr))]

@[simp] theorem sent_self (u : V) : sent rotation u u = 0 :=
  sent_eq_zero_of_not_adj rotation (by simp)

/-- Vertices of degree at least nine never send charge in these rules. -/
theorem sent_eq_zero_of_degree {u v : V} (hd : 9 ≤ G.degree u) : sent rotation u v = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro r _
  have hn : ¬ Applies rotation r u v := by
    rintro ⟨x, hu, _⟩
    have := x.sender_degree_le
    rw [hu] at this
    omega
  simp only [ite_eq_right hn]

/-- The zero-test is valid at either endpoint, with one shared degree-five
witness. It does not approximate the two neighbourhoods independently. -/
theorem sent_eq_zero_of_no_five {u v : V}
    (h : (¬ ∃ w ∈ closedBall G u 2, G.degree w = 5) ∨
      (¬ ∃ w ∈ closedBall G v 2, G.degree w = 5)) : sent rotation u v = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro r _
  have hn : ¬ Applies rotation r u v := by
    intro hr
    obtain ⟨w, hw, hu, hv⟩ := applies_five_near rotation hr
    rcases h with h | h
    · exact h ⟨w, hu, hw⟩
    · exact h ⟨w, hv, hw⟩
  simp only [ite_eq_right hn]

/-- Net charge received from `u` by `v`. -/
def net (u v : V) : ℤ := sent rotation u v - sent rotation v u

@[simp] theorem net_self (u : V) : net rotation u u = 0 := by simp [net]

theorem net_reverse (u v : V) : net rotation u v + net rotation v u = 0 := by
  simp [net]

variable [Fintype V]

/-- The sum over all vertices agrees with the incident-edge convention:
nonedges contribute zero by `sent_eq_zero_of_not_adj`. -/
def finalCharge (v : V) : ℤ :=
  10 * (6 - (G.degree v : ℤ)) + ∑ u : V, net rotation u v

theorem finalCharge_eq_initial_of_no_five {v : V}
    (h : ¬ ∃ w ∈ closedBall G v 2, G.degree w = 5) :
    finalCharge rotation v = 10 * (6 - (G.degree v : ℤ)) := by
  have hz (u : V) : net rotation u v = 0 := by
    rw [net, sent_eq_zero_of_no_five rotation (Or.inr h),
      sent_eq_zero_of_no_five rotation (Or.inl h), sub_self]
  simp [finalCharge, hz]

/-- A first uniform classification prune: a flat centre of degree above six
must see a degree-five vertex within two steps. No planarity is needed. -/
theorem flat_has_five {v : V} (hd : 6 < G.degree v) (hz : finalCharge rotation v = 0) :
    ∃ w ∈ closedBall G v 2, G.degree w = 5 := by
  by_contra h
  have hb := finalCharge_eq_initial_of_no_five rotation h
  rw [hz] at hb
  omega

/-- Charge crossing the boundary of the pair, with the same actual outside
vertex retained in both summands. Transfers between the centres are internal. -/
def pairBoundary (u v : V) : ℤ := by
  classical
  exact ∑ w ∈ (Finset.univ.erase u).erase v, (net rotation w u + net rotation w v)

theorem pair_balance {u v : V} (hne : u ≠ v) :
    finalCharge rotation u + finalCharge rotation v =
      10 * (12 - (G.degree u : ℤ) - (G.degree v : ℤ)) + pairBoundary rotation u v := by
  classical
  let f := fun w => net rotation w u + net rotation w v
  have hsum := Finset.sum_erase_add (Finset.univ : Finset V) f (Finset.mem_univ u)
  have hsum' := Finset.sum_erase_add (Finset.univ.erase u : Finset V) f
    (show v ∈ (Finset.univ : Finset V).erase u by simp [hne.symm])
  have hend : f u + f v = 0 := by
    simp only [f, net_self, zero_add, add_zero]
    exact net_reverse rotation u v
  have hc : (∑ w : V, f w) = pairBoundary rotation u v := by
    change (∑ w : V, f w) = ∑ w ∈ (Finset.univ.erase u).erase v, f w
    omega
  unfold finalCharge
  dsimp only [f] at hc
  rw [Finset.sum_add_distrib] at hc
  linarith

/-- Two flat degree-eight centres require exactly forty units of net
external supply. Their shared edge contributes nothing to this bill. -/
theorem flat_eight_pair_budget {u v : V} (hne : u ≠ v)
    (hu : G.degree u = 8) (hv : G.degree v = 8)
    (hzu : finalCharge rotation u = 0) (hzv : finalCharge rotation v = 0) :
    pairBoundary rotation u v = 40 := by
  have h := pair_balance rotation hne
  rw [hu, hv, hzu, hzv] at h
  norm_num at h
  omega

end
end FourColor.NearLinearCharge
