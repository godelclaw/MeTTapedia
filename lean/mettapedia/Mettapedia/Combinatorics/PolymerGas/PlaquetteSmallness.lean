import Mettapedia.Combinatorics.PolymerGas.PlaquetteExpansion
import Mettapedia.Combinatorics.PolymerGas.ConnectedWeight
import Mettapedia.Combinatorics.PolymerGas.LatticeClustering

/-!
# Uniform smallness of the connected plaquette expansion

Bounded support size, diameter, overlap degree and link incidence give an
explicit, volume-independent strong-coupling threshold for the plaquette
activities in the weighted Kotecký–Preiss norm.
-/

set_option autoImplicit false
noncomputable section

open Finset
open scoped Classical

namespace Mettapedia.Combinatorics.PolymerGas

variable {X Pl : Type*} [Fintype X] [DecidableEq X] [PseudoMetricSpace X]
  [Fintype Pl] [DecidableEq Pl]
variable (supp : Pl → Finset X)

/-- The number of links grows at most linearly with the number of plaquettes. -/
theorem card_plaquetteSupport_le {s : ℕ} (hs : ∀ p, (supp p).card ≤ s)
    (C : Finset Pl) : (plaquetteSupport supp C).card ≤ C.card * s :=
  card_biUnion_le_card_mul C supp s (fun p _ => hs p)

/-- A chain of overlapping plaquettes controls the distance of its endpoints. -/
theorem dist_le_plaquetteWalk {r : ℝ} (hr : ∀ p, polymerDiam (supp p) ≤ r)
    {C : Finset Pl} {p q : C} (w : ((plaquetteGraph supp).induce (C : Set Pl)).Walk p q)
    {x y : X} (hx : x ∈ supp p.1) (hy : y ∈ supp q.1) :
    dist x y ≤ (w.length + 1 : ℝ) * r := by
  induction w generalizing x with
  | nil => simpa using (dist_le_polymerDiam hx hy).trans (hr _)
  | @cons p q z hpq w ih =>
    obtain ⟨a, hap, haq⟩ := not_disjoint_iff.mp hpq.2
    calc
      dist x y ≤ dist x a + dist a y := dist_triangle _ _ _
      _ ≤ r + (w.length + 1 : ℝ) * r :=
        add_le_add ((dist_le_polymerDiam hx hap).trans (hr _)) (ih haq hy)
      _ = _ := by simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- A connected union has diameter at most the number of plaquettes times the
largest plaquette diameter. -/
theorem diam_plaquetteSupport_le {r : ℝ} (hr0 : 0 ≤ r)
    (hr : ∀ p, polymerDiam (supp p) ≤ r) {C : Finset Pl}
    (hC : ((plaquetteGraph supp).induce (C : Set Pl)).Connected) :
    polymerDiam (plaquetteSupport supp C) ≤ C.card * r := by
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp hx
  obtain ⟨q, hq, hyq⟩ := mem_biUnion.mp hy
  apply (hC.preconnected ⟨p, hp⟩ ⟨q, hq⟩).elim_path
  intro w
  have hlen := w.isPath.length_lt
  have hcard : Fintype.card (C : Set Pl) = C.card := Fintype.card_coe C
  have hbound : (w.val.length + 1 : ℝ) ≤ C.card := by
    have : w.val.length + 1 ≤ C.card := by omega
    exact_mod_cast this
  exact (dist_le_plaquetteWalk supp hr w.val hxp hyq).trans
    (mul_le_mul_of_nonneg_right hbound hr0)

/-- The weighted contribution of a connected plaquette set is geometric in
its plaquette cardinality. -/
theorem weighted_plaquette_term_le {δ κ r : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hr0 : 0 ≤ r) {s : ℕ} (hs : ∀ p, (supp p).card ≤ s)
    (hr : ∀ p, polymerDiam (supp p) ≤ r) {C : Finset Pl}
    (hC : ((plaquetteGraph supp).induce (C : Set Pl)).Connected) :
    δ ^ C.card * Real.exp (4 * (plaquetteSupport supp C).card +
      κ * polymerDiam (plaquetteSupport supp C)) ≤
        (δ * Real.exp (4 * s + κ * r)) ^ C.card := by
  have hcard : ((plaquetteSupport supp C).card : ℝ) ≤ C.card * s := by
    exact_mod_cast card_plaquetteSupport_le supp hs C
  have hdiam := diam_plaquetteSupport_le supp hr0 hr hC
  rw [mul_pow, ← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hδ _)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Regroup the per-link majorant sum by its underlying plaquette sets. -/
theorem blockSum_plaquetteMajorant (δ : ℝ) (F : Finset X → ℝ) (x : X) :
    blockSum (fun S => plaquetteMajorant supp δ S * F S) x =
      ∑ C ∈ (connectedPlaquettes supp).filter (fun C => x ∈ plaquetteSupport supp C),
        δ ^ C.card * F (plaquetteSupport supp C) := by
  classical
  symm
  rw [← sum_fiberwise
    ((connectedPlaquettes supp).filter (fun C => x ∈ plaquetteSupport supp C))
    (plaquetteSupport supp) (fun C => δ ^ C.card * F (plaquetteSupport supp C))]
  unfold blockSum
  rw [sum_filter]
  apply sum_congr rfl
  intro S _
  have hfilter :
      ((connectedPlaquettes supp).filter (fun C => x ∈ plaquetteSupport supp C)).filter
        (fun C => plaquetteSupport supp C = S) =
      if x ∈ S then (connectedPlaquettes supp).filter
        (fun C => plaquetteSupport supp C = S) else ∅ := by
    ext C
    by_cases h : plaquetteSupport supp C = S <;>
      by_cases hx : x ∈ S <;> simp [h, hx]
  rw [hfilter]
  by_cases hx : x ∈ S
  · simp only [hx, ↓reduceIte]
    unfold plaquetteMajorant
    rw [sum_mul]
    apply sum_congr rfl
    intro C hC
    rw [(mem_filter.mp hC).2]
  · simp [hx]

/-- Charge a connected set through a link to any plaquette in that set using
the link, then apply the rooted connected-set sum. -/
theorem sum_connected_through_link_le {Δ D : ℕ}
    (hdeg : ∀ p, (plaquetteGraph supp).degree p ≤ Δ)
    (hinc : ∀ x, ((univ : Finset Pl).filter (fun p => x ∈ supp p)).card ≤ D)
    {t : ℝ} (ht : 0 ≤ t) (hsmall : ((Δ + 1 : ℕ) : ℝ) ^ 2 * t ≤ 1 / 2) (x : X) :
    ∑ C ∈ (connectedPlaquettes supp).filter (fun C => x ∈ plaquetteSupport supp C),
      t ^ C.card ≤ 2 * D * (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) := by
  classical
  let incident : Finset Pl := univ.filter (fun p => x ∈ supp p)
  calc
    _ ≤ ∑ C ∈ connectedPlaquettes supp, ∑ p ∈ incident,
        if p ∈ C then t ^ C.card else 0 := by
      rw [sum_filter]
      apply sum_le_sum
      intro C _
      by_cases hx : x ∈ plaquetteSupport supp C
      · simp only [hx, ↓reduceIte]
        obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp hx
        calc t ^ C.card = if p ∈ C then t ^ C.card else 0 := by simp [hp]
          _ ≤ _ := single_le_sum (s := incident)
            (f := fun q => if q ∈ C then t ^ C.card else 0)
            (fun q _ => by split_ifs <;> positivity)
            (mem_filter.mpr ⟨mem_univ _, hxp⟩)
      · simp only [hx, ↓reduceIte]
        exact sum_nonneg fun p _ => by split_ifs <;> positivity
    _ = ∑ p ∈ incident, ∑ C ∈ (univ : Finset (Finset Pl)).filter
        (fun C : Finset Pl => p ∈ C ∧ ((plaquetteGraph supp).induce (C : Set Pl)).Connected),
          t ^ C.card := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      rw [← sum_filter]
      apply sum_congr _ (fun _ _ => rfl)
      ext C
      simp [connectedPlaquettes, and_comm]
    _ ≤ ∑ _p ∈ incident, 2 * (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) := by
      apply sum_le_sum
      intro p _
      exact sum_rootedConnected_pow_le (plaquetteGraph supp) hdeg p ht hsmall
    _ = (incident.card : ℝ) * (2 * (((Δ + 1 : ℕ) : ℝ) ^ 2 * t)) := by simp
    _ ≤ _ := by
      have hcard : (incident.card : ℝ) ≤ D := by exact_mod_cast hinc x
      have hnonneg : 0 ≤ 2 * (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hcard hnonneg]

/-- The weighted per-link sum is bounded uniformly in the ambient volume. -/
theorem blockSum_weighted_plaquetteMajorant_le {δ κ r : ℝ} {s Δ D : ℕ}
    (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hr0 : 0 ≤ r)
    (hs : ∀ p, (supp p).card ≤ s) (hr : ∀ p, polymerDiam (supp p) ≤ r)
    (hdeg : ∀ p, (plaquetteGraph supp).degree p ≤ Δ)
    (hinc : ∀ x, ((univ : Finset Pl).filter (fun p => x ∈ supp p)).card ≤ D)
    (hsmall : ((Δ + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (4 * s + κ * r)) ≤ 1 / 2)
    (x : X) :
    blockSum (fun S => plaquetteMajorant supp δ S *
      Real.exp (4 * S.card + κ * polymerDiam S)) x ≤
        2 * D * (((Δ + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (4 * s + κ * r))) := by
  rw [blockSum_plaquetteMajorant]
  refine (sum_le_sum fun C hC => weighted_plaquette_term_le supp hδ hκ hr0 hs hr
    (mem_filter.mp (mem_filter.mp hC).1).2).trans ?_
  exact sum_connected_through_link_le supp hdeg hinc
    (mul_nonneg hδ (Real.exp_pos _).le) hsmall x

/-- An explicit strong-coupling radius in the norm with weight
`exp (4 * |S| + κ * diam S)`. -/
def strongCouplingThreshold (D Δ s : ℕ) (r κ ε : ℝ) : ℝ :=
  ε / (2 * (D + 1 : ℝ) * ((Δ + 1 : ℕ) : ℝ) ^ 2 * Real.exp (4 * s + κ * r))

/-- The threshold is strictly positive for positive requested smallness. -/
theorem strongCouplingThreshold_pos (D Δ s : ℕ) (r κ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 < strongCouplingThreshold D Δ s r κ ε := by
  unfold strongCouplingThreshold
  positivity

/-- Local perturbations below the explicit threshold satisfy the per-link
Kotecký–Preiss smallness, with constants independent of the volume. -/
theorem activitySmall_plaquetteMajorant {δ κ r ε : ℝ} {s Δ D : ℕ}
    (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hr0 : 0 ≤ r) (hε0 : 0 ≤ ε)
    (hε : ε * Real.exp 1 ≤ 1)
    (hs : ∀ p, (supp p).card ≤ s) (hr : ∀ p, polymerDiam (supp p) ≤ r)
    (hdeg : ∀ p, (plaquetteGraph supp).degree p ≤ Δ)
    (hinc : ∀ x, ((univ : Finset Pl).filter (fun p => x ∈ supp p)).card ≤ D)
    (hbound : δ ≤ strongCouplingThreshold D Δ s r κ ε) :
    ActivitySmall (plaquetteMajorant supp δ) κ ε := by
  have he : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hε1 : ε ≤ 1 := by nlinarith
  have hden : 0 < 2 * (D + 1 : ℝ) * ((Δ + 1 : ℕ) : ℝ) ^ 2 *
      Real.exp (4 * s + κ * r) := by positivity
  have hb := (le_div_iff₀ hden).mp hbound
  have hbudget : 2 * (D + 1 : ℝ) *
      (((Δ + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (4 * s + κ * r))) ≤ ε := by
    nlinarith only [hb]
  have hq : 0 ≤ ((Δ + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (4 * s + κ * r)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg hδ (Real.exp_pos _).le)
  have hD : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hhalf : ((Δ + 1 : ℕ) : ℝ) ^ 2 * (δ * Real.exp (4 * s + κ * r)) ≤ 1 / 2 := by
    nlinarith
  intro x
  exact (blockSum_weighted_plaquetteMajorant_le supp hδ hκ hr0 hs hr hdeg hinc hhalf x).trans
    (by nlinarith)

#print axioms diam_plaquetteSupport_le
#print axioms weighted_plaquette_term_le
#print axioms sum_connected_through_link_le
#print axioms strongCouplingThreshold_pos
#print axioms activitySmall_plaquetteMajorant

end Mettapedia.Combinatorics.PolymerGas
