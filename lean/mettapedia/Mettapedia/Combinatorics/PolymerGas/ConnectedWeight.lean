import Mettapedia.Combinatorics.PolymerGas.ConnectedCount
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summing exponentially weighted connected sets

The uniform connected-set count gives a geometric majorant for the sum over
all connected sets containing a specified vertex.
-/

set_option autoImplicit false
noncomputable section

open Finset
open scoped Classical

namespace Mettapedia.Combinatorics.PolymerGas

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Summing the connected-set count costs at most twice its geometric ratio. -/
theorem sum_rootedConnected_pow_le {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (root : V) {t : ℝ} (ht : 0 ≤ t)
    (hsmall : ((Δ + 1 : ℕ) : ℝ) ^ 2 * t ≤ 1 / 2) :
    ∑ C ∈ (univ : Finset (Finset V)).filter
        (fun C : Finset V => root ∈ C ∧ (G.induce (C : Set V)).Connected), t ^ C.card ≤
      2 * (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) := by
  classical
  let I : Finset (Finset V) := univ.filter
    (fun C : Finset V => root ∈ C ∧ (G.induce (C : Set V)).Connected)
  have hcard : ∀ C ∈ I, 0 < C.card ∧ C.card ≤ Fintype.card V := by
    intro C hC
    exact ⟨card_pos.mpr ⟨root, (mem_filter.mp hC).2.1⟩, card_le_univ C⟩
  have hfibre : ∀ n, I.filter (fun C => C.card - 1 = n) = rootedConnectedSets G root (n + 1) := by
    intro n
    ext C
    simp only [I, rootedConnectedSets, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hr, hc⟩, hn⟩
      have hp : 0 < C.card := card_pos.mpr ⟨root, hr⟩
      exact ⟨hr, by omega, hc⟩
    · rintro ⟨hr, hn, hc⟩
      exact ⟨⟨hr, hc⟩, by omega⟩
  have hgroup :
      ∑ C ∈ I, t ^ C.card = ∑ n ∈ range (Fintype.card V),
        ∑ C ∈ rootedConnectedSets G root (n + 1), t ^ C.card := by
    rw [← sum_fiberwise_of_maps_to
      (s := I) (t := range (Fintype.card V)) (g := fun C => C.card - 1)
      (fun C hC => mem_range.mpr (by have := hcard C hC; omega)) (fun C => t ^ C.card)]
    simp_rw [hfibre]
  change ∑ C ∈ I, t ^ C.card ≤ _
  rw [hgroup]
  calc
    _ ≤ ∑ n ∈ range (Fintype.card V),
        (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) ^ (n + 1) := by
      apply sum_le_sum
      intro n _
      calc
        _ = ((rootedConnectedSets G root (n + 1)).card : ℝ) * t ^ (n + 1) := by
          rw [show (∑ C ∈ rootedConnectedSets G root (n + 1), t ^ C.card) =
              ∑ _C ∈ rootedConnectedSets G root (n + 1), t ^ (n + 1) from
            sum_congr rfl (fun C hC => by rw [(mem_filter.mp hC).2.2.1])]
          simp
        _ ≤ (((Δ + 1) ^ (2 * (n + 1)) : ℕ) : ℝ) * t ^ (n + 1) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht _)
          exact_mod_cast card_rootedConnectedSets_le G hdeg root (n + 1)
        _ = _ := by push_cast; rw [pow_mul, mul_pow]
    _ ≤ ∑ n ∈ range (Fintype.card V),
        (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) * (1 / 2 : ℝ) ^ n := by
      apply sum_le_sum
      intro n _
      rw [pow_succ']
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsmall _)
        (by positivity)
    _ = (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) *
        ∑ n ∈ range (Fintype.card V), (1 / 2 : ℝ) ^ n := by rw [mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (sum_geometric_two_le (Fintype.card V))
        (show 0 ≤ (((Δ + 1 : ℕ) : ℝ) ^ 2 * t) by positivity)
      nlinarith

#print axioms sum_rootedConnected_pow_le

end Mettapedia.Combinatorics.PolymerGas
