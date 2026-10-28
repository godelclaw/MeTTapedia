import Mettapedia.ProbabilityTheory.MarkovChain.Restart
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Personalized PageRank is a successor representation

The successor representation of a walk with discount γ is its discounted
occupancy, the sum of γ^t P^t over t (Dayan 1993). With γ = 1 - α, personalized
PageRank with restart probability α is α times the successor representation
applied to the seed. The partial sums converge to the PageRank vector, and after
k terms every coordinate is within (1 - α)^k times its ℓ¹ norm.
-/

noncomputable section
namespace Mettapedia.ProbabilityTheory.MarkovChain.Restart.RestartWalk
open scoped BigOperators
open Matrix Finset Filter Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (W : RestartWalk ι)

/-- Discounted occupancy of the first `k` steps from seed `s`. -/
def occupancy (s : ι → ℝ) (k : ℕ) : ι → ℝ :=
  ∑ t ∈ range k, (1 - W.α) ^ t • ((W.P ^ t) *ᵥ s)

theorem l1_pow_mulVec_le (x : ι → ℝ) (t : ℕ) : l1 ((W.P ^ t) *ᵥ x) ≤ l1 x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec]
    exact (W.l1_mulVec_le _).trans ih

theorem smul_occupancy (s : ι → ℝ) (k : ℕ) :
    W.α • W.occupancy s k = ∑ t ∈ range k, (W.α * (1 - W.α) ^ t) • ((W.P ^ t) *ᵥ s) := by
  simp only [occupancy, Finset.smul_sum, smul_smul]

/-- After `k` terms each coordinate is within `(1-α)^k` times the PageRank vector's ℓ¹ norm. -/
theorem occupancy_error (s : ι → ℝ) (k : ℕ) (i : ι) :
    |(W.α • W.occupancy s k) i - W.ppr s i| ≤ (1 - W.α) ^ k * l1 (W.ppr s) := by
  cases k with
  | zero =>
    simp only [occupancy, Finset.range_zero, Finset.sum_empty, smul_zero, Pi.zero_apply,
      zero_sub, abs_neg, pow_zero, one_mul]
    exact abs_coordinate_le_l1 (W.ppr s) i
  | succ m =>
    have hu := W.ppr_unroll s m
    have hdiff : (W.α • W.occupancy s (m + 1)) i - W.ppr s i =
        -(((1 - W.α) ^ (m + 1) • ((W.P ^ (m + 1)) *ᵥ W.ppr s)) i) := by
      rw [W.smul_occupancy, congrFun hu i]
      simp only [Pi.add_apply]
      ring
    rw [hdiff, abs_neg]
    calc |((1 - W.α) ^ (m + 1) • ((W.P ^ (m + 1)) *ᵥ W.ppr s)) i|
        ≤ l1 ((1 - W.α) ^ (m + 1) • ((W.P ^ (m + 1)) *ᵥ W.ppr s)) := abs_coordinate_le_l1 _ i
      _ = (1 - W.α) ^ (m + 1) * l1 ((W.P ^ (m + 1)) *ᵥ W.ppr s) := by
          rw [l1_smul, abs_of_nonneg (pow_nonneg W.one_sub_α_nonneg _)]
      _ ≤ (1 - W.α) ^ (m + 1) * l1 (W.ppr s) :=
          mul_le_mul_of_nonneg_left (W.l1_pow_mulVec_le _ _) (pow_nonneg W.one_sub_α_nonneg _)

/-- Personalized PageRank is α times the successor representation of the seed. -/
theorem tendsto_occupancy_ppr (s : ι → ℝ) :
    Tendsto (fun k => W.α • W.occupancy s k) atTop (𝓝 (W.ppr s)) := by
  rw [tendsto_pi_nhds]
  intro i
  have hgeom : Tendsto (fun k : ℕ => (1 - W.α) ^ k * l1 (W.ppr s)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one W.one_sub_α_nonneg
      (by linarith [W.α_pos] : 1 - W.α < 1)
    simpa using h.mul_const (l1 (W.ppr s))
  have hlow : Tendsto (fun k : ℕ => -((1 - W.α) ^ k * l1 (W.ppr s))) atTop (𝓝 0) := by
    simpa using hgeom.neg
  have hzero : Tendsto (fun k => (W.α • W.occupancy s k) i - W.ppr s i) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hgeom
      (fun k => (abs_le.mp (W.occupancy_error s k i)).1)
      (fun k => (abs_le.mp (W.occupancy_error s k i)).2)
  simpa using hzero.add_const (W.ppr s i)

end Mettapedia.ProbabilityTheory.MarkovChain.Restart.RestartWalk
