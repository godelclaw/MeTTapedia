import Mettapedia.Algorithms.Retrieval.TopKSelection
import Mettapedia.CogArch.Attention.PremiseActivation

/-!
# Conditions under which spreading retrieves useful premises

A concept shortcut is a graph statement. Regret separates mismatch to actual
utility from numerical iteration error. Observed usage is not automatically a
calibrated probability of need, and the bound crossing the calibration term
neither proves monotone utility nor zero benefit from further computation.
-/

noncomputable section
namespace Mettapedia.CogArch.Attention.Relevance
open scoped BigOperators
open Matrix
open Mettapedia.ProbabilityTheory.MarkovChain.Restart
open Mettapedia.Algorithms.Retrieval.TopKSelection
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A two-edge concept path contributes at least its discounted path weight.
Fan size and relevance of the concept's members are not inferred here. -/
theorem concept_shortcut (W : RestartWalk ι) (i C j : ι) (β w : ℝ)
    (hβ : W.P C i = β) (hw : W.P j C = w) :
    W.α * (1-W.α)^2 * β * w ≤ W.ppr (Pi.single i 1) j := by
  have hs : ∀ z, 0 ≤ (show ι → ℝ from Pi.single i 1) z := by intro z; simp [Pi.single_apply]; positivity
  have hd := W.ppr_ge_depth hs 2 j
  have he : ((W.P^2) *ᵥ Pi.single i (1:ℝ)) j = ∑ k, W.P j k * W.P k i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, pow_two, Matrix.mul_apply]
  rw [he] at hd
  have hpath : β*w ≤ ∑ k, W.P j k * W.P k i := by
    have h := Finset.single_le_sum (fun k _ => mul_nonneg (W.nonneg j k) (W.nonneg k i))
      (Finset.mem_univ C)
    simpa [hβ, hw, mul_comm] using h
  have hcoef : 0 ≤ W.α * (1-W.α)^2 := mul_nonneg W.α_pos.le (sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hpath hcoef
  nlinarith [hmul, hd]

/-- Approximation regret plus calibration mismatch. No hypothesis identifies
PPR with utility implicitly: the mismatch appears explicitly on the RHS. -/
theorem spreading_regret (W : RestartWalk ι) (s q : ι → ℝ)
    (hs : ∀ i, 0 ≤ s i) (hs1 : mass s = 1)
    (c : ℝ) (hc : 0 < c) (r k : ℕ) (T O : Finset ι)
    (hT : IsTopK ((W.step s)^[r] s) T k) (hO : O.card = k) :
    (∑ i ∈ O, q i) - ∑ i ∈ T, q i ≤
      l1 (q - c • W.ppr s) + 2*c*(1-W.α)^r := by
  let x := (W.step s)^[r] s
  have hr := topk_regret_le_l1_scaled q x T O k c hc hT hO
  have ht := l1_triangle_sub q (c • W.ppr s) (c • x)
  have he : l1 (c • W.ppr s - c • x) = c * l1 (x - W.ppr s) := by
    rw [← smul_sub, l1_smul, abs_of_pos hc, l1_sub_comm]
  rw [he] at ht
  have hb := mul_le_mul_of_nonneg_left (W.iterate_error_dist hs hs1 hs hs1 r) hc.le
  change c * l1 (x - W.ppr s) ≤ _ at hb
  linarith

/-- If need probabilities really are scaled walk scores, the exact top-k is
utility-optimal. This is the substantive world assumption, not a learned fact. -/
theorem walk_generated_needs_optimal (W : RestartWalk ι) (s q : ι → ℝ)
    (c : ℝ) (hc : 0 < c) (hq : q = c • W.ppr s)
    (T O : Finset ι) (k : ℕ) (hT : IsTopK (W.ppr s) T k) (hO : O.card = k) :
    ∑ i ∈ O, q i ≤ ∑ i ∈ T, q i := by
  subst q
  exact calibrated_topk_optimal _ T O k c hc hT hO

end Mettapedia.CogArch.Attention.Relevance
