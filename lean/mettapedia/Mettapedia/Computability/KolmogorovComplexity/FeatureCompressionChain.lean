import Mettapedia.Computability.KolmogorovComplexity.FeatureCompressionRatio
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Geometric and logarithmic bounds for b-compression chains

Every step retains actual extraction, reconstruction and strict complete
feature-plus-residual saving. The extra residual ratio bounds the number of
successful steps. The final residual may be empty; the logarithmic iteration
bound therefore uses the nonempty input to the last step, not the final output.
Shortest-feature optimality is unnecessary for this operational bound.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

inductive BChain (U : ConditionalAlgorithm) (factor : ℝ) : BinString → List BinString → BinString → Prop where
  | nil (source : BinString) : BChain U factor source [] source
  | cons {source residual final feature descriptive : BinString} {features : List BinString}
      (extracts : residual ∈ U descriptive source) (reconstructs : source ∈ U feature residual)
      (smaller : feature.length + residual.length < source.length)
      (ratio : factor * residual.length ≤ source.length)
      (later : BChain U factor residual features final) :
      BChain U factor source (feature :: features) final

theorem BChain.residual_geometric {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) (nonnegative : 0 ≤ factor) :
    factor ^ features.length * final.length ≤ source.length := by
  induction chain with
  | nil source => simp
  | @cons source residual final feature descriptive features _ _ _ ratio _ ih =>
      have scaled := mul_le_mul_of_nonneg_left ih nonnegative
      simpa only [List.length_cons, pow_succ', mul_assoc] using scaled.trans ratio

/-- Each strict step spends at least one source bit, independently of its
feature size or the ratio factor. -/
theorem BChain.length_bound {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) : features.length + final.length ≤ source.length := by
  induction chain with
  | nil source => simp
  | cons _ _ smaller _ _ ih => simp only [List.length_cons]; omega

/-- The input to the last step is nonempty even when its output is empty. -/
theorem BChain.predecessor_geometric {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) (positive : 0 < factor) (nonempty : features ≠ []) :
    factor ^ (features.length - 1) ≤ source.length := by
  induction chain with
  | nil source => exact (nonempty rfl).elim
  | @cons source residual final feature descriptive features _ _ smaller ratio _ ih =>
      cases features with
      | nil =>
          simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.sub_self, pow_zero]
          exact_mod_cast (show 1 ≤ source.length by omega)
      | cons first rest =>
          have remaining := ih (by simp)
          have scaled := mul_le_mul_of_nonneg_left remaining (le_of_lt positive)
          simp only [List.length_cons, Nat.add_sub_cancel] at scaled ⊢
          rw [pow_succ']
          exact scaled.trans ratio

/-- IC's successful-iteration bound for any fixed real factor greater
than one. Search scheduling and inverse-enumeration costs are separate. -/
theorem BChain.logarithmic_length {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) (greater : 1 < factor) (nonempty : features ≠ []) :
    (features.length : ℝ) ≤ Real.log source.length / Real.log factor + 1 := by
  have positive : 0 < factor := by linarith
  have bound := chain.predecessor_geometric positive nonempty
  have logs := Real.log_le_log (pow_pos positive _) bound
  rw [Real.log_pow] at logs
  have divided := (le_div_iff₀ (Real.log_pos greater)).mpr logs
  have lengthPositive : 1 ≤ features.length := by
    cases features <;> simp_all
  have counted : features.length - 1 + 1 = features.length := Nat.sub_add_cancel lengthPositive
  have countedReal : ((features.length - 1 : Nat) : ℝ) + 1 = features.length := by exact_mod_cast counted
  linarith

#print axioms BChain.residual_geometric
#print axioms BChain.predecessor_geometric
#print axioms BChain.logarithmic_length

end KolmogorovComplexity.FeatureTheory
