import Mettapedia.Computability.KolmogorovComplexity.FeatureRationalScheme

/-!
# Self-delimiting complete scheme descriptions

Frame the actual plain scheme packet with the existing exact E2 codec and
compile its existing interpreter into a prefix reference machine. The whole
frame length is charged. The upper comparison transports the source's plain
complexity to the reference machine through a separately proved compiler.
Shortest-feature hypotheses remain relative to the scheme's stated source
interpreter; this construction does not identify plain and prefix machines.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

def prefixSchemeDescription (features : List BinString) (residual : BinString) : BinString :=
  e2encode (schemeDescription features residual)

theorem exact_prefix_scheme_payload (features : List BinString) (residual : BinString) :
    exactE2Payload (prefixSchemeDescription features residual) = some (schemeDescription features residual) :=
  exactE2Payload_e2encode _

theorem prefix_scheme_rejects_extension (U : ConditionalAlgorithm)
    (features : List BinString) (residual suffix condition : BinString) (nonempty : suffix ≠ []) :
    (selfDelimitingConditionalMachine (schemeInterpreter U)).compute
      (prefixSchemeDescription features residual ++ suffix) condition = none :=
  selfDelimitingConditionalMachine_rejects_extension (schemeInterpreter U) _ suffix condition nonempty

theorem BChain.prefix_scheme_program {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString} (chain : BChain U factor source features final) :
    IsProgram (selfDelimitingConditionalMachine (schemeInterpreter U))
      (prefixSchemeDescription features final) [] source :=
  selfDelimitingConditionalMachine_isProgram (schemeInterpreter U) chain.scheme_reconstructs

theorem scheme_description_linear_source_bound {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString} (chain : BChain U factor source features final) :
    (schemeDescription features final).length ≤ 3 * source.length + 1 := by
  have budget := chain.payload_bound
  rw [schemeDescription_length]
  omega

theorem prefix_scheme_header_bound {U : ConditionalAlgorithm} {factor : ℝ}
    {source final : BinString} {features : List BinString} (chain : BChain U factor source features final) :
    (prefixSchemeDescription features final).length ≤
      (schemeDescription features final).length + 2 * Nat.log 2 (source.length + 1) + 7 := by
  have bound := scheme_description_linear_source_bound chain
  have logarithm := Nat.log_mono_right (b := 2)
    (show (schemeDescription features final).length + 1 ≤ (source.length + 1) * 2 * 2 by omega)
  have doubled := Nat.log_mul_base (b := 2) (by decide) (Nat.succ_ne_zero source.length)
  have quadrupled := Nat.log_mul_base (b := 2) (by decide)
    (show (source.length + 1) * 2 ≠ 0 by omega)
  simp only [Nat.succ_eq_add_one] at doubled
  have framed := e2encode_length_le_log (schemeDescription features final)
  change (e2encode (schemeDescription features final)).length ≤ _
  omega

theorem scheme_prefix_complexity_lower (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (effective : Partrec₂ U) (reference : IsReferenceMachine V) :
    ∃ overhead : Nat, ∀ factor source final features, BChain U factor source features final →
      conditionalComplexity V source [] ≤ (prefixSchemeDescription features final).length + overhead := by
  obtain ⟨compiler⟩ := reference.2 (selfDelimitingConditionalMachine (schemeInterpreter U))
    (selfDelimitingConditionalMachine_effective _ (schemeInterpreter_partrec effective))
  refine ⟨compiler.compilerPrefix.length, fun factor source final features chain => ?_⟩
  exact conditionalComplexity_le_simulated_program compiler chain.prefix_scheme_program

theorem nat_binary_log_le_real_log (size : Nat) :
    (Nat.log 2 (size + 1) : ℝ) ≤ Real.log ((size : ℝ) + 1) / Real.log 2 := by
  have power : (2 : ℝ) ^ Nat.log 2 (size + 1) ≤ (size : ℝ) + 1 := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.succ_ne_zero size)
  have logs := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) power
  rw [Real.log_pow] at logs
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).mpr logs

/-- Uniform prefix-reference version of the complete scheme's two-sided
description bound. Feature minima and stopping still belong to the named
plain source interpreter. Every prefix-framing and compiler cost is paid. -/
theorem rational_scheme_prefix_bounds (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (numerator denominator : Nat) (positive : 0 < denominator) (greater : denominator < numerator) :
    ∃ fixedFeature : BinString, ∃ cutoff lowerOverhead : Nat, ∃ slope intercept : ℝ,
      0 ≤ slope ∧ 0 ≤ intercept ∧
      (∀ source, ∃ features final, RationalScheme U numerator denominator cutoff source features final) ∧
      ∀ source features final, RationalScheme U numerator denominator cutoff source features final →
        IsProgram (selfDelimitingConditionalMachine (schemeInterpreter U))
          (prefixSchemeDescription features final) [] source ∧
        conditionalComplexity V source [] ≤ (prefixSchemeDescription features final).length + lowerOverhead ∧
        ((prefixSchemeDescription features final).length : ℝ) ≤
          rationalFactor numerator denominator * conditionalComplexity V source [] +
            slope * Real.log ((source.length : ℝ) + 1) + intercept ∧
        (∀ feature ∈ features, feature.length ≤ fixedFeature.length) ∧
        (features.length : ℝ) ≤
          Real.log ((source.length : ℝ) + 1) / Real.log (rationalFactor numerator denominator) + 1 := by
  obtain ⟨fixed, cutoff, slope, intercept, slopeNonnegative, interceptNonnegative, upper⟩ :=
    rational_scheme_description_upper U universal effective numerator denominator positive greater
  obtain ⟨lowerCost, lower⟩ := scheme_prefix_complexity_lower U V effective reference
  obtain ⟨plainCost, plainBound⟩ := plain_le_reference U V universal reference
  let factor := rationalFactor numerator denominator
  have factorLarge : 1 < factor := rationalFactor_one_lt positive greater
  have logTwoPositive : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨fixed, cutoff, lowerCost, slope + 2 / Real.log 2, intercept + factor * plainCost + 7,
    by positivity, by positivity,
    fun source => exists_rational_scheme U universal numerator denominator cutoff positive greater source,
    fun source features final scheme => ?_⟩
  have chain := scheme.toBChain
  obtain ⟨rawBound, featuresBounded⟩ := upper source features final scheme
  refine ⟨chain.prefix_scheme_program, lower _ _ _ _ chain, ?_, featuresBounded,
    scheme.logarithmic_length positive greater⟩
  have framed : ((prefixSchemeDescription features final).length : ℝ) ≤
      (schemeDescription features final).length + 2 * (Nat.log 2 (source.length + 1) : ℝ) + 7 := by
    exact_mod_cast prefix_scheme_header_bound chain
  have sourceBound : (plainConditionalComplexity U source [] : ℝ) ≤ conditionalComplexity V source [] + plainCost := by
    exact_mod_cast plainBound source []
  have scaledSource := mul_le_mul_of_nonneg_left sourceBound (le_of_lt (lt_trans (by norm_num) factorLarge))
  have logBound := nat_binary_log_le_real_log source.length
  have rearrange : (slope + 2 / Real.log 2) * Real.log ((source.length : ℝ) + 1) =
      slope * Real.log ((source.length : ℝ) + 1) + 2 * (Real.log ((source.length : ℝ) + 1) / Real.log 2) := by ring
  rw [rearrange]
  nlinarith

#print axioms exact_prefix_scheme_payload
#print axioms prefix_scheme_rejects_extension
#print axioms BChain.prefix_scheme_program
#print axioms scheme_description_linear_source_bound
#print axioms prefix_scheme_header_bound
#print axioms scheme_prefix_complexity_lower
#print axioms nat_binary_log_le_real_log
#print axioms rational_scheme_prefix_bounds

end KolmogorovComplexity.FeatureTheory
