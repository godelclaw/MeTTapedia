import Mettapedia.Computability.KolmogorovComplexity.FeatureSchemeCodec
import Mettapedia.Computability.KolmogorovComplexity.FeatureConstrainedSearch
import Mettapedia.Computability.KolmogorovComplexity.ConditionalPlainComposition

/-!
# Complete descriptions of rational-factor compression schemes

Franz, Antonenko and Soletskyi, "A theory of incremental compression",
Information Sciences 547 (2021), Section 3.5 and Theorem 3.9,
https://doi.org/10.1016/j.ins.2020.08.035 (arXiv:1908.03781).

Every nonterminal step has a shortest ratio-restricted feature and map. Its
actual output, not a separately chosen witness, is the next residual. A scheme
stops below the fixed cutoff or when its current source is not compressible by
the declared factor. Existence is a mathematical statement about these ideal
minima, not an algorithm deciding Kolmogorov complexity. Effective rational
ratio checking supplies the uniform short-map compiler used in the upper bound.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

noncomputable abbrev rationalFactor (numerator denominator : Nat) : ℝ := (numerator : ℝ) / denominator

theorem rationalFactor_one_lt {numerator denominator : Nat}
    (positive : 0 < denominator) (greater : denominator < numerator) :
    1 < rationalFactor numerator denominator := by
  apply (one_lt_div₀ (show (0 : ℝ) < denominator by exact_mod_cast positive)).mpr
  exact_mod_cast greater

inductive RationalScheme (U : ConditionalAlgorithm) (numerator denominator cutoff : Nat) :
    BinString → List BinString → BinString → Prop where
  | stop_small (source : BinString) (small : source.length ≤ cutoff) :
      RationalScheme U numerator denominator cutoff source [] source
  | stop_incompressible (source : BinString)
      (incompressible : ¬ rationalFactor numerator denominator * plainConditionalComplexity U source [] ≤ source.length) :
      RationalScheme U numerator denominator cutoff source [] source
  | cons {source residual final feature descriptive : BinString} {features : List BinString}
      (large : cutoff < source.length)
      (compressible : rationalFactor numerator denominator * plainConditionalComplexity U source [] ≤ source.length)
      (minimumFeature : ShortestBFeature U (rationalFactor numerator denominator) feature source)
      (minimumMap : ShortestBDescriptiveMap U (rationalFactor numerator denominator) feature descriptive source)
      (extracts : residual ∈ U descriptive source)
      (later : RationalScheme U numerator denominator cutoff residual features final) :
      RationalScheme U numerator denominator cutoff source (feature :: features) final

theorem RationalScheme.toBChain {U : ConditionalAlgorithm} {numerator denominator cutoff : Nat}
    {source final : BinString} {features : List BinString}
    (scheme : RationalScheme U numerator denominator cutoff source features final) :
    BChain U (rationalFactor numerator denominator) source features final := by
  induction scheme with
  | stop_small source _ => exact .nil source
  | stop_incompressible source _ => exact .nil source
  | cons _ _ _ minimumMap extracts _ ih =>
      have actual := shortest_b_descriptive_actual_output minimumMap extracts
      exact .cons extracts actual.1 actual.2.1 actual.2.2.1 ih

theorem RationalScheme.terminal {U : ConditionalAlgorithm} {numerator denominator cutoff : Nat}
    {source final : BinString} {features : List BinString}
    (scheme : RationalScheme U numerator denominator cutoff source features final) :
    final.length ≤ cutoff ∨
      ¬ rationalFactor numerator denominator * plainConditionalComplexity U final [] ≤ final.length := by
  induction scheme with
  | stop_small source small => exact Or.inl small
  | stop_incompressible source incompressible => exact Or.inr incompressible
  | cons _ _ _ _ _ _ ih => exact ih

theorem RationalScheme.nonempty_of_can_step {U : ConditionalAlgorithm} {numerator denominator cutoff : Nat}
    {source final : BinString} {features : List BinString}
    (scheme : RationalScheme U numerator denominator cutoff source features final)
    (large : cutoff < source.length)
    (compressible : rationalFactor numerator denominator * plainConditionalComplexity U source [] ≤ source.length) :
    features ≠ [] := by
  cases scheme with
  | stop_small _ small => omega
  | stop_incompressible _ impossible => exact (impossible compressible).elim
  | cons => simp

theorem exists_rational_scheme (U : ConditionalAlgorithm) (universal : IsUniversalConditional U)
    (numerator denominator cutoff : Nat) (positive : 0 < denominator) (greater : denominator < numerator)
    (source : BinString) :
    ∃ features final, RationalScheme U numerator denominator cutoff source features final := by
  have factorLarge := rationalFactor_one_lt positive greater
  have byLength : ∀ size : Nat, ∀ input : BinString, input.length = size →
      ∃ features final, RationalScheme U numerator denominator cutoff input features final := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
        intro input length
        by_cases small : input.length ≤ cutoff
        · exact ⟨[], input, .stop_small input small⟩
        by_cases compressed : rationalFactor numerator denominator * plainConditionalComplexity U input [] ≤ input.length
        · have inputPositive : (0 : ℝ) < input.length := by exact_mod_cast (show 0 < input.length by omega)
          have shorterReal : (plainConditionalComplexity U input [] : ℝ) < input.length := by nlinarith
          have shorter : plainConditionalComplexity U input [] < input.length := by exact_mod_cast shorterReal
          obtain ⟨single, admitted, _⟩ := singleton_b_feature U universal
            (rationalFactor numerator denominator) input shorter
          obtain ⟨feature, minimumFeature⟩ := exists_shortest_b_feature U
            (rationalFactor numerator denominator) input ⟨single, admitted⟩
          obtain ⟨descriptive, minimumMap⟩ := exists_shortest_b_descriptive U
            (rationalFactor numerator denominator) feature input minimumFeature.1
          obtain ⟨residual, extracts, _, saving, _⟩ := minimumMap.1
          obtain ⟨features, final, later⟩ := ih residual.length (by omega) residual rfl
          exact ⟨feature :: features, final, .cons (by omega) compressed minimumFeature minimumMap extracts later⟩
        · exact ⟨[], input, .stop_incompressible input compressed⟩
  exact byLength source.length source rfl

theorem rational_scheme_step_bounds (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U)
    (numerator denominator : Nat) (positive : 0 < denominator) (greater : denominator < numerator) :
    ∃ fixedFeature : BinString, ∃ cutoff mapBudget : Nat, ∀ source feature descriptive,
      cutoff < source.length →
      rationalFactor numerator denominator * plainConditionalComplexity U source [] ≤ source.length →
      ShortestBFeature U (rationalFactor numerator denominator) feature source →
      ShortestBDescriptiveMap U (rationalFactor numerator denominator) feature descriptive source →
      feature.length ≤ fixedFeature.length ∧ descriptive.length ≤ mapBudget := by
  obtain ⟨fixed, featureBounds⟩ := b_compressible_feature_bound U universal effective
  obtain ⟨overhead, maps⟩ := shortest_rational_descriptive_linear U universal effective numerator denominator positive
  let factor := rationalFactor numerator denominator
  have factorLarge : 1 < factor := rationalFactor_one_lt positive greater
  have differencePositive : 0 < factor - 1 := by linarith
  let cutoff : Nat := ⌈(fixed.length : ℝ) * factor / (factor - 1)⌉₊
  refine ⟨fixed, cutoff, fixed.length + overhead, fun source feature descriptive large compressed minimumFeature minimumMap => ?_⟩
  have ceiling : (fixed.length : ℝ) * factor / (factor - 1) ≤ cutoff := Nat.le_ceil _
  have sourceLarge : (fixed.length : ℝ) * factor / (factor - 1) < source.length :=
    ceiling.trans_lt (by exact_mod_cast large)
  have threshold : (fixed.length : ℝ) * factor < (factor - 1) * source.length := by
    have scaled := (div_lt_iff₀ differencePositive).mp sourceLarge
    simpa only [mul_comm] using scaled
  have fixedAdmitted := (featureBounds factor factorLarge source compressed).1 threshold
  have features := minimumFeature.2 fixed fixedAdmitted
  have descriptiveBound := maps feature descriptive source minimumMap
  exact ⟨features, by omega⟩

theorem rational_scheme_uniform_bounds (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U)
    (numerator denominator : Nat) (positive : 0 < denominator) (greater : denominator < numerator) :
    ∃ fixedFeature : BinString, ∃ cutoff transportCost : Nat, ∀ source features final,
      RationalScheme U numerator denominator cutoff source features final →
      (∀ feature ∈ features, feature.length ≤ fixedFeature.length) ∧
      plainConditionalComplexity U final [] ≤
        plainConditionalComplexity U source [] + features.length * transportCost := by
  obtain ⟨fixed, cutoff, mapBudget, bounds⟩ := rational_scheme_step_bounds U universal effective
    numerator denominator positive greater
  obtain ⟨compiler, composes⟩ := uniform_plain_bounded_postcomposition U universal effective
  let cost := 2 * mapBudget + 1 + compiler
  refine ⟨fixed, cutoff, cost, fun source features final scheme => ?_⟩
  induction scheme with
  | stop_small source _ => simp
  | stop_incompressible source _ => simp
  | @cons source residual final feature descriptive features large compressed minimumFeature minimumMap extracts _ ih =>
      have sizes := bounds source feature descriptive large compressed minimumFeature minimumMap
      have stepBound := composes mapBudget descriptive [] source residual sizes.2 extracts
      constructor
      · intro current member
        rcases List.mem_cons.mp member with same | later
        · simpa only [same] using sizes.1
        · exact ih.1 current later
      · have remaining := ih.2
        simp only [List.length_cons]
        dsimp [cost] at *
        nlinarith

theorem RationalScheme.logarithmic_length {U : ConditionalAlgorithm} {numerator denominator cutoff : Nat}
    {source final : BinString} {features : List BinString}
    (scheme : RationalScheme U numerator denominator cutoff source features final)
    (positive : 0 < denominator) (greater : denominator < numerator) :
    (features.length : ℝ) ≤ Real.log ((source.length : ℝ) + 1) / Real.log (rationalFactor numerator denominator) + 1 := by
  have factorLarge := rationalFactor_one_lt positive greater
  have logPositive := Real.log_pos factorLarge
  by_cases empty : features = []
  · subst features
    have nonnegative : 0 ≤ Real.log ((source.length : ℝ) + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) source.length])
    simp only [List.length_nil, Nat.cast_zero]
    positivity
  · have chain := scheme.toBChain
    have previous := chain.logarithmic_length factorLarge empty
    have sourcePositive : (0 : ℝ) < source.length := by
      have count := chain.length_bound
      have nonempty : 0 < features.length := List.length_pos_iff.mpr empty
      exact_mod_cast (show 0 < source.length by omega)
    have logs := Real.log_le_log sourcePositive (show (source.length : ℝ) ≤ source.length + 1 by linarith)
    apply previous.trans
    simpa only [add_comm] using add_le_add_right (div_le_div_of_nonneg_right logs logPositive.le) 1

theorem rational_scheme_description_upper (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U)
    (numerator denominator : Nat) (positive : 0 < denominator) (greater : denominator < numerator) :
    ∃ fixedFeature : BinString, ∃ cutoff : Nat, ∃ slope intercept : ℝ, 0 ≤ slope ∧ 0 ≤ intercept ∧
      ∀ source features final, RationalScheme U numerator denominator cutoff source features final →
        (((schemeDescription features final).length : ℝ) ≤
          rationalFactor numerator denominator * plainConditionalComplexity U source [] +
            slope * Real.log ((source.length : ℝ) + 1) + intercept) ∧
          ∀ feature ∈ features, feature.length ≤ fixedFeature.length := by
  obtain ⟨fixed, cutoff, transportCost, bounds⟩ := rational_scheme_uniform_bounds U universal effective
    numerator denominator positive greater
  let factor := rationalFactor numerator denominator
  have factorLarge : 1 < factor := rationalFactor_one_lt positive greater
  have logPositive : 0 < Real.log factor := Real.log_pos factorLarge
  let frameCost : ℝ := 2 * fixed.length + 3
  let stepCost : ℝ := frameCost + factor * transportCost
  have stepNonnegative : 0 ≤ stepCost := by dsimp [stepCost, frameCost]; positivity
  refine ⟨fixed, cutoff, stepCost / Real.log factor, cutoff + 1 + stepCost,
    div_nonneg stepNonnegative logPositive.le, by positivity, fun source features final scheme => ?_⟩
  obtain ⟨featuresBounded, transport⟩ := bounds source features final scheme
  refine ⟨?_, featuresBounded⟩
  have encoded : ((schemeDescription features final).length : ℝ) ≤
      final.length + (features.length : ℝ) * frameCost + 1 := by
    dsimp [frameCost]
    exact_mod_cast schemeDescription_length_le final featuresBounded
  have transported : (plainConditionalComplexity U final [] : ℝ) ≤
      plainConditionalComplexity U source [] + (features.length : ℝ) * transportCost := by
    exact_mod_cast transport
  have terminalBound : (final.length : ℝ) ≤ factor * plainConditionalComplexity U source [] +
      (features.length : ℝ) * (factor * transportCost) + cutoff := by
    rcases scheme.terminal with small | incompressible
    · have smallReal : (final.length : ℝ) ≤ cutoff := by exact_mod_cast small
      have baseNonnegative : 0 ≤ factor * (plainConditionalComplexity U source [] : ℝ) := by positivity
      have incrementNonnegative : 0 ≤ (features.length : ℝ) * (factor * transportCost) := by positivity
      linarith
    · have terminal : (final.length : ℝ) < factor * plainConditionalComplexity U final [] :=
        lt_of_not_ge incompressible
      have scaled := mul_le_mul_of_nonneg_left transported (le_of_lt (lt_trans (by norm_num) factorLarge))
      nlinarith
  have unrolled : ((schemeDescription features final).length : ℝ) ≤
      factor * plainConditionalComplexity U source [] + features.length * stepCost + cutoff + 1 := by
    dsimp [stepCost]
    nlinarith
  have count := scheme.logarithmic_length positive greater
  have weighted := mul_le_mul_of_nonneg_right count stepNonnegative
  have rewriteCost : (Real.log ((source.length : ℝ) + 1) / Real.log factor + 1) * stepCost =
      (stepCost / Real.log factor) * Real.log ((source.length : ℝ) + 1) + stepCost := by ring
  rw [rewriteCost] at weighted
  linarith

/-- Effective rational-factor form of IC Theorem 3.9. The source-independent
constants, complete encoded description, interpreter and terminal condition
belong to the same scheme. A finite ideal scheme exists for every source. -/
theorem rational_scheme_description_bounds (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U)
    (numerator denominator : Nat) (positive : 0 < denominator) (greater : denominator < numerator) :
    ∃ fixedFeature : BinString, ∃ cutoff lowerOverhead : Nat, ∃ slope intercept : ℝ,
      0 ≤ slope ∧ 0 ≤ intercept ∧
      (∀ source, ∃ features final, RationalScheme U numerator denominator cutoff source features final) ∧
      ∀ source features final, RationalScheme U numerator denominator cutoff source features final →
        decodeSchemeDescription (schemeDescription features final) = some (features.reverse, final) ∧
        source ∈ schemeInterpreter U (schemeDescription features final) [] ∧
        plainConditionalComplexity U source [] ≤ (schemeDescription features final).length + lowerOverhead ∧
        ((schemeDescription features final).length : ℝ) ≤
          rationalFactor numerator denominator * plainConditionalComplexity U source [] +
            slope * Real.log ((source.length : ℝ) + 1) + intercept ∧
        (∀ feature ∈ features, feature.length ≤ fixedFeature.length) ∧
        (features.length : ℝ) ≤
          Real.log ((source.length : ℝ) + 1) / Real.log (rationalFactor numerator denominator) + 1 := by
  obtain ⟨fixed, cutoff, slope, intercept, slopeNonnegative, interceptNonnegative, upper⟩ :=
    rational_scheme_description_upper U universal effective numerator denominator positive greater
  obtain ⟨lowerCost, lower⟩ := scheme_description_complexity_lower U universal effective
  refine ⟨fixed, cutoff, lowerCost, slope, intercept, slopeNonnegative, interceptNonnegative,
    fun source => exists_rational_scheme U universal numerator denominator cutoff positive greater source,
    fun source features final scheme => ?_⟩
  have encoded := upper source features final scheme
  exact ⟨decodeSchemeDescription_encode features final, scheme.toBChain.scheme_reconstructs,
    lower _ _ _ _ scheme.toBChain, encoded.1, encoded.2, scheme.logarithmic_length positive greater⟩

#print axioms exists_rational_scheme
#print axioms rational_scheme_step_bounds
#print axioms rational_scheme_uniform_bounds
#print axioms RationalScheme.toBChain
#print axioms RationalScheme.terminal
#print axioms RationalScheme.nonempty_of_can_step
#print axioms RationalScheme.logarithmic_length
#print axioms rational_scheme_description_upper
#print axioms rational_scheme_description_bounds
#print axioms rationalFactor_one_lt

end KolmogorovComplexity.FeatureTheory
