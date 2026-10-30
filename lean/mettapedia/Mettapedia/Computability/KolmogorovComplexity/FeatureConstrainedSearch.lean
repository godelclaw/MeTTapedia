import Mettapedia.Computability.KolmogorovComplexity.FeatureShortMaps

/-!
# Residual selection with effective constraints

Franz, Antonenko and Soletskyi, "A theory of incremental compression",
Information Sciences 547 (2021), Definition 3.1 and Theorem 3.8,
https://doi.org/10.1016/j.ins.2020.08.035 (arXiv:1908.03781).

Apply a constraint to each finite candidate check, before unbounded search.
An inadmissible first reconstruction does not hide later admissible ones.
The generic guard is explicitly effective. Rational compression factors supply
a concrete guard without assuming that comparison with an arbitrary real is
computable. Constants are chosen before the feature, source and length budget.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical

abbrev ResidualGuard := (BinString × BinString) × BinString → Bool

def guardResidualCandidate (guard : ResidualGuard) (context : BinString × BinString)
    (candidate : Option BinString) : Option BinString :=
  candidate.bind fun residual => cond (guard (context, residual)) (some residual) none

def guardedResidualSearchStep (code : Nat.Partrec.Code) (guard : ResidualGuard)
    (input : ResidualSearchInput) : Option BinString :=
  guardResidualCandidate guard input.1 (residualSearchStep code input)

theorem guardedResidualSearchStep_primrec (code : Nat.Partrec.Code) {guard : ResidualGuard}
    (effectiveGuard : Primrec guard) : Primrec (guardedResidualSearchStep code guard) := by
  have check : Primrec fun context : ResidualSearchInput × BinString => guard (context.1.1, context.2) :=
    effectiveGuard.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  exact Primrec.option_bind (residualSearchStep_primrec code)
    (check.cond (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂

theorem guardedResidualSearchStep_some_iff (code : Nat.Partrec.Code) (guard : ResidualGuard)
    (input : ResidualSearchInput) (residual : BinString) :
    guardedResidualSearchStep code guard input = some residual ↔
      residualSearchStep code input = some residual ∧ guard (input.1, residual) = true := by
  unfold guardedResidualSearchStep guardResidualCandidate
  cases found : residualSearchStep code input with
  | none => simp only [Option.bind_none, reduceCtorEq, false_and]
  | some candidate =>
      simp only [Option.bind_some]
      cases admitted : guard (input.1, candidate) with
      | false =>
          constructor
          · intro impossible
            cases impossible
          · rintro ⟨same, accepted⟩
            have equal : candidate = residual := Option.some.inj same
            subst candidate
            simp only [admitted, Bool.false_eq_true] at accepted
      | true =>
          constructor
          · intro same
            have equal : candidate = residual := Option.some.inj same
            exact ⟨same, equal ▸ admitted⟩
          · exact And.left

def guardedResidualSearch (code : Nat.Partrec.Code) (guard : ResidualGuard) : ConditionalAlgorithm :=
  fun feature source => Nat.rfindOpt fun rank => guardedResidualSearchStep code guard ((feature, source), rank)

theorem guardedResidualSearch_partrec (code : Nat.Partrec.Code) {guard : ResidualGuard}
    (effectiveGuard : Primrec guard) : Partrec₂ (guardedResidualSearch code guard) :=
  Partrec.rfindOpt (guardedResidualSearchStep_primrec code effectiveGuard).to_comp

theorem guardedResidualSearch_sound {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {guard : ResidualGuard} {feature source residual : BinString}
    (selected : residual ∈ guardedResidualSearch code guard feature source) :
    source ∈ U feature residual ∧ feature.length + residual.length < source.length ∧
      guard ((feature, source), residual) = true := by
  obtain ⟨rank, found⟩ := Nat.rfindOpt_spec selected
  obtain ⟨base, admitted⟩ := (guardedResidualSearchStep_some_iff code guard _ residual).mp
    (Option.mem_def.mp found)
  have correct := residualSearchStep_sound codeSpec base
  exact ⟨correct.1, correct.2, admitted⟩

theorem guardedResidualSearch_complete {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {guard : ResidualGuard} {feature source residual : BinString}
    (reconstructs : source ∈ U feature residual)
    (smaller : feature.length + residual.length < source.length)
    (admitted : guard ((feature, source), residual) = true) :
    ∃ selected, selected ∈ guardedResidualSearch code guard feature source := by
  obtain ⟨rank, candidate⟩ := residualSearchStep_complete codeSpec reconstructs smaller
  have found := (guardedResidualSearchStep_some_iff code guard ((feature, source), rank) residual).mpr
    ⟨candidate, admitted⟩
  exact Part.dom_iff_mem.mp (Nat.rfindOpt_dom.mpr
    ⟨rank, residual, by simpa only [Option.mem_def] using found⟩)

def GuardedDescriptiveMap (U : ConditionalAlgorithm) (guard : ResidualGuard)
    (feature descriptive source : BinString) : Prop :=
  ∃ residual, residual ∈ U descriptive source ∧ source ∈ U feature residual ∧
    feature.length + residual.length < source.length ∧ guard ((feature, source), residual) = true

def ShortestGuardedDescriptiveMap (U : ConditionalAlgorithm) (guard : ResidualGuard)
    (feature descriptive source : BinString) : Prop :=
  GuardedDescriptiveMap U guard feature descriptive source ∧
    ∀ other, GuardedDescriptiveMap U guard feature other source → descriptive.length ≤ other.length

/-- A single effective guard is compiled once, not selected separately for
each source. Only an actually admitted reconstruction witnesses termination. -/
theorem guarded_descriptive_compiler (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U)
    {guard : ResidualGuard} (effectiveGuard : Primrec guard) :
    ∃ compiler : BinString, ∀ feature source,
      (∃ residual, source ∈ U feature residual ∧ feature.length + residual.length < source.length ∧
        guard ((feature, source), residual) = true) →
      GuardedDescriptiveMap U guard feature (compiler ++ feature) source := by
  obtain ⟨code, codeSpec⟩ := exists_conditional_algorithm_code effective
  obtain ⟨compiler, compiles⟩ := universal (guardedResidualSearch code guard)
    (guardedResidualSearch_partrec code effectiveGuard)
  refine ⟨compiler, fun feature source present => ?_⟩
  obtain ⟨residual, reconstructs, smaller, admitted⟩ := present
  obtain ⟨selected, finds⟩ := guardedResidualSearch_complete codeSpec reconstructs smaller admitted
  have sound := guardedResidualSearch_sound codeSpec finds
  exact ⟨selected, compiles feature source selected finds, sound.1, sound.2.1, sound.2.2⟩

theorem shortest_guarded_descriptive_linear (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U)
    {guard : ResidualGuard} (effectiveGuard : Primrec guard) :
    ∃ overhead : Nat, ∀ feature descriptive source,
      ShortestGuardedDescriptiveMap U guard feature descriptive source →
      descriptive.length ≤ feature.length + overhead := by
  obtain ⟨compiler, compiles⟩ := guarded_descriptive_compiler U universal effective effectiveGuard
  refine ⟨compiler.length, fun feature descriptive source minimum => ?_⟩
  obtain ⟨residual, _, reconstructs, smaller, admitted⟩ := minimum.1
  have competitor := compiles feature source ⟨residual, reconstructs, smaller, admitted⟩
  have bound := minimum.2 (compiler ++ feature) competitor
  simpa only [List.length_append, Nat.add_comm] using bound

def rationalResidualGuard (numerator denominator : Nat) : ResidualGuard :=
  fun input => decide (numerator * input.2.length ≤ denominator * input.1.2.length)

theorem rationalResidualGuard_primrec (numerator denominator : Nat) :
    Primrec (rationalResidualGuard numerator denominator) := by
  have residual : Primrec fun input : (BinString × BinString) × BinString => input.2.length :=
    Primrec.list_length.comp Primrec.snd
  have source : Primrec fun input : (BinString × BinString) × BinString => input.1.2.length :=
    Primrec.list_length.comp (Primrec.snd.comp Primrec.fst)
  exact (Primrec.nat_le.comp
    (Primrec.nat_mul.comp (Primrec.const numerator) residual)
    (Primrec.nat_mul.comp (Primrec.const denominator) source)).decide

theorem rationalResidualGuard_iff (numerator denominator : Nat) (positive : 0 < denominator)
    (feature source residual : BinString) :
    rationalResidualGuard numerator denominator ((feature, source), residual) = true ↔
      ((numerator : ℝ) / denominator) * residual.length ≤ source.length := by
  have realPositive : (0 : ℝ) < denominator := by exact_mod_cast positive
  simp only [rationalResidualGuard, decide_eq_true_eq]
  rw [div_mul_eq_mul_div, div_le_iff₀ realPositive]
  norm_cast
  rw [Nat.mul_comm source.length denominator]

theorem rational_guarded_map_iff (U : ConditionalAlgorithm) (numerator denominator : Nat)
    (positive : 0 < denominator) (feature descriptive source : BinString) :
    GuardedDescriptiveMap U (rationalResidualGuard numerator denominator) feature descriptive source ↔
      BDescriptiveMap U ((numerator : ℝ) / denominator) feature descriptive source := by
  simp only [GuardedDescriptiveMap, BDescriptiveMap,
    rationalResidualGuard_iff numerator denominator positive]

theorem shortest_rational_descriptive_linear (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U)
    (numerator denominator : Nat) (positive : 0 < denominator) :
    ∃ overhead : Nat, ∀ feature descriptive source,
      ShortestBDescriptiveMap U ((numerator : ℝ) / denominator) feature descriptive source →
      descriptive.length ≤ feature.length + overhead := by
  obtain ⟨overhead, bounds⟩ := shortest_guarded_descriptive_linear U universal effective
    (rationalResidualGuard_primrec numerator denominator)
  refine ⟨overhead, fun feature descriptive source minimum => ?_⟩
  apply bounds feature descriptive source
  exact ⟨(rational_guarded_map_iff U numerator denominator positive _ _ _).mpr minimum.1,
    fun other admitted => minimum.2 other
      ((rational_guarded_map_iff U numerator denominator positive _ _ _).mp admitted)⟩

/-- The short-map conclusion also holds for minimum ratio-restricted maps
at every fixed rational factor greater than one. The actual selected residual
continues to meet that factor, rather than merely reconstructing the source. -/
theorem b_compressible_shortest_rational_maps_constant (U : ConditionalAlgorithm)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U)
    (numerator denominator : Nat) (positive : 0 < denominator) (greater : denominator < numerator) :
    ∃ featureBudget mapBudget : Nat, ∀ feature descriptive source residual,
      ((numerator : ℝ) / denominator) * plainConditionalComplexity U source [] ≤ source.length →
      ShortestBFeature U ((numerator : ℝ) / denominator) feature source →
      ShortestBDescriptiveMap U ((numerator : ℝ) / denominator) feature descriptive source →
      residual ∈ U descriptive source →
      feature.length ≤ featureBudget ∧ descriptive.length ≤ mapBudget ∧
        descriptive.length = plainConditionalComplexity U residual source ∧
        ((numerator : ℝ) / denominator) * residual.length ≤ source.length := by
  obtain ⟨fixed, featureBounds⟩ := b_compressible_feature_bound U universal effective
  obtain ⟨overhead, mapBounds⟩ := shortest_rational_descriptive_linear U universal effective
    numerator denominator positive
  let factor : ℝ := (numerator : ℝ) / denominator
  have large : 1 < factor := by
    apply (one_lt_div₀ (show (0 : ℝ) < denominator by exact_mod_cast positive)).mpr
    exact_mod_cast greater
  let budget : Nat := ⌈max (fixed.length : ℝ) (fixed.length / (factor - 1))⌉₊
  refine ⟨budget, budget + overhead, fun feature descriptive source residual compression minimumFeature minimumMap selected => ?_⟩
  have bounds := (featureBounds factor large source compression).2.2 feature minimumFeature
  have ceiling : (feature.length : ℝ) ≤ budget := bounds.trans (Nat.le_ceil _)
  have length : feature.length ≤ budget := by exact_mod_cast ceiling
  have maps := mapBounds feature descriptive source minimumMap
  have correct := shortest_b_descriptive_actual_output minimumMap selected
  exact ⟨length, by omega, correct.2.2.2, correct.2.2.1⟩

#print axioms guardedResidualSearchStep_primrec
#print axioms guardedResidualSearchStep_some_iff
#print axioms guardedResidualSearch_partrec
#print axioms guardedResidualSearch_sound
#print axioms guardedResidualSearch_complete
#print axioms guarded_descriptive_compiler
#print axioms shortest_guarded_descriptive_linear
#print axioms rationalResidualGuard_primrec
#print axioms rationalResidualGuard_iff
#print axioms rational_guarded_map_iff
#print axioms shortest_rational_descriptive_linear
#print axioms b_compressible_shortest_rational_maps_constant

end KolmogorovComplexity.FeatureTheory
