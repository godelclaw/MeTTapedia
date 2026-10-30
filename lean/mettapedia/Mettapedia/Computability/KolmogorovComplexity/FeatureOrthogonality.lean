import Mettapedia.Computability.KolmogorovComplexity.FeatureIncrementalInformation
import Mathlib.Data.Nat.Dist

/-!
# Uniform orthogonality of incremental shortest features

This is IC Theorem 3.5 over the common conditional source interpreter and
effective prefix reference machine. Every chain step retains a shortest
feature and shortest descriptive map. One compiler budget works for all
sources, chains and positions. The practical learner's decreasing archive
cost does not supply either minimum-program premise.

Arthur Franz, Oleksandr Antonenko and Roman Soletskyi, "A theory of
incremental compression" (2020), doi:10.1016/j.ins.2020.08.035.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory

open scoped Classical
open ConditionalInformationTransport

theorem ShortestChain.split {U : ConditionalAlgorithm} {source final : BinString}
    {pre suffix : List BinString} (chain : ShortestChain U source (pre ++ suffix) final) :
    ∃ intermediate, ShortestChain U source pre intermediate ∧
      ShortestChain U intermediate suffix final := by
  induction pre generalizing source with
  | nil => exact ⟨source, .nil source, chain⟩
  | cons first rest ih =>
      cases chain with
      | cons minimalFeature minimalMap extracts reconstructs smaller remaining =>
          obtain ⟨intermediate, before, after⟩ := ih remaining
          exact ⟨intermediate,
            .cons minimalFeature minimalMap extracts reconstructs smaller before, after⟩

theorem ShortestChain.feature_length_le {U : ConditionalAlgorithm} {source final feature : BinString}
    {pre suffix : List BinString} (chain : ShortestChain U source (pre ++ feature :: suffix) final) :
    feature.length ≤ source.length := by
  obtain ⟨intermediate, before, after⟩ := chain.split
  have priorLength := before.residual_le
  cases after with
  | cons _ _ _ _ smaller _ => omega

theorem later_feature_description (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chainRule : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ source pre feature suffix final,
      ShortestChain U source (pre ++ feature :: suffix) final →
      conditionalComplexity V feature source ≤
        (pre.length + 1) * (8 * Nat.log 2 (source.length + 1) + overhead) := by
  obtain ⟨featureCost, featureBound⟩ :=
    reference_shortest_feature_source_bound U V universal effective reference chainRule simulations
  obtain ⟨residualCost, residualBound⟩ :=
    shortest_map_residual_information U V universal effective reference chainRule simulations
  let composeCost := chainRule.constant + simulations.headCondition.compilerPrefix.length +
    simulations.secondOutput.compilerPrefix.length
  refine ⟨featureCost + residualCost + composeCost, fun source pre feature suffix final chain => ?_⟩
  induction pre generalizing source with
  | nil =>
      cases chain with
      | cons minimalFeature _ _ _ _ _ =>
          have bounded := featureBound source feature minimalFeature
          simp only [List.length_nil, zero_add, one_mul]
          omega
  | cons first pre ih =>
      cases chain with
      | @cons source residual final first descriptive features minimalFeature minimalMap extracts reconstructs smaller rest =>
          have remaining := ih residual rest
          have residualInformation := residualBound first descriptive source residual minimalFeature minimalMap extracts
          have composed := conditional_triangle V reference chainRule simulations source residual feature
          have logarithm := Nat.log_mono_right (b := 2)
            (show residual.length + 1 ≤ source.length + 1 by omega)
          let budget := 8 * Nat.log 2 (source.length + 1) + featureCost + residualCost + composeCost
          have raised : conditionalComplexity V feature residual ≤ (pre.length + 1) * budget := by
            apply remaining.trans
            exact Nat.mul_le_mul_left _ (by dsimp [budget]; omega)
          have extra : 8 * Nat.log 2 (source.length + 1) + residualCost + composeCost ≤ budget := by
            dsimp [budget]
            omega
          have total : conditionalComplexity V feature source ≤
              (pre.length + 1) * budget + budget := by
            dsimp only [composeCost] at extra
            omega
          simpa only [List.length_cons, Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul,
            budget, Nat.add_assoc] using total

private theorem add_slack_per_step (steps cost slack : Nat) (positive : 1 ≤ steps) :
    steps * cost + slack ≤ steps * (cost + slack) := by
  rw [Nat.mul_add]
  exact Nat.add_le_add_left (by simpa using Nat.mul_le_mul_right slack positive) _

/-- Split-form orthogonality, in both information directions. The distance
is the number of transitions from the first chosen feature to the second. -/
theorem shortest_chain_pairwise_information (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chainRule : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ source pre first middle second suffix final,
      ShortestChain U source (pre ++ first :: (middle ++ second :: suffix)) final →
      |directedAlgorithmicInformation V first second| ≤
        ((middle.length + 1) * (20 * Nat.log 2 (source.length + 1) + overhead) : Nat) ∧
      |directedAlgorithmicInformation V second first| ≤
        ((middle.length + 1) * (20 * Nat.log 2 (source.length + 1) + overhead) : Nat) := by
  obtain ⟨descriptionCost, descriptionBound⟩ := later_feature_description U V universal effective reference chainRule simulations
  obtain ⟨independenceCost, independenceBound⟩ := reference_residual_independence U V universal effective reference chainRule simulations
  obtain ⟨dataCost, dataBound⟩ := information_data_processing V reference chainRule simulations
  obtain ⟨symmetryCost, symmetryBound⟩ := information_symmetry_uniform V reference chainRule simulations
  obtain ⟨ignoreCost, ignoreBound⟩ := reference_ignore_condition V reference
  let totalCost := descriptionCost + independenceCost + dataCost + symmetryCost + ignoreCost
  refine ⟨totalCost, fun source pre first middle second suffix final chain => ?_⟩
  obtain ⟨intermediate, before, after⟩ := chain.split
  have intermediateLength := before.residual_le
  cases after with
  | @cons intermediate residual final first descriptive features minimalFeature minimalMap extracts reconstructs smaller rest =>
      have firstLength : first.length ≤ source.length := by omega
      have residualLength : residual.length ≤ source.length := by omega
      have secondLength : second.length ≤ source.length :=
        rest.feature_length_le.trans residualLength
      have firstLog := Nat.log_mono_right (b := 2) (Nat.add_le_add_right firstLength 1)
      have residualLog := Nat.log_mono_right (b := 2) (Nat.add_le_add_right residualLength 1)
      have secondLog := Nat.log_mono_right (b := 2) (Nat.add_le_add_right secondLength 1)
      have independent := independenceBound first descriptive intermediate residual minimalFeature extracts reconstructs smaller
      change |directedAlgorithmicInformation V first residual| ≤ _ at independent
      have independentUpper : directedAlgorithmicInformation V first residual ≤
          (4 * Nat.log 2 (source.length + 1) + independenceCost : Nat) := by
        have bounded := (abs_le.mp independent).2
        omega
      have later := descriptionBound residual middle second suffix final rest
      have laterRaised : conditionalComplexity V second residual ≤
          (middle.length + 1) * (8 * Nat.log 2 (source.length + 1) + descriptionCost) :=
        later.trans (Nat.mul_le_mul_left _ (by omega))
      have processing := dataBound first residual second
      have rawForward : directedAlgorithmicInformation V first second ≤
          ((middle.length + 1) * (8 * Nat.log 2 (source.length + 1) + descriptionCost) +
            (6 * Nat.log 2 (source.length + 1) + independenceCost + dataCost) : Nat) := by
        omega
      have promoted := add_slack_per_step (middle.length + 1)
        (8 * Nat.log 2 (source.length + 1) + descriptionCost)
        (6 * Nat.log 2 (source.length + 1) + independenceCost + dataCost) (by omega)
      have normalizeForward :
          (8 * Nat.log 2 (source.length + 1) + descriptionCost) +
            (6 * Nat.log 2 (source.length + 1) + independenceCost + dataCost) =
          14 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost := by ring
      rw [normalizeForward] at promoted
      have forward : directedAlgorithmicInformation V first second ≤
          ((middle.length + 1) *
            (14 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost) : Nat) := by
        have promotedInt :
            (((middle.length + 1) * (8 * Nat.log 2 (source.length + 1) + descriptionCost) +
              (6 * Nat.log 2 (source.length + 1) + independenceCost + dataCost) : Nat) : Int) ≤
            ((middle.length + 1) *
              (14 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost) : Nat) := by
          exact_mod_cast promoted
        exact rawForward.trans promotedInt
      have symmetry := symmetryBound first second
      have symmetricGap :
          |directedAlgorithmicInformation V first second - directedAlgorithmicInformation V second first| ≤
            (4 * Nat.log 2 (source.length + 1) + symmetryCost : Nat) := by
        omega
      have reverseRaw : directedAlgorithmicInformation V second first ≤
          ((middle.length + 1) *
            (14 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost) +
              (4 * Nat.log 2 (source.length + 1) + symmetryCost) : Nat) := by
        have gap := (abs_le.mp symmetricGap).1
        omega
      have promotedReverse := add_slack_per_step (middle.length + 1)
        (14 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost)
        (4 * Nat.log 2 (source.length + 1) + symmetryCost) (by omega)
      have normalizeReverse :
          (14 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost) +
            (4 * Nat.log 2 (source.length + 1) + symmetryCost) =
          18 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost + symmetryCost := by ring
      rw [normalizeReverse] at promotedReverse
      have reverse : directedAlgorithmicInformation V second first ≤
          ((middle.length + 1) *
            (18 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost + symmetryCost) : Nat) := by
        have promotedInt :
            (((middle.length + 1) *
              (14 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost) +
                (4 * Nat.log 2 (source.length + 1) + symmetryCost) : Nat) : Int) ≤
              ((middle.length + 1) *
                (18 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost + symmetryCost) : Nat) := by
          exact_mod_cast promotedReverse
        exact reverseRaw.trans promotedInt
      have forwardBudget := Nat.mul_le_mul_left (middle.length + 1)
        (show 14 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost ≤
          20 * Nat.log 2 (source.length + 1) + totalCost by dsimp [totalCost]; omega)
      have reverseBudget := Nat.mul_le_mul_left (middle.length + 1)
        (show 18 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost + symmetryCost ≤
          20 * Nat.log 2 (source.length + 1) + totalCost by dsimp [totalCost]; omega)
      have costBudget : ignoreCost ≤ (middle.length + 1) * (20 * Nat.log 2 (source.length + 1) + totalCost) := by
        have amplified := Nat.mul_le_mul_right (20 * Nat.log 2 (source.length + 1) + totalCost)
          (show 1 ≤ middle.length + 1 by omega)
        dsimp only [totalCost] at amplified ⊢
        omega
      have forwardInt :
          (((middle.length + 1) * (14 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost) : Nat) : Int) ≤
            ((middle.length + 1) * (20 * Nat.log 2 (source.length + 1) + totalCost) : Nat) := by exact_mod_cast forwardBudget
      have reverseInt :
          (((middle.length + 1) * (18 * Nat.log 2 (source.length + 1) + descriptionCost + independenceCost + dataCost + symmetryCost) : Nat) : Int) ≤
            ((middle.length + 1) * (20 * Nat.log 2 (source.length + 1) + totalCost) : Nat) := by exact_mod_cast reverseBudget
      have costInt : (ignoreCost : Int) ≤
          ((middle.length + 1) * (20 * Nat.log 2 (source.length + 1) + totalCost) : Nat) := by exact_mod_cast costBudget
      have ignoredForward := ignoreBound second first
      have ignoredReverse := ignoreBound first second
      constructor
      · rw [abs_le]
        constructor
        · simp only [directedAlgorithmicInformation, inducedPrefixComplexity]
          omega
        · exact forward.trans forwardInt
      · rw [abs_le]
        constructor
        · simp only [directedAlgorithmicInformation, inducedPrefixComplexity]
          omega
        · exact reverse.trans reverseInt

private theorem list_split_at_indices {α : Type*} (items : List α) (i j : Nat)
    (hi : i < items.length) (hj : j < items.length) (ordered : i < j) :
    items = items.take i ++ items[i] ::
      ((items.drop (i + 1)).take (j - i - 1) ++ items[j] :: items.drop (j + 1)) := by
  have later : (items.drop (i + 1)).drop (j - i - 1) = items[j] :: items.drop (j + 1) := by
    calc
      (items.drop (i + 1)).drop (j - i - 1) = items.drop j := by
        rw [List.drop_drop]
        congr 1
        omega
      _ = items[j] :: items.drop (j + 1) :=
        (List.cons_getElem_drop_succ (l := items) (n := j) (h := hj)).symm
  have rest : items.drop (i + 1) =
      (items.drop (i + 1)).take (j - i - 1) ++ items[j] :: items.drop (j + 1) := by
    calc
      items.drop (i + 1) = (items.drop (i + 1)).take (j - i - 1) ++
          (items.drop (i + 1)).drop (j - i - 1) := (List.take_append_drop _ _).symm
      _ = _ := by rw [later]
  calc
    items = items.take i ++ items.drop i := (List.take_append_drop _ _).symm
    _ = items.take i ++ items[i] :: items.drop (i + 1) := by
      rw [(List.cons_getElem_drop_succ (l := items) (n := i) (h := hi)).symm]
    _ = _ := congrArg (fun tail => items.take i ++ items[i] :: tail) rest

/-- IC Theorem 3.5: the same overhead works for all sources, chain lengths
and distinct positions, and for signed information in either orientation. -/
theorem shortest_chain_orthogonality (U : ConditionalAlgorithm) (V : ConditionalPrefixFreeMachine)
    (universal : IsUniversalConditional U) (effective : Partrec₂ U) (reference : IsReferenceMachine V)
    (chainRule : StrongConditionalChainRule V) (simulations : ReferenceMachineSimulations V) :
    ∃ overhead : Nat, ∀ source features final, ShortestChain U source features final →
      ∀ i j (hi : i < features.length) (hj : j < features.length), i ≠ j →
        |directedAlgorithmicInformation V features[i] features[j]| ≤
          (Nat.dist i j * (20 * Nat.log 2 (source.length + 1) + overhead) : Nat) := by
  obtain ⟨overhead, bound⟩ := shortest_chain_pairwise_information U V universal effective reference chainRule simulations
  refine ⟨overhead, fun source features final chain i j hi hj different => ?_⟩
  rcases Nat.lt_or_gt_of_ne different with ordered | ordered
  · have decomposition := list_split_at_indices features i j hi hj ordered
    have rewritten : ShortestChain U source
        (features.take i ++ features[i] :: ((features.drop (i + 1)).take (j - i - 1) ++
          features[j] :: features.drop (j + 1))) final := by rw [← decomposition]; exact chain
    have pair := (bound source _ _ _ _ _ final rewritten).1
    have count : ((features.drop (i + 1)).take (j - i - 1)).length + 1 = j - i := by
      rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
      omega
    simpa only [count, Nat.dist_eq_sub_of_le ordered.le] using pair
  · have decomposition := list_split_at_indices features j i hj hi ordered
    have rewritten : ShortestChain U source
        (features.take j ++ features[j] :: ((features.drop (j + 1)).take (i - j - 1) ++
          features[i] :: features.drop (i + 1))) final := by rw [← decomposition]; exact chain
    have pair := (bound source _ _ _ _ _ final rewritten).2
    have count : ((features.drop (j + 1)).take (i - j - 1)).length + 1 = i - j := by
      rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
      omega
    simpa only [count, Nat.dist_eq_sub_of_le_right ordered.le] using pair

end KolmogorovComplexity.FeatureTheory
