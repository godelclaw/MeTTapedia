import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportCardinality

/-!
# One-block full-rule support obstruction

Singleton-support corollaries showing that one observed block can have a tiny
observed-output cover while still carrying the full exact-visible rule family.
-/

namespace Mettapedia.Computability.PNP

universe v u w

section OneBlockFullRule

variable {Z : Type v} {k : ℕ}

/-- A one-block actual-local interface whose selected local rules are still the
full exact-visible Boolean rule family.  The block support is the single visible
point `u0`; all off-support values are unconstrained by the observed output. -/
abbrev oneBlockFullRuleActualSwitchedLocalInterface
    (u0 : ExactVisiblePostSwitchSurface Z k) :
    ActualSwitchedLocalInterface
      Z k (ExactVisibleRule Z k) Unit :=
  supportFullRuleActualSwitchedLocalInterface (Block := Unit) (fun _ => u0)

@[simp] theorem oneBlockFullRule_predictorFamily
    (u0 : ExactVisiblePostSwitchSurface Z k) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily =
      fullExactVisibleRuleFamily Z k := by
  rfl

theorem oneBlockFullRule_surjective
    (u0 : ExactVisiblePostSwitchSurface Z k) :
    Function.Surjective
      (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.predict := by
  exact supportFullRule_surjective (Block := Unit) (fun _ => u0)

/-- The observed block-output family has a one-bit truth-table budget, because
the block space is a singleton. -/
theorem oneBlockFullRule_outputFamily_hasBitBudget_one
    (u0 : ExactVisiblePostSwitchSurface Z k) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.HasBitBudget 1 := by
  simpa using
    (supportFullRule_outputFamily_hasBitBudget_card
      (Z := Z) (k := k) (Block := Unit) (fun _ => u0))

/-- Equivalently, the observed block-output family has a predictor cover of
size at most two. -/
theorem oneBlockFullRule_outputFamily_finitePredictorCover_two
    (u0 : ExactVisiblePostSwitchSurface Z k) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.FinitePredictorCover 2 := by
  have hbudget :=
    oneBlockFullRule_outputFamily_hasBitBudget_one (Z := Z) (k := k) u0
  simpa using
    (IndexedPredictorFamily.hasBitBudget_iff_finitePredictorCover.mp hbudget)

/-- A one-block full-rule construction cannot have a uniform visible section
once the exact-visible surface has more than one point. -/
theorem oneBlockFullRule_not_hasUniformVisibleSection_of_one_lt_surfaceCard
    [Fintype Z] (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ sec : ExactVisiblePostSwitchSurface Z k → Unit,
      (oneBlockFullRuleActualSwitchedLocalInterface u0).HasUniformVisibleSection sec := by
  simpa using
    (supportFullRule_not_hasUniformVisibleSection_of_card_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (fun _ => u0) hcard)

/-- A one-block reachable-support quotient cannot distinguish full
exact-visible rules once the exact-visible surface has more than one point. -/
theorem oneBlockFullRule_exists_distinct_rules_same_outputFamily_of_one_lt_surfaceCard
    [Fintype Z] (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule₀ =
          (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule₁ ∧
        (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.predict rule₀ ≠
          (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.predict rule₁ := by
  simpa using
    (supportFullRule_exists_distinct_rules_same_outputFamily_of_card_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (fun _ => u0) hcard)

/-- No decoder from a singleton observed trace can reconstruct every full
exact-visible rule once the exact-visible surface has more than one point. -/
theorem oneBlockFullRule_not_exists_exactDecoder_of_one_lt_surfaceCard
    [Fintype Z] (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Unit → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
          rule := by
  simpa using
    (supportFullRule_not_exists_exactDecoder_of_card_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (fun _ => u0) hcard)

/-- In the one-block case, some exact-visible bit is unobservable whenever the
exact-visible surface has more than one point. -/
theorem oneBlockFullRule_exists_unobservable_eval_of_one_lt_surfaceCard
    [Fintype Z] (u0 : ExactVisiblePostSwitchSurface Z k)
    (hcard : 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Unit → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode ((oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.predict rule) =
            rule u := by
  simpa using
    (supportFullRule_exists_unobservable_eval_of_card_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (fun _ => u0) hcard)

/-- But the full exact-visible local-rule image is still the full Boolean rule
family, so it has no below-surface finite predictor cover. -/
theorem oneBlockFullRule_not_finitePredictorCover_of_lt_surfaceCard
    [Fintype Z] {s : ℕ} (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact
    supportFullRule_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (s := s) (fun _ => u0) hs

/-- The one-block interface therefore refutes the move from a tiny observed
output image to a full exact-visible predictor-image bound. -/
theorem oneBlockFullRule_observedSmall_and_not_exactVisibleCover
    [Fintype Z] {s : ℕ} (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (oneBlockFullRuleActualSwitchedLocalInterface u0).outputFamily.FinitePredictorCover 2 ∧
      ¬ (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact
    ⟨oneBlockFullRule_outputFamily_finitePredictorCover_two (Z := Z) (k := k) u0,
      oneBlockFullRule_not_finitePredictorCover_of_lt_surfaceCard
        (Z := Z) (k := k) (s := s) u0 hs⟩

/-- Likewise, tiny observed support does not give the clocked finite-learning
payload for the full exact-visible local-rule family. -/
theorem oneBlockFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    [Fintype Z] {s clock : ℕ} (u0 : ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (oneBlockFullRuleActualSwitchedLocalInterface u0).predictorFamily s clock := by
  exact
    supportFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (Block := Unit) (s := s) (clock := clock) (fun _ => u0) hs

end OneBlockFullRule

end Mettapedia.Computability.PNP
