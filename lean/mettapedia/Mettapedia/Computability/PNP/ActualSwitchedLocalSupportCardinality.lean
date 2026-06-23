import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportFullRule

/-!
# Full-rule support cardinality consequences

Cardinality consequences of support maps that are smaller than the full
exact-visible surface, including impossible uniform sections and cover bounds.
-/

namespace Mettapedia.Computability.PNP

universe v u w

section FiniteObservedSupportFullRule

variable {Z : Type v} {k : ℕ}
variable {Block : Type*}

/-- If the support map is not surjective, some exact-visible bit is not
observable from the block-output quotient. -/
theorem supportFullRule_exists_unobservable_eval_of_not_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hnot : ¬ Function.Surjective visibleOf) :
    ∃ u₀ : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀ := by
  classical
  simp only [Function.Surjective, not_forall] at hnot
  rcases hnot with ⟨u₀, hmissExists⟩
  have hmiss : ∀ phi, visibleOf phi ≠ u₀ := by
    intro phi hphi
    exact hmissExists ⟨phi, hphi⟩
  exact
    ⟨u₀,
      supportFullRule_not_exists_evalDecoder_of_missed_point
        (Z := Z) (k := k) (Block := Block) visibleOf u₀ hmiss⟩

/-- Therefore a reachable-support quotient with smaller support than the full
surface cannot identify exact-visible rules by their observed outputs. -/
theorem supportFullRule_not_observedRuleMap_injective_of_card_lt_surfaceCard
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Injective
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict := by
  intro hinj
  have hsurj :
      Function.Surjective visibleOf :=
    supportFullRule_observedRuleMap_injective_forces_visibleOf_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hinj
  exact (not_lt_of_ge (Fintype.card_le_of_surjective visibleOf hsurj)) hcard

/-- Cardinally small support gives an explicit pair of distinct exact-visible
rules that the observed block-output quotient cannot distinguish. -/
theorem supportFullRule_exists_distinct_rules_same_outputFamily_of_card_lt_surfaceCard
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ rule₀ rule₁ : ExactVisibleRule Z k,
      rule₀ ≠ rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₀ =
          (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule₁ ∧
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₀ ≠
          (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.predict rule₁ := by
  have hnot : ¬ Function.Surjective visibleOf := by
    intro hsurj
    exact (not_lt_of_ge (Fintype.card_le_of_surjective visibleOf hsurj)) hcard
  exact
    supportFullRule_exists_distinct_rules_same_outputFamily_of_not_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hnot

/-- Cardinally small support rules out every exact decoder from observed block
outputs to full exact-visible rules. -/
theorem supportFullRule_not_exists_exactDecoder_of_card_lt_surfaceCard
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ decode : (Block → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule := by
  have hnot : ¬ Function.Surjective visibleOf := by
    intro hsurj
    exact (not_lt_of_ge (Fintype.card_le_of_surjective visibleOf hsurj)) hcard
  exact
    supportFullRule_not_exists_exactDecoder_of_not_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hnot

/-- Cardinally small support leaves at least one exact-visible rule bit
unobservable from the observed block-output quotient. -/
theorem supportFullRule_exists_unobservable_eval_of_card_lt_surfaceCard
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ∃ u₀ : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀ := by
  have hnot : ¬ Function.Surjective visibleOf := by
    intro hsurj
    exact (not_lt_of_ge (Fintype.card_le_of_surjective visibleOf hsurj)) hcard
  exact
    supportFullRule_exists_unobservable_eval_of_not_surjective
      (Z := Z) (k := k) (Block := Block) visibleOf hnot

/-- If every exact-visible input has an actual block realizing it uniformly in
the output index, the observed finite cover really does transfer to the full
exact-visible family. -/
theorem supportFullRule_predictorFamily_finitePredictorCover_card_of_uniformVisibleSection
    [Fintype Block] (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
      (2 ^ Fintype.card Block) := by
  exact
    ActualSwitchedLocalInterface.predictorFamily_finitePredictorCover_of_outputFamily_finitePredictorCover
      (supportFullRuleActualSwitchedLocalInterface visibleOf) hsec
      (supportFullRule_outputFamily_finitePredictorCover_card
        (Z := Z) (k := k) (Block := Block) visibleOf)

/-- The corresponding clocked payload follows at the block truth-table budget
when the uniform visible section exists. -/
theorem supportFullRule_clockedKpolyFiniteLearningPayload_card_of_uniformVisibleSection
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block} {clock : ℕ}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    ClockedKpolyFiniteLearningPayload
      (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily
      (Fintype.card Block) clock := by
  exact
    ActualSwitchedLocalInterface.clockedKpolyFiniteLearningPayload_of_outputFamily_hasBitBudget
      (supportFullRuleActualSwitchedLocalInterface visibleOf) hsec
      (supportFullRule_outputFamily_hasBitBudget_card
        (Z := Z) (k := k) (Block := Block) visibleOf)

/-- For the finite-support full-rule construction, a uniform visible section
forces `visibleOf` to be surjective, hence the support must be at least as
large as the full exact-visible surface. -/
theorem supportFullRule_surfaceCard_le_blockCard_of_uniformVisibleSection
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ Fintype.card Block := by
  classical
  have hsurj : Function.Surjective visibleOf := by
    intro u
    refine ⟨sec u, ?_⟩
    have h := hsec (fun _ => false) u
    simpa [supportFullRuleActualSwitchedLocalInterface,
      ActualSwitchedLocalInterface.visibleInput] using h
  exact Fintype.card_le_of_surjective visibleOf hsurj

/-- Thus the finite-support repair is impossible when the observed block
support is smaller than the exact-visible surface. -/
theorem supportFullRule_not_hasUniformVisibleSection_of_card_lt_surfaceCard
    [Fintype Z] [Fintype Block]
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ∃ sec : ExactVisiblePostSwitchSurface Z k → Block,
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec := by
  rintro ⟨sec, hsec⟩
  exact
    (not_lt_of_ge
      (supportFullRule_surfaceCard_le_blockCard_of_uniformVisibleSection
        (Z := Z) (k := k) (Block := Block) visibleOf hsec)) hcard

/-- But the selected local-rule image is still the full exact-visible Boolean
rule family, so it has no below-surface finite predictor cover. -/
theorem supportFullRule_not_finitePredictorCover_of_lt_surfaceCard
    [Fintype Z] {s : ℕ} (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  simpa using
    (fullExactVisibleRuleFamily_not_finitePredictorCover_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) hs)

/-- Therefore a finite observed support bound does not imply a full
exact-visible predictor-image bound. -/
theorem supportFullRule_observedSmall_and_not_exactVisibleCover
    [Fintype Z] [Fintype Block] {s : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FinitePredictorCover
        (2 ^ Fintype.card Block) ∧
      ¬ (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
        (2 ^ s) := by
  exact
    ⟨supportFullRule_outputFamily_finitePredictorCover_card
        (Z := Z) (k := k) (Block := Block) visibleOf,
      supportFullRule_not_finitePredictorCover_of_lt_surfaceCard
        (Z := Z) (k := k) (s := s) visibleOf hs⟩

/-- Likewise, finite observed support does not give the clocked finite-learning
payload for the full exact-visible local-rule family. -/
theorem supportFullRule_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
    [Fintype Z] {s clock : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ ClockedKpolyFiniteLearningPayload
        (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily s clock := by
  simpa using
    (fullExactVisibleRuleFamily_not_clockedKpolyFiniteLearningPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs)

end FiniteObservedSupportFullRule

end Mettapedia.Computability.PNP
