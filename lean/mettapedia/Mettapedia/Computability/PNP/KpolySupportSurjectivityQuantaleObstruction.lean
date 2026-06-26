import Mettapedia.Computability.PNP.CruxKpolySupportFullRuleCardinality
import Mettapedia.Computability.PNP.CruxKpolySupportFullRuleUniformSection
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostAdvantageVisiblePair
import Mettapedia.Computability.PNP.ResidualSideInformationResolutionCostSupportedPackagesCore

/-!
# Kpoly support-surjectivity and weakness boundary

This module records the route-class boundary left after the polynomial-image
shortcut is removed.  Observed block-output traces can have a finite image, but
full exact-visible rule recovery requires the support/query map to hit every
exact-visible input.  On the weakness side, positive advantage over an
invariant base is equivalent to supported side information that resolves the
relevant pairs.
-/

namespace Mettapedia.Computability.PNP

universe u v

section KpolySupportBoundary

variable {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block] {k s clock : ℕ}

/-- The observed-support route boundary: finite observed traces coexist with
failure of below-surface full-rule cover, clocked payload, exact decoding,
missed-point querying, and uniform support-section transfer. -/
def KpolyObservedSupportBoundary
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) (s clock : ℕ) : Prop :=
  (supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.FinitePredictorCover
      (2 ^ Fintype.card Block) ∧
    ¬ (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
      (2 ^ s) ∧
    ¬ ClockedKpolyFiniteLearningPayload
      (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily s clock ∧
    (¬ ∃ decode : (Block → Bool) → ExactVisibleRule Z k,
      ∀ rule : ExactVisibleRule Z k,
        decode
            ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
          rule) ∧
    (∃ u₀ : ExactVisiblePostSwitchSurface Z k,
      ¬ ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀) ∧
    ¬ ∃ sec : ExactVisiblePostSwitchSurface Z k → Block,
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec

/-- Positive boundary for a repair: a uniform support section transfers the
observed cover and clocked payload, but it also forces the support cardinality
to cover the whole exact-visible surface. -/
def KpolySupportSurjectiveTransfer
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) (clock : ℕ) : Prop :=
  (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily.FinitePredictorCover
      (2 ^ Fintype.card Block) ∧
    ClockedKpolyFiniteLearningPayload
      (supportFullRuleActualSwitchedLocalInterface visibleOf).predictorFamily
      (Fintype.card Block) clock ∧
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ Fintype.card Block ∧
    Function.Surjective visibleOf

/-- Below the exact-visible surface size, the finite observed image is not
enough; exact full-rule recovery and weakness transfer need a support-surjective
repair. -/
theorem kpolySupportSurjectivity_observedSupport_boundary_packet
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    KpolyObservedSupportBoundary visibleOf s clock := by
  have hobs :=
    kpolyCoverage_anchor_supportFullRule_observedSmall_and_not_exactVisibleCover
      (Z := Z) (Block := Block) (k := k) (s := s) visibleOf hs
  exact
    ⟨hobs.1, hobs.2,
      kpolyCoverage_anchor_supportFullRule_not_clockedPayload_of_lt_surfaceCard
        (Z := Z) (Block := Block) (k := k) (s := s) (clock := clock)
        visibleOf hs,
      kpolyCoverage_anchor_supportFullRule_no_exactDecoder_below_surfaceCard
        (Z := Z) (Block := Block) (k := k) visibleOf hcard,
      kpolyCoverage_anchor_supportFullRule_exists_unobservable_eval_below_surfaceCard
        (Z := Z) (Block := Block) (k := k) visibleOf hcard,
      kpolyCoverage_anchor_supportFullRule_no_uniformSection_below_surfaceCard
        (Z := Z) (Block := Block) (k := k) visibleOf hcard⟩

/-- A support-surjective repair genuinely transfers observed finite cover and
clocked payload, and the same hypothesis records the cardinality floor it pays. -/
theorem kpolySupportSurjectivity_positive_transfer_packet
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    {sec : ExactVisiblePostSwitchSurface Z k → Block}
    (hsec :
      (supportFullRuleActualSwitchedLocalInterface visibleOf).HasUniformVisibleSection sec) :
    KpolySupportSurjectiveTransfer visibleOf clock := by
  have hsurj : Function.Surjective visibleOf := by
    intro u
    refine ⟨sec u, ?_⟩
    have h := hsec (fun _ => false) u
    simpa [supportFullRuleActualSwitchedLocalInterface,
      ActualSwitchedLocalInterface.visibleInput] using h
  exact
    ⟨kpolyCoverage_anchor_supportFullRule_finitePredictorCover_card_of_uniformVisibleSection
        (Z := Z) (Block := Block) (k := k) visibleOf hsec,
      kpolyCoverage_anchor_supportFullRule_clockedPayload_card_of_uniformVisibleSection
        (Z := Z) (Block := Block) (k := k) (clock := clock) visibleOf hsec,
      kpolyCoverage_anchor_supportFullRule_uniformSection_forces_surfaceCard_le_supportCard
        (Z := Z) (Block := Block) (k := k) visibleOf hsec,
      hsurj⟩

end KpolySupportBoundary

section KpolySupportPointQueries

variable {Z : Type v} {Block : Type v} {k : ℕ}

/-- Exact point-query decoding from observed traces is equivalent to
surjectivity of the support/query map. -/
theorem kpolySupportSurjectivity_allPointQueries_iff_surjective
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k) :
    (∀ u₀ : ExactVisiblePostSwitchSurface Z k,
      ∃ decode : (Block → Bool) → Bool,
        ∀ rule : ExactVisibleRule Z k,
          decode
              ((supportFullRuleActualSwitchedLocalInterface visibleOf).outputFamily.predict rule) =
            rule u₀) ↔ Function.Surjective visibleOf :=
  supportFullRule_all_evalDecoders_iff_visibleOf_surjective visibleOf

end KpolySupportPointQueries

section WeaknessBoundary

variable {α Base Side : Type u} [Fintype α]

/-- Supported package extracted exactly from a positive-advantage claim over an
invariant base. -/
def SupportedPositiveAdvantagePackage
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) : Prop :=
  ∃ h : Base × Side → Bool,
    0 < doubledAdvantage (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x))

/-- Supported package extracted exactly from a strict half-accuracy advantage
claim over an invariant base. -/
def SupportedStrictHalfPackage
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) : Prop :=
  ∃ h : Base × Side → Bool,
    weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h ∧
      0 < resolvedMass τ side w ∧
      ¬ SideInfoDeterminedBy base side ∧
      ¬ SupportwiseSourceOnlyPairClassifier base side w h ∧
      (∃ x, 0 < w x ∧ base (τ x) = base x ∧ side (τ x) ≠ side x) ∧
      (∃ x, 0 < w x ∧
        ¬ SourceOnlyPredicateCapturesSideEq base side (side x)) ∧
      (∃ x, 0 < w x ∧
        h (base (τ x), side (τ x)) ≠ h (base x, side x))

/-- If the visible pair is invariant on positive support while the target flips,
no classifier on that pair has positive or strict-half advantage. -/
theorem quantaleWeakness_invariant_visiblePair_blocks_packet
    (σ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hσ : Function.Involutive σ)
    (hy : ∀ x, y (σ x) = !(y x))
    (hw : ∀ x, w (σ x) = w x)
    (hpair : ∀ x, 0 < w x → (base (σ x), side (σ x)) = (base x, side x)) :
    (¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h) ∧
      ¬ weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  exact
    ⟨not_pos_doubledAdvantage_pair_of_supportwise_visiblePair_invariant
        σ base side y w h hσ hy hw hpair,
      not_total_lt_two_mul_weightedCorrectMass_pair_of_supportwise_visiblePair_invariant
        σ base side y w h hσ hy hw hpair⟩

/-- Positive advantage over an invariant base is exactly a supported resolving
side-information package; without that package there is no weakness separation
for this route class. -/
theorem quantaleWeakness_supportResolution_exactBoundary_packet
    (τ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ)
    (hτ : Function.Involutive τ)
    (hbase : ∀ x, base (τ x) = base x)
    (hy : ∀ x, y (τ x) = !(y x))
    (hw : ∀ x, w (τ x) = w x) :
    ((∃ h : Base × Side → Bool,
      0 < doubledAdvantage (fun x => (base x, side x)) y w h) ↔
        SupportedPositiveAdvantagePackage τ base side y w) ∧
      ((∃ h : Base × Side → Bool,
        weightedTotalMass w <
          2 * weightedCorrectMass (fun x => (base x, side x)) y w h) ↔
        SupportedStrictHalfPackage τ base side y w) := by
  exact
    ⟨exists_pos_doubledAdvantage_iff_exists_supported_obstruction_package_invariant_base
        τ base side y w hτ hbase hy hw,
      exists_total_lt_two_mul_weightedCorrectMass_iff_exists_supported_obstruction_package_invariant_base
        τ base side y w hτ hbase hy hw⟩

end WeaknessBoundary

/-- Combined public packet: below-surface observed support blocks the Kpoly
full-rule bridge, and visible-pair invariance blocks the corresponding
weakness/advantage route unless supported side information resolves the pairs. -/
theorem kpolySupportSurjectivityQuantale_obstruction_packet
    {Z : Type v} [Fintype Z] {Block : Type v} [Fintype Block]
    {k s clock : ℕ}
    (visibleOf : Block → ExactVisiblePostSwitchSurface Z k)
    (hcard :
      Fintype.card Block < Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k))
    {α Base Side : Type u} [Fintype α]
    (σ : α → α) (base : α → Base) (side : α → Side)
    (y : α → Bool) (w : α → ℕ) (h : Base × Side → Bool)
    (hσ : Function.Involutive σ)
    (hy : ∀ x, y (σ x) = !(y x))
    (hw : ∀ x, w (σ x) = w x)
    (hpair : ∀ x, 0 < w x → (base (σ x), side (σ x)) = (base x, side x)) :
    KpolyObservedSupportBoundary visibleOf s clock ∧
      (¬ 0 < doubledAdvantage (fun x => (base x, side x)) y w h) ∧
      ¬ weightedTotalMass w <
        2 * weightedCorrectMass (fun x => (base x, side x)) y w h := by
  exact
    ⟨kpolySupportSurjectivity_observedSupport_boundary_packet
        (Z := Z) (Block := Block) (k := k) (s := s) (clock := clock)
        visibleOf hcard hs,
      quantaleWeakness_invariant_visiblePair_blocks_packet
        σ base side y w h hσ hy hw hpair⟩

end Mettapedia.Computability.PNP
