import Mettapedia.Computability.PNP.CruxFiniteCoinPostprocessingAnchorsCore

/-!
# Regression checks for PNP finite-coin core anchors

Core finite-coin recoding regression wrappers for the finite-coin postprocessing anchor surface.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem finite_coin_anchor_predicate_erasure_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔ FiniteCoinOutputPredicateErasing r := by
  exact finiteCoinCoverage_anchor_predicateErasure r

theorem finite_coin_anchor_decoder_half_accuracy_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteCoinOutputDecoderHalfAccurate r decode := by
  exact finiteCoinCoverage_anchor_decoderHalfAccuracy r decode hbal

theorem finite_coin_anchor_exact_scaled_imbalance_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y) =
      Fintype.card Coin * finiteCoinFiberImbalance r y := by
  exact finiteCoinCoverage_anchor_exactScaledFiberImbalance r y

theorem finite_coin_anchor_sub_card_tolerance_quantization_regression
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) {τ : Nat}
    (hlt : τ < Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinCoverage_anchor_subCardinalityToleranceQuantization r hlt

theorem finite_coin_anchor_deterministic_postprocessing_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) := by
  exact finiteCoinCoverage_anchor_deterministicOutputPostprocessing r g hbal

theorem finite_coin_anchor_injective_postprocessing_erasure_equivalence_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinCoverage_anchor_injectivePostprocessingErasureEquivalence
    r g hinj

theorem finite_coin_anchor_observed_left_inverse_postprocessing_erasure_equivalence_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinCoverage_anchor_observedLeftInversePostprocessingErasureEquivalence
    r g recover hrecover

theorem finite_coin_anchor_observed_injective_postprocessing_erasure_equivalence_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r := by
  exact finiteCoinCoverage_anchor_observedInjectivePostprocessingErasureEquivalence
    r g hinjObs

theorem finite_coin_anchor_postprocessing_observed_output_collision_obligation_regression
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) := by
  exact finiteCoinCoverage_anchor_postprocessingObservedOutputCollisionObligation
    r g hbal hnot

theorem finite_coin_anchor_postprocessing_observed_opposite_bias_collision_obligation_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ yTrue yFalse : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue ∧
          coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse := by
  exact finiteCoinCoverage_anchor_postprocessingObservedOppositeBiasCollisionObligation
    r g hbal hnot

theorem finite_coin_anchor_postprocessing_signed_bias_cancellation_certificate_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      ∀ z : β,
        (∑ y ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias r y) = 0 := by
  exact finiteCoinCoverage_anchor_postprocessingSignedBiasCancellationCertificate
    r g

theorem finite_coin_anchor_finite_preimage_postprocessing_blowup_regression
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) {m τ : Nat}
    (hbound : finiteOutputMapFiberCardBound g m)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput (fun b c => g (r b c))) (m * τ) := by
  exact finiteCoinCoverage_anchor_finitePreimagePostprocessingBlowup
    r g hbound happrox

end Mettapedia.Computability.PNP.CruxSynthesisRegression
