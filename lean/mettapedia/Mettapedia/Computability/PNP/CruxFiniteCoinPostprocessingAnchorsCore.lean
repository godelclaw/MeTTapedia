import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedLeftInverse
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactTolerance
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCollision
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationBias
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationTolerance

/-!
# PNP finite-coin postprocessing anchors: core finite-coin recoding

Core finite-coin output-erasure, decoder, imbalance, and deterministic postprocessing anchors.
-/

namespace Mettapedia.Computability.PNP
open scoped BigOperators
universe u v w z

/-- Route-coverage anchor: balanced finite-coin fibers are exactly output
predicate erasure. -/
theorem finiteCoinCoverage_anchor_predicateErasure
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced r ↔ FiniteCoinOutputPredicateErasing r :=
  finiteCoinRecodingFiberBalanced_iff_outputPredicateErasing r

/-- Route-coverage anchor: balanced finite-coin fibers force every Boolean
output decoder to be exactly half-accurate. -/
theorem finiteCoinCoverage_anchor_decoderHalfAccuracy
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (decode : α → Bool)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    finiteCoinOutputDecoderHalfAccurate r decode :=
  finiteCoinOutputDecoderHalfAccurate_of_fiberBalanced r decode hbal

/-- Route-coverage anchor: each finite-coin output fiber's symmetric defect is
the scaled true/false fiber imbalance. -/
theorem finiteCoinCoverage_anchor_exactScaledFiberImbalance
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) (y : α) :
    countIndependentWithinDefect (Ω := Bool × Coin)
        (fun _ω => True)
        (finiteCoinSourceTrue (Coin := Coin))
        (fun ω => finiteCoinOutput r ω = y) =
      Fintype.card Coin * finiteCoinFiberImbalance r y :=
  countIndependentWithinDefect_finiteCoinOutput_fiber r y

/-- Route-coverage anchor: below one coin block of tolerance, approximate
finite-coin output independence is exact balanced-fiber erasure. -/
theorem finiteCoinCoverage_anchor_subCardinalityToleranceQuantization
    {Coin α : Type*} [Fintype Coin] [DecidableEq α]
    (r : Bool → Coin → α) {τ : Nat}
    (hlt : τ < Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Bool × Coin)
      (fun _ω => True)
      (finiteCoinSourceTrue (Coin := Coin))
      (finiteCoinOutput r) τ ↔
    FiniteCoinRecodingFiberBalanced r :=
  countIndependentWithinToleranceOutput_finiteCoinOutput_lt_card_iff_fiberBalanced
    r hlt

/-- Route-coverage anchor: deterministic output postprocessing preserves exact
balanced-fiber erasure. -/
theorem finiteCoinCoverage_anchor_deterministicOutputPostprocessing
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced r) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) :=
  finiteCoinRecodingFiberBalanced_postcompose r g hbal

/-- Route-coverage anchor: lossless deterministic output postprocessing cannot
create finite-coin erasure.  Balanced fibers after an injective postprocessor
are equivalent to balanced fibers before that postprocessor. -/
theorem finiteCoinCoverage_anchor_injectivePostprocessingErasureEquivalence
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinj : Function.Injective g) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r :=
  finiteCoinRecodingFiberBalanced_postcompose_iff_of_injective r g hinj

/-- Route-coverage anchor: even a many-to-one postprocessor cannot create
finite-coin erasure if the original output is recoverable from the
postprocessed value on every observed true/false coin sample. -/
theorem finiteCoinCoverage_anchor_observedLeftInversePostprocessingErasureEquivalence
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) (recover : β → α)
    (hrecover : ∀ b c, recover (g (r b c)) = r b c) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r :=
  finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedLeftInverse
    r g recover hrecover

/-- Route-coverage anchor: a deterministic postprocessor that is injective on
the actually observed finite-coin support cannot create finite-coin erasure. -/
theorem finiteCoinCoverage_anchor_observedInjectivePostprocessingErasureEquivalence
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hinjObs :
      ∀ b1 c1 b2 c2,
        g (r b1 c1) = g (r b2 c2) → r b1 c1 = r b2 c2) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      FiniteCoinRecodingFiberBalanced r :=
  finiteCoinRecodingFiberBalanced_postcompose_iff_of_observedInjective
    r g hinjObs

/-- Route-coverage anchor: if deterministic postprocessing balances an
originally unbalanced finite-coin recoding, then two distinct observed original
outputs must collide under the postprocessor. -/
theorem finiteCoinCoverage_anchor_postprocessingObservedOutputCollisionObligation
    {Coin α β : Type*} [Fintype Coin] [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ b1 : Bool, ∃ c1 : Coin, ∃ b2 : Bool, ∃ c2 : Coin,
      r b1 c1 ≠ r b2 c2 ∧ g (r b1 c1) = g (r b2 c2) :=
  exists_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
    r g hbal hnot

/-- Route-coverage anchor: if deterministic postprocessing balances an
originally unbalanced finite-coin recoding, then one postprocessed fiber must
merge an original true-heavy output with an original false-heavy output. -/
theorem finiteCoinCoverage_anchor_postprocessingObservedOppositeBiasCollisionObligation
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β)
    (hbal : FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)))
    (hnot : ¬ FiniteCoinRecodingFiberBalanced r) :
    ∃ yTrue yFalse : α,
      g yTrue = g yFalse ∧ yTrue ≠ yFalse ∧
        coinFalseFiberCount r yTrue < coinTrueFiberCount r yTrue ∧
          coinTrueFiberCount r yFalse < coinFalseFiberCount r yFalse :=
  exists_oppositeBias_observedOutput_collision_of_postcompose_fiberBalanced_of_not_fiberBalanced
    r g hbal hnot

/-- Route-coverage anchor: balanced deterministic postprocessing is equivalent
to exact zero total signed original bias in every postprocessed fiber. -/
theorem finiteCoinCoverage_anchor_postprocessingSignedBiasCancellationCertificate
    {Coin α β : Type*} [Fintype Coin] [Fintype α]
    [DecidableEq α] [DecidableEq β]
    (r : Bool → Coin → α) (g : α → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => g (r b c)) ↔
      ∀ z : β,
        (∑ y ∈ finiteOutputPreimageFiber g z,
          finiteCoinSignedFiberBias r y) = 0 :=
  finiteCoinRecodingFiberBalanced_postcompose_iff_forall_sum_signedFiberBias_preimage_eq_zero
    r g

/-- Route-coverage anchor: deterministic finite-output postprocessing has
explicit finite-preimage tolerance blowup `τ ↦ m * τ`. -/
theorem finiteCoinCoverage_anchor_finitePreimagePostprocessingBlowup
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
      (finiteCoinOutput (fun b c => g (r b c))) (m * τ) :=
  countIndependentWithinToleranceOutput_finiteCoinOutput_postcompose
    r g hbound happrox

end Mettapedia.Computability.PNP
