import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSidePredicates

/-!
# PNP approximate decorrelation: postprocessed-side layer
-/

namespace Mettapedia.Computability.PNP

/-- Below one lower-bounded source/coin block, approximate independence of a
postprocessed retained-side output forces every downstream Boolean decoder to
be exactly half-accurate in aggregate across the two source sides.  A decoder
cannot recover source information after hashing unless the observed fibers
already violate the below-threshold independence certificate. -/
theorem postprocessedSide_outputDecoder_correctCount_eq_card_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
      finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) =
        Fintype.card Coin := by
  have hbal : FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) :=
    (countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
      C E (fun b c => post (r b c, side c)) htrue hfalse hlt).1 happrox
  simpa using
    finiteCoinRecodingFiberBalanced_outputDecoder_correctCount_eq_card
      (fun b c => post (r b c, side c)) decode hbal

/-- Strict downstream-decoder blocker for a postprocessed retained-side output:
below one lower-bounded source/coin block, any Boolean decoder with
better-than-half aggregate accuracy refutes approximate output independence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_correctCount_gt_card_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      Fintype.card Coin <
        finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
          finiteEventCount Coin
            (fun c => decode (post (r false c, side c)) = false)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.ne_of_gt hgt)
    (postprocessedSide_outputDecoder_correctCount_eq_card_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post decode htrue hfalse hlt happrox)

/-- Uniform downstream-decoder recovery is incompatible with below-threshold
approximate independence of a postprocessed retained-side output. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_recovers_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hdecodeTrue : ∀ c : Coin, decode (post (r true c, side c)) = true)
    (hdecodeFalse : ∀ c : Coin, decode (post (r false c, side c)) = false) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_separates_sourceLowerBounds_lt_coinProduct
      C E r side post (fun z => decode z = true) htrue hfalse hlt
      hdecodeTrue
      (fun c h => by
        have hfalseDecode : decode (post (r false c, side c)) = false :=
          hdecodeFalse c
        rw [h] at hfalseDecode
        cases hfalseDecode)

end Mettapedia.Computability.PNP
