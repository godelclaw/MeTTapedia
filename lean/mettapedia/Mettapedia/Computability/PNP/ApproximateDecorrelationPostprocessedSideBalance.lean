import Mettapedia.Computability.PNP.ApproximateDecorrelationSideRetainedBalance
import Mettapedia.Computability.PNP.ApproximateDecorrelationSideRetainedTrueFiber
import Mettapedia.Computability.PNP.ApproximateDecorrelationSideRetainedFalseFiber

/-!
# PNP approximate decorrelation: postprocessed-side layer
-/

namespace Mettapedia.Computability.PNP

theorem finiteCoinRecodingFiberBalanced_postprocessedSide_iff_observedFiber_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  rfl

/-- Source lower-bound postprocessed-side quantization: below one
lower-bounded source/coin block, approximate independence of any deterministic
postprocessing of the retained-side output is equivalent to exact true/false
balance in every observed postprocessed fiber. -/
theorem countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ
        ↔ FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) :=
          countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
            C E (fun b c => post (r b c, side c)) htrue hfalse hlt
    _ ↔ ∀ z : β,
          finiteEventCount Coin (fun c => post (r true c, side c) = z) =
            finiteEventCount Coin (fun c => post (r false c, side c) = z) :=
          finiteCoinRecodingFiberBalanced_postprocessedSide_iff_observedFiber_count_eq
            r side post

/-- Exact source-count specialization of postprocessed-side quantization. -/
theorem countIndependentWithinToleranceOutput_postprocessedSide_lt_sourceCoinProduct_iff_observedFiber_count_eq
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ : Nat}
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  exact
    countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
      C E r side post le_rfl le_rfl hlt

end Mettapedia.Computability.PNP
