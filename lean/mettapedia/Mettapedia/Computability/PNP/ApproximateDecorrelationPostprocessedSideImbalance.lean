import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideBalance

/-!
# PNP approximate decorrelation: postprocessed-side layer
-/

namespace Mettapedia.Computability.PNP

/-- Quantitative postprocessed-side obligation: approximate output
independence forces every observed postprocessed fiber's true-minus-false and
false-minus-true residual imbalance to fit inside the tolerance budget.  This
does not require an isolated observed value; any imperfect cancellation after
hashing still contributes a source/coin-scaled defect. -/
theorem sourceLowerBounds_observedFiberImbalanceProducts_le_of_CountIndependentWithinToleranceOutput_postprocessedSide
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r true c, side c) = z) -
            finiteEventCount Coin (fun c => post (r false c, side c) = z)) ≤ τ) ∧
    (∀ z : β,
      loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r false c, side c) = z) -
            finiteEventCount Coin (fun c => post (r true c, side c) = z)) ≤ τ) := by
  constructor
  · intro z
    have h :=
      sourceLowerBounds_trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
        C E (fun b c => post (r b c, side c)) z τ loTrue loFalse
        htrue hfalse happrox
    simpa [coinTrueFiberCount, coinFalseFiberCount] using h
  · intro z
    have h :=
      sourceLowerBounds_falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
        C E (fun b c => post (r b c, side c)) z τ loTrue loFalse
        htrue hfalse happrox
    simpa [coinTrueFiberCount, coinFalseFiberCount] using h

/-- Strict-tolerance blocker for a positive true-minus-false observed-fiber
imbalance after deterministic postprocessing of the retained-side output. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_trueMinusFalse_sourceLowerBounds_gt
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r true c, side c) = z) -
            finiteEventCount Coin (fun c => post (r false c, side c) = z))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  have hbounds :=
    sourceLowerBounds_observedFiberImbalanceProducts_le_of_CountIndependentWithinToleranceOutput_postprocessedSide
      C E r side post τ loTrue loFalse htrue hfalse happrox
  exact (Nat.not_le_of_gt htol) (hbounds.1 z)

/-- Strict-tolerance blocker for a positive false-minus-true observed-fiber
imbalance after deterministic postprocessing of the retained-side output. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_falseMinusTrue_sourceLowerBounds_gt
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (finiteEventCount Coin (fun c => post (r false c, side c) = z) -
            finiteEventCount Coin (fun c => post (r true c, side c) = z))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  have hbounds :=
    sourceLowerBounds_observedFiberImbalanceProducts_le_of_CountIndependentWithinToleranceOutput_postprocessedSide
      C E r side post τ loTrue loFalse htrue hfalse happrox
  exact (Nat.not_le_of_gt htol) (hbounds.2 z)

end Mettapedia.Computability.PNP
