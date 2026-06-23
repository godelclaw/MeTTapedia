import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinFibers

/-!
# Finite-coin imbalance tolerance obligations
-/

namespace Mettapedia.Computability.PNP

/-- Obligation form for an arbitrary finite-coin output fiber: approximate
output independence forces the tolerance to dominate the true-minus-false
coin-fiber imbalance, scaled by the source-fiber product and the number of
coins. -/
theorem trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          (coinTrueFiberCount r y - coinFalseFiberCount r y) ≤ τ := by
  have hgap :=
    countIndependentWithinForwardGap_finiteCoinRecoding_fiber C E r y
  simpa [hgap] using (happrox y).1

/-- The corresponding obligation for the false-minus-true coin-fiber
imbalance. -/
theorem falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          (coinFalseFiberCount r y - coinTrueFiberCount r y) ≤ τ := by
  have hgap :=
    countIndependentWithinBackwardGap_finiteCoinRecoding_fiber C E r y
  simpa [hgap] using (happrox y).2

/-- Strict-tolerance blocker for an arbitrary finite-coin output fiber with
positive true-minus-false coin-fiber imbalance. -/
theorem not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_trueMinusFalse_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              (coinTrueFiberCount r y - coinFalseFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ happrox)

/-- Strict-tolerance blocker for an arbitrary finite-coin output fiber with
positive false-minus-true coin-fiber imbalance. -/
theorem not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_falseMinusTrue_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              (coinFalseFiberCount r y - coinTrueFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ happrox)

/-- Source lower-bound form of the true-minus-false mixed-coin obligation. -/
theorem sourceLowerBounds_trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse * Fintype.card Coin *
      (coinTrueFiberCount r y - coinFalseFiberCount r y) ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul_right (coinTrueFiberCount r y - coinFalseFiberCount r y)
      (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse)))
    (trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ happrox)

/-- Source lower-bound form of the false-minus-true mixed-coin obligation. -/
theorem sourceLowerBounds_falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse * Fintype.card Coin *
      (coinFalseFiberCount r y - coinTrueFiberCount r y) ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul_right (coinFalseFiberCount r y - coinTrueFiberCount r y)
      (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse)))
    (falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ happrox)

/-- Source lower-bound strict blocker for a positive true-minus-false
mixed-coin imbalance. -/
theorem not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_sourceLowerBounds_trueMinusFalse_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (coinTrueFiberCount r y - coinFalseFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceLowerBounds_trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ loTrue loFalse htrue hfalse happrox)

/-- Source lower-bound strict blocker for a positive false-minus-true
mixed-coin imbalance. -/
theorem not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_sourceLowerBounds_falseMinusTrue_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol :
      τ <
        loTrue * loFalse * Fintype.card Coin *
          (coinFalseFiberCount r y - coinTrueFiberCount r y)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceLowerBounds_falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
      C E r y τ loTrue loFalse htrue hfalse happrox)


end Mettapedia.Computability.PNP
