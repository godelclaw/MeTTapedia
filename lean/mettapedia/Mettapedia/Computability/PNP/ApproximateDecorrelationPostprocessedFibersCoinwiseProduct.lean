import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideBalance
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideImbalance
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSidePredicates
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideDecoders
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideRanges
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideCollisions
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideSkewMaps
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideCoinEquiv
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideSkewThresholds
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideOutputEquiv

/-!
# Finite-coin postprocessed fiber product bounds
-/

namespace Mettapedia.Computability.PNP

/-- Finite-coin output-variable obligation for a randomized recoding whose
`y`-fiber uniformly selects the `true` source side for every coin.  Certifying
all output fibers still forces the source-fiber product on the source/coin
product space. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    conditionedSourceFiberProduct (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ := by
  refine
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_coupled
      (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2 = y) τ ?_ (happrox y)
  intro xr _hC
  by_cases hE : E xr.1
  · simp [hE, htrue xr.2]
  · simp [hE, hfalse xr.2]

/-- Finite-coin output-variable obligation for a randomized recoding whose
`y`-fiber uniformly selects the `false` source side for every coin. -/
theorem conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    conditionedSourceFiberProduct (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ := by
  refine
    conditionedSourceFiberProduct_le_of_CountIndependentWithinTolerance_anticoupled
      (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2 = y) τ ?_ (happrox y)
  intro xr _hC
  by_cases hE : E xr.1
  · have hnotF : ¬ r (decide (E xr.1)) xr.2 = y := by
      simpa [hE] using htrue xr.2
    exact iff_of_true hE hnotF
  · have hF : r (decide (E xr.1)) xr.2 = y := by
      simpa [hE] using hfalse xr.2
    exact iff_of_false hE (not_not.mpr hF)

/-- Lower-bound transfer for a finite-coin randomized recoding with a uniform
true-side distinguishing output fiber. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct
      (Ω := Ω × Coin) (fun xr => C xr.1) (fun xr => E xr.1)
      loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ htrueFiber hfalseFiber happrox)

/-- Lower-bound transfer for a finite-coin randomized recoding with a uniform
false-side distinguishing output fiber. -/
theorem lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    loTrue * loFalse ≤ τ := by
  exact le_trans
    (lowerBounds_mul_le_conditionedSourceFiberProduct
      (Ω := Ω × Coin) (fun xr => C xr.1) (fun xr => E xr.1)
      loTrue loFalse htrue hfalse)
    (conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ htrueFiber hfalseFiber happrox)

/-- Product-defect blocker for a finite-coin randomized recoding with a
uniform true-side distinguishing output fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_product_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (htol :
      τ <
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) *
          finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  have hle :
      conditionedSourceFiberProduct (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ :=
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ htrue hfalse happrox
  exact (Nat.not_le_of_gt htol) (by
    simpa [conditionedSourceFiberProduct] using hle)

/-- Product-defect blocker for a finite-coin randomized recoding with a
uniform false-side distinguishing output fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_product_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (htol :
      τ <
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) *
          finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  have hle :
      conditionedSourceFiberProduct (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1) ≤ τ :=
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ htrue hfalse happrox
  exact (Nat.not_le_of_gt htol) (by
    simpa [conditionedSourceFiberProduct] using hle)

/-- Lower-bound contradiction for a finite-coin randomized recoding with a
uniform true-side distinguishing output fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_lowerBounds_mul_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox)

/-- Lower-bound contradiction for a finite-coin randomized recoding with a
uniform false-side distinguishing output fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_lowerBounds_mul_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ E xr.1))
    (hfalse : loFalse ≤ finiteEventCount (Ω × Coin)
      (fun xr => C xr.1 ∧ ¬ E xr.1))
    (htol : τ < loTrue * loFalse) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox)

end Mettapedia.Computability.PNP
