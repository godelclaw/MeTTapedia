import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseProduct

/-!
# Finite-coin postprocessed fiber product bounds
-/

namespace Mettapedia.Computability.PNP

/-- Source-count form of the finite-coin true-fiber obligation.  The product
space lower bound factors into the source-side product scaled by the number of
coins on both sides. -/
theorem sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
      (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin) ≤ τ := by
  have hprod :=
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ htrue hfalse happrox
  have hCE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω)
  have hCnotE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ ¬ E ω)
  simpa [conditionedSourceFiberProduct, hCE, hCnotE] using hprod

/-- Source-count form of the finite-coin false-fiber obligation. -/
theorem sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
      (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin) ≤ τ := by
  have hprod :=
    conditionedSourceFiberProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ htrue hfalse happrox
  have hCE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ E ω)
  have hCnotE :
      finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) =
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin := by
    simpa using
      finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
        (fun ω => C ω ∧ ¬ E ω)
  simpa [conditionedSourceFiberProduct, hCE, hCnotE] using hprod

/-- Source-count lower-bound transfer for the finite-coin true-fiber case. -/
theorem sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin) ≤ τ := by
  have htrueLift :
      loTrue * Fintype.card Coin ≤
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) := by
    have hCE :
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) =
          finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin := by
      simpa using
        finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
          (fun ω => C ω ∧ E ω)
    exact le_trans (Nat.mul_le_mul_right (Fintype.card Coin) htrue) (le_of_eq hCE.symm)
  have hfalseLift :
      loFalse * Fintype.card Coin ≤
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) := by
    have hCnotE :
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) =
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin := by
      simpa using
        finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
          (fun ω => C ω ∧ ¬ E ω)
    exact le_trans (Nat.mul_le_mul_right (Fintype.card Coin) hfalse) (le_of_eq hCnotE.symm)
  exact
    lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ (loTrue * Fintype.card Coin) (loFalse * Fintype.card Coin)
      htrueFiber hfalseFiber htrueLift hfalseLift happrox

/-- Source-count lower-bound transfer for the finite-coin false-fiber case. -/
theorem sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ) :
    (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin) ≤ τ := by
  have htrueLift :
      loTrue * Fintype.card Coin ≤
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) := by
    have hCE :
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ E xr.1) =
          finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin := by
      simpa using
        finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
          (fun ω => C ω ∧ E ω)
    exact le_trans (Nat.mul_le_mul_right (Fintype.card Coin) htrue) (le_of_eq hCE.symm)
  have hfalseLift :
      loFalse * Fintype.card Coin ≤
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) := by
    have hCnotE :
        finiteEventCount (Ω × Coin) (fun xr => C xr.1 ∧ ¬ E xr.1) =
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin := by
      simpa using
        finiteEventCount_fst_lift (Ω := Ω) (Coin := Coin)
          (fun ω => C ω ∧ ¬ E ω)
    exact le_trans (Nat.mul_le_mul_right (Fintype.card Coin) hfalse) (le_of_eq hCnotE.symm)
  exact
    lowerBounds_mul_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ (loTrue * Fintype.card Coin) (loFalse * Fintype.card Coin)
      htrueFiber hfalseFiber htrueLift hfalseLift happrox

/-- Source-count lower-bound contradiction for a finite-coin true-side fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_sourceLowerBounds_mul_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c = y)
    (hfalseFiber : ∀ c : Coin, r false c ≠ y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_trueFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox)

/-- Source-count lower-bound contradiction for a finite-coin false-side fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_sourceLowerBounds_mul_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ loTrue loFalse : Nat)
    (htrueFiber : ∀ c : Coin, r true c ≠ y)
    (hfalseFiber : ∀ c : Coin, r false c = y)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < (loTrue * Fintype.card Coin) * (loFalse * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinwise_falseFiber
      C E r y τ loTrue loFalse htrueFiber hfalseFiber htrue hfalse happrox)

end Mettapedia.Computability.PNP
