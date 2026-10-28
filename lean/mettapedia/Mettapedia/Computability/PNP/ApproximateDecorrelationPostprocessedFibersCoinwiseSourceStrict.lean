import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedFibersCoinwiseProduct

/-!
# Finite-coin postprocessed fiber product bounds
-/

namespace Mettapedia.Computability.PNP

/-- Source-count strict-tolerance blocker for a finite-coin true-side fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_sourceProduct_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (htol :
      τ <
        (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
          (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  apply
    not_countIndependentWithinToleranceOutput_of_coinwise_trueFiber_product_gt
      C E r y τ htrue hfalse
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
  simpa [hCE, hCnotE] using htol

/-- Source-count strict-tolerance blocker for a finite-coin false-side fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_sourceProduct_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α) (τ : Nat)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (htol :
      τ <
        (finiteEventCount Ω (fun ω => C ω ∧ E ω) * Fintype.card Coin) *
          (finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) * Fintype.card Coin)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ := by
  apply
    not_countIndependentWithinToleranceOutput_of_coinwise_falseFiber_product_gt
      C E r y τ htrue hfalse
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
  simpa [hCE, hCnotE] using htol

end Mettapedia.Computability.PNP
