import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinFibers
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinBalancedEvidence
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinImbalance
import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinQuantization

namespace Mettapedia.Computability.PNP

/-- If the random coin is retained together with the output, the true-side
fiber at a fixed coin has exactly one supporting coin value. -/
theorem coinTrueFiberCount_withCoin_trueFiber
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin) :
    coinTrueFiberCount (fun b c => (r b c, c)) (r true c₀, c₀) = 1 := by
  have hcongr :
      finiteEventCount Coin
          (fun c => (r true c, c) = (r true c₀, c₀)) =
        finiteEventCount Coin (fun c => c = c₀) := by
    exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
      constructor
      · intro h
        exact congrArg Prod.snd h
      · intro h
        cases h
        rfl)
  exact hcongr.trans (finiteEventCount_eq_self c₀)

/-- If the retained-coin outputs at a fixed coin differ between the true and
false source sides, the matching false-side retained-coin fiber is empty. -/
theorem coinFalseFiberCount_withCoin_trueFiber_eq_zero_of_ne
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) (c₀ : Coin)
    (hsep : r true c₀ ≠ r false c₀) :
    coinFalseFiberCount (fun b c => (r b c, c)) (r true c₀, c₀) = 0 := by
  unfold coinFalseFiberCount
  exact finiteEventCount_zero_of_forall_not
    (fun c => (r false c, c) = (r true c₀, c₀)) (fun c h => by
      have hc : c = c₀ := congrArg Prod.snd h
      subst c
      have hout : r false c₀ = r true c₀ := congrArg Prod.fst h
      exact hsep hout.symm)

/-- Exact forward defect for a retained-coin output fiber.  Balanced marginal
output fibers do not matter here: once the coin is retained, any coin at which
the true and false outputs differ exposes the source bit with the scaled
source-product defect. -/
theorem countIndependentWithinForwardGap_coinRetained_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin)
    (hsep : r true c₀ ≠ r false c₀) :
    countIndependentWithinForwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, xr.2) = (r true c₀, c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin := by
  have hgap :=
    countIndependentWithinForwardGap_finiteCoinRecoding_fiber
      C E (fun b c => (r b c, c)) (r true c₀, c₀)
  have htrue := coinTrueFiberCount_withCoin_trueFiber r c₀
  have hfalse := coinFalseFiberCount_withCoin_trueFiber_eq_zero_of_ne r c₀ hsep
  simpa [htrue, hfalse, Nat.mul_assoc] using hgap

/-- Approximate independence of the retained-coin output forces the tolerance
to dominate the source-product defect at any separated coin. -/
theorem sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin ≤ τ := by
  have hgap := countIndependentWithinForwardGap_coinRetained_trueFiber C E r c₀ hsep
  have hcert :
      countIndependentWithinForwardGap (Ω := Ω × Coin)
          (fun xr => C xr.1) (fun xr => E xr.1)
          (fun xr => (r (decide (E xr.1)) xr.2, xr.2) = (r true c₀, c₀)) ≤ τ :=
    (happrox (r true c₀, c₀)).1
  rw [hgap] at hcert
  exact hcert

/-- Source lower-bound form of the retained-coin preservation obstruction. -/
theorem sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ loTrue loFalse : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse))
    (sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
      C E r c₀ τ hsep happrox)

/-- Strict-tolerance blocker for retained-coin outputs: if the coin is kept,
any separated coin value preserves enough of the source bit to revive the
scaled finite-count obstruction. -/
theorem not_countIndependentWithinToleranceOutput_of_coinRetained_trueFiber_sourceProduct_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceCoinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
      C E r c₀ τ hsep happrox)

/-- Source lower-bound strict-tolerance blocker for retained-coin outputs. -/
theorem not_countIndependentWithinToleranceOutput_of_coinRetained_trueFiber_sourceLowerBounds_mul_gt
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (c₀ : Coin) (τ loTrue loFalse : Nat)
    (hsep : r true c₀ ≠ r false c₀)
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (htol : τ < loTrue * loFalse * Fintype.card Coin) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourceLowerBounds_coinProduct_le_of_CountIndependentWithinToleranceOutput_coinRetained_trueFiber
      C E r c₀ τ loTrue loFalse hsep htrue hfalse happrox)

/-- Retaining the coin turns balanced finite-coin fibers into pointwise
source-blindness at each coin.  Marginal balance can hide source information by
mixing over coins; once the coin itself is part of the certified output, exact
balance is possible only when the true and false outputs agree for every
retained coin value. -/
theorem finiteCoinRecodingFiberBalanced_coinRetained_iff_pointwise_eq
    {Coin α : Type*} [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (r : Bool → Coin → α) :
    FiniteCoinRecodingFiberBalanced (fun b c => (r b c, c)) ↔
      ∀ c : Coin, r true c = r false c := by
  constructor
  · intro hbal c₀
    by_contra hsep
    have htrue := coinTrueFiberCount_withCoin_trueFiber r c₀
    have hfalse := coinFalseFiberCount_withCoin_trueFiber_eq_zero_of_ne r c₀ hsep
    have hfiber := hbal (r true c₀, c₀)
    simp [htrue, hfalse] at hfiber
  · intro hpoint y
    unfold coinTrueFiberCount coinFalseFiberCount
    exact finiteEventCount_congr_approximate (Ω := Coin) (fun c => by
      have hpair : (r true c, c) = (r false c, c) :=
        Prod.ext (hpoint c) rfl
      constructor
      · intro h
        change (r false c, c) = y
        rw [← hpair]
        exact h
      · intro h
        change (r true c, c) = y
        rw [hpair]
        exact h)

/-- Source lower-bound retained-coin quantization: below one lower-bounded
source/coin block, approximate independence of the output that retains the
coin is equivalent to pointwise source-blindness at every retained coin. -/
theorem countIndependentWithinToleranceOutput_coinRetained_sourceLowerBounds_lt_coinProduct_iff_pointwise_eq
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ ↔
    ∀ c : Coin, r true c = r false c := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ
        ↔ FiniteCoinRecodingFiberBalanced (fun b c => (r b c, c)) :=
          countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
            C E (fun b c => (r b c, c)) htrue hfalse hlt
    _ ↔ ∀ c : Coin, r true c = r false c :=
          finiteCoinRecodingFiberBalanced_coinRetained_iff_pointwise_eq r

/-- Exact source-count specialization of retained-coin quantization. -/
theorem countIndependentWithinToleranceOutput_coinRetained_lt_sourceCoinProduct_iff_pointwise_eq
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ : Nat}
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ ↔
    ∀ c : Coin, r true c = r false c := by
  exact
    countIndependentWithinToleranceOutput_coinRetained_sourceLowerBounds_lt_coinProduct_iff_pointwise_eq
      C E r le_rfl le_rfl hlt

end Mettapedia.Computability.PNP
