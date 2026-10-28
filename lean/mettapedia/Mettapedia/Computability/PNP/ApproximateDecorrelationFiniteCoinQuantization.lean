import Mettapedia.Computability.PNP.ApproximateDecorrelationFiniteCoinImbalance

/-!
# Finite-coin source-product quantization boundaries
-/

namespace Mettapedia.Computability.PNP

/-- If the tolerance is below one lower-bounded source/coin imbalance block,
then approximate output independence for a finite-coin recoding forces exact
balanced output fibers.  A nonzero true/false coin-fiber imbalance contributes
at least `loTrue * loFalse * |Coin|` defect. -/
theorem finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ)
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  intro y
  by_contra hneq
  rcases lt_or_gt_of_ne hneq with htrue_lt_false | hfalse_lt_true
  · have hdiff_pos : 0 < coinFalseFiberCount r y - coinTrueFiberCount r y :=
      Nat.sub_pos_of_lt htrue_lt_false
    have hdiff_one : 1 ≤ coinFalseFiberCount r y - coinTrueFiberCount r y := hdiff_pos
    have hblock_le :
        loTrue * loFalse * Fintype.card Coin ≤
          loTrue * loFalse * Fintype.card Coin *
            (coinFalseFiberCount r y - coinTrueFiberCount r y) := by
      calc
        loTrue * loFalse * Fintype.card Coin =
            loTrue * loFalse * Fintype.card Coin * 1 := by simp
        _ ≤
            loTrue * loFalse * Fintype.card Coin *
              (coinFalseFiberCount r y - coinTrueFiberCount r y) :=
          Nat.mul_le_mul_left (loTrue * loFalse * Fintype.card Coin) hdiff_one
    exact (Nat.not_le_of_gt hlt)
      (le_trans hblock_le
        (sourceLowerBounds_falseMinusTrueCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
          C E r y τ loTrue loFalse htrue hfalse happrox))
  · have hdiff_pos : 0 < coinTrueFiberCount r y - coinFalseFiberCount r y :=
      Nat.sub_pos_of_lt hfalse_lt_true
    have hdiff_one : 1 ≤ coinTrueFiberCount r y - coinFalseFiberCount r y := hdiff_pos
    have hblock_le :
        loTrue * loFalse * Fintype.card Coin ≤
          loTrue * loFalse * Fintype.card Coin *
            (coinTrueFiberCount r y - coinFalseFiberCount r y) := by
      calc
        loTrue * loFalse * Fintype.card Coin =
            loTrue * loFalse * Fintype.card Coin * 1 := by simp
        _ ≤
            loTrue * loFalse * Fintype.card Coin *
              (coinTrueFiberCount r y - coinFalseFiberCount r y) :=
          Nat.mul_le_mul_left (loTrue * loFalse * Fintype.card Coin) hdiff_one
    exact (Nat.not_le_of_gt hlt)
      (le_trans hblock_le
        (sourceLowerBounds_trueMinusFalseCoinFiberProduct_le_of_CountIndependentWithinToleranceOutput_finiteCoinRecoding
          C E r y τ loTrue loFalse htrue hfalse happrox))

/-- Below one lower-bounded source/coin imbalance block, approximate output
independence is equivalent to exact balanced fibers. -/
theorem countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  constructor
  · intro happrox
    exact
      finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
        C E r htrue hfalse happrox hlt
  · intro hbal y
    have hzero :=
      countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_fiberBalanced
        C E r hbal
    exact ⟨le_trans (hzero y).1 (Nat.zero_le τ),
      le_trans (hzero y).2 (Nat.zero_le τ)⟩

/-- Exact source-count form of finite-coin tolerance quantization: below the
first source-product times coin-count block, approximate output independence
forces exact balanced fibers. -/
theorem finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_lt_sourceCoinProduct
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ : Nat}
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ)
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    FiniteCoinRecodingFiberBalanced r := by
  exact
    finiteCoinRecodingFiberBalanced_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r le_rfl le_rfl happrox hlt

/-- Below the exact source-product times coin-count block, approximate output
independence is equivalent to exact balanced fibers. -/
theorem countIndependentWithinToleranceOutput_lt_sourceCoinProduct_iff_finiteCoinRecoding_fiberBalanced
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ : Nat}
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ ↔
    FiniteCoinRecodingFiberBalanced r := by
  exact
    countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
      C E r le_rfl le_rfl hlt

/-- Source-side nondegeneracy blocks zero-tolerance output independence for
any finite-coin output fiber with positive true-minus-false imbalance. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_trueMinusFalse_sourceNonconstant
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (himb : coinFalseFiberCount r y < coinTrueFiberCount r y) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  apply
    not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_sourceLowerBounds_trueMinusFalse_gt
      C E r y 0 1 1 hpos hneg
  have hcoin : 0 < Fintype.card Coin := Fintype.card_pos
  have hdiff : 0 < coinTrueFiberCount r y - coinFalseFiberCount r y :=
    Nat.sub_pos_of_lt himb
  simpa using Nat.mul_pos (Nat.mul_pos (Nat.mul_pos Nat.one_pos Nat.one_pos) hcoin) hdiff

/-- Source-side nondegeneracy blocks zero-tolerance output independence for
any finite-coin output fiber with positive false-minus-true imbalance. -/
theorem not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_falseMinusTrue_sourceNonconstant
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (himb : coinTrueFiberCount r y < coinFalseFiberCount r y) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 := by
  apply
    not_countIndependentWithinToleranceOutput_of_finiteCoinRecoding_sourceLowerBounds_falseMinusTrue_gt
      C E r y 0 1 1 hpos hneg
  have hcoin : 0 < Fintype.card Coin := Fintype.card_pos
  have hdiff : 0 < coinFalseFiberCount r y - coinTrueFiberCount r y :=
    Nat.sub_pos_of_lt himb
  simpa using Nat.mul_pos (Nat.mul_pos (Nat.mul_pos Nat.one_pos Nat.one_pos) hcoin) hdiff

/-- On a source-side nondegenerate conditioned surface, exact zero-tolerance
finite-coin output independence is equivalent to balanced output fibers.  This
is the arbitrary finite-coin cancellation boundary: zero slack is possible
exactly when every output fiber has equal true-side and false-side coin counts. -/
theorem countIndependentWithinToleranceOutput_zero_iff_finiteCoinRecoding_fiberBalanced_of_sourceNonconstant
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 ↔
    FiniteCoinRecodingFiberBalanced r := by
  constructor
  · intro happrox y
    by_contra hneq
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact
        (not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_falseMinusTrue_sourceNonconstant
          C E r y hpos hneg hlt) happrox
    · exact
        (not_countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_trueMinusFalse_sourceNonconstant
          C E r y hpos hneg hgt) happrox
  · intro hbal
    exact countIndependentWithinToleranceOutput_zero_of_finiteCoinRecoding_fiberBalanced
      C E r hbal

end Mettapedia.Computability.PNP
