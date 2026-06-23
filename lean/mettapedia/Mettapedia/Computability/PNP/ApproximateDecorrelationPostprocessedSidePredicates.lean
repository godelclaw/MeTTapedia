import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideBalance

/-!
# PNP approximate decorrelation: postprocessed-side layer
-/

namespace Mettapedia.Computability.PNP

/-- Below one lower-bounded source/coin block, approximate independence of a
postprocessed retained-side output erases every decidable downstream property:
the property has exactly the same true-side and false-side coin counts.  This
is the predicate-level form between observed-fiber balance and Boolean decoder
half-accuracy. -/
theorem postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Coin (fun c => P (post (r true c, side c))) =
      finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  have hbal : FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) :=
    (countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
      C E (fun b c => post (r b c, side c)) htrue hfalse hlt).1 happrox
  simpa using
    finiteCoinRecodingFiberBalanced_outputPredicate_count_eq
      (fun b c => post (r b c, side c)) P hbal

/-- Strict downstream-predicate blocker for a postprocessed retained-side
output: below one lower-bounded source/coin block, any predicate with a
true-side count advantage refutes approximate output independence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_trueCount_gt_falseCount_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      finiteEventCount Coin (fun c => P (post (r false c, side c))) <
        finiteEventCount Coin (fun c => P (post (r true c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.ne_of_gt hgt)
    (postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt happrox)

/-- Strict downstream-predicate blocker for a postprocessed retained-side
output: below one lower-bounded source/coin block, any predicate with a
false-side count advantage refutes approximate output independence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_falseCount_gt_trueCount_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hgt :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) <
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.ne_of_gt hgt)
    (postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt happrox).symm

/-- Strict downstream-predicate separation blocker for a postprocessed
retained-side output: below one lower-bounded source/coin block, a predicate
that contains every true-side observation and no false-side observation refutes
approximate output independence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_separates_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (htruePred : ∀ c : Coin, P (post (r true c, side c)))
    (hfalsePred : ∀ c : Coin, ¬ P (post (r false c, side c))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  have hfalseZero :
      finiteEventCount Coin (fun c => P (post (r false c, side c))) = 0 := by
    exact finiteEventCount_zero_of_forall_not
      (fun c => P (post (r false c, side c)))
      (fun c hc => hfalsePred c hc)
  obtain ⟨c₀⟩ := ‹Nonempty Coin›
  have htruePos :
      0 < finiteEventCount Coin (fun c => P (post (r true c, side c))) := by
    unfold finiteEventCount
    exact Fintype.card_pos_iff.mpr ⟨⟨c₀, htruePred c₀⟩⟩
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_trueCount_gt_falseCount_sourceLowerBounds_lt_coinProduct
      C E r side post P htrue hfalse hlt (by simpa [hfalseZero] using htruePos)


end Mettapedia.Computability.PNP
