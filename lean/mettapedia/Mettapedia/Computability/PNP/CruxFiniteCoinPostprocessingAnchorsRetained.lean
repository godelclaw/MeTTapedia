import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedLeftInverse
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactTolerance
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCollision
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationBias
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationTolerance

/-!
# PNP finite-coin postprocessing anchors: retained coin and side surfaces

Exact matching, zero-tolerance, lower-bound quantization, and retained-coin/retained-side collapse anchors.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: below one lower-bounded source/coin block,
postprocessed retained-side approximate independence is exactly the existence
of a preserving true/false coin equivalence.  A repair cannot certify the
independence condition while leaving the finite matching obligation unsolved. -/
theorem finiteCoinCoverage_anchor_postprocessedSideApproxIndependenceCoinMatchingEquivalence
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
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) :=
  countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_coinEquiv_preserving
    C E r side post htrue hfalse hlt

/-- Route-coverage anchor: source-side nondegeneracy rules out zero-tolerance
approximate output independence for a nonempty finite-coin recoding with a
uniform true-side distinguishing fiber. -/
theorem finiteCoinCoverage_anchor_coinwiseTrueFiber_sourceNonconstant_zeroBlock
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c = y)
    (hfalse : ∀ c : Coin, r false c ≠ y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 :=
  not_countIndependentWithinToleranceOutput_zero_of_coinwise_trueFiber_sourceNonconstant
    C E r y htrue hfalse hpos hneg

/-- Route-coverage anchor: source-side nondegeneracy rules out zero-tolerance
approximate output independence for a nonempty finite-coin recoding with a
uniform false-side distinguishing fiber. -/
theorem finiteCoinCoverage_anchor_coinwiseFalseFiber_sourceNonconstant_zeroBlock
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (y : α)
    (htrue : ∀ c : Coin, r true c ≠ y)
    (hfalse : ∀ c : Coin, r false c = y)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 :=
  not_countIndependentWithinToleranceOutput_zero_of_coinwise_falseFiber_sourceNonconstant
    C E r y htrue hfalse hpos hneg

/-- Route-coverage anchor: on any source-side nondegenerate conditioned
surface, zero-tolerance finite-coin output independence is exactly balanced
true/false output fibers. -/
theorem finiteCoinCoverage_anchor_sourceNonconstantZeroIffBalanced
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α)
    (hpos : 0 < finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hneg : 0 < finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω)) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) 0 ↔
    FiniteCoinRecodingFiberBalanced r :=
  countIndependentWithinToleranceOutput_zero_iff_finiteCoinRecoding_fiberBalanced_of_sourceNonconstant
    C E r hpos hneg

/-- Route-coverage anchor: below one lower-bounded source/coin imbalance
block, finite-coin approximate output independence is already equivalent to
balanced true/false output fibers. -/
theorem finiteCoinCoverage_anchor_sourceLowerBoundToleranceQuantization
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => r (decide (E xr.1)) xr.2) τ ↔
    FiniteCoinRecodingFiberBalanced r :=
  countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct_iff_finiteCoinRecoding_fiberBalanced
    C E r htrue hfalse hlt

/-- Route-coverage anchor: if the random coin is retained in the certified
output, then below one lower-bounded source/coin block, approximate output
independence is equivalent to pointwise source-blindness at every coin. -/
theorem finiteCoinCoverage_anchor_retainedCoinTolerancePointwiseCollapse
    {Ω Coin α : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq Coin] [DecidableEq α]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, xr.2)) τ ↔
    ∀ c : Coin, r true c = r false c :=
  countIndependentWithinToleranceOutput_coinRetained_sourceLowerBounds_lt_coinProduct_iff_pointwise_eq
    C E r htrue hfalse hlt

/-- Route-coverage anchor: if side information is retained in the certified
output, then below one lower-bounded source/coin block, approximate output
independence is equivalent to exact true/false balance inside every retained
side/output fiber. -/
theorem finiteCoinCoverage_anchor_retainedSideToleranceSideFiberBalance
    {Ω Coin α Side : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq α]
    [DecidableEq Side]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
    ∀ (y : α) (s : Side),
      finiteEventCount Coin (fun c => r true c = y ∧ side c = s) =
        finiteEventCount Coin (fun c => r false c = y ∧ side c = s) :=
  countIndependentWithinToleranceOutput_sideRetained_sourceLowerBounds_lt_coinProduct_iff_sideFiber_count_eq
    C E r side htrue hfalse hlt

end Mettapedia.Computability.PNP
