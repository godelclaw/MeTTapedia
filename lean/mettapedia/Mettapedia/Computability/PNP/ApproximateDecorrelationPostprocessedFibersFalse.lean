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
# Postprocessed false-side fiber obstructions
-/

namespace Mettapedia.Computability.PNP

/-- If a postprocessed retained side-channel observation separates a selected
false-side value from every true-side value, then the true-side observed fiber
is empty. -/
theorem coinTrueFiberCount_postprocessedSide_falseFiber_eq_zero_of_forall_ne
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀)) :
    coinTrueFiberCount (fun b c => post (r b c, side c))
        (post (r false c₀, side c₀)) = 0 := by
  unfold coinTrueFiberCount
  exact finiteEventCount_zero_of_forall_not
    (fun c => post (r true c, side c) = post (r false c₀, side c₀))
    (fun c h => hsep c h)

/-- Exact backward defect for a postprocessed retained side-channel observation
that isolates a selected false-side observed value from all true-side observed
values. -/
theorem countIndependentWithinBackwardGap_postprocessedSide_falseFiber
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) (c₀ : Coin)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀)) :
    countIndependentWithinBackwardGap (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2) =
          post (r false c₀, side c₀)) =
      finiteEventCount Ω (fun ω => C ω ∧ E ω) *
        finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
          Fintype.card Coin *
            finiteEventCount Coin
              (fun c => post (r false c, side c) = post (r false c₀, side c₀)) := by
  have hgap :=
    countIndependentWithinBackwardGap_finiteCoinRecoding_fiber
      C E (fun b c => post (r b c, side c)) (post (r false c₀, side c₀))
  have htrue := coinTrueFiberCount_postprocessedSide_falseFiber_eq_zero_of_forall_ne
    r side post c₀ hsep
  simpa [coinFalseFiberCount, htrue, Nat.mul_assoc] using hgap

/-- Approximate independence of a postprocessed retained side-channel output
forces the tolerance to dominate the selected false-side observed-fiber
defect. -/
theorem postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_falseFiber
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    finiteEventCount Ω (fun ω => C ω ∧ E ω) *
      finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
        Fintype.card Coin *
          finiteEventCount Coin
            (fun c => post (r false c, side c) = post (r false c₀, side c₀)) ≤ τ := by
  have hgap := countIndependentWithinBackwardGap_postprocessedSide_falseFiber
    C E r side post c₀ hsep
  have hcert :
      countIndependentWithinBackwardGap (Ω := Ω × Coin)
          (fun xr => C xr.1) (fun xr => E xr.1)
          (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2) =
            post (r false c₀, side c₀)) ≤ τ :=
    (happrox (post (r false c₀, side c₀))).2
  rw [hgap] at hcert
  exact hcert

/-- Source and observed-fiber lower-bound form of the postprocessed retained
side-channel false-side obstruction. -/
theorem sourcePostprocessedSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_falseFiber
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r false c, side c) = post (r false c₀, side c₀)))
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    loTrue * loFalse * Fintype.card Coin * loObs ≤ τ := by
  exact le_trans
    (Nat.mul_le_mul
      (Nat.mul_le_mul_right (Fintype.card Coin) (Nat.mul_le_mul htrue hfalse))
      hobs)
    (postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_falseFiber
      C E r side post c₀ τ hsep happrox)

/-- Strict-tolerance blocker for a postprocessed retained side-channel
false-side observed fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_falseFiber_product_gt
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htol :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin *
              finiteEventCount Coin
                (fun c => post (r false c, side c) = post (r false c₀, side c₀))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (postprocessedSideProduct_le_of_CountIndependentWithinToleranceOutput_falseFiber
      C E r side post c₀ τ hsep happrox)

/-- Source/observed-fiber lower-bound strict-tolerance blocker for a
postprocessed retained side-channel false-side observed fiber. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_falseFiber_sourceLowerBounds_mul_gt
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (c₀ : Coin) (τ loTrue loFalse loObs : Nat)
    (hsep :
      ∀ c : Coin, post (r true c, side c) ≠ post (r false c₀, side c₀))
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hobs : loObs ≤ finiteEventCount Coin
      (fun c => post (r false c, side c) = post (r false c₀, side c₀)))
    (htol : τ < loTrue * loFalse * Fintype.card Coin * loObs) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact (Nat.not_le_of_gt htol)
    (sourcePostprocessedSideLowerBounds_product_le_of_CountIndependentWithinToleranceOutput_falseFiber
      C E r side post c₀ τ loTrue loFalse loObs hsep htrue hfalse hobs happrox)

end Mettapedia.Computability.PNP
