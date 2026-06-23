import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideBalance
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideImbalance
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSidePredicates
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideDecoders
import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideRanges

/-!
# PNP approximate decorrelation: postprocessed-side layer

This module contains the postprocessed-side collision witnesses and pointwise collision packages.
-/

namespace Mettapedia.Computability.PNP

/-- Positive collision obligation for a postprocessed retained-side output:
below one lower-bounded source/coin block, approximate output independence
forces at least one true-side observed value and one false-side observed value
to collide after postprocessing.  A deterministic hash repair must therefore
create real observed support overlap, not merely conceal the retained pair. -/
theorem exists_postprocessedSide_true_false_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    ∃ cTrue cFalse : Coin,
      post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse) := by
  classical
  by_contra hnone
  have hsep :
      ∀ cTrue cFalse : Coin,
        post (r true cTrue, side cTrue) ≠ post (r false cFalse, side cFalse) := by
    intro cTrue cFalse hEq
    exact hnone ⟨cTrue, cFalse, hEq⟩
  exact
    (not_countIndependentWithinToleranceOutput_of_postprocessedSide_sourceRangesSeparated_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt hsep) happrox

/-- Pointwise true-side collision obligation for a postprocessed retained-side
output: below one lower-bounded source/coin block, every true-side coin's
observed postprocessed value must also be observed on the false side. -/
theorem exists_false_postprocessedSide_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ)
    (cTrue : Coin) :
    ∃ cFalse : Coin,
      post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse) := by
  classical
  have hcount :=
    postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post (fun z => z = post (r true cTrue, side cTrue))
      htrue hfalse hlt happrox
  have htruePos :
      0 <
        finiteEventCount Coin
          (fun c => post (r true c, side c) = post (r true cTrue, side cTrue)) := by
    unfold finiteEventCount
    exact Fintype.card_pos_iff.mpr ⟨⟨cTrue, rfl⟩⟩
  have hfalsePos :
      0 <
        finiteEventCount Coin
          (fun c => post (r false c, side c) = post (r true cTrue, side cTrue)) := by
    simpa [hcount] using htruePos
  unfold finiteEventCount at hfalsePos
  rcases Fintype.card_pos_iff.mp hfalsePos with ⟨cFalse⟩
  exact ⟨cFalse.1, cFalse.2.symm⟩

/-- Pointwise false-side collision obligation for a postprocessed retained-side
output: below one lower-bounded source/coin block, every false-side coin's
observed postprocessed value must also be observed on the true side. -/
theorem exists_true_postprocessedSide_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ)
    (cFalse : Coin) :
    ∃ cTrue : Coin,
      post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse) := by
  classical
  have hcount :=
    postprocessedSide_outputPredicate_count_eq_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post (fun z => z = post (r false cFalse, side cFalse))
      htrue hfalse hlt happrox
  have hfalsePos :
      0 <
        finiteEventCount Coin
          (fun c => post (r false c, side c) = post (r false cFalse, side cFalse)) := by
    unfold finiteEventCount
    exact Fintype.card_pos_iff.mpr ⟨⟨cFalse, rfl⟩⟩
  have htruePos :
      0 <
        finiteEventCount Coin
          (fun c => post (r true c, side c) = post (r false cFalse, side cFalse)) := by
    simpa [hcount] using hfalsePos
  unfold finiteEventCount at htruePos
  rcases Fintype.card_pos_iff.mp htruePos with ⟨cTrue⟩
  exact ⟨cTrue.1, cTrue.2⟩

/-- Symmetric pointwise collision obligation for a postprocessed retained-side
output: below one lower-bounded source/coin block, the true-side and false-side
observed supports coincide pointwise.  A repair must overlap every observed
coin value on both source sides, not merely produce a single collision. -/
theorem postprocessedSide_pointwise_true_false_collisions_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (happrox : CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ) :
    (∀ cTrue : Coin,
        ∃ cFalse : Coin,
          post (r true cTrue, side cTrue) = post (r false cFalse, side cFalse)) ∧
      (∀ cFalse : Coin,
        ∃ cTrue : Coin,
          post (r true cTrue, side cTrue) =
            post (r false cFalse, side cFalse)) := by
  exact
    ⟨fun cTrue =>
        exists_false_postprocessedSide_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
          C E r side post htrue hfalse hlt happrox cTrue,
      fun cFalse =>
        exists_true_postprocessedSide_collision_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
          C E r side post htrue hfalse hlt happrox cFalse⟩

end Mettapedia.Computability.PNP
