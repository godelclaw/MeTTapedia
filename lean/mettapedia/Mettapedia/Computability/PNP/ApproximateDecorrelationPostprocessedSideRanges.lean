import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSidePredicates

/-!
# PNP approximate decorrelation: postprocessed-side layer
-/

namespace Mettapedia.Computability.PNP

/-- Disjoint true-side and false-side observed supports after retained-side
postprocessing are incompatible with below-threshold approximate output
independence.  Hashing or otherwise postprocessing the retained pair must
create source-side support collisions, not merely hide the original syntax. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_sourceRangesSeparated_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [Nonempty Coin]
    [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hsep :
      ∀ cTrue cFalse : Coin,
        post (r true cTrue, side cTrue) ≠ post (r false cFalse, side cFalse)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  classical
  exact
    not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_separates_sourceLowerBounds_lt_coinProduct
      C E r side post
      (fun z => ∃ cTrue : Coin, post (r true cTrue, side cTrue) = z)
      htrue hfalse hlt
      (fun c => ⟨c, rfl⟩)
      (fun cFalse h => by
        rcases h with ⟨cTrue, hEq⟩
        exact hsep cTrue cFalse hEq)

end Mettapedia.Computability.PNP
