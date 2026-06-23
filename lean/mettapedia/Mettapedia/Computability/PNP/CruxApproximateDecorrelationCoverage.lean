import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedLeftInverse
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactTolerance
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCollision
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationBias
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationTolerance
import Mettapedia.Computability.PNP.CruxRandomizedResidualPromotedPacket

/-!
# PNP approximate-decorrelation coverage ledger

This file contains the coverage package and promoted packet for the broad
approximate-decorrelation repair class.  It builds on the randomized-residual
packet and promotes approximate decorrelation to a theorem-backed coverage
surface, leaving only the manuscript-specific `Kpoly` bridge open.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- The broad approximate-decorrelation repair class is covered in the precise
theorem-backed sense that below the natural source/coin threshold,
approximate independence of a postprocessed retained-side observation is
already equivalent to an exact preserving coin equivalence, while the concrete
three-coin skew witness shows that two-sided support collisions and even a
one-sided preserving map still fail below the tolerance threshold `3`. -/
def ApproximateDecorrelationCoverage : Prop :=
  (∀ {Ω Coin α Side β : Type} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ : Nat},
      τ <
          finiteEventCount Ω (fun ω => C ω ∧ E ω) *
            finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
              Fintype.card Coin →
        (CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
            (fun xr => C xr.1) (fun xr => E xr.1)
            (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
          ∃ e : Coin ≃ Coin,
            ∀ c : Coin,
              post (r true c, side c) =
                post (r false (e c), side (e c)))) ∧
  (∀ {τ : Nat}, τ < 3 →
      ((∀ cTrue : Fin 3,
          ∃ cFalse : Fin 3,
            postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
              postprocessedSidePointwiseCollisionSkewRecoding false cFalse) ∧
        (∀ cFalse : Fin 3,
          ∃ cTrue : Fin 3,
            postprocessedSidePointwiseCollisionSkewRecoding true cTrue =
              postprocessedSidePointwiseCollisionSkewRecoding false cFalse)) ∧
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          postprocessedSidePointwiseCollisionSkewRecoding true c =
            postprocessedSidePointwiseCollisionSkewRecoding false (f c)) ∧
      ¬ CountIndependentWithinToleranceOutput (Ω := Bool × Fin 3)
          (fun _xr => True)
          (fun xr => xr.1 = true)
          (fun xr =>
            postprocessedSidePointwiseCollisionSkewRecoding xr.1 xr.2) τ)

@[simp] theorem approximateDecorrelationCoverage :
    ApproximateDecorrelationCoverage := by
  refine ⟨?_, ?_⟩
  · intro Ω Coin α Side β _ _ _ C E _ _ r side post τ hlt
    exact
      countIndependentWithinToleranceOutput_postprocessedSide_lt_sourceCoinProduct_iff_coinEquiv_preserving
        C E r side post hlt
  · intro τ htol
    exact
      postprocessedSidePointwiseCollisionSkew_collision_and_oneSidedMap_counterexample_of_lt_three
        htol


end Mettapedia.Computability.PNP
