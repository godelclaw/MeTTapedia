import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCore
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedLeftInverse
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactObservedInjective
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactTolerance
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationExactCollision
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationBias
import Mettapedia.Computability.PNP.FiniteCoinPostprocessingFoundationTolerance

/-!
# PNP finite-coin postprocessing anchors: matching obstructions

Counterexamples and obstruction anchors showing when pointwise or predicate information is weaker than a preserving coin matching.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: two-sided pointwise support collisions are strictly
weaker than a preserving postprocessed-side coin equivalence.  The three-coin
audit instance has support overlap in both directions but no bijective
observation-preserving matching. -/
theorem finiteCoinCoverage_anchor_postprocessedSidePointwiseCollisionInsufficient :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      ((∀ cTrue : Fin 3,
          ∃ cFalse : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse)) ∧
        (∀ cFalse : Fin 3,
          ∃ cTrue : Fin 3,
            post (r true cTrue, side cTrue) =
              post (r false cFalse, side cFalse))) ∧
        ¬ ∃ e : Fin 3 ≃ Fin 3,
          ∀ c : Fin 3,
            post (r true c, side c) = post (r false (e c), side (e c)) :=
  postprocessedSide_pointwise_collisions_do_not_imply_coinEquiv_preserving

/-- Route-coverage anchor: one-sided true-to-false witness maps are still
weaker than a preserving postprocessed-side coin equivalence.  In the
three-coin audit instance, such maps exist, but every preserving one-sided map
is non-injective and therefore cannot be promoted to a bijective matching. -/
theorem finiteCoinCoverage_anchor_postprocessedSideOneSidedCoinMapInsufficient :
    ∃ r : Bool → Fin 3 → Bool,
    ∃ side : Fin 3 → Unit,
    ∃ post : Bool × Unit → Bool,
      (∃ f : Fin 3 → Fin 3,
        ∀ c : Fin 3,
          post (r true c, side c) = post (r false (f c), side (f c))) ∧
        (∀ f : Fin 3 → Fin 3,
          (∀ c : Fin 3,
            post (r true c, side c) = post (r false (f c), side (f c))) →
            ¬ Function.Injective f) ∧
          ¬ ∃ e : Fin 3 ≃ Fin 3,
            ∀ c : Fin 3,
              post (r true c, side c) = post (r false (e c), side (e c)) :=
  postprocessedSide_oneSided_coinMap_preserving_does_not_imply_coinEquiv_preserving

/-- Route-coverage anchor: the injective one-sided witness-map repair is not a
new intermediate target.  For finite coins it is equivalent to the preserving
postprocessed-side coin equivalence, and with decidable observed outputs it is
therefore the same observed-fiber multiplicity-balance obligation. -/
theorem finiteCoinCoverage_anchor_postprocessedSideInjectiveWitnessMapEquivalence
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    ((∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) ∧
      ((∃ f : Coin → Coin,
        (∀ c : Coin,
          post (r true c, side c) = post (r false (f c), side (f c))) ∧
          Function.Injective f) ↔
        ∀ z : β,
          finiteEventCount Coin (fun c => post (r true c, side c) = z) =
            finiteEventCount Coin (fun c => post (r false c, side c) = z)) := by
  exact
    ⟨exists_injective_postprocessedSide_coinMap_preserving_iff_exists_coinEquiv_preserving
      r side post,
    exists_injective_postprocessedSide_coinMap_preserving_iff_observedFiber_count_eq
      r side post⟩

/-- Route-coverage anchor: below one lower-bounded source/coin block,
deterministic retained-side postprocessing must provide a bijective matching of
true-side and false-side coin choices preserving every observed value if
approximate output independence is to hold. -/
theorem finiteCoinCoverage_anchor_postprocessedSideCoinMatchingObligation
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
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) :=
  exists_postprocessedSide_coinEquiv_preserving_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
    C E r side post htrue hfalse hlt happrox

/-- Route-coverage anchor: a single observed postprocessed value with unequal
true-side and false-side coin-fiber multiplicities blocks the coin-matching
repair, hence also blocks below-threshold approximate independence for
deterministic retained-side postprocessing. -/
theorem finiteCoinCoverage_anchor_postprocessedSideCoinMatchingCardinalityBlock
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ :=
  not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_count_ne_sourceLowerBounds_lt_coinProduct
    C E r side post z htrue hfalse hlt hne

/-- Route-coverage anchor: a downstream predicate with unequal true-side and
false-side coin counts blocks the postprocessed-side coin-matching repair,
hence also blocks below-threshold approximate independence for deterministic
retained-side postprocessing.  Decoder-only probes are a special case of this
predicate obstruction. -/
theorem finiteCoinCoverage_anchor_postprocessedSideCoinMatchingPredicateBlock
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P] {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) ≠
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ :=
  not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_count_ne_sourceLowerBounds_lt_coinProduct
    C E r side post P htrue hfalse hlt hne

/-- Route-coverage anchor: all downstream decidable predicates are neutral
exactly when the postprocessed retained-side observations support a preserving
true/false coin equivalence.  Predicate-only certificates therefore do not
avoid the full observed-fiber matching obligation. -/
theorem finiteCoinCoverage_anchor_postprocessedSidePredicateMatchingEquivalence
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) ↔
      ∀ P : β → Prop, [DecidablePred P] →
        finiteEventCount Coin (fun c => P (post (r true c, side c))) =
          finiteEventCount Coin (fun c => P (post (r false c, side c))) :=
  exists_postprocessedSide_coinEquiv_preserving_iff_outputPredicate_count_eq
    r side post

end Mettapedia.Computability.PNP
