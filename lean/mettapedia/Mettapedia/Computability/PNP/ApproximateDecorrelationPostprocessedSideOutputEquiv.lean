import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideSkewThresholds

/-!
# PNP approximate decorrelation: postprocessed-side layer

This module contains the output-predicate/output-decoder equivalences and final tolerance criteria.
-/

namespace Mettapedia.Computability.PNP

/-- Any preserving postprocessed-side coin matching erases every downstream
decidable predicate at the level of true/false coin counts.  This packages the
observed-fiber cardinality obligation for repairs that only expose a Boolean
test of the postprocessed observation. -/
theorem postprocessedSide_outputPredicate_count_eq_of_coinEquiv_preserving
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P]
    (e : Coin ≃ Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) :
    finiteEventCount Coin (fun c => P (post (r true c, side c))) =
      finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  have hcount :=
    postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving
      r side post e hpres
  have hbal : FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) :=
    (finiteCoinRecodingFiberBalanced_postprocessedSide_iff_observedFiber_count_eq
      r side post).2 hcount
  simpa using
    finiteCoinRecodingFiberBalanced_outputPredicate_count_eq
      (fun b c => post (r b c, side c)) P hbal

/-- A single downstream predicate with unequal true-side and false-side coin
counts rules out every preserving postprocessed-side coin equivalence. -/
theorem not_exists_postprocessedSide_coinEquiv_preserving_of_outputPredicate_count_ne
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (P : β → Prop) [DecidablePred P]
    (hne :
      finiteEventCount Coin (fun c => P (post (r true c, side c))) ≠
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) :
    ¬ ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  rintro ⟨e, hpres⟩
  exact hne
    (postprocessedSide_outputPredicate_count_eq_of_coinEquiv_preserving
      r side post P e hpres)

/-- Predicate-level coin-matching blocker for postprocessed retained-side
outputs: below one lower-bounded source/coin block, unequal downstream
predicate counts refute approximate output independence by ruling out the
required preserving coin equivalence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputPredicate_count_ne_sourceLowerBounds_lt_coinProduct
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
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_no_postprocessedSide_coinEquiv_preserving_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt
      (not_exists_postprocessedSide_coinEquiv_preserving_of_outputPredicate_count_ne
        r side post P hne)

/-- Any preserving postprocessed-side coin matching makes every downstream
Boolean decoder exactly half-accurate in aggregate across the two source
sides. -/
theorem postprocessedSide_outputDecoder_correctCount_eq_card_of_coinEquiv_preserving
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool)
    (e : Coin ≃ Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) :
    finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
      finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) =
        Fintype.card Coin := by
  have hpred :=
    postprocessedSide_outputPredicate_count_eq_of_coinEquiv_preserving
      r side post (fun z => decode z = true) e hpres
  rw [hpred]
  exact finiteEventCount_bool_true_add_false
    (fun c => decode (post (r false c, side c)))

/-- A downstream decoder whose aggregate correctness is not exactly half
rules out every preserving postprocessed-side coin equivalence. -/
theorem not_exists_postprocessedSide_coinEquiv_preserving_of_outputDecoder_correctCount_ne_card
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool)
    (hne :
      finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
        finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) ≠
          Fintype.card Coin) :
    ¬ ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  rintro ⟨e, hpres⟩
  exact hne
    (postprocessedSide_outputDecoder_correctCount_eq_card_of_coinEquiv_preserving
      r side post decode e hpres)

/-- Decoder-level coin-matching blocker for postprocessed retained-side
outputs: below one lower-bounded source/coin block, any downstream decoder
whose aggregate correctness is not exactly half refutes approximate output
independence by ruling out the required preserving coin equivalence. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_outputDecoder_correctCount_ne_card_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (decode : β → Bool) {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hne :
      finiteEventCount Coin (fun c => decode (post (r true c, side c)) = true) +
        finiteEventCount Coin (fun c => decode (post (r false c, side c)) = false) ≠
          Fintype.card Coin) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_no_postprocessedSide_coinEquiv_preserving_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt
      (not_exists_postprocessedSide_coinEquiv_preserving_of_outputDecoder_correctCount_ne_card
        r side post decode hne)

/-- Downstream predicate erasure for a postprocessed retained-side observation
is exactly observed-fiber balance.  Quantifying over all decidable predicates
does not weaken the coin-matching obligation: singleton predicates recover
the original observed fibers. -/
theorem postprocessedSide_outputPredicate_count_eq_iff_observedFiber_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∀ P : β → Prop, [DecidablePred P] →
      finiteEventCount Coin (fun c => P (post (r true c, side c))) =
        finiteEventCount Coin (fun c => P (post (r false c, side c)))) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  constructor
  · intro hpred z
    simpa using hpred (fun y : β => y = z)
  · intro hcount P _hP
    have hbal : FiniteCoinRecodingFiberBalanced (fun b c => post (r b c, side c)) :=
      (finiteCoinRecodingFiberBalanced_postprocessedSide_iff_observedFiber_count_eq
        r side post).2 hcount
    simpa using
      finiteCoinRecodingFiberBalanced_outputPredicate_count_eq
        (fun b c => post (r b c, side c)) P hbal

/-- Predicate-only certificates are equivalent to the full preserving
postprocessed-side coin matching.  A repair that claims all downstream
Boolean tests are source-neutral has already accepted the exact observed-fiber
multiplicity obligation needed to build the coin equivalence. -/
theorem exists_postprocessedSide_coinEquiv_preserving_iff_outputPredicate_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) ↔
      ∀ P : β → Prop, [DecidablePred P] →
        finiteEventCount Coin (fun c => P (post (r true c, side c))) =
          finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  constructor
  · rintro ⟨e, hpres⟩ P _hP
    exact postprocessedSide_outputPredicate_count_eq_of_coinEquiv_preserving
      r side post P e hpres
  · intro hpred
    exact
      exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_eq
        r side post
        ((postprocessedSide_outputPredicate_count_eq_iff_observedFiber_count_eq
          r side post).1 hpred)

/-- Preserving postprocessed-side coin equivalences are exactly observed-fiber
count balance.  This is the finite distribution form of the coin-matching
obligation, independent of how the repair phrases the matching certificate. -/
theorem exists_postprocessedSide_coinEquiv_preserving_iff_observedFiber_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  constructor
  · rintro ⟨e, hpres⟩
    exact postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving
      r side post e hpres
  · exact exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_eq
      r side post

/-- Below one lower-bounded source/coin block, approximate independence of a
postprocessed retained-side observation is equivalent to downstream predicate
erasure.  This is the predicate-only view of the same observed-fiber matching
boundary. -/
theorem countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_outputPredicate_count_eq
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
      ∀ P : β → Prop, [DecidablePred P] →
        finiteEventCount Coin (fun c => P (post (r true c, side c))) =
          finiteEventCount Coin (fun c => P (post (r false c, side c))) := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ
        ↔ ∀ z : β,
            finiteEventCount Coin (fun c => post (r true c, side c) = z) =
              finiteEventCount Coin (fun c => post (r false c, side c) = z) :=
          countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
            C E r side post htrue hfalse hlt
    _ ↔ ∀ P : β → Prop, [DecidablePred P] →
          finiteEventCount Coin (fun c => P (post (r true c, side c))) =
            finiteEventCount Coin (fun c => P (post (r false c, side c))) :=
          (postprocessedSide_outputPredicate_count_eq_iff_observedFiber_count_eq
            r side post).symm

/-- Below one lower-bounded source/coin block, approximate independence of a
postprocessed retained-side observation is equivalent to the existence of a
preserving true/false coin equivalence.  Thus an independence certificate below
this threshold must solve the full finite matching problem. -/
theorem countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_coinEquiv_preserving
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
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  calc
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
        (fun xr => C xr.1) (fun xr => E xr.1)
        (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ
        ↔ ∀ z : β,
            finiteEventCount Coin (fun c => post (r true c, side c) = z) =
              finiteEventCount Coin (fun c => post (r false c, side c) = z) :=
          countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
            C E r side post htrue hfalse hlt
    _ ↔ ∃ e : Coin ≃ Coin,
          ∀ c : Coin,
            post (r true c, side c) =
              post (r false (e c), side (e c)) :=
          (exists_postprocessedSide_coinEquiv_preserving_iff_observedFiber_count_eq
            r side post).symm

/-- Exact source-count specialization of the postprocessed-side coin-matching
equivalence. -/
theorem countIndependentWithinToleranceOutput_postprocessedSide_lt_sourceCoinProduct_iff_coinEquiv_preserving
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ : Nat}
    (hlt :
      τ <
        finiteEventCount Ω (fun ω => C ω ∧ E ω) *
          finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω) *
            Fintype.card Coin) :
    CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ ↔
      ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_coinEquiv_preserving
      C E r side post le_rfl le_rfl hlt

end Mettapedia.Computability.PNP
