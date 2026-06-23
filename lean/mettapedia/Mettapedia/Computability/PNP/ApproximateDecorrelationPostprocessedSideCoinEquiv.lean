import Mettapedia.Computability.PNP.ApproximateDecorrelationPostprocessedSideSkewMaps

/-!
# PNP approximate decorrelation: postprocessed-side layer

This module contains the coin-map and coin-equivalence preservation criteria.
-/

namespace Mettapedia.Computability.PNP

/-- Exact fiber matching for postprocessed retained-side observations: if the
true-side and false-side observed fibers have equal finite counts at every
postprocessed value, then there is a global equivalence of coin choices that
preserves the postprocessed observation.  This records the multiplicity-level
obligation behind pointwise support overlap. -/
theorem exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (hcount :
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  classical
  let trueObs : Coin → β := fun c => post (r true c, side c)
  let falseObs : Coin → β := fun c => post (r false c, side c)
  let fiberEquiv :
      ∀ z : β, {c : Coin // trueObs c = z} ≃ {c : Coin // falseObs c = z} :=
    fun z =>
      Fintype.equivOfCardEq (by
        simpa [trueObs, falseObs, finiteEventCount] using hcount z)
  let e : Coin ≃ Coin :=
    (Equiv.sigmaFiberEquiv trueObs).symm.trans
      ((Equiv.sigmaCongrRight fiberEquiv).trans
        (Equiv.sigmaFiberEquiv falseObs))
  refine ⟨e, ?_⟩
  intro c
  let x : {cFalse : Coin // falseObs cFalse = trueObs c} :=
    fiberEquiv (trueObs c) ⟨c, rfl⟩
  have hx : falseObs x.1 = trueObs c := x.2
  change trueObs c = falseObs (e c)
  rw [show e c = x.1 from rfl]
  exact hx.symm

/-- Global matching obligation for a postprocessed retained-side output:
below one lower-bounded source/coin block, approximate output independence
forces a bijective matching of coin choices that preserves every
postprocessed observation.  A deterministic postprocessing repair must
therefore preserve exact observed multiplicities, not just create support
overlap. -/
theorem exists_postprocessedSide_coinEquiv_preserving_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
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
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  exact
    exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_eq
      r side post
      ((countIndependentWithinToleranceOutput_postprocessedSide_sourceLowerBounds_lt_coinProduct_iff_observedFiber_count_eq
        C E r side post htrue hfalse hlt).mp happrox)

/-- Contrapositive matching blocker for postprocessed retained-side outputs:
if there is no bijection of coin choices preserving the postprocessed
observation from the true side to the false side, then below-threshold
approximate output independence is impossible. -/
theorem not_countIndependentWithinToleranceOutput_of_no_postprocessedSide_coinEquiv_preserving_sourceLowerBounds_lt_coinProduct
    {Ω Coin α Side β : Type*} [Fintype Ω] [Fintype Coin] [DecidableEq β]
    (C E : Ω → Prop) [DecidablePred C] [DecidablePred E]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    {τ loTrue loFalse : Nat}
    (htrue : loTrue ≤ finiteEventCount Ω (fun ω => C ω ∧ E ω))
    (hfalse : loFalse ≤ finiteEventCount Ω (fun ω => C ω ∧ ¬ E ω))
    (hlt : τ < loTrue * loFalse * Fintype.card Coin)
    (hno :
      ¬ ∃ e : Coin ≃ Coin,
        ∀ c : Coin,
          post (r true c, side c) = post (r false (e c), side (e c))) :
    ¬ CountIndependentWithinToleranceOutput (Ω := Ω × Coin)
      (fun xr => C xr.1) (fun xr => E xr.1)
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  intro happrox
  exact hno
    (exists_postprocessedSide_coinEquiv_preserving_of_countIndependentWithinToleranceOutput_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt happrox)

/-- Any bijective true/false coin matching that preserves postprocessed
observations forces exact equality of every observed postprocessed fiber count.
This is the converse audit for proposed matching repairs: a bijection cannot
repair even one multiplicity mismatch. -/
theorem postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (e : Coin ≃ Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c))) :
    ∀ z : β,
      finiteEventCount Coin (fun c => post (r true c, side c) = z) =
        finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  classical
  intro z
  let trueObs : Coin → β := fun c => post (r true c, side c)
  let falseObs : Coin → β := fun c => post (r false c, side c)
  let fiberEquiv :
      {c : Coin // trueObs c = z} ≃ {c : Coin // falseObs c = z} :=
    { toFun := fun c => by
        refine ⟨e c.1, ?_⟩
        change post (r false (e c.1), side (e c.1)) = z
        rw [← hpres c.1]
        simpa [trueObs] using c.2
      invFun := fun c => by
        refine ⟨e.symm c.1, ?_⟩
        change post (r true (e.symm c.1), side (e.symm c.1)) = z
        rw [hpres (e.symm c.1)]
        simpa [falseObs] using c.2
      left_inv := by
        intro c
        ext
        simp
      right_inv := by
        intro c
        ext
        simp }
  simpa [finiteEventCount, trueObs, falseObs] using Fintype.card_congr fiberEquiv

/-- Injective one-sided witness maps are exactly the observed-fiber
multiplicity-balance obligation.  This removes the apparent intermediate repair
target: with finite coins, proving an injective one-sided choice of false-side
witnesses is the same count-theoretic burden as proving a preserving
postprocessed-side coin equivalence. -/
theorem exists_injective_postprocessedSide_coinMap_preserving_iff_observedFiber_count_eq
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β) :
    (∃ f : Coin → Coin,
      (∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c))) ∧
        Function.Injective f) ↔
      ∀ z : β,
        finiteEventCount Coin (fun c => post (r true c, side c) = z) =
          finiteEventCount Coin (fun c => post (r false c, side c) = z) := by
  constructor
  · intro h
    rcases
      (exists_injective_postprocessedSide_coinMap_preserving_iff_exists_coinEquiv_preserving
        r side post).1 h with ⟨e, hpres⟩
    exact postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving r side post e hpres
  · intro hcount
    rcases exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_eq
      r side post hcount with ⟨e, hpres⟩
    exact
      (exists_injective_postprocessedSide_coinMap_preserving_iff_exists_coinEquiv_preserving
        r side post).2 ⟨e, hpres⟩

/-- A single postprocessed observed-fiber multiplicity mismatch rules out every
coin equivalence preserving the postprocessed observation.  This makes the
coin-matching repair obligation checkable by local fiber counts rather than by
searching over all bijections. -/
theorem not_exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_ne
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (z : β)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ ∃ e : Coin ≃ Coin,
      ∀ c : Coin,
        post (r true c, side c) = post (r false (e c), side (e c)) := by
  rintro ⟨e, hpres⟩
  exact hne
    (postprocessedSide_observedFiber_count_eq_of_coinEquiv_preserving
      r side post e hpres z)

/-- A single postprocessed observed-fiber multiplicity mismatch forces every
one-sided preserving witness map to be non-injective.  This is the general
pigeonhole form of the one-sided-map blocker; it is not tied to the concrete
three-coin skew instance. -/
theorem not_injective_postprocessedSide_coinMap_preserving_of_observedFiber_count_ne
    {Coin α Side β : Type*} [Fintype Coin] [DecidableEq β]
    (r : Bool → Coin → α) (side : Coin → Side) (post : α × Side → β)
    (f : Coin → Coin)
    (hpres :
      ∀ c : Coin,
        post (r true c, side c) = post (r false (f c), side (f c)))
    (z : β)
    (hne :
      finiteEventCount Coin (fun c => post (r true c, side c) = z) ≠
        finiteEventCount Coin (fun c => post (r false c, side c) = z)) :
    ¬ Function.Injective f := by
  exact
    not_injective_postprocessedSide_coinMap_preserving_of_no_coinEquiv
      r side post f hpres
      (not_exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_ne
        r side post z hne)

/-- Concrete multiplicity blocker for postprocessed retained-side outputs:
below one lower-bounded source/coin block, one observed postprocessed fiber
with unequal true-side and false-side coin counts refutes approximate output
independence.  Equivalently, the proposed postprocessing must solve the exact
coin-matching obligation at every observed value. -/
theorem not_countIndependentWithinToleranceOutput_of_postprocessedSide_observedFiber_count_ne_sourceLowerBounds_lt_coinProduct
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
      (fun xr => post (r (decide (E xr.1)) xr.2, side xr.2)) τ := by
  exact
    not_countIndependentWithinToleranceOutput_of_no_postprocessedSide_coinEquiv_preserving_sourceLowerBounds_lt_coinProduct
      C E r side post htrue hfalse hlt
      (not_exists_postprocessedSide_coinEquiv_preserving_of_observedFiber_count_ne
        r side post z hne)

end Mettapedia.Computability.PNP
