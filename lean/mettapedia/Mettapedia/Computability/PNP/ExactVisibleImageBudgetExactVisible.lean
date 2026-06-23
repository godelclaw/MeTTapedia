import Mettapedia.Computability.PNP.ExactVisibleImageBudgetLowerBounds

/-!
# Exact-visible finite image budgets

The exact-visible compression interface is re-expressed as finite predictor
covers, representative-index covers, and quotient-code presentations, then
inherits the abstract predictor-image lower bounds.
-/

namespace Mettapedia.Computability.PNP

section ExactVisible

variable {Z : Type*} {k s clock : ℕ} {Index : Type*}

/-- Exact visible compression is just a finite predictor-image cover with
`2^s` allowed predictors. -/
theorem exactVisibleCompressionTarget_iff_finitePredictorCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finitePredictorCover

/-- Exact visible compression is equivalently represented by at most `2^s`
actual indices from the family. -/
theorem exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finiteIndexRepresentativeCover

/-- Exact visible compression is equivalently represented by a finite
quotient-code presentation of size at most `2^s`. -/
theorem exactVisibleCompressionTarget_iff_finitePredictorQuotient
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  exact IndexedPredictorFamily.hasBitBudget_iff_finitePredictorQuotient

/-- The clocked exact-visible realization interface has the same predictor-image
content. -/
theorem exists_clockedExactVisibleRealization_iff_finitePredictorCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorCover (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget,
    exactVisibleCompressionTarget_iff_finitePredictorCover]

/-- The clocked exact-visible realization interface is equivalently represented
by at most `2^s` actual selected indices. -/
theorem exists_clockedExactVisibleRealization_iff_finiteIndexRepresentativeCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget,
    exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover]

/-- The clocked exact-visible realization interface is equivalently a finite
quotient-code presentation with at most `2^s` codes. -/
theorem exists_clockedExactVisibleRealization_iff_finitePredictorQuotient
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget,
    exactVisibleCompressionTarget_iff_finitePredictorQuotient]

/-- Negative form of the predictor-image characterization for clocked
exact-visible realization. -/
theorem not_exists_clockedExactVisibleRealization_iff_not_finitePredictorCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorCover (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorCover]

/-- Negative form of the representative-index characterization for clocked
exact-visible realization. -/
theorem not_exists_clockedExactVisibleRealization_iff_not_finiteIndexRepresentativeCover
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FiniteIndexRepresentativeCover (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_finiteIndexRepresentativeCover]

/-- Negative form of the quotient-code characterization for clocked
exact-visible realization. -/
theorem not_exists_clockedExactVisibleRealization_iff_not_finitePredictorQuotient
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorQuotient (2 ^ s) := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorQuotient]

/-- Exact visible finite-image covers must contain every injectively realized
finite probe family of exact-surface classifiers. -/
theorem exactVisible_finitePredictorCover_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hcover : G.FinitePredictorCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorCover_card_le_of_injective_realization
    target hinj hreal hcover

/-- Exact visible representative-index covers must contain every injectively
realized finite probe family of exact-surface classifiers. -/
theorem exactVisible_finiteIndexRepresentativeCover_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_injective_realization
    target hinj hreal hrep

/-- Exact visible quotient-code presentations must contain every injectively
realized finite probe family of exact-surface classifiers. -/
theorem exactVisible_finitePredictorQuotient_card_le_of_injective_realization
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hquot : G.FinitePredictorQuotient N) :
    Fintype.card Probe ≤ N :=
  IndexedPredictorFamily.finitePredictorQuotient_card_le_of_injective_realization
    target hinj hreal hquot

/-- Negative exact-visible cover form of the injective finite-probe lower
bound. -/
theorem not_exactVisible_finitePredictorCover_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorCover N :=
  IndexedPredictorFamily.not_finitePredictorCover_of_injective_realization_of_lt_card
    target hinj hreal hN

/-- Negative exact-visible representative-index form of the injective finite
probe lower bound. -/
theorem not_exactVisible_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.not_finiteIndexRepresentativeCover_of_injective_realization_of_lt_card
    target hinj hreal hN

/-- Negative exact-visible quotient-code form of the injective finite-probe
lower bound. -/
theorem not_exactVisible_finitePredictorQuotient_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hN : N < Fintype.card Probe) :
    ¬ G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.not_finitePredictorQuotient_of_injective_realization_of_lt_card
    target hinj hreal hN

/-- Exact visible compression is impossible below the size of any injectively
realized finite probe family. -/
theorem not_exactVisibleCompressionTarget_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  rw [exactVisibleCompressionTarget_iff_finitePredictorCover]
  exact
    not_exactVisible_finitePredictorCover_of_injective_realization_of_lt_card
      target hinj hreal hs

/-- Clocked exact-visible realization is impossible below the size of any
injectively realized finite probe family. -/
theorem not_exists_clockedExactVisibleRealization_of_injective_realization_of_lt_card
    {Probe : Type*} [Fintype Probe]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (target : Probe → ExactVisiblePostSwitchSurface Z k → Bool)
    (hinj : Function.Injective target)
    (hreal : ∀ p, ∃ i, G.predict i = target p)
    (hs : 2 ^ s < Fintype.card Probe) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorCover]
  exact
    not_exactVisible_finitePredictorCover_of_injective_realization_of_lt_card
      target hinj hreal hs

/-- If an exact visible family already realizes every Boolean rule on the exact
post-switch surface, then any finite predictor-image cover must be at least the
full Boolean classifier-space cardinality. -/
theorem exactVisible_finitePredictorCover_card_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hcover : G.FinitePredictorCover N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorCover_card_le_of_surjective_predict
      (G := G) hsurj hcover

/-- If an exact visible family already realizes every Boolean rule on the exact
post-switch surface, then any finite representative-index cover must be at
least the full Boolean classifier-space cardinality. -/
theorem exactVisible_finiteIndexRepresentativeCover_card_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hrep : G.FiniteIndexRepresentativeCover N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact
    IndexedPredictorFamily.finiteIndexRepresentativeCover_card_le_of_factorsThrough_of_rightInverse_of_surjective_predict
      (G := G) (H := G) (view := id) (sec := id)
      (by intro i x; rfl)
      (by intro x; rfl)
      hsurj hrep

/-- If an exact visible family already realizes every Boolean rule on the exact
post-switch surface, then any finite quotient-code presentation must be at
least the full Boolean classifier-space cardinality. -/
theorem exactVisible_finitePredictorQuotient_card_le_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hsurj : Function.Surjective G.predict)
    (hquot : G.FinitePredictorQuotient N) :
    2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ N := by
  exact
    IndexedPredictorFamily.finitePredictorQuotient_card_le_of_surjective_predict
      (G := G) hsurj hquot

/-- Fully expressive exact visible families have no finite predictor-image cover
below the full exact visible Boolean classifier-space cardinality. -/
theorem not_exactVisible_finitePredictorCover_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorCover N := by
  exact
    IndexedPredictorFamily.not_finitePredictorCover_of_surjective_predict
      (G := G) hN hsurj

/-- Fully expressive exact visible families have no finite representative-index
cover below the full exact visible Boolean classifier-space cardinality. -/
theorem not_exactVisible_finiteIndexRepresentativeCover_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FiniteIndexRepresentativeCover N := by
  intro hrep
  exact Nat.not_le_of_lt hN
    (exactVisible_finiteIndexRepresentativeCover_card_le_of_surjective_predict
      hsurj hrep)

/-- Fully expressive exact visible families have no finite quotient-code
presentation below the full exact visible Boolean classifier-space cardinality. -/
theorem not_exactVisible_finitePredictorQuotient_of_surjective_predict
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index} {N : ℕ}
    (hN : N < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ G.FinitePredictorQuotient N := by
  intro hquot
  exact Nat.not_le_of_lt hN
    (exactVisible_finitePredictorQuotient_card_le_of_surjective_predict
      hsurj hquot)

/-- Image-cardinality form of the exact visible compression obstruction. -/
theorem not_exactVisibleCompressionTarget_of_surjective_predict_of_lt_predictorCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  rw [exactVisibleCompressionTarget_iff_finitePredictorCover]
  exact not_exactVisible_finitePredictorCover_of_surjective_predict hs hsurj

/-- Image-cardinality form of the clocked exact-visible realization obstruction. -/
theorem not_exists_clockedExactVisibleRealization_of_surjective_predict_of_lt_predictorCard
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    (hs : 2 ^ s < 2 ^ Fintype.card (ExactVisiblePostSwitchSurface Z k))
    (hsurj : Function.Surjective G.predict) :
    ¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F := by
  rw [exists_clockedExactVisibleRealization_iff_finitePredictorCover]
  exact not_exactVisible_finitePredictorCover_of_surjective_predict hs hsurj

end ExactVisible

end Mettapedia.Computability.PNP
