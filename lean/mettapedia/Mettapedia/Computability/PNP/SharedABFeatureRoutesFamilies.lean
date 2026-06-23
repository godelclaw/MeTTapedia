import Mettapedia.Computability.PNP.SharedABFeatureRoutesPredictors

/-!
# Shared `(a,b)` feature route families and bit budgets

This module packages reduced-surface realizability predicates, their encoded
classifier families, and the resulting bit-budget lower-bound interfaces.
-/

namespace Mettapedia.Computability.PNP

section

variable {r k : ℕ}

/-- Reduced-surface family using one shared raw `(a, b)` affine basis and an
arbitrary truth-table combiner. -/
def RealizedBySharedABAffineFeatureFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (H : ABVisibleSwitchedFamily k Index) : Prop :=
  ∀ i, ∃ table : BitCode (2 ^ r),
    H.predict i = sharedABAffineFeaturePredict (k := k) features table

/-- Reduced-surface family using one shared raw `(a, b)` affine basis and a
sparse-threshold combiner. -/
def RealizedBySharedABSparseThresholdAffineFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (H : ABVisibleSwitchedFamily k Index) : Prop :=
  ∀ i, ∃ code : SharedSparseThresholdCode r,
    H.predict i = sharedABSparseThresholdAffinePredict (k := k) features code

/-- Reduced-surface family using one shared raw `(a, b)` affine basis and a
fixed-order decision-list combiner. -/
def RealizedBySharedABAffineDecisionListFamily
    {Index : Type*} (features : Fin r → AffineColumnCode (k + k))
    (H : ABVisibleSwitchedFamily k Index) : Prop :=
  ∀ i, ∃ code : SharedAffineDecisionListCode r,
    H.predict i = sharedABAffineDecisionListPredict (k := k) features code

/-- Shared truth-table family directly on the reduced raw `(a, b)` surface. -/
noncomputable def sharedABAffineFeatureBitFamily
    (features : Fin r → AffineColumnCode (k + k)) :
    BitEncodedClassifierFamily (ABVisibleSurface k) (2 ^ r) where
  decode table := sharedABAffineFeaturePredict (k := k) features table

/-- Shared sparse-threshold family directly on the reduced raw `(a, b)` surface. -/
noncomputable def sharedABSparseThresholdAffineBitFamily
    (features : Fin r → AffineColumnCode (k + k)) :
    BitEncodedClassifierFamily (ABVisibleSurface k) (2 * r) where
  decode raw x :=
    let code := (sharedSparseThresholdCodeEquivBitCode r).symm raw
    sharedABSparseThresholdAffinePredict (k := k) features code x

/-- Shared decision-list family directly on the reduced raw `(a, b)` surface. -/
noncomputable def sharedABAffineDecisionListBitFamily
    (features : Fin r → AffineColumnCode (k + k)) :
    BitEncodedClassifierFamily (ABVisibleSurface k) (r + 1) where
  decode raw x :=
    let code := (sharedAffineDecisionListCodeEquivBitCode r).symm raw
    sharedABAffineDecisionListPredict (k := k) features code x

@[simp] theorem sharedABAffineFeatureBitFamily_decode
    (features : Fin r → AffineColumnCode (k + k)) (table : BitCode (2 ^ r)) :
    (sharedABAffineFeatureBitFamily (r := r) (k := k) features).decode table =
      sharedABAffineFeaturePredict (k := k) features table := rfl

@[simp] theorem sharedABSparseThresholdAffineBitFamily_decode_code
    (features : Fin r → AffineColumnCode (k + k)) (code : SharedSparseThresholdCode r) :
    (sharedABSparseThresholdAffineBitFamily (r := r) (k := k) features).decode
        (sharedSparseThresholdCodeEquivBitCode r code) =
      sharedABSparseThresholdAffinePredict (k := k) features code := by
  funext x
  simp [sharedABSparseThresholdAffineBitFamily, sharedSparseThresholdCodeEquivBitCode]

@[simp] theorem sharedABAffineDecisionListBitFamily_decode_code
    (features : Fin r → AffineColumnCode (k + k)) (code : SharedAffineDecisionListCode r) :
    (sharedABAffineDecisionListBitFamily (r := r) (k := k) features).decode
        (sharedAffineDecisionListCodeEquivBitCode r code) =
      sharedABAffineDecisionListPredict (k := k) features code := by
  funext x
  simp [sharedABAffineDecisionListBitFamily, sharedAffineDecisionListCodeEquivBitCode]

theorem abVisibleHasBitBudget_of_realizedBySharedABAffineFeatureFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    H.HasBitBudget (2 ^ r) := by
  refine ⟨sharedABAffineFeatureBitFamily (r := r) (k := k) features, ?_⟩
  intro i
  rcases hreal i with ⟨table, hi⟩
  refine ⟨table, ?_⟩
  exact (sharedABAffineFeatureBitFamily_decode (r := r) (k := k) features table).trans hi.symm

theorem abVisibleHasBitBudget_of_realizedBySharedABSparseThresholdAffineFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hreal : RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    H.HasBitBudget (2 * r) := by
  refine ⟨sharedABSparseThresholdAffineBitFamily (r := r) (k := k) features, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedSparseThresholdCodeEquivBitCode r code, ?_⟩
  exact
    (sharedABSparseThresholdAffineBitFamily_decode_code
      (r := r) (k := k) features code).trans hi.symm

theorem abVisibleHasBitBudget_of_realizedBySharedABAffineDecisionListFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hreal : RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    H.HasBitBudget (r + 1) := by
  refine ⟨sharedABAffineDecisionListBitFamily (r := r) (k := k) features, ?_⟩
  intro i
  rcases hreal i with ⟨code, hi⟩
  refine ⟨sharedAffineDecisionListCodeEquivBitCode r code, ?_⟩
  exact
    (sharedABAffineDecisionListBitFamily_decode_code
      (r := r) (k := k) features code).trans hi.symm

theorem abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABAffineFeatureFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H) :
    Fintype.card (ABVisibleSurface k) ≤ 2 ^ r := by
  exact
    IndexedPredictorFamily.bitBudget_lowerBound_of_surjective_predict_fintype
      (G := H) (s := 2 ^ r) hsurj
      (abVisibleHasBitBudget_of_realizedBySharedABAffineFeatureFamily
        (r := r) (k := k) hreal)

theorem abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABSparseThresholdAffineFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H) :
    Fintype.card (ABVisibleSurface k) ≤ 2 * r := by
  exact
    IndexedPredictorFamily.bitBudget_lowerBound_of_surjective_predict_fintype
      (G := H) (s := 2 * r) hsurj
      (abVisibleHasBitBudget_of_realizedBySharedABSparseThresholdAffineFamily
        (r := r) (k := k) hreal)

theorem abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABAffineDecisionListFamily
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hsurj : Function.Surjective H.predict)
    (hreal : RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H) :
    Fintype.card (ABVisibleSurface k) ≤ r + 1 := by
  exact
    IndexedPredictorFamily.bitBudget_lowerBound_of_surjective_predict_fintype
      (G := H) (s := r + 1) hsurj
      (abVisibleHasBitBudget_of_realizedBySharedABAffineDecisionListFamily
        (r := r) (k := k) hreal)

theorem not_realizedBySharedABAffineFeatureFamily_of_surjective_predict_of_lt_surfaceCard
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 ^ r < Fintype.card (ABVisibleSurface k))
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedABAffineFeatureFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABAffineFeatureFamily
      (r := r) (k := k) hsurj hreal

theorem not_realizedBySharedABSparseThresholdAffineFamily_of_surjective_predict_of_lt_surfaceCard
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : 2 * r < Fintype.card (ABVisibleSurface k))
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedABSparseThresholdAffineFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABSparseThresholdAffineFamily
      (r := r) (k := k) hsurj hreal

theorem not_realizedBySharedABAffineDecisionListFamily_of_surjective_predict_of_lt_surfaceCard
    {Index : Type*}
    {H : ABVisibleSwitchedFamily k Index}
    {features : Fin r → AffineColumnCode (k + k)}
    (hs : r + 1 < Fintype.card (ABVisibleSurface k))
    (hsurj : Function.Surjective H.predict) :
    ¬ RealizedBySharedABAffineDecisionListFamily (r := r) (k := k) features H := by
  intro hreal
  exact Nat.not_le_of_lt hs <|
    abVisible_surfaceCard_le_of_surjective_predict_of_realizedBySharedABAffineDecisionListFamily
      (r := r) (k := k) hsurj hreal

end

end Mettapedia.Computability.PNP
