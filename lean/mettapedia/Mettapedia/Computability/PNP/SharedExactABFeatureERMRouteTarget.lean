import Mettapedia.Computability.PNP.SharedExactABFeatureERMRouteCore

/-!
# Shared exact `(a,b)` affine-feature ERM targets

This module derives target data, compression targets, surface-card bounds, and
non-surjectivity consequences for shared exact affine-feature and
sparse-threshold ERM families.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

def sharedExactABAffineFeatureERMTargetData
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SharedABAffineFeatureTargetData
      (Z := Z) (r := r) (k := k) (Index := Index)
      (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples) where
  features := features
  invariant :=
    sharedExactABAffineFeatureERMFamily_invariant
      (Z := Z) (r := r) (k := k) (Index := Index) features samples
  realized :=
    sharedExactABAffineFeatureERMFamily_realized
      (Z := Z) (r := r) (k := k) (Index := Index) features samples

def sharedExactABSparseThresholdAffineERMTargetData
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SharedABSparseThresholdTargetData
      (Z := Z) (r := r) (k := k) (Index := Index)
      (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples) where
  features := features
  invariant :=
    sharedExactABSparseThresholdAffineERMFamily_invariant
      (Z := Z) (r := r) (k := k) (Index := Index) features samples
  realized :=
    sharedExactABSparseThresholdAffineERMFamily_realized
      (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem sharedExactABAffineFeatureERMCompressionTarget
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples)
      (2 ^ r) := by
  exact
    (sharedExactABAffineFeatureERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).compressionTarget

theorem sharedExactABSparseThresholdAffineERMCompressionTarget
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples)
      (2 * r) := by
  exact
    (sharedExactABSparseThresholdAffineERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).compressionTarget

theorem sharedExactABAffineFeatureERMFamily_surfaceCard_le_of_surjective_predict
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactABAffineFeatureERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 ^ r := by
  exact
    (sharedExactABAffineFeatureERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem sharedExactABSparseThresholdAffineERMFamily_surfaceCard_le_of_surjective_predict
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactABSparseThresholdAffineERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ 2 * r := by
  exact
    (sharedExactABSparseThresholdAffineERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem sharedExactABAffineFeatureERMFamily_not_surjective_of_lt_surfaceCard
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : 2 ^ r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (sharedExactABAffineFeatureERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict := by
  exact
    (sharedExactABAffineFeatureERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).not_surjective_predict_of_lt_surfaceCard
      hs

theorem sharedExactABSparseThresholdAffineERMFamily_not_surjective_of_lt_surfaceCard
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : 2 * r < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (sharedExactABSparseThresholdAffineERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict := by
  exact
    (sharedExactABSparseThresholdAffineERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).not_surjective_predict_of_lt_surfaceCard
      hs

end

end Mettapedia.Computability.PNP
