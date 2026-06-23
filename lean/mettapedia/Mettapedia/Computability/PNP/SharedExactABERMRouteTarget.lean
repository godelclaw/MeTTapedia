import Mettapedia.Computability.PNP.SharedExactABERMRouteCore

/-!
# Shared exact `(a,b)` decision-list ERM target consequences

This module packages target data, compression targets, surface-card bounds, and
non-surjectivity consequences for the shared decision-list ERM family.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

def sharedExactABAffineDecisionListERMTargetData
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    SharedABDecisionListTargetData
      (Z := Z) (r := r) (k := k) (Index := Index)
      (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples) where
  features := features
  invariant :=
    sharedExactABAffineDecisionListERMFamily_invariant
      (Z := Z) (r := r) (k := k) (Index := Index) features samples
  realized :=
    sharedExactABAffineDecisionListERMFamily_realized
      (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem sharedExactABAffineDecisionListERMCompressionTarget
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleCompressionTarget
      (Z := Z) (k := k) (Index := Index)
      (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples)
      (r + 1) := by
  exact
    (sharedExactABAffineDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).compressionTarget

theorem sharedExactABAffineDecisionListERMFamily_surfaceCard_le_of_surjective_predict
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hsurj :
      Function.Surjective
        (sharedExactABAffineDecisionListERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ r + 1 := by
  exact
    (sharedExactABAffineDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).surfaceCard_le_of_surjective_predict
      hsurj

theorem sharedExactABAffineDecisionListERMFamily_not_surjective_of_lt_surfaceCard
    [Inhabited Z] [Fintype Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (hs : r + 1 < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Function.Surjective
        (sharedExactABAffineDecisionListERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict := by
  exact
    (sharedExactABAffineDecisionListERMTargetData
      (Z := Z) (r := r) (k := k) (Index := Index) features samples).not_surjective_predict_of_lt_surfaceCard
      hs

end

end Mettapedia.Computability.PNP
