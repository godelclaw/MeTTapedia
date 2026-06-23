import Mettapedia.Computability.PNP.SharedExactABFeatureERMRouteTarget

/-!
# Shared exact `(a,b)` affine-feature ERM recovery

This module packages recovery data and exact-recovery lower bounds for shared
exact affine-feature and sparse-threshold ERM families.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}
variable [Inhabited Z] [Fintype Z]

def sharedExactABAffineFeatureERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABAffineFeatureBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABAffineFeatureBitFamily Z features).decode c.1) ≤ q) :
    SharedABAffineFeatureRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ
      (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples) q := by
  refine ⟨features, ?_, ?_, hq⟩
  · exact
      sharedExactABAffineFeatureERMFamily_invariant
        (Z := Z) (r := r) (k := k) (Index := Index) features samples
  · exact
      sharedExactABAffineFeatureERMFamily_realized
        (Z := Z) (r := r) (k := k) (Index := Index) features samples

def sharedExactABSparseThresholdAffineERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABSparseThresholdAffineBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABSparseThresholdAffineBitFamily Z features).decode c.1) ≤ q) :
    SharedABSparseThresholdRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ
      (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples) q := by
  refine ⟨features, ?_, ?_, hq⟩
  · exact
      sharedExactABSparseThresholdAffineERMFamily_invariant
        (Z := Z) (r := r) (k := k) (Index := Index) features samples
  · exact
      sharedExactABSparseThresholdAffineERMFamily_realized
        (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem sharedExactABAffineFeatureERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABAffineFeatureBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABAffineFeatureERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABAffineFeatureBitFamily Z features).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 ^ r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABAffineFeatureBitFamily Z features).bitExactRecoverySampleMass
        μ
        ((sharedExactABAffineFeatureERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i)
        m := by
  simpa [sharedExactABAffineFeatureERMRecoveryData] using
    (sharedExactABAffineFeatureERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ features samples q hq).recoveryLowerBound i m

theorem sharedExactABSparseThresholdAffineERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABSparseThresholdAffineBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABSparseThresholdAffineERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABSparseThresholdAffineBitFamily Z features).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * r) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABSparseThresholdAffineBitFamily Z features).bitExactRecoverySampleMass
        μ
        ((sharedExactABSparseThresholdAffineERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i)
        m := by
  simpa [sharedExactABSparseThresholdAffineERMRecoveryData] using
    (sharedExactABSparseThresholdAffineERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ features samples q hq).recoveryLowerBound i m

end

end Mettapedia.Computability.PNP
