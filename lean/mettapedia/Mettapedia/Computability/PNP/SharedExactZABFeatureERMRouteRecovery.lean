import Mettapedia.Computability.PNP.SharedExactZABFeatureERMRouteTargets

/-!
# P vs NP grassroots: shared exact ZAB feature ERM recovery

This module packages recovery-data constructors and weighted recovery lower
bounds for the shared-basis exact `(zfeat(z), a, b)` ERM routes.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {p r k : ℕ} {Index : Type*}

section

variable [Fintype Z]

def sharedExactZABAffineFeatureERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactZABAffineFeatureBitFamily Z zfeat features).toEncodedFamily.BadCodes
            ((sharedExactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i),
          agreementMass μ
            ((sharedExactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
            ((sharedExactZABAffineFeatureBitFamily Z zfeat features).decode c.1) ≤ q) :
    SharedExactZABAffineFeatureRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat
      (sharedExactZABAffineFeatureERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples) q := by
  refine ⟨features, ?_, hq⟩
  exact
    (sharedExactZABAffineFeatureERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).realized

def sharedExactZABSparseThresholdAffineERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).toEncodedFamily.BadCodes
            ((sharedExactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i),
          agreementMass μ
            ((sharedExactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
            ((sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).decode c.1) ≤ q) :
    SharedExactZABSparseThresholdRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat
      (sharedExactZABSparseThresholdAffineERMFamily
        (Z := Z) (p := p) (r := r) (k := k) zfeat features samples) q := by
  refine ⟨features, ?_, hq⟩
  exact
    (sharedExactZABSparseThresholdAffineERMTargetData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      zfeat features samples).realized

theorem sharedExactZABAffineFeatureERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactZABAffineFeatureBitFamily Z zfeat features).toEncodedFamily.BadCodes
            ((sharedExactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i),
          agreementMass μ
            ((sharedExactZABAffineFeatureERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
            ((sharedExactZABAffineFeatureBitFamily Z zfeat features).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 ^ p) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABAffineFeatureBitFamily Z zfeat features).bitExactRecoverySampleMass
        μ
        ((sharedExactZABAffineFeatureERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
        m := by
  simpa [sharedExactZABAffineFeatureERMRecoveryData] using
    (sharedExactZABAffineFeatureERMRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat features samples q hq).recoveryLowerBound i m

theorem sharedExactZABSparseThresholdAffineERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (zfeat : Z → BitVec r)
    (features : Fin p → AffineColumnCode (r + (k + k)))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).toEncodedFamily.BadCodes
            ((sharedExactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i),
          agreementMass μ
            ((sharedExactZABSparseThresholdAffineERMFamily
              (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
            ((sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (2 * p) : ℝ≥0∞) * q ^ m ≤
      (sharedExactZABSparseThresholdAffineBitFamily Z zfeat features).bitExactRecoverySampleMass
        μ
        ((sharedExactZABSparseThresholdAffineERMFamily
          (Z := Z) (p := p) (r := r) (k := k) zfeat features samples).predict i)
        m := by
  simpa [sharedExactZABSparseThresholdAffineERMRecoveryData] using
    (sharedExactZABSparseThresholdAffineERMRecoveryData
      (Z := Z) (p := p) (r := r) (k := k) (Index := Index)
      μ zfeat features samples q hq).recoveryLowerBound i m

end

end

end Mettapedia.Computability.PNP
