import Mettapedia.Computability.PNP.SharedExactABERMRouteTarget

/-!
# Shared exact `(a,b)` decision-list ERM recovery

This module packages recovery data and exact-recovery lower bounds for the
shared decision-list ERM family.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}
variable [Inhabited Z] [Fintype Z]

theorem sharedExactABAffineDecisionListERMRecoveryData
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABAffineDecisionListBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABAffineDecisionListBitFamily Z features).decode c.1) ≤ q) :
    SharedABDecisionListRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ features
      (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples) q := by
  refine ⟨?_, ?_, hq⟩
  · exact
      sharedExactABAffineDecisionListERMFamily_invariant
        (Z := Z) (r := r) (k := k) (Index := Index) features samples
  · exact
      sharedExactABAffineDecisionListERMFamily_realized
        (Z := Z) (r := r) (k := k) (Index := Index) features samples

theorem sharedExactABAffineDecisionListERMRecoveryLowerBound
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool)
    (q : ℝ≥0∞)
    (hq :
      ∀ i,
        ∀ c :
          (sharedExactABAffineDecisionListBitFamily Z features).toEncodedFamily.BadCodes
            ((sharedExactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i),
          agreementMass μ
            ((sharedExactABAffineDecisionListERMFamily
              (Z := Z) (r := r) (k := k) features samples).predict i)
            ((sharedExactABAffineDecisionListBitFamily Z features).decode c.1) ≤ q)
    (i : Index) (m : ℕ) :
    1 - (2 ^ (r + 1) : ℝ≥0∞) * q ^ m ≤
      (sharedExactABAffineDecisionListBitFamily Z features).bitExactRecoverySampleMass
        μ
        ((sharedExactABAffineDecisionListERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i)
        m := by
  exact
    (sharedExactABAffineDecisionListERMRecoveryData
      (Z := Z) (r := r) (k := k) (Index := Index)
      μ features samples q hq).recoveryLowerBound i m

end

end Mettapedia.Computability.PNP
