import Mettapedia.Computability.PNP.SharedExactABERMRouteRecovery

/-!
# Shared exact `(a,b)` ERM interface data

This module contains the final manuscript-facing recovery-data structure for
the shared-basis raw exact `(a,b)` ERM route.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

structure SharedExactABERMRecoveryData
    [Inhabited Z] [Fintype Z]
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (G : ExactVisibleSwitchedFamily Z k Index)
    (q : ℝ≥0∞) where
  features : Fin r → AffineColumnCode (k + k)
  samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool
  exact_family :
    G = sharedExactABAffineDecisionListERMFamily (Z := Z) (r := r) (k := k) features samples
  agreement_le :
    ∀ i,
      ∀ c :
        (sharedExactABAffineDecisionListBitFamily Z features).toEncodedFamily.BadCodes
          (G.predict i),
        agreementMass μ (G.predict i)
          ((sharedExactABAffineDecisionListBitFamily Z features).decode c.1) ≤ q

end

end Mettapedia.Computability.PNP
