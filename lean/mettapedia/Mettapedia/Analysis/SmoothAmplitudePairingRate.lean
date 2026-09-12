import Mettapedia.Analysis.SmoothAmplitudePairingEvolution

/-!
# Signed material channels of smooth amplitude retention

The common-strain commutator is inherited from the signed paired rate.
Weight amplification, relative kernel transport and viscosity remain
separate signed terms. This algebra supplies no channel budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SmoothAmplitudePairing

open SmoothAmplitudeCutoff SignedCrossKernel
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def retainedStrainRate (n : ℕ) (L : ℝ) (S T H : Op) (a b : R3) : ℝ :=
  pairRate L a b (S a) (T b) * pairedStretch (2 * (n + 1)) H a b +
    pairWeight L a b * pairedStretchRate n S T H 0 a b 0 0

theorem retainedRate_eq_strain_add_kernel_add_endpoint
    (n : ℕ) (L c : ℝ) (S T H Hdot : Op) (a b f g : R3) :
    pairRate L a b (S a + c • f) (T b + c • g) * pairedStretch (2 * (n + 1)) H a b +
      pairWeight L a b * pairedStretchRate n S T H Hdot a b (c • f) (c • g) =
        retainedStrainRate n L S T H a b + retainedStretch (2 * (n + 1)) L Hdot a b +
          c * retainedEndpointRate n L H a b f g := by
  rw [pairRate_add, pairRate_smul,
    pairedStretchRate_eq_strain_add_kernel_add_endpoint, pairedEndpointRate_smul]
  unfold retainedStrainRate retainedStretch retainedEndpointRate
  ring

end Mettapedia.Analysis.SmoothAmplitudePairing
