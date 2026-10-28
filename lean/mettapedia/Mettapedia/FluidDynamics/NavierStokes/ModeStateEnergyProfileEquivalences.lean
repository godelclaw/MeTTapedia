import Mettapedia.FluidDynamics.NavierStokes.ModeStateEnergyProfileConcrete

/-!
# Hard profile detectors agree with the hard Sobolev radius

For each strictly positive concrete profile, the induced hard detector is the hard
Sobolev radius. The identity and logarithmic equivalences live with their charts, in
`ModeStateEnergyProfileFork` and `ModeStateLogEnergyChartFork`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped Classical

section ModeStateEnergyProfileEquivalences

theorem hardProfileThresholdRadius_rationalMax_eq_hardSobolevRadius
    (m : ℕ) :
    hardProfileThresholdRadius rationalMaxEnergyProfile m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := rationalMaxEnergyProfile) m

theorem hardProfileThresholdRadius_expNegMax_eq_hardSobolevRadius
    (m : ℕ) :
    hardProfileThresholdRadius expNegMaxEnergyProfile m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := expNegMaxEnergyProfile) m

theorem hardProfileThresholdRadius_smoothTransition_eq_hardSobolevRadius
    (m : ℕ) :
    hardProfileThresholdRadius smoothTransitionEnergyProfile m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := smoothTransitionEnergyProfile) m

theorem hardProfileThresholdRadius_scaledSmoothTransition_eq_hardSobolevRadius
    (c : ℝ) (hc : 0 < c) (m : ℕ) :
    hardProfileThresholdRadius (scaledSmoothTransitionEnergyProfile c hc) m = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := scaledSmoothTransitionEnergyProfile c hc) m

theorem hardProfileThresholdRadius_affineSmoothTransition_eq_hardSobolevRadius
    (c d : ℝ) (hc : 0 < c) (hd : 0 ≤ d) (m : ℕ) :
    hardProfileThresholdRadius (affineSmoothTransitionEnergyProfile c d hc hd) m
      = hardSobolevRadius m := by
  simpa using
    hardProfileThresholdRadius_eq_hardSobolevRadius
      (P := affineSmoothTransitionEnergyProfile c d hc hd) m

end ModeStateEnergyProfileEquivalences

end NavierStokes
end FluidDynamics
end Mettapedia
