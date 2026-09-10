import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLowPressureBudget

/-!
# Exact pressure as a finite sum of pair contributions

Each contribution evaluates the pressure multiplier at its own output
frequency. This includes zero output and does not require that any input
coefficient be transverse. Incompressibility is imposed separately when
identifying a physical velocity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressurePairSum

open scoped BigOperators
open PeriodicFourierTriad PancakeFourierPressureStrain PancakeLowPressureBudget

theorem pressureCoeff_eq_pairSum (modes : Finset Wavevector) (u : FourierVelocity) (q : Wavevector) :
    pressureCoeff modes u q = ∑ r ∈ modes, ∑ s ∈ modes,
      if r + s = q then -modeDot (r + s) (orderedConvection r s u) / modeSquare (r + s) else 0 := by
  calc
    _ = ∑ r ∈ modes, ∑ s ∈ modes,
        -modeDot q (if r + s = q then orderedConvection r s u else 0) / modeSquare q := by
      simp only [pressureCoeff, convectionConvolution, modeDot_sum,
        Finset.sum_div, ← Finset.sum_neg_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      by_cases h : r + s = q
      · subst q
        simp
      · simp [h, modeDot]

def outputIndicator (q k : Wavevector) : ℂ := if k = q then 1 else 0

theorem pressureCoeff_eq_indicatorPairSum (modes : Finset Wavevector) (u : FourierVelocity)
    (q : Wavevector) :
    pressureCoeff modes u q = ∑ r ∈ modes, ∑ s ∈ modes,
      outputIndicator q (r + s) * (-modeDot (r + s) (orderedConvection r s u) / modeSquare (r + s)) := by
  rw [pressureCoeff_eq_pairSum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  simp only [outputIndicator]
  split_ifs <;> simp

end Mettapedia.FluidDynamics.NavierStokes.FourierPressurePairSum
