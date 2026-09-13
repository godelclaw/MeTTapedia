import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredAngularMean
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAngularCurlEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.MonochromaticShearEvolution
import Mettapedia.Analysis.AngularCurlEvolutionTests

/-! The new angular correction passes the exact unforced shear test. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.AngularEvolutionTests

open MonochromaticShearProjection LocalVorticityEighthMoment

theorem shear_correctedEnergy (κ A : ℝ) :
    FiniteBandAngularEnergy.correctedEnergy κ (velocity A) = meanEnergy (velocity A) / 8 := by
  simp [FiniteBandAngularEnergy.correctedEnergy, angularCurlEnergy_eq_zero]

theorem heat_correctedEnergy_pos {ν : ℝ} (hν : 0 ≤ ν) (κ A T t : ℝ) (hA : 0 < A) :
    0 < FiniteBandAngularEnergy.correctedEnergy κ ((heatSolution hν A T).coefficients t) := by
  rw [heatSolution_coefficients, shear_correctedEnergy]
  exact div_pos (meanEnergy_pos _ (mul_pos hA (Real.exp_pos _))) (by norm_num)

/-- Opposite signs on the same actual unforced trajectory distinguish the
two functionals. This is not a global coercivity theorem at the matched scale. -/
theorem heat_matched_corrections_separated {ν : ℝ} (hν : 0 ≤ ν)
    (δ A T t : ℝ) (hδ : 0 < δ) (hA : 0 < A) :
    FilteredProjectionMean.meanCorrectedEnergy δ eigenvalue ((heatSolution hν A T).coefficients t) < 0 ∧
      0 < FiniteBandAngularEnergy.correctedEnergy eigenvalue ((heatSolution hν A T).coefficients t) :=
  ⟨heatSolution_matched_correctedMean_neg hν δ A T t hδ hA,
    heat_correctedEnergy_pos hν eigenvalue A T t hA⟩

end Mettapedia.FluidDynamics.NavierStokes.AngularEvolutionTests
