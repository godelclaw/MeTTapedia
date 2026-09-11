import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootDiffusionBudget

/-! Matrix normalization, incompressibility, and actual diffusion-budget tests. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootDiffusionAudit

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeBlockReality
open PancakeFourierPressureStrain PancakeFourierStrainGradient PancakeFrequencyProjectorCommutator
open PancakeInfiniteFourierDerivative PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation
open PancakePeriodicComplexStretch PancakeCurlOutputTail PancakeTransverseEnergyFreezing
open PancakeDyadicDirectionEvolution FourierMatrixEnergy StrainGradientEnergy
open VorticityGradientEnergy GaussianRootDiffusionBudget GaussianRootInputBudget

local notation "T3" => UnitAddTorus (Fin 3)

open MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example : matrixEnergy (1 : MatrixCoefficient) = 3 := by
  norm_num [matrixEnergy, Fin.sum_univ_three, Matrix.one_apply, Fin.ext_iff]

example (A : MatrixCoefficient) (hA : A.transpose = -A) :
    matrixEnergy ((1 / 2 : ℂ) • (A + A.transpose)) = 0 := by
  simp [hA, matrixEnergy]

/-- A longitudinal mode refutes the strain-to-curl estimate without incompressibility. -/
example : ¬ (∀ u : FourierVelocity, ∀ q : Wavevector, ∀ j : Fin 3,
    matrixEnergy (strainDerivativeCoeff j u q) ≤
      coefficientEnergy (indexedDerivativeCoeff id j (fourierCurl u) q)) := by
  intro h
  have h0 := h (fun _ ↦ ![1, 0, 0]) ![1, 0, 0] 0
  norm_num [matrixEnergy, strainDerivativeCoeff, strainCoeff, gradientCoeff, indexedDerivativeCoeff,
    fourierCurl, coefficientEnergy, coefficientCross, wavevectorCoefficient, Fin.sum_univ_three,
    norm_mul, unitTorusDerivativePhase, Real.pi_pos.le] at h0
  have he : (1 / 2 : ℂ) * (2 * Real.pi * Complex.I) +
      (1 / 2 : ℂ) * (2 * Real.pi * Complex.I) = 2 * Real.pi * Complex.I := by ring
  rw [he, show (![0, 0, 0] : VelocityCoefficient) 2 = 0 from rfl] at h0
  norm_num [norm_mul, abs_of_pos Real.pi_pos] at h0

/-- The parameter-free norm bound is obtained for every contractive finite filter. -/
example (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (hd : ∀ q, modeDot q (u q) = 0)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (hchi : ∀ q ∈ modes, ‖chi q‖ ≤ 1) :
    (∫ x : T3, ∑ j : Fin 3,
      ‖strainGradient modes (PancakeFilteredStrainDynamics.filteredVelocity chi u) x j‖ ^ 2) ≤
      gradientEnergy u :=
  integral_sum_strainGradient_sq_le chi modes hchi u hu hr (fun q _ ↦ hd q)

example (D : ℝ) (hD : 0 ≤ D) :
    Real.sqrt D ≤ D + 1 / 4 := by
  simpa using Mettapedia.Analysis.SqrtEnergyAbsorption.mul_sqrt_le 1 D 1 hD (by norm_num)

/-- The cover bound precedes every filter sequence in the stronger physical estimate. -/
example (u : FourierVelocity) (hu : Summable (fourierMoment 3 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (hd : ∀ q, modeDot q (u q) = 0)
    (gamma : ℝ) (hg : 0 < gamma) (rho : ℝ) (hrho : 0 < rho) :
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ chi : ℕ → Wavevector → ℂ, ∀ modes : ℕ → Finset Wavevector,
      (∀ j q, q ∈ modes j → ‖chi j q‖ ≤ 1) →
      ∃ centers : ℕ → Finset T3,
        (∀ j, (centers j).Nonempty ∧ (centers j).card ≤ M) ∧
        Summable (fun j : ℕ ↦ fullOutputNorm (inputScale N j) (inputScale_pos N hN j)
          gamma (chi j) (modes j) u (centers j) rho) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_input_diffusion_budget
  obtain ⟨M, hM, hfamily⟩ := h u hu hr hd gamma hg rho hrho
  refine ⟨M, hM, ?_⟩
  intro N hN chi modes hchi
  obtain ⟨centers, hp, hs, _⟩ := hfamily N hN chi modes hchi
  exact ⟨centers, fun j ↦ ⟨(hp j).1, (hp j).2.1⟩, hs⟩

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootDiffusionAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierMatrixEnergy.matrixEnergy_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierMatrixEnergy.matrixEnergy_smul
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierMatrixEnergy.matrixEnergy_transpose
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierMatrixEnergy.matrixEnergy_symmetrize_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierMatrixEnergy.realMatrixOperator_basisFun
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierMatrixEnergy.matrixReconstruction_column
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierMatrixEnergy.continuous_operatorField
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierMatrixEnergy.integral_operator_norm_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityGradientEnergy.hasSum_coefficientEnergy_real
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityGradientEnergy.coefficientGradientEnergy_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityGradientEnergy.gradientEnergy_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityGradientEnergy.hasSum_coefficientGradientEnergy
#print axioms Mettapedia.FluidDynamics.NavierStokes.VorticityGradientEnergy.sum_coefficientGradientEnergy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.StrainGradientEnergy.matrixEnergy_gradientCoeff
#print axioms Mettapedia.FluidDynamics.NavierStokes.StrainGradientEnergy.matrixEnergy_strainDerivativeCoeff_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.StrainGradientEnergy.strainDerivativeCoeff_filtered
#print axioms Mettapedia.FluidDynamics.NavierStokes.StrainGradientEnergy.matrixEnergy_filtered_strainDerivativeCoeff_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.StrainGradientEnergy.integral_sum_strainGradient_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootInputBudget.exists_uniform_input_operator_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootInputBudget.exists_uniform_input_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootDiffusionBudget.energyMultiplier_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootDiffusionBudget.input_bound_absorb
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootDiffusionBudget.integral_gradientDensity_le_energy
#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianRootDiffusionBudget.exists_uniform_input_diffusion_budget
