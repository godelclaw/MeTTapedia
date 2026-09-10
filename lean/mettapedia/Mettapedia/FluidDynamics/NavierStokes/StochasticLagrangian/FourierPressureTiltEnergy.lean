import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTilt
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBoundaryEnergy

/-!
# Pressure-tilt energy without an output-count loss

For a fixed real direction, the actual filtered full-pressure tilt is the
real part of a finite Fourier field. Parseval bounds its squared spatial
norm by a sum of squared coefficients, retaining the longitudinal and
transverse angular factors. No direction regularity or coefficient reality
is needed for this upper bound. The direction is spatially constant.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy

open scoped BigOperators RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicVorticityEquation
open PancakeFrequencyProjectorCommutator PancakeViscousMisalignmentAbsorption
open PancakeAnisotropyDepletion PancakeTransverseEnergyFreezing PancakeDyadicDirectionEvolution
open PancakeInfinitePressureCoefficients LocalPressureCommutator FourierPressureCommutator
open FourierPressureTilt PancakeBoundaryEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def pressureAmplitude (chi : Wavevector → ℂ) (u : FourierVelocity) (q : Wavevector) : ℂ :=
  chi q * unitTorusDerivativePhase ^ 2 * infinitePressureCoeff u q

def tiltCoefficient (chi : Wavevector → ℂ) (u : FourierVelocity) (e : R3) : FourierVelocity :=
  fun q i ↦ pressureAmplitude chi u q *
    ((⟪realFrequency q, e⟫ * lineRemainder e (realFrequency q) i : ℝ) : ℂ)

def angularEnergy (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : R3) : ℝ :=
  ∑ q ∈ outputs, ‖pressureAmplitude chi u q‖ ^ 2 * ⟪realFrequency q, e⟫ ^ 2 *
    ‖lineRemainder e (realFrequency q)‖ ^ 2

/-- The full Hessian coefficient energy before selecting a direction. -/
def hessianEnergy (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) : ℝ :=
  ∑ q ∈ outputs, ‖pressureAmplitude chi u q‖ ^ 2 * ‖realFrequency q‖ ^ 4

theorem coefficientEnergy_real_multiple (a : ℂ) (v : R3) :
    coefficientEnergy (fun i ↦ a * (v i : ℂ)) = ‖a‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [← norm_coefficientVec_sq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coefficientVec, PiLp.toLp_apply, norm_mul, Complex.norm_real, mul_pow]

theorem coefficientEnergy_tiltCoefficient (chi : Wavevector → ℂ) (u : FourierVelocity)
    (e : R3) (q : Wavevector) :
    coefficientEnergy (tiltCoefficient chi u e q) = ‖pressureAmplitude chi u q‖ ^ 2 *
      ⟪realFrequency q, e⟫ ^ 2 * ‖lineRemainder e (realFrequency q)‖ ^ 2 := by
  change coefficientEnergy (fun i ↦ pressureAmplitude chi u q *
    (((⟪realFrequency q, e⟫ • lineRemainder e (realFrequency q)) i : ℝ) : ℂ)) = _
  rw [coefficientEnergy_real_multiple, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem fullEnergy_tiltCoefficient (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : R3) :
    fullEnergy outputs (tiltCoefficient chi u e) = angularEnergy chi outputs u e := by
  simp only [fullEnergy, coefficientEnergy_tiltCoefficient, angularEnergy]

theorem transverse_pressure_eq_real_reconstruction (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) (e : R3) :
    lineRemainder e (filteredPressureOperator chi outputs u x e) =
      complexRealPartEuclidean (finiteFourierReconstruction outputs (tiltCoefficient chi u e) x) := by
  rw [transverse_filteredPressure_eq_sum]
  ext i
  simp only [WithLp.ofLp_sum, PiLp.smul_apply, smul_eq_mul,
    complexRealPartEuclidean, PiLp.toLp_apply, finiteFourierReconstruction,
    Finset.sum_apply, Pi.smul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [tiltCoefficient, pressureModeAmplitude, pressureAmplitude,
    Complex.ofReal_mul, ← mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem continuous_transverse_pressure (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : R3) :
    Continuous (fun x ↦ lineRemainder e (filteredPressureOperator chi outputs u x e)) := by
  simp_rw [transverse_pressure_eq_real_reconstruction]
  exact complexRealPartEuclideanCLM.continuous.comp (continuous_finiteFourierReconstruction _ _)

theorem integral_transverse_pressure_sq_le_angularEnergy (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : R3) :
    (∫ x : T3, ‖lineRemainder e (filteredPressureOperator chi outputs u x e)‖ ^ 2) ≤
      angularEnergy chi outputs u e := by
  simp_rw [transverse_pressure_eq_real_reconstruction]
  rw [← fullEnergy_tiltCoefficient]
  exact integral_real_reconstruction_energy_le outputs (tiltCoefficient chi u e)

theorem angularEnergy_eq (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : R3) (he : ‖e‖ = 1) :
    angularEnergy chi outputs u e = ∑ q ∈ outputs,
      ‖pressureAmplitude chi u q‖ ^ 2 * ⟪realFrequency q, e⟫ ^ 2 *
        (‖realFrequency q‖ ^ 2 - ⟪realFrequency q, e⟫ ^ 2) := by
  simp only [angularEnergy, norm_lineRemainder_sq _ _ he, real_inner_comm e]

theorem angularEnergy_nonneg (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : R3) : 0 ≤ angularEnergy chi outputs u e := by
  unfold angularEnergy
  exact Finset.sum_nonneg (fun _ _ ↦ by positivity)

theorem angularEnergy_le_quarter_hessianEnergy (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : R3) (he : ‖e‖ = 1) :
    angularEnergy chi outputs u e ≤ (1 / 4 : ℝ) * hessianEnergy chi outputs u := by
  rw [angularEnergy_eq chi outputs u e he, hessianEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  have h : ⟪realFrequency q, e⟫ ^ 2 * (‖realFrequency q‖ ^ 2 - ⟪realFrequency q, e⟫ ^ 2) ≤
      ‖realFrequency q‖ ^ 4 / 4 := by
    nlinarith only [sq_nonneg (‖realFrequency q‖ ^ 2 - 2 * ⟪realFrequency q, e⟫ ^ 2)]
  have h' := mul_le_mul_of_nonneg_left h (sq_nonneg ‖pressureAmplitude chi u q‖)
  nlinarith only [h']

/-- A longitudinal cone restriction gives a squared angular gain. This
frequency restriction is an explicit hypothesis, not inferred from alignment. -/
theorem angularEnergy_le_of_longitudinal_bound (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : R3) (he : ‖e‖ = 1) (eta : ℝ)
    (hcone : ∀ q ∈ outputs, ‖pressureAmplitude chi u q‖ ≠ 0 →
      ⟪realFrequency q, e⟫ ^ 2 ≤ eta ^ 2 * ‖realFrequency q‖ ^ 2) :
    angularEnergy chi outputs u e ≤ eta ^ 2 * hessianEnergy chi outputs u := by
  rw [angularEnergy, hessianEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  by_cases hz : ‖pressureAmplitude chi u q‖ = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, le_refl]
  · have hm := pow_le_pow_left₀ (norm_nonneg _) (norm_lineRemainder_le e (realFrequency q) he) 2
    have h := mul_le_mul (hcone q hq hz) hm (sq_nonneg _) (by positivity)
    have h' := mul_le_mul_of_nonneg_left h (sq_nonneg ‖pressureAmplitude chi u q‖)
    nlinarith only [h']

end Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltEnergy
