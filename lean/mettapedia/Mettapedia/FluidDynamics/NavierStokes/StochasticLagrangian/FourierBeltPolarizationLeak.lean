import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierSingleBeltStretch
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFilteredEquation

/-!
# Axial velocity created from planar input modes

Two transverse, exactly planar velocity modes can create an almost axial
velocity at their sum frequency through the Leray pressure correction.
The four-mode datum includes the conjugate input modes, so it is real.
The calculation concerns the actual infinite unforced Fourier right-hand
side at that datum. It does not assert an invariant finite support or a
failure of a weighted remainder budget.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierBeltPolarizationLeak

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
  PancakeFrequencyProjectorCommutator PancakeGalerkinKineticEnergy
  PancakePeriodicVorticityEquation PancakeInfinitePressureCoefficients
  InfiniteFilteredEquation PancakeCoefficientLimitEquation

def firstMode (L : ℤ) : Wavevector := ![L, 0, 1]
def secondMode (L : ℤ) : Wavevector := ![0, L, 1]
def outputMode (L : ℤ) : Wavevector := ![L, L, 2]
def inputModes (L : ℤ) : Finset Wavevector :=
  {firstMode L, -firstMode L, secondMode L, -secondMode L}

/-- The positive and negative coefficients agree and are real. -/
def velocity (L : ℤ) : FourierVelocity := fun k ↦
  if k = firstMode L ∨ k = -firstMode L then ![0, 1, 0]
  else if k = secondMode L ∨ k = -secondMode L then ![1, 0, 0] else 0

theorem velocity_supported (L : ℤ) (k : Wavevector) (hk : k ∉ inputModes L) :
    velocity L k = 0 := by
  simp only [inputModes, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  simp [velocity, hk]

theorem velocity_axial_zero (L : ℤ) (k : Wavevector) : velocity L k 2 = 0 := by
  unfold velocity
  split_ifs <;> rfl

theorem velocity_reality (L : ℤ) (k : Wavevector) :
    velocity L (-k) = fun i ↦ conj (velocity L k i) := by
  have he : velocity L (-k) = velocity L k := by
    simp only [velocity, neg_eq_iff_eq_neg, neg_neg, or_comm]
  rw [he]
  unfold velocity
  split_ifs <;> ext i <;> fin_cases i <;> simp

theorem velocity_transverse (L : ℤ) (k : Wavevector) : modeDot k (velocity L k) = 0 := by
  unfold velocity
  split_ifs with h h
  · rcases h with rfl | rfl <;> simp [modeDot, firstMode, Fin.sum_univ_three]
  · rcases h with rfl | rfl <;> simp [modeDot, secondMode, Fin.sum_univ_three]
  · simp [modeDot]

theorem input_nonzero (L : ℤ) (k : Wavevector) (hk : k ∈ inputModes L) : k ≠ 0 := by
  simp only [inputModes, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp [firstMode, secondMode, funext_iff, Fin.forall_fin_succ]

theorem velocity_output_zero (L : ℤ) : velocity L (outputMode L) = 0 := by
  simp [velocity, outputMode, firstMode, secondMode, funext_iff, Fin.forall_fin_succ]

theorem convection_output (L : ℤ) (hL : L ≠ 0) :
    convectionConvolution (inputModes L) (velocity L) (outputMode L) =
      ![(L : ℂ), (L : ℂ), 0] := by
  ext i
  fin_cases i <;>
    simp [convectionConvolution, orderedConvection, modeDot, inputModes, velocity,
      firstMode, secondMode, outputMode, funext_iff, Fin.forall_fin_succ,
      Fin.sum_univ_three, hL]

/-- The pressure projection makes the newly created coefficient almost axial. -/
theorem leray_output (L : ℤ) :
    lerayMode (outputMode L) ![(L : ℂ), (L : ℂ), 0] =
      ![2 * (L : ℂ) / ((L : ℂ) ^ 2 + 2),
        2 * (L : ℂ) / ((L : ℂ) ^ 2 + 2),
        -2 * (L : ℂ) ^ 2 / ((L : ℂ) ^ 2 + 2)] := by
  have hd : (L : ℂ) ^ 2 + 2 ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < (L : ℝ) ^ 2 + 2).ne'
  have he : modeSquare (outputMode L) = 2 * ((L : ℂ) ^ 2 + 2) := by
    simp [modeSquare, outputMode, Fin.sum_univ_three]
    ring
  have hsq : modeSquare (outputMode L) ≠ 0 := by
    rw [he]
    exact mul_ne_zero (by norm_num) hd
  simp only [lerayMode, hsq, ↓reduceDIte]
  rw [he]
  ext i
  fin_cases i <;> simp [modeDot, outputMode, Fin.sum_univ_three] <;>
    field_simp <;> ring

/-- The actual unforced right-hand side at the absent output has no viscous contribution. -/
theorem infinite_rhs_output (L : ℤ) (hL : L ≠ 0) (ν : ℝ) :
    infiniteVelocityRHS ν (velocity L) (outputMode L) =
      (-unitTorusDerivativePhase) •
        ![2 * (L : ℂ) / ((L : ℂ) ^ 2 + 2),
          2 * (L : ℂ) / ((L : ℂ) ^ 2 + 2),
          -2 * (L : ℂ) ^ 2 / ((L : ℂ) ^ 2 + 2)] := by
  rw [infiniteVelocityRHS_eq_finite (inputModes L) (velocity L)
    (velocity_supported L) (fun k hk ↦ frequencyVec_ne_zero (input_nonzero L k hk))
    (fun k _ ↦ velocity_transverse L k) ν (outputMode L)]
  rw [velocityRHS, finiteTransport_fourierCurl_eq (inputModes L) (velocity L)
    (fun k hk ↦ frequencyVec_ne_zero (input_nonzero L k hk))
    (fun k _ ↦ velocity_transverse L k), convection_output L hL,
    lerayMode_smul, leray_output]
  simp [unitTorusViscousVorticityCoeff, velocity_output_zero]

/-- Exact axial polarization is not preserved by the unforced Fourier vector field. -/
theorem rhs_axial_ne_zero (L : ℤ) (hL : L ≠ 0) (ν : ℝ) :
    infiniteVelocityRHS ν (velocity L) (outputMode L) 2 ≠ 0 := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hd : (L : ℂ) ^ 2 + 2 ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < (L : ℝ) ^ 2 + 2).ne'
  rw [infinite_rhs_output L hL ν]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two]
  exact mul_ne_zero (neg_ne_zero.mpr unitTorusDerivativePhase_ne_zero)
    (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hLc)) hd)

/-- The created velocity points along `(1,1,-L)`, independently of viscosity and phase. -/
def sourceDirection (L : ℤ) : VelocityCoefficient := ![1, 1, -(L : ℂ)]

theorem infinite_rhs_output_factored (L : ℤ) (hL : L ≠ 0) (ν : ℝ) :
    infiniteVelocityRHS ν (velocity L) (outputMode L) =
      ((-unitTorusDerivativePhase) * (2 * (L : ℂ) / ((L : ℂ) ^ 2 + 2))) •
        sourceDirection L := by
  rw [infinite_rhs_output L hL ν]
  ext i
  fin_cases i
  · simp [sourceDirection]
  · simp [sourceDirection]
  · simp [sourceDirection]
    ring

theorem sourceDirection_axial_energy (L : ℤ) (c : ℂ) :
    Complex.normSq ((c • sourceDirection L) 2) * ((L : ℝ) ^ 2 + 2) =
      (L : ℝ) ^ 2 * coefficientEnergy (c • sourceDirection L) := by
  rw [PancakeViscousMisalignmentAbsorption.coefficientEnergy_smul,
    ← Complex.normSq_eq_norm_sq]
  simp [sourceDirection, coefficientEnergy, Fin.sum_univ_three, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

/-- The squared axial fraction is `L²/(L²+2)`, expressed without a division by energy. -/
theorem rhs_axial_energy_identity (L : ℤ) (hL : L ≠ 0) (ν : ℝ) :
    Complex.normSq (infiniteVelocityRHS ν (velocity L) (outputMode L) 2) *
        ((L : ℝ) ^ 2 + 2) =
      (L : ℝ) ^ 2 * coefficientEnergy (infiniteVelocityRHS ν (velocity L) (outputMode L)) := by
  rw [infinite_rhs_output_factored L hL ν]
  exact sourceDirection_axial_energy L _

end Mettapedia.FluidDynamics.NavierStokes.FourierBeltPolarizationLeak
