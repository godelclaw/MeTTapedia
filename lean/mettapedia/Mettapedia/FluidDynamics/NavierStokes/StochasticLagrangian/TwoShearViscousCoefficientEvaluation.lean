import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousData
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.RationalStretchingFlux

/-!
# Exact evaluation of the constructed two-shear coefficients

The finite support is enumerated without duplicate modes. Coefficient
identities below refer to the actual collected cubic flux and retain
the physical unit-torus derivative factors.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousCoefficientEvaluation

open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation
open PancakeInfiniteFourierDerivative PancakeDyadicDirectionEvolution
open PeriodicGradientFluxTriple PeriodicGradientFluxSymbol PeriodicTensorParseval
open TwoShearViscousData StretchingFluxCoefficients
open RationalStretchingFlux

def rationalData (q : Wavevector) : RationalCoefficient :=
  ![if firstHorizontal q then -(q 1 : ℚ) * profile (q 2) / 2 else 0,
    if secondHorizontal q then -(q 0 : ℚ) * reflectedProfile (q 2) / 2 else 0, 0]

theorem imaginaryLift_rationalData : imaginaryLift rationalData = velocity := by
  ext q i
  fin_cases i <;> simp [imaginaryLift, rationalData, velocity] <;> split_ifs <;> push_cast <;> ring

theorem rationalData_supported (q : Wavevector) (hq : q ∉ modes) : rationalData q = 0 := by
  have h := supported q hq
  rw [← imaginaryLift_rationalData] at h
  ext i
  have hi := congrFun h i
  change Complex.I * (rationalData q i : ℂ) = 0 at hi
  exact_mod_cast (mul_eq_zero.mp hi).resolve_left Complex.I_ne_zero

theorem longitudinal_modes_eq : Finset.Icc (-3 : ℤ) 3 = {-3, -2, -1, 0, 1, 2, 3} := by decide

theorem sum_modes {E : Type*} [AddCommMonoid E] (f : Wavevector → E) :
    ∑ q ∈ modes, f q = ∑ h ∈ horizontalModes, ∑ k ∈ Finset.Icc (-3 : ℤ) 3, f ![h.1, h.2, k] := by
  classical
  rw [modes, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro a _ b _ h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    apply Prod.ext
    · exact Prod.ext h0 h1
    · exact h2

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2048 in
theorem rational_divergence_mode_zero_one_one :
    rationalDivergenceCoefficient modes rationalData ![0, 1, 1] = ![-429 / 1024, 0, 0] := by
  ext i
  fin_cases i <;>
    simp only [rationalDivergenceCoefficient, rationalFluxCoefficient, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Int.cast_zero, Int.cast_one, zero_mul, one_mul, zero_add]
    <;> simp_rw [sum_modes]
    <;> decide +kernel

theorem divergence_mode_zero_one_one :
    divergenceCoeff ![0, 1, 1] (fun j ↦ coefficients velocity j ![0, 1, 1]) =
      (Complex.I * (((2 * Real.pi : ℝ) : ℂ) ^ 4)) • ![-429 / 1024, 0, 0] := by
  rw [← imaginaryLift_rationalData]
  ext i
  rw [divergence_imaginaryLift modes rationalData rationalData_supported,
    rational_divergence_mode_zero_one_one]
  fin_cases i <;> simp

end Mettapedia.FluidDynamics.NavierStokes.TwoShearViscousCoefficientEvaluation
