import MettapediaNS.WholeSpacePressure
import NavierStokes.R3.PressureRecoveryHelpers
import NavierStokes.R3.PressureFunctionals
import NavierStokes.R3.RieszTestOperators
import NavierStokes.R3.HarmonicTestFunctionals
import Euler.MeanVectorIdentities

/-!
# Riesz test representation of the constructed Helmholtz pressure

The pressure is the upstream Helmholtz pressure of a smooth solenoidal
velocity. To reuse the upstream instantaneous pressure identities, an affine
time extension realizes the viscous right-hand side as a tangent at time one.
This extension is not asserted to solve Navier–Stokes at any other time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureRecovery

open MeasureTheory EulerLpTranslation EulerOrdinarySobolev
  EulerLpTranslation.SmoothL2Field WholeSpaceViscousEnergy
open EulerSmoothLimit (divergence divergence_eq_coordinate_sum)
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokesR3 ConservativeDifference PressureRecovery
open NavierStokesR3.Comparison (ComplexTest pressurePair)
open NavierStokesR3.HarmonicTestFunctionals (partialCLM laplacianCLM)
open scoped ContDiff

/-- An affine tangent extension, not an evolution theorem. -/
def velocityTangent (A : SmoothL2Field Space) : VelocityField :=
  fun z ↦ A.field z.2 + (z.1 - 1) • (projectedNavierStokesRhs 1 A).field z.2

theorem contDiff_velocityTangent (A : SmoothL2Field Space) :
    ContDiff ℝ ∞ (velocityTangent A) :=
  (A.smooth.comp contDiff_snd).add
    ((contDiff_fst.sub contDiff_const).smul
      ((projectedNavierStokesRhs 1 A).smooth.comp contDiff_snd))

@[simp] theorem velocityTangent_one (A : SmoothL2Field Space) (x : Space) :
    velocityTangent A (1, x) = A.field x := by simp [velocityTangent]

theorem temporalDerivative_velocityTangent (A : SmoothL2Field Space) (t : ℝ) (x : Space) :
    temporalDerivative (velocityTangent A) t x =
      (projectedNavierStokesRhs 1 A).field x := by
  have h := (((hasDerivAt_id t).sub_const 1).smul_const
    ((projectedNavierStokesRhs 1 A).field x)).const_add (A.field x)
  simpa only [temporalDerivative, velocityTangent, deriv, one_smul, id_eq] using h.deriv

theorem spatialDivergence_velocityTangent (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) (t : ℝ) (x : Space) :
    spatialDivergence (velocityTangent A) t x = 0 := by
  have hB := divergence_projectedNavierStokesRhs_eq_zero 1 A hdiv x
  rw [divergence_eq_coordinate_sum] at hB
  have hA := hdiv x
  rw [divergence_eq_coordinate_sum] at hA
  simp only [spatialDivergence, spatialDerivative, velocityTangent]
  rw [fderiv_fun_add (g := fun y ↦ (t - 1) • (projectedNavierStokesRhs 1 A).field y)
    (A.smooth.differentiable (by simp) x)
    (((projectedNavierStokesRhs 1 A).smooth.differentiable (by simp) x).const_smul (t - 1)),
    fderiv_fun_const_smul ((projectedNavierStokesRhs 1 A).smooth.differentiable (by simp) x)]
  simp only [_root_.add_apply, _root_.smul_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, coordinateVector, hA, hB, mul_zero, add_zero]

theorem pressurePotential_partial (A : SmoothL2Field Space) (k : Fin 3) (x : Space) :
    spatialPartial k (pressurePotential A) x = (pressureField A).field x k := by
  rw [← (pressurePotential_spec A).2.2 x]
  exact (EulerMeanHarmonic.gradient_coordinate (pressurePotential A) x k).symm

/-- The tangent realizes the unit-viscosity equation only at its center. -/
theorem navierStokesResidual_velocityTangent_one (A : SmoothL2Field Space) (x : Space) :
    navierStokesResidual (velocityTangent A) (fun z ↦ pressurePotential A z.2) 1 x = 0 := by
  have hslice : (fun y ↦ velocityTangent A (1, y)) = A.field :=
    funext (velocityTangent_one A)
  have hΔ : spatialLaplacian (velocityTangent A) 1 x =
      Laplacian.laplacian A.field x := by
    simp only [spatialLaplacian, spatialDerivative, hslice]
    exact (congrFun (EulerMeanVectorIdentities.vector_laplacian_eq_sum A.field A.smooth) x).symm
  have hP : pressureGradient (fun z ↦ pressurePotential A z.2) 1 x =
      _root_.gradient (pressurePotential A) x := by
    change (∑ i : Fin 3, spatialPartial i (pressurePotential A) x • coordinateVector i) = _
    simp only [pressurePotential_partial]
    rw [NavierStokes.PeriodicUniqueness.sum_coordinates, (pressurePotential_spec A).2.2 x]
  rw [navierStokesResidual, temporalDerivative_velocityTangent, hΔ, hP,
    projectedNavierStokesRhs_field]
  simp only [advection, spatialDerivative, velocityTangent_one, one_smul]
  abel

/-- Compact weak gradient identity for the actual constructed pressure. -/
theorem integral_pressureField_mul (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, (pressureField A).field x k * ψ x) =
      (∫ x, A.field x k * scalarLaplacian ψ x) -
      (∫ x, (projectedNavierStokesRhs 1 A).field x k * ψ x) +
      ∑ i : Fin 3, ∫ x, A.field x k * A.field x i * spatialPartial i ψ x := by
  have h := weak_pressure_gradient_on_slab
    (a := 0) (b := 2) (t := 1) (u := velocityTangent A) (v := fun _ ↦ 0)
    (p := fun z ↦ pressurePotential A z.2) (q := fun _ ↦ 0)
    (contDiff_velocityTangent A).contDiffOn contDiff_const.contDiffOn
    ((pressurePotential_spec A).1.comp contDiff_snd).contDiffOn contDiff_const.contDiffOn
    (by constructor <;> norm_num) (spatialDivergence_velocityTangent A hdiv 1)
    (by intro x; simp [spatialDivergence, spatialDerivative])
    (by intro x; rw [zero_residual]; exact navierStokesResidual_velocityTangent_one A x)
    hψ hcψ k
  simpa only [← Pi.zero_def, sub_zero, Pi.sub_apply, Pi.zero_apply, PiLp.zero_apply, velocityTangent_one,
    temporalDerivative_velocityTangent, pressurePotential_partial,
    Comparison.tensorDiff, mul_zero] using h

/-- The differentiated Poisson identity uses the same upstream instantaneous
equation theorem; it does not require a Navier–Stokes trajectory. -/
theorem integral_pressureField_mul_laplacian (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    (∫ x, (pressureField A).field x k * scalarLaplacian ψ x) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, A.field x i * A.field x j *
        spatialPartial i (spatialPartial j (spatialPartial k ψ)) x := by
  have h := gradient_poisson_test
    (T := 2) (t := 1) (u := velocityTangent A) (v := fun _ ↦ 0)
    (p := fun z ↦ pressurePotential A z.2) (q := fun _ ↦ 0)
    (contDiff_velocityTangent A).contDiffOn contDiff_const.contDiffOn
    ((pressurePotential_spec A).1.comp contDiff_snd).contDiffOn contDiff_const.contDiffOn
    (by constructor <;> norm_num) (fun t _ ↦ spatialDivergence_velocityTangent A hdiv t)
    (by intro t _ x; simp [spatialDivergence, spatialDerivative])
    (by intro x; rw [zero_residual]; exact navierStokesResidual_velocityTangent_one A x)
    hψ hcψ k
  simpa only [Pi.sub_apply, sub_zero, pressurePotential_partial, PiLp.zero_apply,
    Comparison.tensorDiff, velocityTangent_one, mul_zero] using h

private abbrev pressureDifference (A : SmoothL2Field Space) (k : Fin 3) :
    ComplexTest →ₗ[ℂ] ℂ :=
  PressureFunctionals.averagedPressureDifference (fun x ↦ A.field x k)
    (fun x ↦ -(projectedNavierStokesRhs 1 A).field x k)
    (fun i j x ↦ A.field x i * A.field x j)
    (componentField A k).memLp (componentField (projectedNavierStokesRhs 1 A) k).memLp.neg
    (fun i j ↦ (componentField A i).memLp.integrable_mul (componentField A j).memLp) k

set_option backward.isDefEq.respectTransparency.types false in
private theorem pressureDifference_realTest (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    pressureDifference A k (realTest ψ hψ hcψ) =
      ((∫ x, (pressureField A).field x k * ψ x : ℝ) : ℂ) +
      ∑ i : Fin 3, ∑ j : Fin 3,
        pressurePair i j (fun x ↦ A.field x i * A.field x j)
          (partialCLM k (realTest ψ hψ hcψ)) := by
  change PressureFunctionals.averagedPressureDifferenceValue (fun x ↦ A.field x k)
    (fun x ↦ -(projectedNavierStokesRhs 1 A).field x k)
    (fun i j x ↦ A.field x i * A.field x j) k (realTest ψ hψ hcψ) = _
  unfold PressureFunctionals.averagedPressureDifferenceValue
  simp only [laplacianCLM_realTest,
    partialCLM_realTest, realTest_apply, ← Complex.ofReal_mul, integral_complex_ofReal,
    neg_mul, integral_neg, Complex.ofReal_neg]
  congr 1
  simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_sum, sub_eq_add_neg,
    Complex.ofReal_neg] using
    congrArg Complex.ofReal (integral_pressureField_mul A hdiv ψ hψ hcψ k).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem pressureDifference_laplacian_realTest (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    pressureDifference A k (laplacianCLM (realTest ψ hψ hcψ)) = 0 := by
  have hp := pressureDifference_realTest A hdiv (scalarLaplacian ψ)
    (scalarLaplacian_contDiff hψ) (compact_scalarLaplacian hcψ) k
  rw [← laplacianCLM_realTest ψ hψ hcψ] at hp
  rw [hp]
  simp only [partial_laplacian_realTest, RieszTestOperators.pressurePair_laplacianCLM,
    Finset.sum_neg_distrib, partialCLM_realTest, realTest_apply,
    ← Complex.ofReal_mul, integral_complex_ofReal, ← Complex.ofReal_sum]
  rw [integral_pressureField_mul_laplacian A hdiv ψ hψ hcψ k, add_neg_cancel]

/-- OpenAI's Fourier `H³` bound and harmonic uniqueness identify the constructed
pressure with its Riesz representation; neither result is reproved here. -/
private theorem pressureDifference_eq_zero (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) (k : Fin 3) : pressureDifference A k = 0 := by
  obtain ⟨C, hC, hb⟩ := PressureFunctionals.averagedPressureDifference_bound
    (componentField A k).memLp (componentField (projectedNavierStokesRhs 1 A) k).memLp.neg
    (fun i j ↦ (componentField A i).memLp.integrable_mul (componentField A j).memLp) k
  apply HarmonicTestFunctionals.eq_zero_of_compact_harmonic (pressureDifference A k) hC hb
  apply compact_harmonic_of_real
  intro ψ hψ hcψ
  exact pressureDifference_laplacian_realTest A hdiv ψ hψ hcψ k

/-- The actual Helmholtz pressure gradient paired with any compact real test
equals the differentiated double-Riesz pairing of the actual velocity tensor. -/
theorem integral_pressureField_mul_eq_rieszPair (A : SmoothL2Field Space)
    (hdiv : ∀ x, divergence A.field x = 0) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (k : Fin 3) :
    ((∫ x, (pressureField A).field x k * ψ x : ℝ) : ℂ) =
      -(∑ i : Fin 3, ∑ j : Fin 3,
        pressurePair i j (fun x ↦ A.field x i * A.field x j)
          (partialCLM k (realTest ψ hψ hcψ))) := by
  have h := pressureDifference_realTest A hdiv ψ hψ hcψ k
  rw [pressureDifference_eq_zero A hdiv k, LinearMap.zero_apply] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end Mettapedia.FluidDynamics.NavierStokes.WholeSpacePressureRecovery
