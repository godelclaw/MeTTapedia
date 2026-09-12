import Mettapedia.FluidDynamics.NavierStokes.VectorCalculusR3Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Stretching production in an unforced Navier--Stokes initial jet

The periodic datum `u₀(x,y,z) = (sin y, 0, sin x)` has zero vorticity
stretching everywhere. Its Navier--Stokes initial acceleration, with zero
pressure, is `(-ν sin y, 0, -sin y cos x - ν sin x)`.

The affine time jet constructed here satisfies the full unforced momentum
equation at time zero. Curl and velocity gradient are differentiated from
that same jet. The eighth-moment stretching density has initial derivative
`(cos² x + cos² y)³ cos² x cos² y`, independently of viscosity.

This is an initial-jet test, not a claim that the affine path solves the
equation at positive times. Positive initial production rules out a
zero-source differential damping law for NS-compatible jets. It does not
rule out a quantitative integrated stretching budget or imply blowup.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.TwoShearStretchingJet

open Real
open scoped RealInnerProductSpace Laplacian ContDiff

private abbrev basis (i : Fin 3) : NSSpace := EuclideanSpace.single i 1

private def coordinateMap (i j : Fin 3) : NSSpace →L[ℝ] NSSpace :=
  (EuclideanSpace.proj j).smulRight (basis i)

private theorem coordinateMap_apply (i j : Fin 3) (v : NSSpace) :
    coordinateMap i j v = v j • basis i := rfl

/-- The affine path with the initial derivative prescribed by the NS equation. -/
def velocity (ν t : ℝ) (x : NSSpace) : NSSpace :=
  ((1 - ν * t) * sin (x 1)) • basis 0 +
    ((1 - ν * t) * sin (x 0) - t * sin (x 1) * cos (x 0)) • basis 2

/-- The explicit gradient, subsequently identified with the actual derivative. -/
def velocityGradient (ν t : ℝ) (x : NSSpace) : NSSpace →L[ℝ] NSSpace :=
  ((1 - ν * t) * cos (x 1)) • coordinateMap 0 1 +
    ((1 - ν * t) * cos (x 0) + t * sin (x 1) * sin (x 0)) • coordinateMap 2 0 -
    (t * cos (x 1) * cos (x 0)) • coordinateMap 2 1

private theorem hasFDerivAt_sin_coordinate (i : Fin 3) (x : NSSpace) :
    HasFDerivAt (fun y : NSSpace => sin (y i))
      (cos (x i) • (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ)) x := by
  have h : HasFDerivAt (fun y : NSSpace => y i)
      (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt
  exact h.sin

private theorem hasFDerivAt_cos_coordinate (i : Fin 3) (x : NSSpace) :
    HasFDerivAt (fun y : NSSpace => cos (y i))
      (-sin (x i) • (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ)) x := by
  have h : HasFDerivAt (fun y : NSSpace => y i)
      (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).hasFDerivAt
  exact h.cos

theorem hasFDerivAt_velocity (ν t : ℝ) (x : NSSpace) :
    HasFDerivAt (velocity ν t) (velocityGradient ν t x) x := by
  have h := (((hasFDerivAt_sin_coordinate 1 x).const_mul (1 - ν * t)).smul_const
      (basis 0)).add
    ((((hasFDerivAt_sin_coordinate 0 x).const_mul (1 - ν * t)).sub
      (((hasFDerivAt_sin_coordinate 1 x).const_mul t).mul
        (hasFDerivAt_cos_coordinate 0 x))).smul_const (basis 2))
  apply h.congr_fderiv
  ext v i
  fin_cases i <;>
    simp [velocityGradient, coordinateMap, basis, ContinuousLinearMap.smulRight_apply] <;> ring

theorem spatialFDeriv_velocity (ν t : ℝ) (x : NSSpace) :
    spatialFDeriv (velocity ν) t x = velocityGradient ν t x :=
  (hasFDerivAt_velocity ν t x).fderiv

theorem velocity_divergence_zero (ν t : ℝ) (x : NSSpace) :
    spatialDivergence (velocity ν) t x = 0 := by
  simp [spatialDivergence, spatialFDeriv_velocity, velocityGradient,
    coordinateMap, basis, Fin.sum_univ_three]

theorem velocity_periodic (ν t : ℝ) (x : NSSpace) (i : Fin 3) :
    velocity ν t (x + (2 * π) • basis i) = velocity ν t x := by
  fin_cases i <;> simp [velocity, basis, sin_add_two_pi, cos_add_two_pi]

theorem contDiff_velocity (ν t : ℝ) : ContDiff ℝ ∞ (velocity ν t) := by
  unfold velocity
  fun_prop

theorem smoothSpaceTimeVelocity_velocity (ν : ℝ) : smoothSpaceTimeVelocity (velocity ν) := by
  unfold smoothSpaceTimeVelocity spaceTimeVelocityMap velocity
  fun_prop

/-- Actual curl, evaluated from the spatial Fréchet derivative. -/
theorem spatialVorticity_velocity (ν t : ℝ) (x : NSSpace) :
    spatialVorticity (velocity ν) t x =
      (-t * cos (x 1) * cos (x 0)) • basis 0 +
      (-(1 - ν * t) * cos (x 0) - t * sin (x 1) * sin (x 0)) • basis 1 +
      (-(1 - ν * t) * cos (x 1)) • basis 2 := by
  ext i
  fin_cases i <;>
    simp [spatialVorticity, spatialDerivativeComponent, spatialFDeriv_velocity,
      velocityGradient, coordinateMap, basis, nsCoord0, nsCoord1, nsCoord2] <;> ring

theorem hasDerivAt_velocity (ν t : ℝ) (x : NSSpace) :
    HasDerivAt (fun s => velocity ν s x)
      ((-ν * sin (x 1)) • basis 0 +
        (-ν * sin (x 0) - sin (x 1) * cos (x 0)) • basis 2) t := by
  have h := ((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).const_mul ν)).mul_const
      (sin (x 1))).smul_const (basis 0)).add
    (((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).const_mul ν)).mul_const
      (sin (x 0))).sub (((hasDerivAt_id t).mul_const (sin (x 1))).mul_const
        (cos (x 0)))).smul_const (basis 2))
  convert! h using 1
  simp

theorem spatialLaplacian_velocity_zero (ν : ℝ) (x : NSSpace) :
    spatialLaplacian (velocity ν) 0 x = -velocity ν 0 x := by
  have hgrad : fderiv ℝ (velocity ν 0) = fun y =>
      cos (y 1) • coordinateMap 0 1 + cos (y 0) • coordinateMap 2 0 := by
    funext y
    rw [(hasFDerivAt_velocity ν 0 y).fderiv]
    ext v i
    simp [velocityGradient, coordinateMap, basis]
  have hd := ((hasFDerivAt_cos_coordinate 1 x).smul_const (coordinateMap 0 1)).add
    ((hasFDerivAt_cos_coordinate 0 x).smul_const (coordinateMap 2 0))
  have hd' : HasFDerivAt (fun y : NSSpace =>
      cos (y 1) • coordinateMap 0 1 + cos (y 0) • coordinateMap 2 0)
      (((-sin (x 1)) • (EuclideanSpace.proj 1 : NSSpace →L[ℝ] ℝ)).smulRight
        (coordinateMap 0 1) +
       ((-sin (x 0)) • (EuclideanSpace.proj 0 : NSSpace →L[ℝ] ℝ)).smulRight
        (coordinateMap 2 0)) x := by convert! hd using 1
  unfold spatialLaplacian
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (velocity ν 0) (EuclideanSpace.basisFun (Fin 3) ℝ)) x]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    hgrad, hd'.fderiv]
  ext i
  fin_cases i <;>
    simp [Fin.sum_univ_three, EuclideanSpace.basisFun_apply, coordinateMap, basis,
      velocity]

/-- The full unforced momentum equation holds at the initial time, with
identically zero pressure. No pressure or nonlinear-convection term is omitted. -/
theorem momentum_equation_zero (ν : ℝ) (x : NSSpace) :
    timeVelocityDerivative (velocity ν) 0 x + spatialConvection (velocity ν) 0 x +
      spatialPressureGradient (0 : NSPressureField) 0 x =
        ν • spatialLaplacian (velocity ν) 0 x := by
  have ht : timeVelocityDerivative (velocity ν) 0 x =
      (-ν * sin (x 1)) • basis 0 +
        (-ν * sin (x 0) - sin (x 1) * cos (x 0)) • basis 2 := by
    simpa [timeVelocityDerivative, timeFDeriv, hasDerivAt_iff_hasFDerivAt] using
      congrArg (fun L : ℝ →L[ℝ] NSSpace => L 1) (hasDerivAt_velocity ν 0 x).hasFDerivAt.fderiv
  rw [ht, spatialLaplacian_velocity_zero]
  ext i
  fin_cases i <;>
    simp [spatialConvection, spatialFDeriv_velocity, velocityGradient, coordinateMap,
      basis, velocity, spatialPressureGradient]
  all_goals ring

/-- The physical eighth-moment stretching density `|curl u|⁶ curl u · Du(curl u)`. -/
def eighthStretchingDensity (ν t : ℝ) (x : NSSpace) : ℝ :=
  ‖spatialVorticity (velocity ν) t x‖ ^ 6 *
    ⟪spatialVorticity (velocity ν) t x,
      spatialFDeriv (velocity ν) t x (spatialVorticity (velocity ν) t x)⟫

/-- A polynomial expression for the squared norm of the actual curl. -/
def vorticityNormSq (ν t : ℝ) (x : NSSpace) : ℝ :=
  (t * cos (x 1) * cos (x 0)) ^ 2 +
  ((1 - ν * t) * cos (x 0) + t * sin (x 1) * sin (x 0)) ^ 2 +
  ((1 - ν * t) * cos (x 1)) ^ 2

theorem norm_spatialVorticity_sq (ν t : ℝ) (x : NSSpace) :
    ‖spatialVorticity (velocity ν) t x‖ ^ 2 = vorticityNormSq ν t x := by
  rw [← real_inner_self_eq_norm_sq, spatialVorticity_velocity]
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_three, basis, vorticityNormSq]
  ring

theorem stretching_power (ν t : ℝ) (x : NSSpace) :
    ⟪spatialVorticity (velocity ν) t x,
      spatialFDeriv (velocity ν) t x (spatialVorticity (velocity ν) t x)⟫ =
        t * (1 - ν * t) * cos (x 1) ^ 2 * cos (x 0) *
          ((1 - ν * t) * cos (x 0) + t * sin (x 1) * sin (x 0)) := by
  rw [spatialVorticity_velocity, spatialFDeriv_velocity]
  simp [velocityGradient, coordinateMap, PiLp.inner_apply, Fin.sum_univ_three, basis]
  ring

theorem eighthStretchingDensity_eq (ν t : ℝ) (x : NSSpace) :
    eighthStretchingDensity ν t x = t *
      (vorticityNormSq ν t x ^ 3 * (1 - ν * t) * cos (x 1) ^ 2 * cos (x 0) *
        ((1 - ν * t) * cos (x 0) + t * sin (x 1) * sin (x 0))) := by
  unfold eighthStretchingDensity
  rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, norm_spatialVorticity_sq,
    stretching_power]
  ring

@[simp] theorem eighthStretchingDensity_zero (ν : ℝ) (x : NSSpace) :
    eighthStretchingDensity ν 0 x = 0 := by
  simp [eighthStretchingDensity_eq]

/-- Despite identically zero initial stretching, its initial rate is
nonnegative and not identically zero, for every viscosity. -/
theorem hasDerivAt_eighthStretchingDensity_zero (ν : ℝ) (x : NSSpace) :
    HasDerivAt (fun t => eighthStretchingDensity ν t x)
      ((cos (x 0) ^ 2 + cos (x 1) ^ 2) ^ 3 * cos (x 0) ^ 2 * cos (x 1) ^ 2) 0 := by
  let g : ℝ → ℝ := fun t =>
    vorticityNormSq ν t x ^ 3 * (1 - ν * t) * cos (x 1) ^ 2 * cos (x 0) *
      ((1 - ν * t) * cos (x 0) + t * sin (x 1) * sin (x 0))
  have hg : DifferentiableAt ℝ g 0 := by dsimp [g, vorticityNormSq]; fun_prop
  have h := (hasDerivAt_id (0 : ℝ)).mul hg.hasDerivAt
  change HasDerivAt (fun t => t * g t) (1 * g 0 + 0 * deriv g 0) 0 at h
  have heq : (fun t => t * g t) = fun t => eighthStretchingDensity ν t x := by
    funext t
    exact (eighthStretchingDensity_eq ν t x).symm
  rw [heq] at h
  convert h using 1
  simp [g, vorticityNormSq]
  ring

theorem initial_density_rate_nonneg (ν : ℝ) (x : NSSpace) :
    0 ≤ deriv (fun t => eighthStretchingDensity ν t x) 0 := by
  rw [(hasDerivAt_eighthStretchingDensity_zero ν x).deriv]
  positivity

theorem initial_density_rate_origin (ν : ℝ) :
    deriv (fun t => eighthStretchingDensity ν t 0) 0 = 8 := by
  rw [(hasDerivAt_eighthStretchingDensity_zero ν 0).deriv]
  norm_num

/-- No multiplicative damping coefficient can bound this rate by the
initial density, which is zero. This tests the initial-jet law only. -/
theorem not_initial_multiplicative_damping (ν b : ℝ) :
    ¬ deriv (fun t => eighthStretchingDensity ν t 0) 0 ≤
      b * eighthStretchingDensity ν 0 0 := by
  rw [initial_density_rate_origin, eighthStretchingDensity_zero]
  norm_num

end Mettapedia.FluidDynamics.NavierStokes.TwoShearStretchingJet
