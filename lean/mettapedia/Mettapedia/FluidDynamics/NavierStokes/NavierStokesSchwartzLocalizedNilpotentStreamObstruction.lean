import Mettapedia.FluidDynamics.NavierStokes.NavierStokesNilpotentShearObstruction
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesSchwartzLocalizedStreamFunction

/-!
# Localized Nilpotent Stream Obstruction

The linear nilpotent shear `u(x) = (x_1, x_2, 0)` has a proved nonzero
pressure-residual curl, but it is not a Schwartz velocity profile.  This file
localizes the scalar stream function
`phi(x) = x_1^2 / 2 - x_0 x_2` with the unit bump.  The stream-function
construction keeps the resulting profile divergence-free and Schwartz, while
the bump is identically one near the origin, so the stationary inviscid
pressure-residual curl at the origin is still the nilpotent one.

This is an obstruction for a concrete localized nonzero divergence-free
Schwartz candidate.  It does not claim an exact nonzero Navier-Stokes solution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Filter
open scoped ContDiff LineDeriv SchwartzMap Topology

/-- The scalar polynomial whose stream velocity is the nilpotent shear
`(x_1, x_2, 0)`. -/
def nilpotentStreamPolynomialScalar (x : NSSpace) : ℝ :=
  (2 : ℝ)⁻¹ • x nsCoord1 ^ (2 : ℕ) - x nsCoord0 * x nsCoord2

/-- Compactly supported scalar stream function obtained by multiplying the
nilpotent stream polynomial by the unit bump. -/
def nsLocalizedNilpotentStreamFunctionScalarFun (x : NSSpace) : ℝ :=
  nilpotentStreamPolynomialScalar x * nsUnitBumpScalar x

/-- The localized nilpotent stream function as a Schwartz scalar. -/
def nsLocalizedNilpotentStreamFunction : NSSchwartzScalar :=
  (nsUnitBumpScalar.hasCompactSupport.mul_left :
      HasCompactSupport nsLocalizedNilpotentStreamFunctionScalarFun).toSchwartzMap <| by
    change ContDiff ℝ ∞
      (fun x : NSSpace => nilpotentStreamPolynomialScalar x * nsUnitBumpScalar x)
    unfold nilpotentStreamPolynomialScalar
    exact
      (((((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).contDiff.pow 2).const_smul (2 : ℝ)⁻¹).sub
        (((EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ).contDiff).mul
          ((EuclideanSpace.proj nsCoord2 : NSSpace →L[ℝ] ℝ).contDiff))).mul
        nsUnitBumpScalar.contDiff)

theorem nsLocalizedNilpotentStreamFunction_apply (x : NSSpace) :
    nsLocalizedNilpotentStreamFunction x =
      nilpotentStreamPolynomialScalar x * nsUnitBumpScalar x :=
  rfl

theorem nilpotentStreamPolynomialScalar_fderiv_e1 (x : NSSpace) :
    fderiv ℝ nilpotentStreamPolynomialScalar x
        (EuclideanSpace.single nsCoord1 (1 : ℝ)) =
      x nsCoord1 := by
  let c0 : NSSpace → ℝ := fun y => y nsCoord0
  let c1 : NSSpace → ℝ := fun y => y nsCoord1
  let c2 : NSSpace → ℝ := fun y => y nsCoord2
  have hc0 : DifferentiableAt ℝ c0 x :=
    (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ).differentiableAt
  have hc1 : DifferentiableAt ℝ c1 x :=
    (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).differentiableAt
  have hc2 : DifferentiableAt ℝ c2 x :=
    (EuclideanSpace.proj nsCoord2 : NSSpace →L[ℝ] ℝ).differentiableAt
  change
    (fderiv ℝ
      ((fun y : NSSpace => (2 : ℝ)⁻¹ • c1 y ^ (2 : ℕ)) -
        fun y : NSSpace => c0 y * c2 y) x)
        (EuclideanSpace.single nsCoord1 (1 : ℝ)) =
      c1 x
  rw [fderiv_sub
    (f := fun y : NSSpace => (2 : ℝ)⁻¹ • c1 y ^ (2 : ℕ))
    (g := fun y : NSSpace => c0 y * c2 y)
    ((hc1.pow 2).const_smul (2 : ℝ)⁻¹) (hc0.mul hc2)]
  rw [fderiv_fun_const_smul
    (f := fun y : NSSpace => c1 y ^ (2 : ℕ)) (hc1.pow 2) (2 : ℝ)⁻¹]
  rw [fderiv_fun_pow 2 hc1]
  rw [fderiv_fun_mul hc0 hc2]
  have hc0_fderiv :
      fderiv ℝ c0 x =
        (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ) := by
    simpa [c0] using
      ((EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ).fderiv (x := x))
  have hc1_fderiv :
      fderiv ℝ c1 x =
        (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ) := by
    simpa [c1] using
      ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).fderiv (x := x))
  have hc2_fderiv :
      fderiv ℝ c2 x =
        (EuclideanSpace.proj nsCoord2 : NSSpace →L[ℝ] ℝ) := by
    simpa [c2] using
      ((EuclideanSpace.proj nsCoord2 : NSSpace →L[ℝ] ℝ).fderiv (x := x))
  rw [hc0_fderiv, hc1_fderiv, hc2_fderiv]
  simp [c0, c1, c2, nsCoord0, nsCoord1, nsCoord2]

theorem nilpotentStreamPolynomialScalar_fderiv_e0 (x : NSSpace) :
    fderiv ℝ nilpotentStreamPolynomialScalar x
        (EuclideanSpace.single nsCoord0 (1 : ℝ)) =
      -x nsCoord2 := by
  let c0 : NSSpace → ℝ := fun y => y nsCoord0
  let c1 : NSSpace → ℝ := fun y => y nsCoord1
  let c2 : NSSpace → ℝ := fun y => y nsCoord2
  have hc0 : DifferentiableAt ℝ c0 x :=
    (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ).differentiableAt
  have hc1 : DifferentiableAt ℝ c1 x :=
    (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).differentiableAt
  have hc2 : DifferentiableAt ℝ c2 x :=
    (EuclideanSpace.proj nsCoord2 : NSSpace →L[ℝ] ℝ).differentiableAt
  change
    (fderiv ℝ
      ((fun y : NSSpace => (2 : ℝ)⁻¹ • c1 y ^ (2 : ℕ)) -
        fun y : NSSpace => c0 y * c2 y) x)
        (EuclideanSpace.single nsCoord0 (1 : ℝ)) =
      -c2 x
  rw [fderiv_sub
    (f := fun y : NSSpace => (2 : ℝ)⁻¹ • c1 y ^ (2 : ℕ))
    (g := fun y : NSSpace => c0 y * c2 y)
    ((hc1.pow 2).const_smul (2 : ℝ)⁻¹) (hc0.mul hc2)]
  rw [fderiv_fun_const_smul
    (f := fun y : NSSpace => c1 y ^ (2 : ℕ)) (hc1.pow 2) (2 : ℝ)⁻¹]
  rw [fderiv_fun_pow 2 hc1]
  rw [fderiv_fun_mul hc0 hc2]
  have hc0_fderiv :
      fderiv ℝ c0 x =
        (EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ) := by
    simpa [c0] using
      ((EuclideanSpace.proj nsCoord0 : NSSpace →L[ℝ] ℝ).fderiv (x := x))
  have hc1_fderiv :
      fderiv ℝ c1 x =
        (EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ) := by
    simpa [c1] using
      ((EuclideanSpace.proj nsCoord1 : NSSpace →L[ℝ] ℝ).fderiv (x := x))
  have hc2_fderiv :
      fderiv ℝ c2 x =
        (EuclideanSpace.proj nsCoord2 : NSSpace →L[ℝ] ℝ) := by
    simpa [c2] using
      ((EuclideanSpace.proj nsCoord2 : NSSpace →L[ℝ] ℝ).fderiv (x := x))
  rw [hc0_fderiv, hc1_fderiv, hc2_fderiv]
  simp [c0, c1, c2, nsCoord0, nsCoord1, nsCoord2]

/-- Near the origin the localized scalar stream function is the underlying
nilpotent stream polynomial. -/
theorem nsLocalizedNilpotentStreamFunction_eventuallyEq_polynomial_origin :
    (fun x : NSSpace => nsLocalizedNilpotentStreamFunction x) =ᶠ[𝓝 (0 : NSSpace)]
      nilpotentStreamPolynomialScalar := by
  filter_upwards [nsUnitBumpScalar.eventuallyEq_one] with x hx
  simp [nsLocalizedNilpotentStreamFunction_apply, hx]

/-- At every point inside the bump-one ball, the localized scalar stream
function has the same germ as the underlying nilpotent stream polynomial. -/
theorem nsLocalizedNilpotentStreamFunction_eventuallyEq_polynomial_of_mem_ball
    {x : NSSpace} (hx : x ∈ Metric.ball (0 : NSSpace) nsUnitBumpScalar.rIn) :
    (fun y : NSSpace => nsLocalizedNilpotentStreamFunction y) =ᶠ[𝓝 x]
      nilpotentStreamPolynomialScalar := by
  filter_upwards [nsUnitBumpScalar.eventuallyEq_one_of_mem_ball hx] with y hy
  simp [nsLocalizedNilpotentStreamFunction_apply, hy]

/-- The concrete curl operator only depends on a velocity field germ at the
sampled spatial point. -/
theorem spatialVorticity_congr_nhds_at
    {u v : NSVelocityField} {t : NSTime} {x : NSSpace}
    (h : (fun y : NSSpace => u t y) =ᶠ[𝓝 x] fun y : NSSpace => v t y) :
    spatialVorticity u t x = spatialVorticity v t x := by
  have hderiv :
      ∀ coord comp : Fin 3,
        spatialDerivativeComponent u t x coord comp =
          spatialDerivativeComponent v t x coord comp := by
    intro coord comp
    unfold spatialDerivativeComponent spatialFDeriv
    exact congrArg (fun L : NSSpace →L[ℝ] NSSpace =>
        (L (EuclideanSpace.single coord (1 : ℝ))) comp)
      (Filter.EventuallyEq.fderiv_eq h)
  ext i
  fin_cases i <;>
    simp [spatialVorticity, hderiv]

/-- The localized stream velocity has the same germ at the origin as the
nilpotent shear. -/
theorem streamFunctionVelocity_nsLocalizedNilpotent_eventuallyEq_nilpotent_origin :
    (fun x : NSSpace =>
        (streamFunctionVelocity nsLocalizedNilpotentStreamFunction : NSInitialVelocity) x) =ᶠ[𝓝 (0 : NSSpace)]
      fun x : NSSpace => nilpotentLinearShearInitialVelocity x := by
  have hscalar := nsLocalizedNilpotentStreamFunction_eventuallyEq_polynomial_origin
  have hderiv := Filter.EventuallyEq.fderiv (𝕜 := ℝ) hscalar
  filter_upwards [hderiv] with x hx
  have h1 :
      (∂_{EuclideanSpace.single nsCoord1 (1 : ℝ)} nsLocalizedNilpotentStreamFunction) x =
        x nsCoord1 := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [hx]
    exact nilpotentStreamPolynomialScalar_fderiv_e1 x
  have h0 :
      (∂_{EuclideanSpace.single nsCoord0 (1 : ℝ)} nsLocalizedNilpotentStreamFunction) x =
        -x nsCoord2 := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [hx]
    exact nilpotentStreamPolynomialScalar_fderiv_e0 x
  have h1' :
      (∂_{EuclideanSpace.single (1 : Fin 3) (1 : ℝ)}
          nsLocalizedNilpotentStreamFunction) x =
        x (1 : Fin 3) := by
    simpa [nsCoord1] using h1
  have h0' :
      (∂_{EuclideanSpace.single (0 : Fin 3) (1 : ℝ)}
          nsLocalizedNilpotentStreamFunction) x =
        -x (2 : Fin 3) := by
    simpa [nsCoord0, nsCoord2] using h0
  ext i
  fin_cases i <;>
    simp [streamFunctionVelocity, nilpotentLinearShearInitialVelocity,
      nilpotentLinearShearMap_apply, coordEmbedding_apply, h1', h0',
      nsCoord0, nsCoord1, nsCoord2]

/-- Inside the bump-one ball, the localized nilpotent stream velocity equals
the nilpotent shear at the sampled point. -/
theorem streamFunctionVelocity_nsLocalizedNilpotent_eq_nilpotent_of_mem_ball
    {x : NSSpace} (hx : x ∈ Metric.ball (0 : NSSpace) nsUnitBumpScalar.rIn) :
    streamFunctionVelocity nsLocalizedNilpotentStreamFunction x =
      nilpotentLinearShearInitialVelocity x := by
  have hscalar :=
    nsLocalizedNilpotentStreamFunction_eventuallyEq_polynomial_of_mem_ball hx
  have hderiv := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hscalar
  have h1 :
      (∂_{EuclideanSpace.single nsCoord1 (1 : ℝ)} nsLocalizedNilpotentStreamFunction) x =
        x nsCoord1 := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [hderiv]
    exact nilpotentStreamPolynomialScalar_fderiv_e1 x
  have h0 :
      (∂_{EuclideanSpace.single nsCoord0 (1 : ℝ)} nsLocalizedNilpotentStreamFunction) x =
        -x nsCoord2 := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    rw [hderiv]
    exact nilpotentStreamPolynomialScalar_fderiv_e0 x
  have h1' :
      (∂_{EuclideanSpace.single (1 : Fin 3) (1 : ℝ)}
          nsLocalizedNilpotentStreamFunction) x =
        x (1 : Fin 3) := by
    simpa [nsCoord1] using h1
  have h0' :
      (∂_{EuclideanSpace.single (0 : Fin 3) (1 : ℝ)}
          nsLocalizedNilpotentStreamFunction) x =
        -x (2 : Fin 3) := by
    simpa [nsCoord0, nsCoord2] using h0
  ext i
  fin_cases i <;>
    simp [streamFunctionVelocity, nilpotentLinearShearInitialVelocity,
      nilpotentLinearShearMap_apply, coordEmbedding_apply, h1', h0',
      nsCoord0, nsCoord1, nsCoord2]

/-- A concrete point inside the bump-one ball where the localized nilpotent
stream velocity is nonzero. -/
def nsLocalizedNilpotentStreamWitnessPoint : NSSpace :=
  EuclideanSpace.single nsCoord2 (nsUnitBumpScalar.rIn / 2)

theorem nsLocalizedNilpotentStreamWitnessPoint_mem_ball :
    nsLocalizedNilpotentStreamWitnessPoint ∈
      Metric.ball (0 : NSSpace) nsUnitBumpScalar.rIn := by
  have hhalf_pos : 0 < nsUnitBumpScalar.rIn / 2 :=
    half_pos nsUnitBumpScalar.rIn_pos
  have hhalf_lt : nsUnitBumpScalar.rIn / 2 < nsUnitBumpScalar.rIn :=
    half_lt_self nsUnitBumpScalar.rIn_pos
  have hr_abs : |nsUnitBumpScalar.rIn| = nsUnitBumpScalar.rIn :=
    abs_of_nonneg nsUnitBumpScalar.rIn_pos.le
  simp [nsLocalizedNilpotentStreamWitnessPoint, Metric.mem_ball,
    dist_zero_right, nsCoord2, Real.norm_eq_abs, hr_abs, hhalf_lt]

theorem streamFunctionVelocity_nsLocalizedNilpotent_witness_value :
    streamFunctionVelocity nsLocalizedNilpotentStreamFunction
        nsLocalizedNilpotentStreamWitnessPoint =
      EuclideanSpace.single nsCoord1 (nsUnitBumpScalar.rIn / 2) := by
  rw [streamFunctionVelocity_nsLocalizedNilpotent_eq_nilpotent_of_mem_ball
    nsLocalizedNilpotentStreamWitnessPoint_mem_ball]
  ext i
  fin_cases i <;>
    simp [nsLocalizedNilpotentStreamWitnessPoint, nilpotentLinearShearInitialVelocity,
      nilpotentLinearShearMap_apply, nsCoord0, nsCoord1, nsCoord2]

theorem streamFunctionVelocity_nsLocalizedNilpotent_nonzero :
    ∃ x : NSSpace, streamFunctionVelocity nsLocalizedNilpotentStreamFunction x ≠ 0 := by
  refine ⟨nsLocalizedNilpotentStreamWitnessPoint, ?_⟩
  rw [streamFunctionVelocity_nsLocalizedNilpotent_witness_value]
  intro hzero
  have hcoord := congrArg (fun v : NSSpace => v nsCoord1) hzero
  have hhalf_pos : 0 < nsUnitBumpScalar.rIn / 2 :=
    half_pos nsUnitBumpScalar.rIn_pos
  have hcoord' : nsUnitBumpScalar.rIn / 2 = 0 := by
    simpa [nsCoord1] using hcoord
  exact hhalf_pos.ne' hcoord'

/-- Time-independent velocity generated by the localized nilpotent stream
profile. -/
def localizedNilpotentStreamVelocityField : NSVelocityField :=
  timeIndependentVelocity
    (streamFunctionVelocity nsLocalizedNilpotentStreamFunction : NSInitialVelocity)

theorem localizedNilpotentStreamVelocityField_eventuallyEq_nilpotent_origin :
    (fun x : NSSpace => localizedNilpotentStreamVelocityField 0 x) =ᶠ[𝓝 (0 : NSSpace)]
      fun x : NSSpace => nilpotentLinearShearVelocityField 0 x := by
  simpa [localizedNilpotentStreamVelocityField, nilpotentLinearShearVelocityField,
    timeIndependentVelocity] using
    streamFunctionVelocity_nsLocalizedNilpotent_eventuallyEq_nilpotent_origin

theorem momentumPressureResidual_zero_localizedNilpotentStreamVelocityField_eventuallyEq_origin :
    (fun x : NSSpace =>
        momentumPressureResidual 0 localizedNilpotentStreamVelocityField 0 x) =ᶠ[𝓝 (0 : NSSpace)]
      fun x : NSSpace =>
        momentumPressureResidual 0 nilpotentLinearShearVelocityField 0 x := by
  have hvel := localizedNilpotentStreamVelocityField_eventuallyEq_nilpotent_origin
  have hfderiv := Filter.EventuallyEq.fderiv (𝕜 := ℝ) hvel
  filter_upwards [hvel, hfderiv] with x hx hdx
  unfold momentumPressureResidual
  have htime_local :
      timeVelocityDerivative localizedNilpotentStreamVelocityField 0 x = 0 := by
    simpa [localizedNilpotentStreamVelocityField] using
      timeVelocityDerivative_timeIndependentVelocity
        (streamFunctionVelocity nsLocalizedNilpotentStreamFunction : NSInitialVelocity) 0 x
  have htime_nil :
      timeVelocityDerivative nilpotentLinearShearVelocityField 0 x = 0 :=
    timeVelocityDerivative_nilpotentLinearShearVelocityField 0 x
  have hconv :
      spatialConvection localizedNilpotentStreamVelocityField 0 x =
        spatialConvection nilpotentLinearShearVelocityField 0 x := by
    unfold spatialConvection spatialFDeriv
    rw [hdx, hx]
  simp [htime_local, htime_nil, hconv]

theorem spatialVorticity_momentumPressureResidual_zero_localizedNilpotentStreamVelocityField_origin :
    spatialVorticity
        (momentumPressureResidual 0 localizedNilpotentStreamVelocityField) 0 0 =
      EuclideanSpace.single nsCoord1 (-1 : ℝ) := by
  rw [spatialVorticity_congr_nhds_at
    momentumPressureResidual_zero_localizedNilpotentStreamVelocityField_eventuallyEq_origin]
  exact spatialVorticity_momentumPressureResidual_nilpotentLinearShearVelocityField 0 0 0

theorem spatialVorticity_momentumPressureResidual_zero_localizedNilpotentStreamVelocityField_origin_ne_zero :
    spatialVorticity
        (momentumPressureResidual 0 localizedNilpotentStreamVelocityField) 0 0 ≠
      0 := by
  rw [spatialVorticity_momentumPressureResidual_zero_localizedNilpotentStreamVelocityField_origin]
  intro h
  have hcoord := congrArg (fun v : NSSpace => v nsCoord1) h
  norm_num [nsCoord1] at hcoord

/-- No smooth pressure can make the localized nilpotent stream velocity a
stationary inviscid exact solution.  The obstruction is local and
pressure-agnostic: the required pressure residual has nonzero curl at the
origin. -/
theorem not_exists_smoothPressure_momentumEquation_zero_localizedNilpotentStreamVelocityField :
    ¬ ∃ p : NSPressureField,
      smoothSpaceTimePressure p ∧
        ∀ t x,
          timeVelocityDerivative localizedNilpotentStreamVelocityField t x +
              spatialConvection localizedNilpotentStreamVelocityField t x +
              spatialPressureGradient p t x =
            (0 : ℝ) • spatialLaplacian localizedNilpotentStreamVelocityField t x := by
  exact
    not_exists_smoothPressure_momentumEquation_of_momentumPressureResidual_vorticity_ne_zero
      (ν := 0) (u := localizedNilpotentStreamVelocityField)
      ⟨0, 0,
        spatialVorticity_momentumPressureResidual_zero_localizedNilpotentStreamVelocityField_origin_ne_zero⟩

/-- The localized nilpotent stream gives a concrete divergence-free Schwartz
initial velocity. -/
def nsLocalizedNilpotentStreamDivergenceFreeInitialVelocity :
    NSSchwartzDivergenceFreeInitialVelocity where
  val := streamFunctionVelocity nsLocalizedNilpotentStreamFunction
  property := initialSpatialDivergence_streamFunctionVelocity nsLocalizedNilpotentStreamFunction

theorem nsLocalizedNilpotentStreamDivergenceFreeInitialVelocity_nonzero :
    ∃ x : NSSpace,
      nsLocalizedNilpotentStreamDivergenceFreeInitialVelocity.1 x ≠ 0 :=
  streamFunctionVelocity_nsLocalizedNilpotent_nonzero

end NavierStokes
end FluidDynamics
end Mettapedia
