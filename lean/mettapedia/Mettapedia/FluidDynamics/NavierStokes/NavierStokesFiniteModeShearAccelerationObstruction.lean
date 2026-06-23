import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePolynomialPressurePrimitive
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePolynomialPressureEvaluation
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePolynomialPressureDefect
import Mettapedia.FluidDynamics.NavierStokes.NavierStokesFiniteModePolynomialPressureClosure

/-!
# One-mode shear-acceleration obstruction showing projected coefficient dynamics do not force pressure closure.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open Set
open scoped BigOperators
open scoped ContDiff
open scoped Laplacian

/-- A one-mode spatial forcing direction shaped like the shear vector field
`x₁ e₀`.  It is used below as a concrete obstruction to the idea that the
abstract projected finite-mode RHS forces the full spatial residual to be a
gradient. -/
def finiteModeShearAccelerationMode (_ : PUnit) : NSSpace → NSSpace :=
  fun x => EuclideanSpace.single (0 : Fin 3) (x (1 : Fin 3))

/-- One-mode projected coefficients with unit forcing and no linear or
quadratic terms. -/
def finiteModeUnitForcingCoefficients : FiniteModeProjectedNSCoefficients PUnit where
  forcing := fun _ => 1
  linear := fun _ _ => 0
  quadratic := fun _ _ _ => 0

/-- The identically zero coefficient curve for a one-mode system. -/
def finiteModeZeroCoefficientCurve : ℝ → FiniteModeState PUnit :=
  fun _ _ => 0

/-- The identity coefficient curve for the one-mode unit-forcing system. -/
def finiteModeIdentityCoefficientCurve : ℝ → FiniteModeState PUnit :=
  fun t _ => t

/-- One-mode projected coefficients with constant scalar forcing and no linear
or quadratic terms. -/
def finiteModeScalarForcingCoefficients
    (c : ℝ) : FiniteModeProjectedNSCoefficients PUnit.{1} where
  forcing := fun _ => c
  linear := fun _ _ => 0
  quadratic := fun _ _ _ => 0

/-- A one-mode coefficient curve with arbitrary scalar amplitude `g(t)`. -/
def finiteModeScalarAmplitudeCoefficientCurve
    (g : NSTime → ℝ) : NSTime → FiniteModeState PUnit.{1} :=
  fun t _ => g t

/-- If the scalar amplitude has derivative `gdot t`, then the corresponding
one-mode coefficient curve solves the projected ODE with constant forcing
`gdot t` at that time. -/
theorem finiteModeScalarAmplitudeCoefficientCurve_hasDerivAt
    (g gdot : NSTime → ℝ) {t : NSTime}
    (hg : HasDerivAt g (gdot t) t) :
    HasDerivAt (finiteModeScalarAmplitudeCoefficientCurve g)
      (finiteModeProjectedNSRHS
        (finiteModeScalarForcingCoefficients (gdot t))
        (finiteModeScalarAmplitudeCoefficientCurve g t)) t := by
  rw [hasDerivAt_pi]
  intro i
  cases i
  simpa [finiteModeScalarAmplitudeCoefficientCurve, finiteModeProjectedNSRHS,
    finiteModeScalarForcingCoefficients] using hg

/-- The identity curve solves the abstract one-mode projected ODE with unit
forcing and no linear or quadratic terms. -/
theorem finiteModeIdentityCoefficientCurve_hasDerivAt
    (t : NSTime) :
    HasDerivAt finiteModeIdentityCoefficientCurve
      (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
        (finiteModeIdentityCoefficientCurve t)) t := by
  rw [hasDerivAt_pi]
  intro i
  cases i
  simpa [finiteModeIdentityCoefficientCurve, finiteModeProjectedNSRHS,
    finiteModeUnitForcingCoefficients] using (hasDerivAt_id t)

/-- The polynomial vector field `(X₁, 0, 0)`, matching
`finiteModeShearAccelerationMode`. -/
def finiteModeShearAccelerationPolynomialVectorField :
    Fin 3 → MvPolynomial (Fin 3) ℝ :=
  fun j => if j = (0 : Fin 3) then MvPolynomial.X (1 : Fin 3) else 0

/-- With zero coefficient velocity, unit projected forcing into the shear mode,
and zero viscosity, the non-pressure finite-mode residual is the polynomial
vector field `(X₁, 0, 0)`. -/
theorem finiteModeShearAcceleration_nonPressureDefect_eq_polynomial
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
        finiteModeUnitForcingCoefficients finiteModeZeroCoefficientCurve t x =
      finiteModePolynomialVectorFieldEval
        finiteModeShearAccelerationPolynomialVectorField x := by
  ext j
  fin_cases j <;>
    simp [finiteModeNonPressureMomentumDefect, finiteModeReconstructedAcceleration,
      finiteModeReconstructedVelocity, finiteModeReconstructionCLM, finiteModeProjectedNSRHS,
      finiteModeUnitForcingCoefficients, finiteModeZeroCoefficientCurve,
      finiteModeShearAccelerationMode, spatialConvection, spatialLaplacian,
      finiteModeShearAccelerationPolynomialVectorField,
      finiteModePolynomialVectorFieldEval, Pi.single_apply]

/-- The identity coefficient reconstruction is the time-dependent linear shear
slice `x ↦ t x₁ e₀`. -/
theorem finiteModeShearAcceleration_identityVelocity_eq_linearShear
    (t : NSTime) (x : NSSpace) :
    finiteModeReconstructedVelocity finiteModeShearAccelerationMode
        finiteModeIdentityCoefficientCurve t x =
      linearShearVelocityField t t x := by
  ext j
  fin_cases j <;>
    simp [finiteModeReconstructedVelocity, finiteModeReconstructionCLM,
      finiteModeIdentityCoefficientCurve, finiteModeShearAccelerationMode,
      linearShearVelocityField, linearShearInitialVelocity,
      linearShearMap, nsCoord0, nsCoord1, ContinuousLinearMap.smulRight_apply,
      mul_comm]

/-- The identity-coefficient shear reconstruction has zero convection at every
point. -/
theorem finiteModeShearAcceleration_identity_spatialConvection_zero
    (t : NSTime) (x : NSSpace) :
    spatialConvection
        (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  unfold spatialConvection
  have hfderiv :
      spatialFDeriv
          (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
            finiteModeIdentityCoefficientCurve) t x =
        spatialFDeriv (linearShearVelocityField t) t x := by
    unfold spatialFDeriv
    congr 1
    funext y
    exact finiteModeShearAcceleration_identityVelocity_eq_linearShear t y
  rw [hfderiv, finiteModeShearAcceleration_identityVelocity_eq_linearShear]
  exact spatialConvection_linearShearVelocityField t t x

/-- The identity-coefficient shear reconstruction has zero spatial Laplacian at
every point. -/
theorem finiteModeShearAcceleration_identity_spatialLaplacian_zero
    (t : NSTime) (x : NSSpace) :
    spatialLaplacian
        (finiteModeReconstructedVelocity finiteModeShearAccelerationMode
          finiteModeIdentityCoefficientCurve) t x = 0 := by
  unfold spatialLaplacian
  have hslice :
      (fun y : NSSpace =>
        finiteModeReconstructedVelocity finiteModeShearAccelerationMode
          finiteModeIdentityCoefficientCurve t y) =
      fun y : NSSpace => linearShearVelocityField t t y := by
    funext y
    exact finiteModeShearAcceleration_identityVelocity_eq_linearShear t y
  rw [hslice]
  exact spatialLaplacian_linearShearVelocityField t t x

/-- Even when the coefficient curve is an actual solution of the unit-forcing
projected ODE, the abstract finite-mode non-pressure defect can be the
non-gradient shear polynomial `(X₁, 0, 0)`. -/
theorem finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial
    (t : NSTime) (x : NSSpace) :
    finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
        finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x =
      finiteModePolynomialVectorFieldEval
        finiteModeShearAccelerationPolynomialVectorField x := by
  unfold finiteModeNonPressureMomentumDefect
  rw [finiteModeShearAcceleration_identity_spatialConvection_zero t x,
    finiteModeShearAcceleration_identity_spatialLaplacian_zero t x]
  ext j
  fin_cases j <;>
    simp [finiteModeReconstructedAcceleration,
      finiteModeReconstructedVelocity, finiteModeReconstructionCLM, finiteModeProjectedNSRHS,
      finiteModeUnitForcingCoefficients, finiteModeIdentityCoefficientCurve,
      finiteModeShearAccelerationMode,
      finiteModeShearAccelerationPolynomialVectorField,
      finiteModePolynomialVectorFieldEval, Pi.single_apply]

/-- The shear acceleration polynomial vector field is not curl-free. -/
theorem finiteModeShearAccelerationPolynomialVectorField_not_curlFree :
    ¬ (∀ i j,
      MvPolynomial.pderiv i (finiteModeShearAccelerationPolynomialVectorField j) =
        MvPolynomial.pderiv j (finiteModeShearAccelerationPolynomialVectorField i)) := by
  intro h
  have h10 := h (1 : Fin 3) (0 : Fin 3)
  norm_num [finiteModeShearAccelerationPolynomialVectorField] at h10

/-- Consequently the concrete shear acceleration residual has no polynomial
pressure primitive in its natural polynomial representation. -/
theorem finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive :
    ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
      MvPolynomial.pderiv j p =
        finiteModeShearAccelerationPolynomialVectorField j := by
  intro hp
  exact finiteModeShearAccelerationPolynomialVectorField_not_curlFree
    ((finiteModePolynomialPressurePrimitive_exists_iff_curlFree
      finiteModeShearAccelerationPolynomialVectorField).mp hp)

/-- The sign required to close momentum also has no polynomial pressure
primitive: if `∇p = -(X₁ e₀)`, then `-p` would primitive `X₁ e₀`. -/
theorem finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive :
    ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
      MvPolynomial.pderiv j p =
        -finiteModeShearAccelerationPolynomialVectorField j := by
  intro hp
  rcases hp with ⟨p, hp⟩
  exact finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive
    ⟨-p, by
      intro j
      calc
        MvPolynomial.pderiv j (-p) =
            -MvPolynomial.pderiv j p := by
              simp
        _ = finiteModeShearAccelerationPolynomialVectorField j := by
              rw [hp j]
              simp⟩

/-- No time-dependent scalar polynomial pressure can satisfy the coefficient
obligation `∇p(t) = -(X₁ e₀)` required to close the identity-coefficient shear
residual. -/
theorem finiteModeShearAcceleration_solution_no_timeDependentPolynomialPressurePrimitive :
    ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ, ∀ t j,
      MvPolynomial.pderiv j (P t) =
        -finiteModeShearAccelerationPolynomialVectorField j := by
  intro hP
  rcases hP with ⟨P, hP⟩
  exact finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive
    ⟨P 0, hP 0⟩

/-- No time-dependent scalar polynomial pressure can close the identity-curve
shear residual through the actual pointwise `spatialPressureGradient` API.  The
proof reflects pointwise equality of polynomial gradients back to coefficient
equality by `MvPolynomial.funext`. -/
theorem finiteModeShearAcceleration_solution_no_pointwisePolynomialPressureGradient :
    ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
      ∀ t x,
        spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
          -finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x := by
  intro hP
  rcases hP with ⟨P, hP⟩
  exact finiteModeShearAccelerationPolynomialVectorField_no_negative_pressurePrimitive
    ⟨P 0, by
      intro j
      exact
        (finiteModeTimePolynomialPressureGradient_eq_eval_iff_pderiv P
          (fun _ j => -finiteModeShearAccelerationPolynomialVectorField j)).mp
          (by
            intro t x
            rw [hP t x,
              finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial]
            ext k
            simp [finiteModePolynomialVectorFieldEval_apply])
          0 j⟩

/-- Obstruction to the universal residual-curl-free claim for the abstract
finite-mode API: the projected ODE can force the zero velocity curve in a
non-gradient shear direction.  Additional projection/Leray structure is needed
before the polynomial pressure theorem can close the residual. -/
theorem finiteModeProjectedNS_nonPressureDefect_curlFree_not_forced_obstruction :
    (∀ t : NSTime,
      finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
          finiteModeUnitForcingCoefficients finiteModeZeroCoefficientCurve t =
        finiteModePolynomialVectorFieldEval
          finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
        MvPolynomial.pderiv j p =
          finiteModeShearAccelerationPolynomialVectorField j := by
  constructor
  · intro t
    funext x
    exact finiteModeShearAcceleration_nonPressureDefect_eq_polynomial t x
  · exact finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive

/-- Stronger obstruction to the universal residual-curl-free claim: the
counterexample can use an actual coefficient solution of the abstract projected
ODE.  Thus the missing pressure theorem needs an additional Helmholtz/Leray
compatibility hypothesis tying the coefficient ODE to the spatial residual. -/
theorem finiteModeProjectedNS_coefficientSolution_nonPressureDefect_curlFree_not_forced_obstruction :
    (∀ t : NSTime,
      HasDerivAt finiteModeIdentityCoefficientCurve
        (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
          (finiteModeIdentityCoefficientCurve t)) t) ∧
      (∀ t : NSTime,
        finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t =
          finiteModePolynomialVectorFieldEval
            finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ p : MvPolynomial (Fin 3) ℝ, ∀ j,
        MvPolynomial.pderiv j p =
          finiteModeShearAccelerationPolynomialVectorField j := by
  refine ⟨finiteModeIdentityCoefficientCurve_hasDerivAt, ?_, ?_⟩
  · intro t
    funext x
    exact finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial t x
  · exact finiteModeShearAccelerationPolynomialVectorField_no_pressurePrimitive

/-- The coefficient-solution obstruction with the sign needed by the momentum
equation: even time-dependent polynomial pressures cannot close the shear
residual produced by the abstract projected ODE. -/
theorem finiteModeProjectedNS_coefficientSolution_no_polynomialPressurePrimitive_obstruction :
    (∀ t : NSTime,
      HasDerivAt finiteModeIdentityCoefficientCurve
        (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
          (finiteModeIdentityCoefficientCurve t)) t) ∧
      (∀ t : NSTime,
        finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t =
          finiteModePolynomialVectorFieldEval
            finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ, ∀ t j,
        MvPolynomial.pderiv j (P t) =
          -finiteModeShearAccelerationPolynomialVectorField j := by
  refine ⟨finiteModeIdentityCoefficientCurve_hasDerivAt, ?_, ?_⟩
  · intro t
    funext x
    exact finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial t x
  · exact
      finiteModeShearAcceleration_solution_no_timeDependentPolynomialPressurePrimitive

/-- Pointwise version of the coefficient-solution obstruction: the actual
`spatialPressureGradient` of a time-dependent polynomial pressure cannot close
the shear residual produced by the abstract projected ODE. -/
theorem finiteModeProjectedNS_coefficientSolution_no_pointwisePolynomialPressureGradient_obstruction :
    (∀ t : NSTime,
      HasDerivAt finiteModeIdentityCoefficientCurve
        (finiteModeProjectedNSRHS finiteModeUnitForcingCoefficients
          (finiteModeIdentityCoefficientCurve t)) t) ∧
      (∀ t : NSTime,
        finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
            finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t =
          finiteModePolynomialVectorFieldEval
            finiteModeShearAccelerationPolynomialVectorField) ∧
      ¬ ∃ P : NSTime → MvPolynomial (Fin 3) ℝ,
        ∀ t x,
          spatialPressureGradient (fun s y => MvPolynomial.eval y (P s)) t x =
            -finiteModeNonPressureMomentumDefect (0 : ℝ) finiteModeShearAccelerationMode
              finiteModeUnitForcingCoefficients finiteModeIdentityCoefficientCurve t x := by
  refine ⟨finiteModeIdentityCoefficientCurve_hasDerivAt, ?_, ?_⟩
  · intro t
    funext x
    exact finiteModeShearAcceleration_solution_nonPressureDefect_eq_polynomial t x
  · exact finiteModeShearAcceleration_solution_no_pointwisePolynomialPressureGradient

end NavierStokes
end FluidDynamics
end Mettapedia
