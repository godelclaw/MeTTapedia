import MettapediaNS.WholeSpacePressureRecovery
import Euler.OrdinaryVorticityCoordinates

/-!
# Constructed whole-space stretching-flux receiver

Vorticity, products, advection, and the Helmholtz projection are the upstream
ordinary smooth L² constructions. Projection acts on the spatial flux index:
each column is projected separately. The resulting receiver is the one paired
with the actual pressure Hessian in the material rate of `-ω ⊗ ((ω·∇)u)`.

These are spatial constructions. No time evolution, endpoint bound, or
identification with a periodic lift is asserted.
-/

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WholeSpaceStretchingFlux

open MeasureTheory EulerLpTranslation EulerLpTranslation.SmoothL2Field
open EulerOrdinarySobolev EulerMeanSolenoidal
open NavierStokes.ProblemStatement (Space)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NavierStokes.PeriodicUniqueness
open scoped ContDiff

/-- The actual vorticity stretching, constructed using upstream advection. -/
def stretching (A : SmoothL2Field Space) : SmoothL2Field Space :=
  advectionField (vorticityField A) A

theorem stretching_field (A : SmoothL2Field Space) (x : Space) :
    (stretching A).field x = fderiv ℝ A.field x ((vorticityField A).field x) :=
  advectionField_field _ _ _

/-- Fixing the output component leaves a vector in the spatial flux index. -/
def fluxColumn (A : SmoothL2Field Space) (a : Fin 3) : SmoothL2Field Space :=
  fieldNeg (scalarProduct (componentField (stretching A) a) (vorticityField A))

theorem fluxColumn_field (A : SmoothL2Field Space) (a j : Fin 3) (x : Space) :
    (fluxColumn A a).field x j =
      -((vorticityField A).field x j * (stretching A).field x a) := by
  simp only [fluxColumn, fieldNeg_field, scalarProduct_field, componentField_apply,
    PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The gradient part is the complement of the actual upstream solenoidal
projection, not an independently supplied tensor field. -/
def projectedColumn (A : SmoothL2Field Space) (a : Fin 3) : SmoothL2Field Space :=
  fieldSub (fluxColumn A a) (solenoidalField (fluxColumn A a))

theorem projectedColumn_toLp (A : SmoothL2Field Space) (a : Fin 3) :
    (projectedColumn A a).toLp =
      (fluxColumn A a).toLp - solenoidalProjection (fluxColumn A a).toLp := by
  rw [projectedColumn, toLp_fieldSub, solenoidalField_toLp]

theorem projectedColumn_mem_gradient (A : SmoothL2Field Space) (a : Fin 3) :
    (projectedColumn A a).toLp ∈ gradientSpace := by
  rw [projectedColumn_toLp]
  exact sub_solenoidalProjection_mem_gradient _

/-- Contract the projected stretching flux with one vorticity, keeping its
output component. Upstream field algebra supplies all actual L² jets. -/
def receiverVectorComponent (A : SmoothL2Field Space) (a : Fin 3) : SmoothL2Field ℝ :=
  sumField Finset.univ (fun j : Fin 3 =>
    scalarProduct (componentField (vorticityField A) j) (componentField (projectedColumn A a) j))

/-- The tensor paired with the pressure Hessian. Its two indices are the
pressure-gradient component and the differentiating coordinate. -/
def receiver (A : SmoothL2Field Space) (a b : Fin 3) : SmoothL2Field ℝ :=
  scalarProduct (componentField (vorticityField A) b) (receiverVectorComponent A a)

theorem receiver_field (A : SmoothL2Field Space) (a b : Fin 3) (x : Space) :
    (receiver A a b).field x = (vorticityField A).field x b *
      ∑ j : Fin 3, (vorticityField A).field x j * (projectedColumn A a).field x j := by
  simp only [receiver, receiverVectorComponent, scalarProduct_field, componentField_apply,
    sumField_field, smul_eq_mul]

/-- The contraction uses the derivative of the constructed pressure gradient,
so it is the actual pressure-Hessian action. No receiver is postulated. -/
theorem pressure_contraction_eq (A : SmoothL2Field Space) (x : Space) :
    (∑ j : Fin 3, (vorticityField A).field x j * ∑ a : Fin 3,
      (projectedColumn A a).field x j *
        (fderiv ℝ (pressureField A).field x ((vorticityField A).field x)) a) =
      ∑ a : Fin 3, ∑ b : Fin 3, (receiver A a b).field x *
        spatialPartial b (fun y => (pressureField A).field y a) x := by
  have he (a : Fin 3) :
      (fderiv ℝ (pressureField A).field x ((vorticityField A).field x)) a =
        ∑ b : Fin 3, (vorticityField A).field x b *
          spatialPartial b (fun y => (pressureField A).field y a) x := by
    rw [← fderiv_component (pressureField A).smooth a x ((vorticityField A).field x)]
    exact fderiv_apply_eq_sum _ _ _
  simp only [he, receiver_field, Fin.sum_univ_three]
  ring

end Mettapedia.FluidDynamics.NavierStokes.WholeSpaceStretchingFlux
