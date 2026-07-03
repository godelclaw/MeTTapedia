import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityStretchingGate

/-!
# Stochastic-Lagrangian layer: regression checks

Theorem-level checks that the momentum-transport pushdown, the gate
consumers, and the conditional route assemble and evaluate on concrete
instances: the rest state (zero velocity, zero gauge) with the uniform
two-point noise model and unit Jacobian envelopes.  These checks confirm the
structures are genuinely inhabited and the hypothesis fields are usable, and
that the conditional route theorem specializes without friction.  They make
no claim beyond the instances they name.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace StochasticLagrangianRegression

open scoped RealInnerProductSpace BigOperators

/-- Three-dimensional coordinate space. -/
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The uniform probability on two samples. -/
def uniformTwoPoint : FiniteProbability (Fin 2) where
  weight := fun _ => 1 / 2
  weight_nonneg := fun _ => by norm_num
  weight_sum_one := by
    rw [Fin.sum_univ_two]
    norm_num

/-- Expectation of a deterministic family under the uniform two-point
probability. -/
theorem expectedOneForm_uniformTwoPoint (μ : R3 → R3) :
    expectedOneForm uniformTwoPoint (fun _ => μ) = μ :=
  expectedOneForm_const uniformTwoPoint μ

/-- The identity cotangent state transports the initial momentum. -/
theorem cotangentStateAtId_transport (u₀ : R3 → R3) :
    (cotangentStateAtId u₀).IsTransportOf u₀ :=
  cotangentStateAtId_isTransportOf u₀

/-- The representation pressure of the rest state vanishes pointwise. -/
theorem rest_pressure_eq_zero (ν t : ℝ) (y : R3) :
    (TransportedMomentumData.rest ν).pressure t y = 0 := by
  unfold TransportedMomentumData.pressure TransportedMomentumData.rest
  simp

/-- The pushdown theorem specializes to the rest state. -/
theorem rest_navierStokes (ν t : ℝ) (x : R3) :
    deriv (fun s => (TransportedMomentumData.rest ν).u s x) t +
      fderiv ℝ ((TransportedMomentumData.rest ν).u t) x
        ((TransportedMomentumData.rest ν).u t x) +
      gradField ((TransportedMomentumData.rest ν).pressure t) x =
    ν • coordLaplacian ((TransportedMomentumData.rest ν).u t) x :=
  (TransportedMomentumData.rest ν).navierStokes_of_transportedMomentum t x

/-- Averaged-Cauchy vorticity data for the rest state: zero vorticity, unit
Jacobian envelopes, uniform two-point noise. -/
def restVorticityData : StochasticCauchyVorticityData (Fin 2) where
  prob := uniformTwoPoint
  jacobianBound := fun _ _ => 1
  jacobianBound_nonneg := fun _ _ => by norm_num
  vorticity := fun _ _ => 0
  vorticity_time_aestronglyMeasurable := fun _ =>
    MeasureTheory.aestronglyMeasurable_const
  initialBound := 0
  initialBound_nonneg := le_refl 0
  cauchy_bound := fun t x => by simp

/-- The expected Jacobian envelope of the rest data is constantly `1`. -/
theorem restVorticityData_expectedJacobianBound (t : ℝ) :
    restVorticityData.expectedJacobianBound t = 1 := by
  unfold StochasticCauchyVorticityData.expectedJacobianBound restVorticityData
  rw [Fin.sum_univ_two]
  norm_num [uniformTwoPoint]

/-- The vorticity-stretching gate holds for the rest data on every horizon
(the envelope is constant — this instance shows the gate is satisfiable; it
says nothing about nontrivial data). -/
theorem restVorticityData_gate (T : ℝ) :
    StochasticStretchingEstimate restVorticityData T := by
  unfold StochasticStretchingEstimate
  have hfun : restVorticityData.expectedJacobianBound = fun _ => 1 := by
    funext t
    exact restVorticityData_expectedJacobianBound t
  rw [hfun]
  exact intervalIntegrable_const

/-- **End-to-end instantiation of the conditional route** on the rest state:
the pushdown identity and the gate consumers hold simultaneously, with the
gate discharged by the constant envelope. -/
theorem conditional_route_rest (ν T : ℝ) (hT : 0 ≤ T) :
    (∀ t x, deriv (fun s => (TransportedMomentumData.rest ν).u s x) t +
        fderiv ℝ ((TransportedMomentumData.rest ν).u t) x
          ((TransportedMomentumData.rest ν).u t x) +
        gradField ((TransportedMomentumData.rest ν).pressure t) x =
      ν • coordLaplacian ((TransportedMomentumData.rest ν).u t) x) ∧
    (∀ x : R3,
      IntervalIntegrable
        (fun t => ‖curlField ((TransportedMomentumData.rest ν).u t) x‖)
        MeasureTheory.volume 0 T ∧
      ∫ t in (0 : ℝ)..T,
          ‖curlField ((TransportedMomentumData.rest ν).u t) x‖ ≤
        restVorticityData.initialBound *
          ∫ t in (0 : ℝ)..T, restVorticityData.expectedJacobianBound t) :=
  stochasticLagrangian_conditional_route (TransportedMomentumData.rest ν)
    restVorticityData
    (fun _ x => (curlField_const 0 x).symm)
    hT
    (restVorticityData_gate T)

end StochasticLagrangianRegression
end NavierStokes
end FluidDynamics
end Mettapedia
