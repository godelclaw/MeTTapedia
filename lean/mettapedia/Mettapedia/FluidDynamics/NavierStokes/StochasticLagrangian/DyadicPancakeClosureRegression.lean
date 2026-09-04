import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.DyadicPancakeClosure

/-!
# Dyadic pancake-closure skeleton: regression checks

Theorem-level checks that the relaxation-data structure is inhabited, the
sector-estimate and strain-budget propositions are satisfiable, the
ε-absorption evaluates, and the headline conditional route specializes to
the rest state end-to-end.  These confirm the conditional chain is
non-vacuous — its hypotheses are simultaneously satisfiable — and make no
claim beyond the instances they name.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace DyadicPancakeClosureRegression

open scoped RealInnerProductSpace BigOperators

/-- Three-dimensional coordinate space. -/
local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The rest relaxation data: all functionals vanish on `[0, 1]`. -/
def restDyadicData : DyadicVorticityStretchingData where
  T := 1
  T_nonneg := zero_le_one
  highBlockSum := fun _ => 0
  highBlockSum_nonneg := fun _ => le_refl 0
  highBlockSum_integrable := intervalIntegrable_const
  pancakeStretchSum := fun _ => 0
  pancakeStretchSum_nonneg := fun _ => le_refl 0
  pancakeStretchSum_integrable := intervalIntegrable_const
  coerciveStretchSum := fun _ => 0
  coerciveStretchSum_nonneg := fun _ => le_refl 0
  coerciveStretchSum_integrable := intervalIntegrable_const
  residualSum := fun _ => 0
  residualSum_nonneg := fun _ => le_refl 0
  residualSum_integrable := intervalIntegrable_const
  relaxationConst := 0
  relaxation_bound := by simp

/-- The rest data satisfies the scale-local strain budget with zero
constant and zero gain. -/
theorem restDyadicData_strainBudget :
    ScaleLocalPancakeStrainBudget restDyadicData 0 0 := by
  refine ⟨fun _ => 0, intervalIntegrable_const, by simp, ?_⟩
  intro t _
  simp [restDyadicData]

/-- The coercive sector estimate holds on the rest data. -/
theorem restDyadicData_coercive : CoerciveSectorEstimate restDyadicData 0 0 := by
  unfold CoerciveSectorEstimate
  simp [restDyadicData]

/-- The residual sector estimate holds on the rest data. -/
theorem restDyadicData_residual : ResidualSectorEstimate restDyadicData 0 0 := by
  unfold ResidualSectorEstimate
  simp [restDyadicData]

/-- The ε-absorption closure evaluates on the rest data. -/
theorem restDyadicData_absorption :
    (∫ t in (0 : ℝ)..restDyadicData.T, restDyadicData.highBlockSum t) ≤
      (restDyadicData.relaxationConst + (0 + 0 + 0)) / (1 - (0 + 0 + 0)) :=
  highBlockIntegral_le_of_sectorEstimates restDyadicData
    (pancakeSectorEstimate_of_scaleLocalStrainBudget restDyadicData
      restDyadicData_strainBudget)
    restDyadicData_coercive restDyadicData_residual (by norm_num)

/-- **End-to-end canary:** the headline conditional route specializes to the
rest state — the Navier–Stokes equations hold and the BKM integrand is
interval-integrable with the explicit bound.  The hypotheses of
`stochasticLagrangian_conditional_route_of_pancakeBudget` are therefore
simultaneously satisfiable. -/
theorem rest_conditional_route (ν : ℝ) :
    (∀ t x, deriv (fun s => (TransportedMomentumData.rest ν).u s x) t +
        fderiv ℝ ((TransportedMomentumData.rest ν).u t) x
          ((TransportedMomentumData.rest ν).u t x) +
        gradField ((TransportedMomentumData.rest ν).pressure t) x =
        (TransportedMomentumData.rest ν).ν •
          coordLaplacian ((TransportedMomentumData.rest ν).u t) x) ∧
    (∀ x : R3,
      IntervalIntegrable
        (fun t => ‖curlField ((TransportedMomentumData.rest ν).u t) x‖)
        MeasureTheory.volume 0 restDyadicData.T ∧
      ∫ t in (0 : ℝ)..restDyadicData.T,
          ‖curlField ((TransportedMomentumData.rest ν).u t) x‖ ≤
        (∫ t in (0 : ℝ)..restDyadicData.T, (fun _ : ℝ => (0 : ℝ)) t) +
          (restDyadicData.relaxationConst + (0 + 0 + 0)) /
            (1 - (0 + 0 + 0))) := by
  refine stochasticLagrangian_conditional_route_of_pancakeBudget
    (TransportedMomentumData.rest ν) restDyadicData
    (fun _ => 0) (fun _ => le_refl 0) intervalIntegrable_const
    (fun x => ?_) (fun t _ x => ?_)
    restDyadicData_strainBudget restDyadicData_coercive
    restDyadicData_residual (by norm_num)
  · have hconst : (fun t => curlField ((TransportedMomentumData.rest ν).u t) x) =
        fun _ => curlField (fun _ => (0 : R3)) x := rfl
    rw [hconst]
    exact MeasureTheory.aestronglyMeasurable_const
  · have hcurl : curlField ((TransportedMomentumData.rest ν).u t) x = 0 :=
      curlField_const 0 x
    rw [hcurl]
    simp [restDyadicData]

end DyadicPancakeClosureRegression
end NavierStokes
end FluidDynamics
end Mettapedia
