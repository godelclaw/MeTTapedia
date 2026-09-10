import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalInitialGradient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMaterialStrain
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpatialNavierStokesTangent

/-!
# Initial right derivative of the velocity gradient on a material trajectory

The material gradient equation extends to the initial endpoint by the
continuity of the actual gradient, pressure Hessian and viscous term.
The trajectory need only satisfy the equation in the interior and be
continuous on the closed existence interval.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MaterialInitialGradient

open scoped Topology Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeLocalMaterialTrajectories PancakeFourierMaterialPaths
open PancakeLocalMaterialGradient PancakeCurlOutputTail PancakeLocalGradientEquation
open PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian PancakeInfiniteSpatialCurl
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakePeriodicVorticityEquation
open PancakeLocalPressureContinuity PancakeCoefficientLimitEquation
open PancakeHigherDerivativeMoments
open LocalMaterialStrain LocalInitialGradient EndpointDerivative SpatialNavierStokesTangent

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "M3" => Matrix (Fin 3) (Fin 3) ℂ

/-- The ordinary material gradient rate, including the physical pressure and viscosity. -/
def materialGradientRate (nu : ℝ) (u : FourierVelocity) (x : T3) : M3 :=
  -spatialVelocityGradient (fullFourierField id u) x *
      spatialVelocityGradient (fullFourierField id u) x -
    spatialHessian (spatialPressure u) x +
    (nu : ℂ) • matrixLaplacian (spatialVelocityGradient (fullFourierField id u)) x

theorem materialGradientRate_eq_velocityRHS_of_stagnation (nu : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (x : T3) (hx : fullFourierField id u x = 0) :
    materialGradientRate nu u x =
      spatialVelocityGradient (fullFourierField id (infiniteVelocityRHS nu u)) x := by
  simpa only [materialGradientRate, neg_mul] using
    (gradient_infiniteVelocityRHS_of_stagnation nu u hu hd x hx).symm

/-- Evaluation on a continuous path preserves continuity at the initial endpoint. -/
theorem continuousOn_material_eval_closed {E : Type*} [TopologicalSpace E] {T : ℝ}
    (f : ℝ → T3 → E)
    (hf : Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ f z.1 z.2))
    (X : ℝ → X3) (hX : ContinuousOn X (Set.Icc (0 : ℝ) T)) :
    ContinuousOn (fun t ↦ f t (torusPoint (X t))) (Set.Icc (0 : ℝ) T) := by
  have hcX : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ X t) := hX.restrict
  have hp : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ torusPoint (X t)) :=
    continuous_pi (fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp hcX))
  exact continuousOn_iff_continuous_restrict.mpr (hf.comp (continuous_id.prodMk hp))

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
  (hu : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 3 (s.coefficients t) k ≤ g k)

include hSum hu

theorem continuous_velocityGradient_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      spatialVelocityGradient (spatialField s z.1) z.2) := by
  have hm (t : Set.Icc (0 : ℝ) T) : Summable (indexedFirstMoment id (s.coefficients t)) := by
    simpa only [indexedFirstMoment_id] using summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t t.2))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [spatialVelocityGradient, spatialField, coordinateDerivative_fullFourierField id _ (hm _)]
  exact (continuous_apply i).comp (continuous_eval.comp
    (((continuous_gradientField s g hSum hu j).comp continuous_fst).prodMk continuous_snd))

include hg

theorem continuous_materialGradientRate_spaceTime (hB : 0 ≤ B) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      materialGradientRate nu (s.coefficients z.1) z.2) := by
  have hu2 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients t) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q)
  have hG := continuous_velocityGradient_spaceTime s g hSum hu
  exact ((hG.neg.mul hG).sub
    (continuous_spatialHessian_pressure_spaceTime s hB g hg hSum hu2)).add
      ((continuous_laplacianGradient_spaceTime s g hSum hu).const_smul (nu : ℂ))

theorem velocityGradient_hasDerivWithinAt_initial (hT : 0 < T) (hB : 0 ≤ B)
    (X : ℝ → X3) (hXc : ContinuousOn X (Set.Icc (0 : ℝ) T))
    (hX : ∀ t ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s t (X t)) t) :
    HasDerivWithinAt (fun t ↦ spatialVelocityGradient (spatialField s t) (torusPoint (X t)))
      (materialGradientRate nu u₀ (torusPoint (X 0))) (Set.Ici (0 : ℝ)) 0 := by
  have hc := continuousOn_material_eval_closed (E := M3)
    (fun t x ↦ spatialVelocityGradient (spatialField s t) x)
    (continuous_velocityGradient_spaceTime s g hSum hu) X hXc
  have hdc := continuousOn_material_eval_closed (E := M3)
    (fun t x ↦ materialGradientRate nu (s.coefficients t) x)
    (continuous_materialGradientRate_spaceTime s g hg hSum hu hB) X hXc
  apply hasDerivWithinAt_pi.mpr
  intro i
  apply hasDerivWithinAt_pi.mpr
  intro j
  have hd := hasDerivWithinAt_Ici_of_continuousOn hT
    (f := fun t ↦ spatialVelocityGradient (spatialField s t) (torusPoint (X t)) i j)
    (df := fun t ↦ materialGradientRate nu (s.coefficients t) (torusPoint (X t)) i j)
    ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hc))
    ((continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn hdc))
    (fun t ht ↦ (hasDerivAt_pi.mp ((hasDerivAt_pi.mp
      (velocityGradient_material s g hg hSum hu X hX t ht)) i)) j)
  simpa only [s.initial] using hd

end Mettapedia.FluidDynamics.NavierStokes.MaterialInitialGradient
