import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.EndpointDerivative
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalGradientEquation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityDiffusion

/-!
# Initial right derivative of the actual local velocity gradient

The third-moment envelope controls both the gradient series and its
Navier–Stokes time derivative continuously up to time zero. The interior
equation therefore extends to a right derivative at the initial endpoint.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalInitialGradient

open scoped Topology Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCoefficientLimitEquation
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity PancakeInfiniteFourierTime
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeCurlOutputTail
open PancakeIndexedFourierMoments PancakeHigherDerivativeMoments PancakeVelocityGradientEnvelope
open PancakeInfiniteVelocityEnvelope PancakePeriodicVorticityEquation PancakeLocalVelocityGradientTime
open PancakeLocalGradientEquation LocalVorticityDiffusion EndpointDerivative

local notation "T3" => UnitAddTorus (Fin 3)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
  (hu : ∀ t, t ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 3 (s.coefficients t) k ≤ g k)

include hSum hu

theorem continuous_gradientField (j : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      fullFourierField id (indexedDerivativeCoeff id j (s.coefficients t))) := by
  refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi) * g q)
    (hSum.mul_left _) ?_
  · intro q i
    exact continuous_const.mul ((s.continuous q i).comp continuous_subtype_val)
  · intro t q
    calc
      _ ≤ fourierMoment 0 (indexedDerivativeCoeff id j (s.coefficients t)) q := by
        simpa only [fourierMoment, pow_zero, one_mul] using
          norm_coefficient_sup_le_euclidean (indexedDerivativeCoeff id j (s.coefficients t) q)
      _ ≤ (2 * Real.pi) * fourierMoment 1 (s.coefficients t) q :=
        fourierMoment_derivative_le 0 _ j q
      _ ≤ (2 * Real.pi) * g q := mul_le_mul_of_nonneg_left
        ((fourierMoment_mono _ (by omega : 1 ≤ 3) q).trans (hu t t.2 q)) (by positivity)

include hg

theorem continuous_gradientRHSField (hB : 0 ≤ B) (j : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ fullFourierField id
      (indexedDerivativeCoeff id j (infiniteVelocityRHS nu (s.coefficients t)))) := by
  refine continuous_fullFourierField_of_norm_le _ ?_
    (fun q ↦ (2 * Real.pi) * velocityEnvelope nu g q)
    ((summable_velocityEnvelope nu g hg hSum).mul_left _) ?_
  · intro q i
    exact continuous_const.mul (continuous_velocityRHS_component s hB q i)
  · intro t q
    exact norm_velocityRHS_derivative_le nu _ g hg hSum (hu t t.2) j q

theorem gradientField_hasDerivWithinAt_initial (hT : 0 < T) (hB : 0 ≤ B) (j : Fin 3) :
    HasDerivWithinAt
      (fun t ↦ fullFourierField id (indexedDerivativeCoeff id j (s.coefficients t)))
      (fullFourierField id (indexedDerivativeCoeff id j (infiniteVelocityRHS nu u₀)))
      (Set.Ici (0 : ℝ)) 0 := by
  have hd := hasDerivWithinAt_Ici_of_continuousOn hT
    (f := fun t ↦ fullFourierField id (indexedDerivativeCoeff id j (s.coefficients t)))
    (df := fun t ↦ fullFourierField id
      (indexedDerivativeCoeff id j (infiniteVelocityRHS nu (s.coefficients t))))
    (continuousOn_iff_continuous_restrict.mpr (continuous_gradientField s g hSum hu j))
    (continuousOn_iff_continuous_restrict.mpr (continuous_gradientRHSField s g hg hSum hu hB j))
    (fullGradientField_hasDerivAt s g hg hSum hu j)
  simpa only [s.initial] using hd

theorem coordinateDerivative_hasDerivWithinAt_initial
    (hT : 0 < T) (hB : 0 ≤ B) (j : Fin 3) (x : T3) :
    HasDerivWithinAt (fun t ↦ coordinateDerivative (spatialField s t) j x)
      (coordinateDerivative (fullFourierField id (infiniteVelocityRHS nu u₀)) j x)
      (Set.Ici (0 : ℝ)) 0 := by
  have hm (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      Summable (fourierMoment 3 (s.coefficients t)) :=
    hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)
  have hmi : Summable (fourierMoment 3 u₀) := by
    simpa only [s.initial] using hm 0 ⟨le_rfl, hT.le⟩
  rw [coordinateDerivative_fullFourierField id _
    (by simpa only [indexedFirstMoment_id] using summable_firstMoment_velocityRHS nu u₀ hmi)]
  have hd := (ContinuousMap.evalCLM (R := ℝ) (M := VelocityCoefficient) x).hasFDerivAt.comp_hasDerivWithinAt
    0 (gradientField_hasDerivWithinAt_initial s g hg hSum hu hT hB j)
  apply hd.congr_of_eventuallyEq
  · filter_upwards [Icc_mem_nhdsGE hT] with t ht
    exact coordinateDerivative_fullFourierField id _
      (by simpa only [indexedFirstMoment_id] using
        summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) (hm t ht)) j x
  · exact coordinateDerivative_fullFourierField id _
      (by simpa only [indexedFirstMoment_id] using
        summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) (hm 0 ⟨le_rfl, hT.le⟩)) j x

theorem velocityGradient_hasDerivWithinAt_initial (hT : 0 < T) (hB : 0 ≤ B) (x : T3) :
    HasDerivWithinAt (fun t ↦ spatialVelocityGradient (spatialField s t) x)
      (spatialVelocityGradient (fullFourierField id (infiniteVelocityRHS nu u₀)) x)
      (Set.Ici (0 : ℝ)) 0 := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  apply hasDerivWithinAt_pi.mpr
  intro j
  exact hasDerivWithinAt_pi.mp
    (coordinateDerivative_hasDerivWithinAt_initial s g hg hSum hu hT hB j x) i

end Mettapedia.FluidDynamics.NavierStokes.LocalInitialGradient
