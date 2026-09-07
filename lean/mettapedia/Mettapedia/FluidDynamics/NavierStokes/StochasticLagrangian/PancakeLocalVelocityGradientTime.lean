import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeVelocityGradientEnvelope

/-!
# Time differentiation of the actual local velocity gradient

The common third-moment envelope pays the differentiated RHS. Equality
with ordinary spatial derivatives is used only on the local interval.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalVelocityGradientTime

open scoped Topology
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCoefficientLimitEquation
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity PancakeInfiniteFourierTime
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeCurlOutputTail
open PancakeIndexedFourierMoments PancakeHigherDerivativeMoments PancakeVelocityGradientEnvelope
open PancakeInfiniteVelocityEnvelope PancakePeriodicVorticityEquation

local notation "T3" => UnitAddTorus (Fin 3)

theorem coefficientGradient_hasDerivAt {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (j : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (q : Wavevector) (i : Fin 3) :
    HasDerivAt (fun τ ↦ indexedDerivativeCoeff id j (s.coefficients τ) q i)
      (indexedDerivativeCoeff id j (infiniteVelocityRHS nu (s.coefficients t)) q i) t := by
  exact (s.equation t ht q i).const_mul _

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
  (hu : ∀ τ, τ ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 3 (s.coefficients τ) k ≤ g k)

include hg hSum hu

theorem fullGradientField_hasDerivAt (j : Fin 3) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ fullFourierField id (indexedDerivativeCoeff id j (s.coefficients τ)))
      (fullFourierField id (indexedDerivativeCoeff id j
        (infiniteVelocityRHS nu (s.coefficients t)))) t := by
  apply hasDerivAt_fullFourierField_time
    (fun τ ↦ indexedDerivativeCoeff id j (s.coefficients τ))
    (fun τ ↦ indexedDerivativeCoeff id j (infiniteVelocityRHS nu (s.coefficients τ)))
    (Set.Ioo (0 : ℝ) T) isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
    (fun q ↦ (2 * Real.pi) * velocityEnvelope nu g q)
    ((summable_velocityEnvelope nu g hg hSum).mul_left (2 * Real.pi))
    (coefficientGradient_hasDerivAt s j)
  · intro τ hτ q
    exact norm_velocityRHS_derivative_le nu _ g hg hSum (hu τ ⟨hτ.1.le, hτ.2.le⟩) j q
  · exact ht
  · apply summable_norm_derivativeCoefficients id _ _ j
    simpa only [indexedFirstMoment_id] using
      summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
        (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩))

theorem spatialField_coordinateDerivative_hasDerivAt (j : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun τ ↦ coordinateDerivative (spatialField s τ) j x)
      (fullFourierField id (indexedDerivativeCoeff id j
        (infiniteVelocityRHS nu (s.coefficients t))) x) t := by
  have h := (ContinuousMap.evalCLM (R := ℝ) (M := VelocityCoefficient) x).hasFDerivAt.comp_hasDerivAt t (fullGradientField_hasDerivAt s g hg hSum hu j t ht)
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ ⟨hτ.1.le, hτ.2.le⟩)
  exact coordinateDerivative_fullFourierField id _
    (by simpa only [indexedFirstMoment_id] using
      (summable_fourierMoment_of_le _ (by omega : 1 ≤ 3) hm)) j x

theorem spatialField_gradient_time_space (j : Fin 3)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun τ ↦ coordinateDerivative (spatialField s τ) j x)
      (coordinateDerivative
        (fullFourierField id (infiniteVelocityRHS nu (s.coefficients t))) j x) t := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  rw [coordinateDerivative_fullFourierField id _
    (by simpa only [indexedFirstMoment_id] using summable_firstMoment_velocityRHS nu _ hm) j x]
  exact spatialField_coordinateDerivative_hasDerivAt s g hg hSum hu j t ht x

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalVelocityGradientTime
