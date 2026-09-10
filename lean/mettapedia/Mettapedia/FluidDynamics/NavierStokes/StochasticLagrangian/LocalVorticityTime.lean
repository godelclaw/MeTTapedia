import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAlignmentContinuity

/-!
# Uniform time regularity of the actual full vorticity

The curl of the actual velocity RHS has a summable envelope under a common
third velocity moment. Differentiation in the continuous-field norm gives
a spatially uniform time Lipschitz estimate on compact interior intervals.
No closed finite-mode equation or externally supplied vorticity rate is used.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityTime

open scoped Topology NNReal
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeInfiniteFourierDerivative PancakeInfiniteFourierTime PancakeInfiniteSpatialCurl
open PancakeCurlOutputTail PancakeGalerkinKineticEnergy PancakeGalerkinVorticityBridge
open PancakeIndexedFourierMoments PancakeVelocityGradientEnvelope PancakeCoefficientLimitEquation
open PancakeInfiniteVelocityEnvelope PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeFourierMaterialPaths PancakeDyadicDirectionEvolution PancakeFourierTranslationCurve
open LocalVorticityDiffusion LocalLowDiffusionBudget

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem norm_fullFourierField_uniform_le (u : FourierVelocity)
    (g : Wavevector → ℝ) (hSum : Summable g) (hu : ∀ q, ‖u q‖ ≤ g q) :
    ‖fullFourierField id u‖ ≤ ∑' q, g q := by
  exact tsum_of_norm_bounded hSum.hasSum (fun q ↦ (norm_modeField_le q (u q)).trans (hu q))

theorem norm_curl_velocityRHS_le (nu : ℝ) (u : FourierVelocity)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ q, fourierMoment 3 u q ≤ g q) (q : Wavevector) :
    ‖fourierCurl (infiniteVelocityRHS nu u) q‖ ≤ (2 * Real.pi) * velocityEnvelope nu g q := by
  calc
    _ ≤ ‖coefficientVec (fourierCurl (infiniteVelocityRHS nu u) q)‖ :=
      norm_coefficient_sup_le_euclidean _
    _ ≤ (2 * Real.pi) * ‖frequencyVec q‖ * ‖coefficientVec (infiniteVelocityRHS nu u q)‖ :=
      norm_fourierCurl_le _ q
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (norm_frequency_mul_velocityRHS_le nu u g hg hSum hu q)
        (by positivity)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hg hSum hu

theorem fullCurlField_hasDerivAt (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ fullFourierField id (fourierCurl (s.coefficients τ)))
      (fullFourierField id (fourierCurl (infiniteVelocityRHS nu (s.coefficients t)))) t := by
  apply hasDerivAt_fullFourierField_time
    (fun τ ↦ fourierCurl (s.coefficients τ))
    (fun τ ↦ fourierCurl (infiniteVelocityRHS nu (s.coefficients τ)))
    (Set.Ioo (0 : ℝ) T) isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
    (fun q ↦ (2 * Real.pi) * velocityEnvelope nu g q)
    ((summable_velocityEnvelope nu g hg hSum).mul_left _)
  · intro τ hτ q i
    exact hasDerivAt_fourierCurl s.coefficients _ τ q (s.equation τ hτ q) i
  · intro τ hτ q
    exact norm_curl_velocityRHS_le nu _ g hg hSum (hu τ ⟨hτ.1.le, hτ.2.le⟩) q
  · exact ht
  · have hm := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
      (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩))
    exact summable_norm_curlCoefficients id _ (by simpa only [indexedFirstMoment_id] using hm)

theorem fullVorticity_hasDerivAt (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : T3) :
    HasDerivAt (fun τ ↦ fullVorticity (s.coefficients τ) x)
      (complexRealPartEuclideanCLM
        (fullFourierField id (fourierCurl (infiniteVelocityRHS nu (s.coefficients t))) x)) t := by
  have hd := complexRealPartEuclideanCLM.hasFDerivAt.comp_hasDerivAt t
    ((ContinuousMap.evalCLM (R := ℝ) (M := VelocityCoefficient) x).hasFDerivAt.comp_hasDerivAt t
      (fullCurlField_hasDerivAt s g hg hSum hu t ht))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
  have hm := summable_fourierMoment_of_le _ (by omega : 1 ≤ 3)
    (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu τ ⟨hτ.1.le, hτ.2.le⟩))
  simp only [Function.comp_def, ContinuousMap.evalCLM_apply, fullVorticity, spatialCurl_velocity _ hm]

theorem lipschitzOnWith_fullCurlField {a b : ℝ} (hI : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) T) :
    LipschitzOnWith (Real.toNNReal (∑' q, (2 * Real.pi) * velocityEnvelope nu g q))
      (fun τ ↦ fullFourierField id (fourierCurl (s.coefficients τ))) (Set.Icc a b) := by
  apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun τ hτ ↦ (fullCurlField_hasDerivAt s g hg hSum hu τ (hI hτ)).hasDerivWithinAt)
  intro τ hτ
  have hb := norm_fullFourierField_uniform_le _ _
    ((summable_velocityEnvelope nu g hg hSum).mul_left (2 * Real.pi))
    (norm_curl_velocityRHS_le nu _ g hg hSum (hu τ (Set.Ioo_subset_Icc_self (hI hτ))))
  exact_mod_cast hb.trans (Real.le_coe_toNNReal _)

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityTime
