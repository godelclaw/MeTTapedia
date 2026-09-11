import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthSpatialBalance
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalMeanAlignmentBalance

/-!
# Endpoint continuity of the actual eighth-moment densities

A common third absolute Fourier moment justifies space-time continuity,
including the initial endpoint. It is used only for convergence and
integrability, not as an asserted uniform estimate at a singular time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment

open scoped RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeFourierMaterialPaths PancakeHigherDerivativeMoments PancakeLocalInfiniteVelocity
open PancakeFourierTranslationCurve PancakeDyadicDirectionEvolution PancakeIndexedFourierMoments
open PancakeInfiniteFourierDerivative
open PancakeGalerkinKineticEnergy PancakePeriodicComplexStretch
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityDiffusion LocalAlignmentContinuity
open GaussianRootWeightedIncrement (weightedPalinstrophyDensity)

local notation "T3" => UnitAddTorus (Fin 3)
local instance eighthContinuityCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance eighthContinuityCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance eighthContinuityCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hSum : Summable g)
  (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)

include hSum hu

theorem continuous_fullCurlGradient_spaceTime (j : Fin 3) :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ fullCurlGradient (s.coefficients z.1) j z.2) := by
  have hc : Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      fullFourierField id (indexedDerivativeCoeff id j (fourierCurl (s.coefficients t)))) := by
    refine continuous_fullFourierField_of_norm_le _ ?_ (fun q ↦ (2 * Real.pi) ^ 2 * g q)
      (hSum.mul_left _) ?_
    · intro q i
      have hc (k : Fin 3) : Continuous (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t q k) :=
        (s.continuous q k).comp continuous_subtype_val
      fin_cases i <;> simp only [indexedDerivativeCoeff, fourierCurl, coefficientCross,
        Pi.smul_apply, smul_eq_mul] <;> fun_prop
    · intro t q
      calc
        _ ≤ fourierMoment 0 (indexedDerivativeCoeff id j (fourierCurl (s.coefficients t))) q := by
          simpa only [fourierMoment, pow_zero, one_mul] using norm_coefficient_sup_le_euclidean
            (indexedDerivativeCoeff id j (fourierCurl (s.coefficients t)) q)
        _ ≤ (2 * Real.pi) * fourierMoment 1 (fourierCurl (s.coefficients t)) q :=
          fourierMoment_derivative_le 0 _ j q
        _ ≤ (2 * Real.pi) * ((2 * Real.pi) * fourierMoment 2 (s.coefficients t) q) :=
          mul_le_mul_of_nonneg_left (fourierMoment_curl_le 1 _ q) (by positivity)
        _ ≤ (2 * Real.pi) * ((2 * Real.pi) * g q) := by
          gcongr
          exact (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t t.2 q)
        _ = _ := by ring
  exact complexRealPartEuclideanCLM.continuous.comp
    (continuous_eval.comp ((hc.comp continuous_fst).prodMk continuous_snd))

theorem continuous_energy_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ energy (s.coefficients z.1) z.2) :=
  (((continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))).norm.pow 2).pow 4)

theorem continuous_weightedPalinstrophyDensity_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ weightedPalinstrophyDensity (s.coefficients z.1) z.2) := by
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))
  exact (hw.norm.pow 6).mul (continuous_finsetSum _
    (fun j _ ↦ (continuous_fullCurlGradient_spaceTime s g hSum hu j).norm.pow 2))

theorem continuous_radialGradientDensity_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ radialGradientDensity (s.coefficients z.1) z.2) := by
  have hw := continuous_fullVorticity_spaceTime s g hSum
    (fun t ht q ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q))
  exact (hw.norm.pow 4).mul (continuous_finsetSum _
    (fun j _ ↦ (hw.inner (continuous_fullCurlGradient_spaceTime s g hSum hu j)).pow 2))

theorem continuous_stretchingDensity_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ stretchingDensity (s.coefficients z.1) z.2) := by
  have hu2 (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :
      fourierMoment 2 (s.coefficients t) q ≤ g q :=
    (fourierMoment_mono _ (by omega : 2 ≤ 3) q).trans (hu t ht q)
  have hw := continuous_fullVorticity_spaceTime s g hSum hu2
  have hS := continuous_fullStrainOperator_parametric
    (fun t : Set.Icc (0 : ℝ) T ↦ s.coefficients t)
    (fun q i ↦ (s.continuous q i).comp continuous_subtype_val) g hSum (fun t ↦ hu2 t t.2)
  exact (hw.norm.pow 6).mul (hw.inner (hS.clm_apply hw))

end Mettapedia.FluidDynamics.NavierStokes.LocalVorticityEighthMoment
