import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfinitePressurePoisson

/-!
# Local time-space continuity of pressure and its Hessian

The same local second-moment envelope controls the pressure, gradient, and
Hessian uniformly in time. The pressure Hessian in the strain equation
therefore belongs to the constructed evolving velocity, not a separate field.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalPressureContinuity

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCoefficientLimitEquation PancakeConvectionPathLimit PancakeLocalInfiniteVelocity
open PancakeLocalSpatialVelocity PancakeInfiniteFourierDerivative PancakeFourierTranslationCurve
open PancakeInfinitePressureCoefficients PancakeInfiniteSpatialPressure PancakeInfinitePressureHessian
open PancakeInfiniteVelocityEnvelope PancakeCurlOutputTail PancakePeriodicVorticityEquation

local notation "T3" => UnitAddTorus (Fin 3)

theorem continuous_scalarFullFourierField {X : Type*} [TopologicalSpace X]
    (a : X → Wavevector → ℂ) (hc : ∀ q, Continuous (fun t ↦ a t q))
    (g : Wavevector → ℝ) (hg : Summable g) (ha : ∀ t q, ‖a t q‖ ≤ g q) :
    Continuous (fun t ↦ fullFourierField id (a t)) := by
  have hm (q : Wavevector) : Continuous (fun t ↦ modeField q (a t q)) := by
    have he : (fun t ↦ modeField q (a t q)) = fun t ↦ a t q • modeField q (1 : ℂ) := by
      funext t
      rw [← modeField_smul]
      simp only [smul_eq_mul, mul_one]
    rw [he]
    exact (hc q).smul continuous_const
  exact continuous_tsum hm hg (fun q t ↦ (norm_modeField_le q _).trans (ha t q))

theorem continuous_infiniteConvection_component {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
    (q : Wavevector) (i : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ infiniteConvection (s.coefficients t) q i) := by
  have he :
      (fun t : Set.Icc (0 : ℝ) T ↦ infiniteConvection (s.coefficients t) q i) =
      fun t ↦ convectionPath q (infiniteSolutionPaths s) i t := by
    funext t
    exact (convectionPath_apply q (infiniteSolutionPaths s) B hB
      (fun t F ↦ s.sobolev_bound t t.2 F) i t).symm
  rw [he]
  exact (convectionPath q (infiniteSolutionPaths s) i).continuous

theorem continuous_infinitePressureCoeff {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B) (q : Wavevector) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ infinitePressureCoeff (s.coefficients t) q) := by
  have hc := continuous_infiniteConvection_component s hB q
  unfold infinitePressureCoeff modeDot
  fun_prop

variable {nu T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution nu u₀ T B) (hB : 0 ≤ B)
  (g : Wavevector → ℝ) (hg : ∀ k, 0 ≤ g k) (hSum : Summable g)
  (hu : ∀ τ, τ ∈ Set.Icc (0 : ℝ) T → ∀ k, fourierMoment 2 (s.coefficients τ) k ≤ g k)

include hB hg hSum hu

theorem continuous_spatialPressure_field :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ spatialPressure (s.coefficients t)) := by
  apply continuous_scalarFullFourierField _ (continuous_infinitePressureCoeff s hB)
    (fun q ↦ 3 * convolutionEnvelope g q)
    ((summable_convolutionEnvelope g hg hSum).mul_left 3)
  intro t q
  exact (norm_infinitePressureCoeff_le _ q).trans
    (norm_infiniteConvection_le _ g hg hSum (hu t t.2) q)

theorem continuous_pressureDerivative_field (j : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      fullFourierField id (indexedDerivativeCoeff id j (infinitePressureCoeff (s.coefficients t)))) := by
  have hc (q : Wavevector) : Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      indexedDerivativeCoeff id j (infinitePressureCoeff (s.coefficients t)) q) := by
    unfold indexedDerivativeCoeff
    exact continuous_const.smul (continuous_infinitePressureCoeff s hB q)
  apply continuous_scalarFullFourierField _ hc
    (fun q ↦ ((2 * Real.pi) * 3) * convolutionEnvelope g q)
    ((summable_convolutionEnvelope g hg hSum).mul_left _)
  intro t q
  apply (norm_infinitePressureDerivative_le _ j q).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (norm_infiniteConvection_le _ g hg hSum (hu t t.2) q)
      (by positivity : 0 ≤ 2 * Real.pi)

theorem continuous_pressureSecondDerivative_field (i j : Fin 3) :
    Continuous (fun t : Set.Icc (0 : ℝ) T ↦ fullFourierField id
      (indexedDerivativeCoeff id j
        (indexedDerivativeCoeff id i (infinitePressureCoeff (s.coefficients t))))) := by
  have hc (q : Wavevector) : Continuous (fun t : Set.Icc (0 : ℝ) T ↦
      indexedDerivativeCoeff id j
        (indexedDerivativeCoeff id i (infinitePressureCoeff (s.coefficients t))) q) := by
    unfold indexedDerivativeCoeff
    exact continuous_const.smul (continuous_const.smul (continuous_infinitePressureCoeff s hB q))
  apply continuous_scalarFullFourierField _ hc
    (fun q ↦ ((2 * Real.pi)^2 * 3) * convolutionEnvelope g q)
    ((summable_convolutionEnvelope g hg hSum).mul_left _)
  intro t q
  apply (norm_infinitePressureSecondDerivative_le _ i j q).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (norm_frequency_mul_infiniteConvection_le _ g hg hSum (hu t t.2) q)
      (sq_nonneg (2 * Real.pi))

theorem continuous_spatialPressure_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦ spatialPressure (s.coefficients z.1) z.2) :=
  continuous_eval.comp
    (((continuous_spatialPressure_field s hB g hg hSum hu).comp continuous_fst).prodMk continuous_snd)

theorem continuous_spatialGradient_pressure_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      spatialGradient (spatialPressure (s.coefficients z.1)) z.2) := by
  apply continuous_pi
  intro j
  have he : (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      spatialGradient (spatialPressure (s.coefficients z.1)) z.2 j) =
      fun z ↦ fullFourierField id
        (indexedDerivativeCoeff id j (infinitePressureCoeff (s.coefficients z.1))) z.2 := by
    funext z
    have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu z.1 z.1.2)
    exact scalarCoordinateDerivative_fullFourierField _
      (summable_norm_infinitePressure _ hm) j
      (summable_norm_infinitePressureDerivative _ hm j) z.2
  rw [he]
  exact continuous_eval.comp
    (((continuous_pressureDerivative_field s hB g hg hSum hu j).comp continuous_fst).prodMk continuous_snd)

theorem continuous_spatialHessian_pressure_spaceTime :
    Continuous (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      spatialHessian (spatialPressure (s.coefficients z.1)) z.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have he : (fun z : Set.Icc (0 : ℝ) T × T3 ↦
      spatialHessian (spatialPressure (s.coefficients z.1)) z.2 i j) =
      fun z ↦ fullFourierField id
        (indexedDerivativeCoeff id j
          (indexedDerivativeCoeff id i (infinitePressureCoeff (s.coefficients z.1)))) z.2 := by
    funext z
    have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu z.1 z.1.2)
    exact scalarCoordinateDerivative2_spatialPressure _ hm i j z.2
  rw [he]
  exact continuous_eval.comp
    (((continuous_pressureSecondDerivative_field s hB g hg hSum hu i j).comp continuous_fst).prodMk continuous_snd)

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalPressureContinuity
