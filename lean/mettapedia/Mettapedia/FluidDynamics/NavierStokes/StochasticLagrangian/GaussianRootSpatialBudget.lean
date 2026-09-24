import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianSquaredRootTranslation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A first-moment spatial budget for Gaussian pressure localization

We integrate the actual finite patch-square sum in space before taking
its square root. The common kernel envelope then occurs to the first
power, so its wrapped first moment retains the inverse input-scale gain.
The vorticity supremum and the actual squared-patch gradient energy are
explicit costs, not estimates uniform in time or in the adaptive gates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialBudget

open MeasureTheory Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakeHigherDerivativeMoments PancakeFrequencyProjectorCommutator FourierPressureTraceSymbol
open LocalLowDiffusionBudget LocalGaussianPressurePartition GaussianRootVorticity GaussianRootPartition
open GaussianSquaredRootLocalization GaussianSquaredRootTranslation GaussianRootEnvelope
open PancakeBilinearPeriodization PressureDyadicPeriodization FrequencyPairPeriodization

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def rootLocalizationSpatialNorm (N : ℝ) (hN : 0 < N) (t gamma : ℝ)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) (q : T6) : ℝ :=
  Real.sqrt (∫ x : T3, ∑ i : ↑centers,
    ‖rootLocalizationIntegrand N hN t gamma chi modes u centers tau q x i‖ ^ 2)

theorem rootLocalizationSpatialNorm_nonneg (N : ℝ) (hN : 0 < N) (t gamma : ℝ)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) (q : T6) :
    0 ≤ rootLocalizationSpatialNorm N hN t gamma chi modes u centers tau q := Real.sqrt_nonneg _

theorem continuous_rootLocalizationIntegrand (N : ℝ) (hN : 0 < N) (t gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (q : T6) (i : ↑centers) :
    Continuous (fun x ↦ rootLocalizationIntegrand N hN t gamma chi modes u centers tau q x i) := by
  have hp := continuous_rootPatch gamma hg chi modes u hu centers hc tau i
  have hw := continuous_fullVorticity u hu
  have hwc : Continuous (fun x ↦ complexifyVector (fullVorticity u x)) := by
    unfold complexifyVector coefficientVec
    fun_prop
  unfold rootLocalizationIntegrand
  fun_prop

theorem integrable_sum_norm_rootLocalizationIntegrand_sq
    (N : ℝ) (hN : 0 < N) (t gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (q : T6) :
    Integrable (fun x : T3 ↦ ∑ i : ↑centers,
      ‖rootLocalizationIntegrand N hN t gamma chi modes u centers tau q x i‖ ^ 2) := by
  apply integrable_finsetSum
  intro i _
  exact ((continuous_rootLocalizationIntegrand N hN t gamma hg chi modes u hu centers hc tau q i
    ).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem measurable_rootLocalizationSpatialNorm (N : ℝ) (hN : 0 < N) (t gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) :
    Measurable (rootLocalizationSpatialNorm N hN t gamma chi modes u centers tau) := by
  have hp := continuous_rootPatch gamma hg chi modes u hu centers hc tau
  have hw := continuous_fullVorticity u hu
  have hwc : Continuous (fun x ↦ complexifyVector (fullVorticity u x)) := by
    unfold complexifyVector coefficientVec
    fun_prop
  have hi (i : ↑centers) : Measurable (fun z : T6 × T3 ↦
      rootLocalizationIntegrand N hN t gamma chi modes u centers tau z.1 z.2 i) := by
    have hK : Measurable (fun z : T6 × T3 ↦ periodicKernel N hN t
        (localDirection chi modes u i.1) z.1) :=
      (measurable_periodicKernel N hN t (localDirection chi modes u i.1)).comp measurable_fst
    have hfirst : Continuous (fun z : T6 × T3 ↦ z.2 - firstTorusDisplacement z.1) := by fun_prop
    have hsecond : Continuous (fun z : T6 × T3 ↦ z.2 - secondTorusDisplacement z.1) := by fun_prop
    have happly := (continuous_fst.clm_apply continuous_snd).measurable.comp
      (hK.prodMk (hwc.comp hfirst).measurable)
    have happly2 := (continuous_fst.clm_apply continuous_snd).measurable.comp
      (happly.prodMk (hwc.comp hsecond).measurable)
    have hweighted := (continuous_fst.clm_apply continuous_snd).measurable.comp
      (hK.prodMk (((Complex.continuous_ofReal.comp (hp i)).comp hfirst).smul
        (hwc.comp hfirst)).measurable)
    have hweighted2 := (continuous_fst.clm_apply continuous_snd).measurable.comp
      (hweighted.prodMk (((Complex.continuous_ofReal.comp (hp i)).comp hsecond).smul
        (hwc.comp hsecond)).measurable)
    exact (((Complex.continuous_ofReal.comp (hp i)).comp continuous_snd).measurable.mul
      ((Complex.continuous_ofReal.comp (hp i)).comp continuous_snd).measurable).smul happly2
      |>.sub hweighted2
  have hm : StronglyMeasurable (fun z : T6 × T3 ↦ ∑ i : ↑centers,
      ‖rootLocalizationIntegrand N hN t gamma chi modes u centers tau z.1 z.2 i‖ ^ 2) :=
    (Finset.measurable_sum _ (fun i _ ↦ (hi i).norm.pow_const 2)).stronglyMeasurable
  exact hm.integral_prod_right.measurable.sqrt

theorem ae_rootLocalizationSpatialNorm_le (N : ℝ) (hN : 0 < N) (t : ℝ)
    (M : T6 → ℝ) (hMn : ∀ q, 0 ≤ M q)
    (hM : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 → ‖periodicKernel N hN t e q‖ ≤ M q)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau W : ℝ)
    (hW : ∀ x : T3, ‖fullVorticity u x‖ ≤ W) :
    ∀ᵐ q : T6, rootLocalizationSpatialNorm N hN t gamma chi modes u centers tau q ≤
      (M q * ‖q‖) * (W ^ 2 * Real.sqrt (6 *
        ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x)) := by
  let G := ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x
  have hG : 0 ≤ G := integral_nonneg (squaredRootGradientSquare_nonneg gamma chi modes u centers tau)
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu
  have hD (a : T3) : Integrable (fun x : T3 ↦
      squaredPatchDifference gamma chi modes u centers tau x (x - a)) :=
    (continuous_squaredPatchDifference_translate gamma hg chi modes u hu1 centers hc tau a
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgrad := integral_squaredPatchDifference_translate_le gamma hg chi modes u hu centers hc tau
  filter_upwards [ae_sum_norm_rootLocalizationIntegrand_sq_le N hN t M hM gamma chi modes u centers tau]
    with q hq
  have hMq := hMn q
  let a := firstTorusDisplacement q
  let b := secondTorusDisplacement q
  have hnonneg (x y : T3) : 0 ≤ squaredPatchDifference gamma chi modes u centers tau x y :=
    Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hpoint (x : T3) : (∑ i : ↑centers,
      ‖rootLocalizationIntegrand N hN t gamma chi modes u centers tau q x i‖ ^ 2) ≤
      M q ^ 2 * W ^ 4 * (squaredPatchDifference gamma chi modes u centers tau x (x - a) +
        squaredPatchDifference gamma chi modes u centers tau x (x - b)) := by
    apply (hq x).trans
    have ha := pow_le_pow_left₀ (norm_nonneg _) (hW (x - a)) 2
    have hb := pow_le_pow_left₀ (norm_nonneg _) (hW (x - b)) 2
    have hh := mul_le_mul ha hb (sq_nonneg _) (sq_nonneg W)
    calc
      _ = M q ^ 2 * (‖fullVorticity u (x - a)‖ ^ 2 * ‖fullVorticity u (x - b)‖ ^ 2) *
          (squaredPatchDifference gamma chi modes u centers tau x (x - a) +
            squaredPatchDifference gamma chi modes u centers tau x (x - b)) := by ring
      _ ≤ M q ^ 2 * (W ^ 2 * W ^ 2) * _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (sq_nonneg _))
          (add_nonneg (hnonneg _ _) (hnonneg _ _))
      _ = _ := by ring
  have hbound := integral_mono_ae
    (integrable_sum_norm_rootLocalizationIntegrand_sq N hN t gamma hg chi modes u hu1 centers hc tau q)
    (((hD a).add (hD b)).const_mul (M q ^ 2 * W ^ 4)) (Eventually.of_forall hpoint)
  rw [integral_const_mul] at hbound
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hD a) (hD b)] at hbound
  have htrans : (∫ x : T3, squaredPatchDifference gamma chi modes u centers tau x (x - a)) +
      (∫ x : T3, squaredPatchDifference gamma chi modes u centers tau x (x - b)) ≤ 6 * ‖q‖ ^ 2 * G := by
    have ha := (hgrad a).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_firstTorusDisplacement_le q) 2)
        (by norm_num : (0 : ℝ) ≤ 3)) hG)
    have hb := (hgrad b).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_secondTorusDisplacement_le q) 2)
        (by norm_num : (0 : ℝ) ≤ 3)) hG)
    linarith
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hs : (Real.sqrt (6 * G)) ^ 2 = 6 * G := Real.sq_sqrt (by positivity)
  calc
    _ ≤ M q ^ 2 * W ^ 4 * (6 * ‖q‖ ^ 2 * G) := hbound.trans
      (mul_le_mul_of_nonneg_left htrans (by positivity))
    _ = _ := by
      change _ = ((M q * ‖q‖) * (W ^ 2 * Real.sqrt (6 * G))) ^ 2
      simp only [mul_pow, hs]
      ring

theorem integrable_rootLocalizationSpatialNorm_and_integral_le
    (N : ℝ) (hN : 0 < N) (t : ℝ) (M : T6 → ℝ) (hMn : ∀ q, 0 ≤ M q)
    (hMi : Integrable (fun q : T6 ↦ ‖q‖ * M q))
    (hM : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 → ‖periodicKernel N hN t e q‖ ≤ M q)
    (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
    (centers : Finset T3) (hc : centers.Nonempty) (tau W : ℝ)
    (hW : ∀ x : T3, ‖fullVorticity u x‖ ≤ W) :
    Integrable (rootLocalizationSpatialNorm N hN t gamma chi modes u centers tau) ∧
    (∫ q : T6, rootLocalizationSpatialNorm N hN t gamma chi modes u centers tau q) ≤
      (∫ q : T6, ‖q‖ * M q) * (W ^ 2 * Real.sqrt (6 *
        ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x)) := by
  let B := W ^ 2 * Real.sqrt (6 * ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x)
  have hb := ae_rootLocalizationSpatialNorm_le N hN t M hMn hM gamma hg chi modes u hu centers hc tau W hW
  simp only [mul_comm (M _) ‖_‖] at hb
  have hi : Integrable (rootLocalizationSpatialNorm N hN t gamma chi modes u centers tau) := by
    apply (hMi.mul_const B).mono'
      (measurable_rootLocalizationSpatialNorm N hN t gamma hg chi modes u
        (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau).aestronglyMeasurable
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (rootLocalizationSpatialNorm_nonneg N hN t gamma chi modes u centers tau _)] using hb
  refine ⟨hi, ?_⟩
  simpa only [integral_mul_const] using integral_mono_ae hi (hMi.mul_const B) hb

/-- The kernel constants are uniform in scale and in the entire adaptive patch family.
The vorticity and patch-gradient factors on the right are not declared uniformly bounded. -/
theorem exists_uniform_spatial_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ gamma : ℝ, 0 < gamma → ∀ chi : Wavevector → ℂ, ∀ modes : Finset Wavevector,
      ∀ u : FourierVelocity, Summable (fourierMoment 2 u) →
      ∀ centers : Finset T3, centers.Nonempty → ∀ tau W : ℝ,
      (∀ x : T3, ‖fullVorticity u x‖ ≤ W) →
      (∀ n : ℕ, Integrable (rootLocalizationSpatialNorm N hN
        (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau)) ∧
      Summable (fun n : ℕ ↦ ∫ q : T6, rootLocalizationSpatialNorm N hN
        (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau q) ∧
      (∑' n : ℕ, ∫ q : T6, rootLocalizationSpatialNorm N hN
        (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau q) ≤
        (C / N) * (W ^ 2 * Real.sqrt (6 *
          ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x)) := by
  obtain ⟨C0, C1, hC0, hC1, M, h⟩ := PressurePeriodicEnvelope.exists_uniform_dyadic_envelope
  refine ⟨C1, hC1, ?_⟩
  intro N hN gamma hg chi modes u hu centers hc tau W hW
  obtain ⟨hprop, hdom, hs0, hb0, hs1, hb1⟩ := h N hN
  let B := W ^ 2 * Real.sqrt (6 * ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x)
  have hn (n : ℕ) := integrable_rootLocalizationSpatialNorm_and_integral_le N hN
    (PressureLowOutputDyadicBudget.dyadicParameter n) (M N hN n) (hprop n).1 (hprop n).2.2.2
    (by filter_upwards [hdom] with q hq; exact hq n)
    gamma hg chi modes u hu centers hc tau W hW
  have hs := (hs1.mul_right B).of_nonneg_of_le
    (fun n ↦ integral_nonneg (rootLocalizationSpatialNorm_nonneg N hN
      (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau)) (fun n ↦ (hn n).2)
  refine ⟨fun n ↦ (hn n).1, hs, ?_⟩
  calc
    _ ≤ ∑' n, (∫ q : T6, ‖q‖ * M N hN n q) * B := hs.tsum_le_tsum (fun n ↦ (hn n).2) (hs1.mul_right B)
    _ = (∑' n, ∫ q : T6, ‖q‖ * M N hN n q) * B := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right hb1 (by dsimp [B]; positivity)

/-- The actual continuous vorticity supplies its own supremum bound;
no additional field-size hypothesis is needed. -/
theorem exists_uniform_spatial_budget_for_fullVorticity :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ gamma : ℝ, 0 < gamma → ∀ chi : Wavevector → ℂ, ∀ modes : Finset Wavevector,
      ∀ u : FourierVelocity, ∀ hu : Summable (fourierMoment 2 u),
      ∀ centers : Finset T3, centers.Nonempty → ∀ tau : ℝ,
      let w : C(T3, R3) := ⟨fullVorticity u, continuous_fullVorticity u
        (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu)⟩
      (∀ n : ℕ, Integrable (rootLocalizationSpatialNorm N hN
        (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau)) ∧
      Summable (fun n : ℕ ↦ ∫ q : T6, rootLocalizationSpatialNorm N hN
        (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau q) ∧
      (∑' n : ℕ, ∫ q : T6, rootLocalizationSpatialNorm N hN
        (PressureLowOutputDyadicBudget.dyadicParameter n) gamma chi modes u centers tau q) ≤
        (C / N) * (‖w‖ ^ 2 * Real.sqrt (6 *
          ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_spatial_budget
  refine ⟨C, hC, ?_⟩
  intro N hN gamma hg chi modes u hu centers hc tau
  let w : C(T3, R3) := ⟨fullVorticity u, continuous_fullVorticity u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu)⟩
  exact h N hN gamma hg chi modes u hu centers hc tau ‖w‖ w.norm_coe_le_norm

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootSpatialBudget
