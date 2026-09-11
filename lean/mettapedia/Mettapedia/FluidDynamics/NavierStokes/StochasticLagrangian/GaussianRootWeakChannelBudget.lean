import Mettapedia.Analysis.BilinearTranslatedFamilyEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootWeakPressureAction

/-!
# Weak pressure-channel patch sums with the shifted weights retained

The output-square sum is transferred to the actual two-point derivative
density before any individual input supremum is extracted. The common
kernel envelope and exact inverse-input-scale normalization are retained.
Bounding the shifted density by a dynamically affordable cost is a
separate obligation; a same-point weighted budget is not substituted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakChannelBudget

open MeasureTheory Filter PeriodicFourierTriad PancakeCurlOutputTail
open PancakePeriodicCoherentSplit PancakeSpectralProjectorRegularity
open LocalLowDiffusionBudget PancakeSpectralFiniteDifference
open GaussianRootVorticity GaussianRootWeakDivergence GaussianRootWeakPressureAction
open PressureKernelAction PressureCoherentChannelPeriodization PancakeBilinearPeriodization
open FourierPressureTraceSymbol LocalGaussianPressurePartition
open PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakePeriodicVorticityEquation (unitTorusDerivativePhase)

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

variable (gamma : ℝ) (hg : 0 < gamma) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
variable (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))
variable (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ)

omit hg hu hc in
def twoPointDerivativeDensity (j : Fin 3) (y z : T3) : ℝ :=
  ‖fullVorticity u z‖ ^ 2 * ∑ i : ↑centers, rootPatch gamma chi modes u centers tau i z ^ 2 *
    ‖coordinateDerivative gamma chi modes u centers tau i j y‖ ^ 2

theorem sum_input_product_eq (j : Fin 3) (y z : T3) :
    (∑ i : ↑centers, (‖derivativeInput gamma chi modes u centers tau i j y‖ *
      ‖rootInput gamma hg chi modes u hu centers hc tau i z‖) ^ 2) =
      twoPointDerivativeDensity gamma chi modes u centers tau j y z := by
  simp only [derivativeInput, rootInput, ContinuousMap.coe_mk, norm_complexifyVector,
    rootVorticity, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, twoPointDerivativeDensity,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

include hg hu hc in
/-- Both choices of displacement order have a genuine integrable cost. -/
theorem integrable_twoPointDerivativeDensity (j : Fin 3)
    (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (a b : T6 → T3) (ha : Measurable a) (hb : Measurable b) :
    Integrable (fun p : T6 × T3 ↦ M p.1 *
      twoPointDerivativeDensity gamma chi modes u centers tau j
        (p.2 - a p.1) (p.2 - b p.1)) ((volume : Measure T6).prod (volume : Measure T3)) := by
  have hi (i : ↑centers) :=
    Mettapedia.Analysis.BilinearTranslatedFamilyEnergy.integrable_weighted_input_product
      M hM hMn a b ha hb (derivativeInput gamma chi modes u centers tau i j)
      (rootInput gamma hg chi modes u hu centers hc tau i)
      (memLp_derivativeInput gamma hg chi modes u hu centers hc tau i j)
      (rootInput gamma hg chi modes u hu centers hc tau i).continuous.aestronglyMeasurable
      (norm_nonneg _) (rootInput gamma hg chi modes u hu centers hc tau i).norm_coe_le_norm
  have ht := integrable_finsetSum Finset.univ (fun i _ ↦ hi i)
  simpa only [← Finset.mul_sum, sum_input_product_eq] using ht

theorem firstDerivativeAction_sum_energy_le (N : ℝ) (hN : 0 < N) (t : ℝ) (j : Fin 3)
    (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (hdom : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 →
      ‖periodicKernel N hN t e .undifferentiated q‖ ≤ M q) :
    (∫ x : T3, ∑ i : ↑centers, ‖firstDerivativeAction gamma hg chi modes u hu centers hc tau i
      N hN t (localDirection chi modes u i.1) j x‖ ^ 2) ≤
      (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
        twoPointDerivativeDensity gamma chi modes u centers tau j
          (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) := by
  have h := Mettapedia.Analysis.BilinearTranslatedFamilyEnergy.integral_sum_action_energy_le
    (fun i : ↑centers ↦ periodicKernel N hN t (localDirection chi modes u i.1) .undifferentiated)
    (fun i ↦ integrable_periodicKernel N hN t (localDirection chi modes u i.1) .undifferentiated)
    M hM hMn (hdom.mono (fun q hq i ↦ hq _ (topVector_norm _)))
    firstTorusDisplacement secondTorusDisplacement (by fun_prop) (by fun_prop)
    (fun i ↦ derivativeInput gamma chi modes u centers tau i j)
    (fun i ↦ ⇑(rootInput gamma hg chi modes u hu centers hc tau i))
    (fun i ↦ memLp_derivativeInput gamma hg chi modes u hu centers hc tau i j)
    (fun i ↦ (rootInput gamma hg chi modes u hu centers hc tau i).continuous.aestronglyMeasurable)
    (fun i ↦ ‖rootInput gamma hg chi modes u hu centers hc tau i‖)
    (fun _ ↦ norm_nonneg _) (fun i ↦ (rootInput gamma hg chi modes u hu centers hc tau i).norm_coe_le_norm)
  change (∫ x : T3, ∑ i : ↑centers, ‖firstDerivativeAction gamma hg chi modes u hu centers hc tau i
      N hN t (localDirection chi modes u i.1) j x‖ ^ 2) ≤
      (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
        ∑ i : ↑centers, (‖derivativeInput gamma chi modes u centers tau i j (x - firstTorusDisplacement q)‖ *
          ‖rootInput gamma hg chi modes u hu centers hc tau i (x - secondTorusDisplacement q)‖) ^ 2 at h
  simpa only [sum_input_product_eq] using h

theorem first_channel_sum_energy_le (N : ℝ) (hN : 0 < N) (t : ℝ) (j : Fin 3)
    (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (hdom : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 →
      ‖periodicKernel N hN t e .undifferentiated q‖ ≤ M q) :
    (2 * Real.pi * N) ^ 2 * (∫ x : T3, ∑ i : ↑centers,
      ‖kernelAction (periodicKernel N hN t (localDirection chi modes u i.1) (.first j))
        (rootInput gamma hg chi modes u hu centers hc tau i)
        (rootInput gamma hg chi modes u hu centers hc tau i) x‖ ^ 2) ≤
      (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
        twoPointDerivativeDensity gamma chi modes u centers tau j
          (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) := by
  have he : (∫ x : T3, ∑ i : ↑centers,
      ‖(unitTorusDerivativePhase * (N : ℂ)) •
        kernelAction (periodicKernel N hN t (localDirection chi modes u i.1) (.first j))
          (rootInput gamma hg chi modes u hu centers hc tau i)
          (rootInput gamma hg chi modes u hu centers hc tau i) x‖ ^ 2) =
      ∫ x : T3, ∑ i : ↑centers, ‖firstDerivativeAction gamma hg chi modes u hu centers hc tau i
        N hN t (localDirection chi modes u i.1) j x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun i : ↑centers ↦
      GaussianRootWeakPressureAction.first_channel_eq_ae gamma hg chi modes u hu centers hc tau i
        N hN t (localDirection chi modes u i.1) j)] with x hx
    exact Finset.sum_congr rfl (fun i _ ↦ congrArg (fun v : C3 ↦ ‖v‖ ^ 2) (hx i))
  simp only [norm_smul, mul_pow, ← Finset.mul_sum, integral_const_mul,
    norm_mul, PancakeIncomingLowSourceEnergy.norm_derivativePhase,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN] at he
  simp only [mul_pow] at ⊢
  rw [he]
  exact firstDerivativeAction_sum_energy_le gamma hg chi modes u hu centers hc tau N hN t j M hM hMn hdom

theorem secondDerivativeAction_sum_energy_le (N : ℝ) (hN : 0 < N) (t : ℝ) (j : Fin 3)
    (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (hdom : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 →
      ‖periodicKernel N hN t e .undifferentiated q‖ ≤ M q) :
    (∫ x : T3, ∑ i : ↑centers, ‖secondDerivativeAction gamma hg chi modes u hu centers hc tau i
      N hN t (localDirection chi modes u i.1) j x‖ ^ 2) ≤
      (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
        twoPointDerivativeDensity gamma chi modes u centers tau j
          (x - secondTorusDisplacement q) (x - firstTorusDisplacement q) := by
  have h := Mettapedia.Analysis.BilinearTranslatedFamilyEnergy.integral_sum_action_energy_le_right
    (fun i : ↑centers ↦ periodicKernel N hN t (localDirection chi modes u i.1) .undifferentiated)
    (fun i ↦ integrable_periodicKernel N hN t (localDirection chi modes u i.1) .undifferentiated)
    M hM hMn (hdom.mono (fun q hq i ↦ hq _ (topVector_norm _)))
    firstTorusDisplacement secondTorusDisplacement (by fun_prop) (by fun_prop)
    (fun i ↦ ⇑(rootInput gamma hg chi modes u hu centers hc tau i))
    (fun i ↦ derivativeInput gamma chi modes u centers tau i j)
    (fun i ↦ memLp_derivativeInput gamma hg chi modes u hu centers hc tau i j)
    (fun i ↦ (rootInput gamma hg chi modes u hu centers hc tau i).continuous.aestronglyMeasurable)
    (fun i ↦ ‖rootInput gamma hg chi modes u hu centers hc tau i‖)
    (fun _ ↦ norm_nonneg _) (fun i ↦ (rootInput gamma hg chi modes u hu centers hc tau i).norm_coe_le_norm)
  change (∫ x : T3, ∑ i : ↑centers, ‖secondDerivativeAction gamma hg chi modes u hu centers hc tau i
      N hN t (localDirection chi modes u i.1) j x‖ ^ 2) ≤
      (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
        ∑ i : ↑centers, (‖derivativeInput gamma chi modes u centers tau i j (x - secondTorusDisplacement q)‖ *
          ‖rootInput gamma hg chi modes u hu centers hc tau i (x - firstTorusDisplacement q)‖) ^ 2 at h
  simpa only [sum_input_product_eq] using h

theorem second_channel_sum_energy_le (N : ℝ) (hN : 0 < N) (t : ℝ) (j : Fin 3)
    (M : T6 → ℝ) (hM : Integrable M) (hMn : ∀ q, 0 ≤ M q)
    (hdom : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 →
      ‖periodicKernel N hN t e .undifferentiated q‖ ≤ M q) :
    (2 * Real.pi * N) ^ 2 * (∫ x : T3, ∑ i : ↑centers,
      ‖kernelAction (periodicKernel N hN t (localDirection chi modes u i.1) (.second j))
        (rootInput gamma hg chi modes u hu centers hc tau i)
        (rootInput gamma hg chi modes u hu centers hc tau i) x‖ ^ 2) ≤
      (∫ q : T6, M q) * ∫ x : T3, ∫ q : T6, M q *
        twoPointDerivativeDensity gamma chi modes u centers tau j
          (x - secondTorusDisplacement q) (x - firstTorusDisplacement q) := by
  have he : (∫ x : T3, ∑ i : ↑centers,
      ‖(unitTorusDerivativePhase * (N : ℂ)) •
        kernelAction (periodicKernel N hN t (localDirection chi modes u i.1) (.second j))
          (rootInput gamma hg chi modes u hu centers hc tau i)
          (rootInput gamma hg chi modes u hu centers hc tau i) x‖ ^ 2) =
      ∫ x : T3, ∑ i : ↑centers, ‖secondDerivativeAction gamma hg chi modes u hu centers hc tau i
        N hN t (localDirection chi modes u i.1) j x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun i : ↑centers ↦
      GaussianRootWeakPressureAction.second_channel_eq_ae gamma hg chi modes u hu centers hc tau i
        N hN t (localDirection chi modes u i.1) j)] with x hx
    exact Finset.sum_congr rfl (fun i _ ↦ congrArg (fun v : C3 ↦ ‖v‖ ^ 2) (hx i))
  simp only [norm_smul, mul_pow, ← Finset.mul_sum, integral_const_mul,
    norm_mul, PancakeIncomingLowSourceEnergy.norm_derivativePhase,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN] at he
  simp only [mul_pow] at ⊢
  rw [he]
  exact secondDerivativeAction_sum_energy_le gamma hg chi modes u hu centers hc tau N hN t j M hM hMn hdom

/-- A constructed common envelope carries both patch-family estimates,
uniform mass control, and the capped first moment needed for spatial variation. -/
theorem exists_uniform_channel_sum_envelope :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M : (N : ℝ) → 0 < N → ℝ → T6 → ℝ,
      ∀ N : ℝ, ∀ hN : 0 < N, ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2),
        (∀ q, 0 ≤ M N hN t q) ∧ Measurable (M N hN t) ∧ Integrable (M N hN t) ∧
        Integrable (fun q ↦ ‖q‖ * M N hN t q) ∧
        (∫ q : T6, M N hN t q) ≤ PressureLowOutputCutoff.ratio t * C ∧
        (∫ q : T6, ‖q‖ * M N hN t q) ≤ C * min (PressureLowOutputCutoff.ratio t / 2) N⁻¹ ∧
        ∀ j : Fin 3,
          (2 * Real.pi * N) ^ 2 * (∫ x : T3, ∑ i : ↑centers,
            ‖kernelAction (periodicKernel N hN t (localDirection chi modes u i.1) (.first j))
              (rootInput gamma hg chi modes u hu centers hc tau i)
              (rootInput gamma hg chi modes u hu centers hc tau i) x‖ ^ 2) ≤
            (∫ q : T6, M N hN t q) * ∫ x : T3, ∫ q : T6, M N hN t q *
              twoPointDerivativeDensity gamma chi modes u centers tau j
                (x - firstTorusDisplacement q) (x - secondTorusDisplacement q) ∧
          (2 * Real.pi * N) ^ 2 * (∫ x : T3, ∑ i : ↑centers,
            ‖kernelAction (periodicKernel N hN t (localDirection chi modes u i.1) (.second j))
              (rootInput gamma hg chi modes u hu centers hc tau i)
              (rootInput gamma hg chi modes u hu centers hc tau i) x‖ ^ 2) ≤
            (∫ q : T6, M N hN t q) * ∫ x : T3, ∫ q : T6, M N hN t q *
              twoPointDerivativeDensity gamma chi modes u centers tau j
                (x - secondTorusDisplacement q) (x - firstTorusDisplacement q) := by
  obtain ⟨C, hC, M, hb⟩ := exists_uniform_periodic_envelope
  refine ⟨C, hC, M, fun N hN t ht ↦ ?_⟩
  obtain ⟨hn, hm, hi, him, hdom, hmass, hmoment⟩ := hb N hN t ht
  have hd := hdom.mono (fun q hq e he ↦ hq e he .undifferentiated)
  exact ⟨hn, hm, hi, him, hmass, hmoment, fun j ↦
    ⟨first_channel_sum_energy_le gamma hg chi modes u hu centers hc tau N hN t j (M N hN t) hi hn hd,
      second_channel_sum_energy_le gamma hg chi modes u hu centers hc tau N hN t j (M N hN t) hi hn hd⟩⟩

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootWeakChannelBudget
