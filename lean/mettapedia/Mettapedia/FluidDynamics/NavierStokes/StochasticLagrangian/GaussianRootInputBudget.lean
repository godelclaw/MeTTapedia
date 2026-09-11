import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.UniformGaussianGradientBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.UniformStrainGradientBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootOperatorBudget
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Adaptive pressure localization across high input scales

The actual smooth field supplies a common gradient-energy majorant for all
contractive finite filters. Adaptive covers have uniformly bounded size,
so their Gaussian temperatures have a common positive lower bound. The
inverse input-scale gain can then be summed along a dyadic sequence.

The retained full second Fourier moment, vorticity supremum, and vorticity
gradient energy are not dynamically controlled. This is a fixed-field
summation result for this pressure sector, not a scale-critical time budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootInputBudget

open MeasureTheory
open PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeFilteredStrainDynamics PancakeFourierStrainGradient LocalSpatialVorticityJets
open LocalSquaredGapPressure LocalGaussianPressurePartition LocalLowDiffusionBudget
open GaussianSquaredRootTranslation GaussianRootOperatorBudget UniformGaussianGradientBudget
open UniformStrainGradientBudget AdaptiveGaussianLinePartition SpectralTiltFreezing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def gradientEnergyBudget (gamma W A : ℝ) (u : FourierVelocity) : ℝ :=
  (4 * A / gamma ^ 2) * (∫ x : T3, ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2) +
    ((72 + 1600 * A) * W ^ 2 / gamma ^ 4) * (3 * envelope u ^ 2)

theorem gradientEnergyBudget_nonneg (gamma W A : ℝ) (hA : 0 ≤ A) (u : FourierVelocity) :
    0 ≤ gradientEnergyBudget gamma W A u := by
  have hi : 0 ≤ ∫ x : T3, ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2 :=
    integral_nonneg (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  unfold gradientEnergyBudget
  positivity

theorem integral_gradientDensity_le (gamma W A : ℝ) (hA : 0 ≤ A)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (hchi : ∀ q ∈ modes, ‖chi q‖ ≤ 1)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    (∫ x : T3, gradientDensity gamma W A chi modes u x) ≤ gradientEnergyBudget gamma W A u := by
  let F := fun x : T3 ↦ ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2
  have hF : Continuous F := continuous_finsetSum _
    (fun j _ ↦ (LocalSquaredGapGradient.continuous_fullCurlGradient u j).norm.pow 2)
  have hiF : Integrable F := hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let b := (72 + 1600 * A) * W ^ 2 / gamma ^ 4
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hiD : Integrable (gradientDensity gamma W A chi modes u) :=
    (continuous_gradientDensity gamma W A chi modes u).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiB : Integrable (fun x : T3 ↦ (4 * A / gamma ^ 2) * F x + b * (3 * envelope u ^ 2)) :=
    (hiF.const_mul _).add (integrable_const _)
  have h := integral_mono hiD hiB (fun x ↦ add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (sum_norm_strainGradient_sq_le chi modes hchi u hu x) hb))
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [integral_add (hiF.const_mul _) (integrable_const _), integral_const_mul]
      simp [gradientEnergyBudget, F, b]

def inputScale (N : ℝ) (j : ℕ) : ℝ := N * 2 ^ j

theorem inputScale_pos (N : ℝ) (hN : 0 < N) (j : ℕ) : 0 < inputScale N j :=
  mul_pos hN (pow_pos (by norm_num) j)

def fullOutputNorm (N : ℝ) (hN : 0 < N) (gamma : ℝ) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (centers : Finset T3) (rho : ℝ) : ℝ :=
  Real.sqrt (∫ x : T3, ∑ i : ↑centers,
    ‖rootLocalizationSumAction N hN gamma chi modes u centers (temperature centers.card rho) x i‖ ^ 2)

/-- Operator summation with an explicit common gradient bound. The adaptive
construction and the choice of this bound are supplied by the subsequent
actual-data theorems, rather than hidden in the operator constant. -/
theorem exists_uniform_input_operator_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : FourierVelocity, ∀ hu : Summable (fourierMoment 2 u),
      let w : C(T3, R3) := ⟨fullVorticity u, continuous_fullVorticity u
        (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu)⟩
      ∀ gamma : ℝ, 0 < gamma → ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ chi : ℕ → Wavevector → ℂ, ∀ modes : ℕ → Finset Wavevector,
      ∀ centers : ℕ → Finset T3, (∀ j, (centers j).Nonempty) → ∀ rho E : ℝ,
      (∀ j, (∫ x : T3, squaredRootGradientSquare gamma (chi j) (modes j) u (centers j)
        (temperature (centers j).card rho) x) ≤ E) →
      Summable (fun j : ℕ ↦ fullOutputNorm (inputScale N j) (inputScale_pos N hN j)
        gamma (chi j) (modes j) u (centers j) rho) ∧
      (∑' j : ℕ, fullOutputNorm (inputScale N j) (inputScale_pos N hN j)
        gamma (chi j) (modes j) u (centers j) rho) ≤
        (2 * C / N) * (‖w‖ ^ 2 * Real.sqrt (6 * E)) := by
  obtain ⟨C, hC, hpressure⟩ := exists_uniform_sum_operator_budget_for_fullVorticity
  refine ⟨C, hC, ?_⟩
  intro u hu w gamma hg N hN chi modes centers hc rho E hE
  let B := (C / N) * (‖w‖ ^ 2 * Real.sqrt (6 * E))
  have hbound (j : ℕ) : fullOutputNorm (inputScale N j) (inputScale_pos N hN j)
      gamma (chi j) (modes j) u (centers j) rho ≤ B * (1 / 2 : ℝ) ^ j := by
    have hp := hpressure (inputScale N j) (inputScale_pos N hN j) gamma hg (chi j) (modes j)
      u hu (centers j) (hc j) (temperature (centers j).card rho)
    calc
      _ ≤ _ := hp
      _ ≤ (C / inputScale N j) * (‖w‖ ^ 2 * Real.sqrt (6 * E)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
            (mul_le_mul_of_nonneg_left (hE j) (by norm_num))) (sq_nonneg _))
          (div_nonneg hC (inputScale_pos N hN j).le)
      _ = _ := by
        simp only [B, inputScale, div_eq_mul_inv, mul_inv_rev, one_mul, inv_pow]
        ring
  have hgeom : HasSum (fun j : ℕ ↦ (1 / 2 : ℝ) ^ j) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) using 1
    norm_num
  have hB := hgeom.mul_left B
  have hs := hB.summable.of_nonneg_of_le (fun j ↦ Real.sqrt_nonneg _) hbound
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' j : ℕ, B * (1 / 2 : ℝ) ^ j := hs.tsum_le_tsum hbound hB.summable
    _ = B * 2 := hB.tsum_eq
    _ = _ := by dsimp [B]; ring

/-- The common cover bound is chosen before the input scale and all filters.
All patch families are constructed, and their true output sums are used. -/
theorem exists_uniform_input_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : FourierVelocity, ∀ hu : Summable (fourierMoment 3 u),
      ∀ gamma : ℝ, 0 < gamma → ∀ rho : ℝ, 0 < rho →
      let w : C(T3, R3) := ⟨fullVorticity u, continuous_fullVorticity u
        (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)⟩
      ∃ M : ℕ, 0 < M ∧ ∀ N : ℝ, ∀ hN : 0 < N,
        ∀ chi : ℕ → Wavevector → ℂ, ∀ modes : ℕ → Finset Wavevector,
        (∀ j q, q ∈ modes j → ‖chi j q‖ ≤ 1) →
        ∃ centers : ℕ → Finset T3,
          (∀ j, (centers j).Nonempty ∧ (centers j).card ≤ M ∧
            let tau := temperature (centers j).card rho
            (∀ x, (∑ i : ↑(centers j), patch gamma (chi j) (modes j) u (centers j) tau i x ^ 2) =
              localWeight gamma (chi j) (modes j) u x) ∧
            (∀ x, (∑ i : ↑(centers j), patch gamma (chi j) (modes j) u (centers j) tau i x ^ 2 *
              lineDistanceSq (localDirection (chi j) (modes j) u x)
                (localDirection (chi j) (modes j) u i.1)) ≤ rho ^ 2)) ∧
          Summable (fun j : ℕ ↦ fullOutputNorm (inputScale N j) (inputScale_pos N hN j)
            gamma (chi j) (modes j) u (centers j) rho) ∧
          (∑' j : ℕ, fullOutputNorm (inputScale N j) (inputScale_pos N hN j)
            gamma (chi j) (modes j) u (centers j) rho) ≤
            (2 * C / N) * (‖w‖ ^ 2 * Real.sqrt (6 *
              gradientEnergyBudget gamma ‖w‖ (partitionMultiplier M gamma ‖w‖ rho) u)) := by
  obtain ⟨C, hC, hpressure⟩ := exists_uniform_input_operator_budget
  refine ⟨C, hC, ?_⟩
  intro u hu gamma hg rho hrho
  let w : C(T3, R3) := ⟨fullVorticity u, continuous_fullVorticity u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)⟩
  have hu2 := summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu
  obtain ⟨M, hM, hgeometry⟩ := exists_uniform_root_gradient_budget gamma hg ‖w‖ rho hrho
  refine ⟨M, hM, ?_⟩
  intro N hN chi modes hchi
  choose centers hc hcard hT hTle hmass hline hiG hAE hG using
    (fun j : ℕ ↦ hgeometry (chi j) (modes j) u hu w.norm_coe_le_norm)
  let A := partitionMultiplier M gamma ‖w‖ rho
  let E := gradientEnergyBudget gamma ‖w‖ A u
  have hE (j : ℕ) :
      (∫ x : T3, squaredRootGradientSquare gamma (chi j) (modes j) u (centers j)
        (temperature (centers j).card rho) x) ≤ E :=
    (hG j).trans (integral_gradientDensity_le gamma ‖w‖ A
      (partitionMultiplier_nonneg M gamma ‖w‖ rho) (chi j) (modes j) (hchi j) u hu2)
  exact ⟨centers, fun j ↦ ⟨hc j, hcard j, hmass j, hline j⟩,
    hpressure u hu2 gamma hg N hN chi modes centers hc rho E hE⟩

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootInputBudget
