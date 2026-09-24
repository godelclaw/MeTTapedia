import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureMovingDirectionEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootHighInputBudget

/-!
# Spatial transfer of the moving pressure field to actual localized inputs

The constructed Gaussian family freezes the moving spectral line and
localizes both full vorticity inputs. The integral retains two distinct
errors: angular freezing and the actual localization residual, the latter
paid by the proved gradient budget. Neither spatial cost is asserted to
have a finite time integral up to a singular time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootMovingPressureBudget

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget LocalGaussianPressurePartition GaussianRootOperatorBudget
open GaussianRootPartition GaussianRootDirectionFreezing GaussianSquaredRootTranslation
open PressureHighInputAction PressureHighInputLocalization AdaptiveGaussianLinePartition

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_local_root_budget :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ J : ℕ,
      ∀ gamma : ℝ, ∀ hg : 0 < gamma, ∀ chi : Wavevector → ℂ, ∀ modes : Finset Wavevector,
      ∀ u : FourierVelocity, ∀ hu : Summable (fourierMoment 2 u), ∀ rho : ℝ, 0 < rho →
      ∃ centers : Finset T3, ∃ hc : centers.Nonempty,
      let tau := temperature centers.card rho
      let hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu
      let w := complexVorticityField u hu1
      let c := complexRootPatch gamma hg chi modes u hu1 centers hc tau
      0 < tau ∧
        (∫ x : T3, PressureMovingDirectionEnergy.energy N hN J gamma chi modes u w w x) ≤
          4 * (∫ x : T3, ∑ i : ↑centers,
            ‖tailOperator N hN J (localDirection chi modes u i.1) (c i • w) (c i • w) x‖ ^ 2) +
          4 * ((C₁ / N) * (1 / 4 : ℝ) ^ J) ^ 2 * ‖w‖ ^ 4 *
            (6 * ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x) +
          2 * (C₀ * (1 / 4 : ℝ) ^ J) ^ 2 * ‖w‖ ^ 4 * rho ^ 2 := by
  obtain ⟨C₀, hC₀, hfreeze⟩ := exists_local_root_transfer
  obtain ⟨C₁, hC₁, hlocal⟩ := GaussianRootHighInputBudget.exists_uniform_root_budget
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro N hN J gamma hg chi modes u hu rho hrho
  obtain ⟨centers, hc, ht, hfreeze⟩ := hfreeze N hN J gamma hg chi modes u hu rho hrho
  refine ⟨centers, hc, ht, ?_⟩
  let tau := temperature centers.card rho
  let hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu
  let w := complexVorticityField u hu1
  let c := complexRootPatch gamma hg chi modes u hu1 centers hc tau
  let A (i : ↑centers) := tailOperator N hN J (localDirection chi modes u i.1) (c i • w) (c i • w)
  let R (i : ↑centers) := tailLocalization N hN J (localDirection chi modes u i.1) w w (c i) (c i)
  let E₀ := 2 * (C₀ * (1 / 4 : ℝ) ^ J) ^ 2 * ‖w‖ ^ 4 * rho ^ 2
  have hAi : Integrable (fun x : T3 ↦ ∑ i : ↑centers, ‖A i x‖ ^ 2) :=
    (continuous_finsetSum _ (fun i _ ↦ (A i).continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRi : Integrable (fun x : T3 ↦ ∑ i : ↑centers, ‖R i x‖ ^ 2) :=
    (continuous_finsetSum _ (fun i _ ↦ (R i).continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp (x : T3) : PressureMovingDirectionEnergy.energy N hN J gamma chi modes u w w x ≤
      4 * (∑ i, ‖A i x‖ ^ 2) + 4 * (∑ i, ‖R i x‖ ^ 2) + E₀ := by
    have hi (i : ↑centers) := norm_weighted_action_sq_le N hN J
      (localDirection chi modes u i.1) w w (c i) (c i) x
    have heq (i : ↑centers) : ‖c i x‖ ^ 2 * ‖c i x‖ ^ 2 =
        GaussianRootVorticity.rootPatch gamma chi modes u centers tau i x ^ 4 := by
      simp only [c, complexRootPatch, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    simp only [heq] at hi
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    exact (hfreeze x).trans (by dsimp only [A, R, E₀]; linarith only [hs])
  have hint := integral_mono (PressureMovingDirectionEnergy.integrable_energy N hN J gamma hg chi modes u hu1 w w)
    (((hAi.const_mul 4).add (hRi.const_mul 4)).add (integrable_const E₀)) hp
  simp only [Pi.add_apply] at hint
  have hadd := integral_add ((hAi.const_mul 4).add (hRi.const_mul 4)) (integrable_const E₀)
  simp only [Pi.add_apply] at hadd
  rw [hadd,
    integral_add (hAi.const_mul 4) (hRi.const_mul 4), integral_const_mul, integral_const_mul] at hint
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
  have hW (x : T3) : ‖fullVorticity u x‖ ≤ ‖w‖ := by
    have h := ContinuousMap.norm_coe_le_norm w x
    simpa only [w, complexVorticityField, ContinuousMap.coe_mk,
      FourierPressureTraceSymbol.norm_complexifyVector] using h
  have hb := hlocal N hN J gamma hg chi modes u hu centers hc tau ‖w‖ hW
  have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
  have hR0 : 0 ≤ ∫ x : T3, ∑ i : ↑centers, ‖R i x‖ ^ 2 :=
    integral_nonneg (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  have hG : 0 ≤ ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x :=
    integral_nonneg (squaredRootGradientSquare_nonneg gamma chi modes u centers tau)
  change (Real.sqrt (∫ x : T3, ∑ i : ↑centers, ‖R i x‖ ^ 2)) ^ 2 ≤ _ at hs
  rw [Real.sq_sqrt hR0] at hs
  simp only [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hG)] at hs
  have hfinal := hint.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by norm_num))) le_rfl)
  convert hfinal using 1 <;> first | rfl | ring

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootMovingPressureBudget
