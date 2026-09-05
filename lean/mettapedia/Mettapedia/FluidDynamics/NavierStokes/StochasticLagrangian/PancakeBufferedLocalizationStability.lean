import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBilinearActionStability
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBufferedAnnularPhysicalFrameTransfer

/-!
# Stability of the physical buffered pancake operator

The generic bilinear input-stability estimate is specialized to the
localization-stable pancake kernel and transferred through a physical oriented
frame.  This is the operator estimate needed to turn a quantitative Fourier
tail for a smooth cutoff into a controlled localization error.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeBufferedLocalizationStability

open MeasureTheory
open PeriodicFourierTriad
open PancakeBilinearPeriodization
open PancakePeriodicCoherentSplit
open PancakeSmoothCoherentSymbol
open PancakeFrameCovariance
open PancakeFrozenFrameKernelTransfer
open PancakePhysicalFrameKernelTransfer
open PancakeBufferedAnnularFrozenFrameTransfer
open PancakeBufferedAnnularPhysicalFrameTransfer
open PancakeBilinearActionStability

/-- **Uniform physical stability of the buffered multiplier.**  Approximating
both inputs costs the two expected bilinear error terms, still with the sharp
scale factor `1/N` and no Fourier-cardinality constant. -/
theorem exists_uniform_physicalLocalization_stability :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), 2 ≤ N →
      ∀ (f f₀ g g₀ : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus) (E P M Q : ℝ),
        Continuous f → Continuous f₀ → Continuous g → Continuous g₀ →
        (∀ y, ‖f y - f₀ y‖ ≤ E) →
        (∀ y, ‖g y‖ ≤ P) →
        (∀ y, ‖f₀ y‖ ≤ M) →
        (∀ y, ‖g y - g₀ y‖ ≤ Q) →
        ‖physicalOrientedFrameLocalizationSquareDyadicKernelAction F N f g x -
            physicalOrientedFrameLocalizationSquareDyadicKernelAction
              F N f₀ g₀ x‖ ≤
          243 * (C / N) * E * P + 243 * (C / N) * M * Q := by
  rcases exists_uniform_unitTorusRotatedLocalizationSquareDyadicKernel_mass
    with ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro F N hN f f₀ g g₀ x E P M Q hf hf₀ hg hg₀
    hfError hgBound hf₀Bound hgError
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hE : 0 ≤ E := (norm_nonneg (f x - f₀ x)).trans (hfError x)
  have hP : 0 ≤ P := (norm_nonneg (g x)).trans (hgBound x)
  have hM : 0 ≤ M := (norm_nonneg (f₀ x)).trans (hf₀Bound x)
  have hQ : 0 ≤ Q := (norm_nonneg (g x - g₀ x)).trans (hgError x)
  let K := unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel
    (orientedFrameFrequencyPairLinearIsometryEquiv F) N
  have hKint : Integrable K frequencyPairUnitTorusMeasure :=
    integrable_unitTorusRotatedLocalizationSquareDyadicKernel
      (orientedFrameFrequencyPairLinearIsometryEquiv F) hN
  have hKmeas : Measurable K :=
    measurable_unitTorusPeriodizedRotatedLocalizationSquareDyadicKernel
      (orientedFrameFrequencyPairLinearIsometryEquiv F) N
  have hmassReal :
      (∫ q : FrequencyPairUnitTorus, ‖K q‖
        ∂frequencyPairUnitTorusMeasure) ≤ C / N := by
    apply (ENNReal.ofReal_le_ofReal_iff (div_nonneg hC hNR.le)).mp
    rw [ofReal_integral_norm_eq_lintegral_enorm hKint]
    exact hmass (orientedFrameFrequencyPairLinearIsometryEquiv F) N hN
  let frameMap := orientedFrameComplexLinearMap F
  have hfFrame : Continuous (fun y ↦ frameMap (f y)) :=
    frameMap.continuous_of_finiteDimensional.comp hf
  have hf₀Frame : Continuous (fun y ↦ frameMap (f₀ y)) :=
    frameMap.continuous_of_finiteDimensional.comp hf₀
  have hgFrame : Continuous (fun y ↦ frameMap (g y)) :=
    frameMap.continuous_of_finiteDimensional.comp hg
  have hg₀Frame : Continuous (fun y ↦ frameMap (g₀ y)) :=
    frameMap.continuous_of_finiteDimensional.comp hg₀
  have hfFrameError : ∀ y,
      ‖frameMap (f y) - frameMap (f₀ y)‖ ≤ 3 * E := by
    intro y
    rw [← map_sub]
    exact (norm_orientedFrameComplexLinearMap_le F (f y - f₀ y)).trans
      (mul_le_mul_of_nonneg_left (hfError y) (by norm_num))
  have hgFrameBound : ∀ y, ‖frameMap (g y)‖ ≤ 3 * P := by
    intro y
    exact (norm_orientedFrameComplexLinearMap_le F (g y)).trans
      (mul_le_mul_of_nonneg_left (hgBound y) (by norm_num))
  have hf₀FrameBound : ∀ y, ‖frameMap (f₀ y)‖ ≤ 3 * M := by
    intro y
    exact (norm_orientedFrameComplexLinearMap_le F (f₀ y)).trans
      (mul_le_mul_of_nonneg_left (hf₀Bound y) (by norm_num))
  have hgFrameError : ∀ y,
      ‖frameMap (g y) - frameMap (g₀ y)‖ ≤ 3 * Q := by
    intro y
    rw [← map_sub]
    exact (norm_orientedFrameComplexLinearMap_le F (g y - g₀ y)).trans
      (mul_le_mul_of_nonneg_left (hgError y) (by norm_num))
  have htorus := norm_torusBilinearKernelAction_sub_le
    K (fun y ↦ frameMap (f y)) (fun y ↦ frameMap (f₀ y))
      (fun y ↦ frameMap (g y)) (fun y ↦ frameMap (g₀ y))
      x (3 * E) (3 * P) (3 * M) (3 * Q)
      hKint hKmeas hfFrame hf₀Frame hgFrame hg₀Frame
      hfFrameError hgFrameBound hf₀FrameBound hgFrameError
  unfold physicalOrientedFrameLocalizationSquareDyadicKernelAction
  change ‖orientedFrameInverseComplexLinearMap F
        (torusBilinearKernelAction K
          (fun y ↦ frameMap (f y)) (fun y ↦ frameMap (g y)) x) -
      orientedFrameInverseComplexLinearMap F
        (torusBilinearKernelAction K
          (fun y ↦ frameMap (f₀ y)) (fun y ↦ frameMap (g₀ y)) x)‖ ≤ _
  rw [← map_sub]
  calc
    _ ≤ 3 * ‖torusBilinearKernelAction K
          (fun y ↦ frameMap (f y)) (fun y ↦ frameMap (g y)) x -
        torusBilinearKernelAction K
          (fun y ↦ frameMap (f₀ y)) (fun y ↦ frameMap (g₀ y)) x‖ :=
      norm_orientedFrameInverseComplexLinearMap_le F _
    _ ≤ 3 *
        (9 * (∫ q, ‖K q‖ ∂frequencyPairUnitTorusMeasure) * (3 * E) * (3 * P) +
          9 * (∫ q, ‖K q‖ ∂frequencyPairUnitTorusMeasure) * (3 * M) * (3 * Q)) := by
      gcongr
    _ = 243 * (∫ q, ‖K q‖ ∂frequencyPairUnitTorusMeasure) * E * P +
        243 * (∫ q, ‖K q‖ ∂frequencyPairUnitTorusMeasure) * M * Q := by
      ring
    _ ≤ 243 * (C / N) * E * P + 243 * (C / N) * M * Q := by
      gcongr

/-- A uniform scalar cutoff-approximation error transfers directly to the
physical buffered operator.  This is the interface consumed by a Fourier-tail
estimate for genuinely localized smooth cell cutoffs. -/
theorem exists_uniform_cutoffApproximation_stability :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : OrientedFrameEquiv) (N : ℕ), 2 ≤ N →
      ∀ (χ χ₀ ψ ψ₀ : BilinearSpatialTorus → ℂ)
        (U V : BilinearSpatialTorus → ComplexVec3)
        (x : BilinearSpatialTorus) (εχ B A εψ M P : ℝ),
        Continuous χ → Continuous χ₀ → Continuous ψ → Continuous ψ₀ →
        Continuous U → Continuous V →
        (∀ y, ‖χ y - χ₀ y‖ ≤ εχ) →
        (∀ y, ‖ψ y‖ ≤ B) →
        (∀ y, ‖χ₀ y‖ ≤ A) →
        (∀ y, ‖ψ y - ψ₀ y‖ ≤ εψ) →
        (∀ y, ‖U y‖ ≤ M) →
        (∀ y, ‖V y‖ ≤ P) →
        ‖physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
              (fun y ↦ χ y • U y) (fun y ↦ ψ y • V y) x -
            physicalOrientedFrameLocalizationSquareDyadicKernelAction F N
              (fun y ↦ χ₀ y • U y) (fun y ↦ ψ₀ y • V y) x‖ ≤
          243 * (C / N) * (εχ * M) * (B * P) +
            243 * (C / N) * (A * M) * (εψ * P) := by
  rcases exists_uniform_physicalLocalization_stability with ⟨C, hC, hstable⟩
  refine ⟨C, hC, ?_⟩
  intro F N hN χ χ₀ ψ ψ₀ U V x εχ B A εψ M P
    hχ hχ₀ hψ hψ₀ hU hV hχError hψBound hχ₀Bound hψError hUBound hVBound
  have hεχ : 0 ≤ εχ := (norm_nonneg (χ x - χ₀ x)).trans (hχError x)
  have hB : 0 ≤ B := (norm_nonneg (ψ x)).trans (hψBound x)
  have hA : 0 ≤ A := (norm_nonneg (χ₀ x)).trans (hχ₀Bound x)
  have hεψ : 0 ≤ εψ := (norm_nonneg (ψ x - ψ₀ x)).trans (hψError x)
  have hM : 0 ≤ M := (norm_nonneg (U x)).trans (hUBound x)
  have hP : 0 ≤ P := (norm_nonneg (V x)).trans (hVBound x)
  apply hstable F N hN
    (fun y ↦ χ y • U y) (fun y ↦ χ₀ y • U y)
    (fun y ↦ ψ y • V y) (fun y ↦ ψ₀ y • V y)
    x (εχ * M) (B * P) (A * M) (εψ * P)
  · exact hχ.smul hU
  · exact hχ₀.smul hU
  · exact hψ.smul hV
  · exact hψ₀.smul hV
  · intro y
    rw [← sub_smul, norm_smul]
    exact mul_le_mul (hχError y) (hUBound y) (norm_nonneg _) hεχ
  · intro y
    rw [norm_smul]
    exact mul_le_mul (hψBound y) (hVBound y) (norm_nonneg _) hB
  · intro y
    rw [norm_smul]
    exact mul_le_mul (hχ₀Bound y) (hUBound y) (norm_nonneg _) hA
  · intro y
    rw [← sub_smul, norm_smul]
    exact mul_le_mul (hψError y) (hVBound y) (norm_nonneg _) hεψ

end PancakeBufferedLocalizationStability
end NavierStokes
end FluidDynamics
end Mettapedia
