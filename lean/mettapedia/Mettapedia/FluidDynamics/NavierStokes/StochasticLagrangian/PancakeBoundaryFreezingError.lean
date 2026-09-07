import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeightedBoundaryDepletion
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralFiniteDifference

/-!
# Unfreezing the assembled boundary field

The full strain-weighted boundary energy is controlled by the actual
spectral residual and the quadratic weighted strain variation of the
patches. This is a spatial estimate, not a bound on the nonlinear output
paired with that boundary field or on time-dependent localization costs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeBoundaryFreezingError

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeTransverseEnergyFreezing
open PancakeDyadicDirectionEvolution PancakeQuadraticProjectionLocalization
open PancakeWeightedBoundaryAssembly PancakeWeightedBoundaryDepletion
open PancakeRegularizedDiffusion PancakeSpectralFiniteDifference
open PancakeTopEigenvalueDerivative PancakeQuadraticFourierSupport
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem norm_gap_difference_apply_sq_le (S T : SymmetricStrain) (delta : ℝ) (w : R3) :
    ‖(regularizedGap T delta - regularizedGap S delta) w‖ ^ 2 ≤
      4 * ‖T.1 - S.1‖ ^ 2 * ‖w‖ ^ 2 := by
  calc
    _ ≤ (‖regularizedGap T delta - regularizedGap S delta‖ * ‖w‖) ^ 2 := by
      gcongr
      exact (regularizedGap T delta - regularizedGap S delta).le_opNorm w
    _ ≤ ((2 * ‖T.1 - S.1‖) * ‖w‖) ^ 2 := by
      gcongr
      exact regularizedGap_sub_norm S T delta
    _ = _ := by ring

theorem norm_gap_apply_sq_le_unfrozen (S T : SymmetricStrain) (delta : ℝ) (w : R3) :
    ‖regularizedGap T delta w‖ ^ 2 ≤
      2 * ‖regularizedGap S delta w‖ ^ 2 + 8 * ‖T.1 - S.1‖ ^ 2 * ‖w‖ ^ 2 := by
  let G := regularizedGap T delta - regularizedGap S delta
  have hid : regularizedGap T delta w = regularizedGap S delta w + G w := by
    simp only [G, sub_apply]
    abel
  have hn : ‖regularizedGap T delta w‖ ≤ ‖regularizedGap S delta w‖ + ‖G w‖ :=
    hid ▸ norm_add_le _ _
  have hg := norm_gap_difference_apply_sq_le S T delta w
  change ‖G w‖ ^ 2 ≤ _ at hg
  nlinarith [sq_nonneg (‖regularizedGap S delta w‖ - ‖G w‖),
    norm_nonneg (regularizedGap T delta w), norm_nonneg (regularizedGap S delta w), norm_nonneg (G w)]

theorem norm_weighted_gap_sum_sq_le_unfrozen {ι : Type*} [Fintype ι]
    (rho : ι → ℝ) (T : ι → SymmetricStrain) (S : SymmetricStrain) (w : R3) (C delta : ℝ)
    (hr : ∀ i, 0 ≤ rho i) (hC : ∑ i : ι, rho i ≤ C) :
    ‖∑ i : ι, rho i • regularizedGap (T i) delta w‖ ^ 2 ≤
      2 * C ^ 2 * ‖regularizedGap S delta w‖ ^ 2 +
        8 * C * ∑ i : ι, rho i * ‖(T i).1 - S.1‖ ^ 2 * ‖w‖ ^ 2 := by
  have hr0 : 0 ≤ ∑ i : ι, rho i := Finset.sum_nonneg (fun i _ ↦ hr i)
  have hC0 : 0 ≤ C := hr0.trans hC
  calc
    _ ≤ C * ∑ i : ι, rho i * ‖regularizedGap (T i) delta w‖ ^ 2 :=
      norm_weighted_sum_sq_le_coverage _ _ C hr hC
    _ ≤ C * ∑ i : ι, rho i * (2 * ‖regularizedGap S delta w‖ ^ 2 +
        8 * ‖(T i).1 - S.1‖ ^ 2 * ‖w‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left
        (norm_gap_apply_sq_le_unfrozen S (T i) delta w) (hr i))
    _ = 2 * C * (∑ i : ι, rho i) * ‖regularizedGap S delta w‖ ^ 2 +
        8 * C * ∑ i : ι, rho i * ‖(T i).1 - S.1‖ ^ 2 * ‖w‖ ^ 2 := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hC
        (show 0 ≤ 2 * C * ‖regularizedGap S delta w‖ ^ 2 by positivity)
      nlinarith

theorem continuous_gap_field {X : Type*} [TopologicalSpace X]
    (S : X → SymmetricStrain) (delta : ℝ) (hS : Continuous S) :
    Continuous (fun x ↦ regularizedGap (S x) delta) :=
  (((lipschitzWith_topEigenvalue.continuous.comp hS).add continuous_const).smul continuous_const).sub
    (continuous_subtype_val.comp hS)

theorem integral_assembled_gapBoundary_energy_unfrozen {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (T : ι → SymmetricStrain) (S : T3 → SymmetricStrain)
    (modes : Finset Wavevector) (w : FourierVelocity) (C delta : ℝ)
    (hS : Continuous S) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hC : ∀ x : T3, ∑ i : ι, quadraticWeight (c i) x ≤ C) :
    (∫ x : T3, ‖assembledBoundaryField c (fun i ↦ regularizedGap (T i) delta) modes w x‖ ^ 2) ≤
      2 * C ^ 2 * (∫ x : T3, ‖regularizedGap (S x) delta
        (complexRealPartEuclidean (finiteFourierReconstruction modes w x))‖ ^ 2) +
      8 * C * ∫ x : T3, ∑ i : ι, quadraticWeight (c i) x * ‖(T i).1 - (S x).1‖ ^ 2 *
        ‖complexRealPartEuclidean (finiteFourierReconstruction modes w x)‖ ^ 2 := by
  let W := fun x : T3 ↦ complexRealPartEuclidean (finiteFourierReconstruction modes w x)
  have hw : Continuous W :=
    complexRealPartEuclideanCLM.continuous.comp (continuous_finiteFourierReconstruction _ _)
  have hz : Continuous (fun x : T3 ↦ ‖regularizedGap (S x) delta (W x)‖ ^ 2) :=
    (((continuous_gap_field S delta hS).clm_apply hw).norm.pow 2)
  have he : Continuous (fun x : T3 ↦ ∑ i : ι, quadraticWeight (c i) x *
      ‖(T i).1 - (S x).1‖ ^ 2 * ‖W x‖ ^ 2) :=
    continuous_finsetSum _ (fun i _ ↦ ((continuous_quadraticWeight (c i)).mul
      ((continuous_const.sub (continuous_subtype_val.comp hS)).norm.pow 2)).mul (hw.norm.pow 2))
  have hiz : Integrable (fun x : T3 ↦ 2 * C ^ 2 * ‖regularizedGap (S x) delta (W x)‖ ^ 2) :=
    (hz.const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hie : Integrable (fun x : T3 ↦ 8 * C * ∑ i : ι, quadraticWeight (c i) x *
      ‖(T i).1 - (S x).1‖ ^ 2 * ‖W x‖ ^ 2) :=
    (he.const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply (integral_assembled_boundary_energy_le c (fun i ↦ regularizedGap (T i) delta) modes w hs).trans
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add hiz hie]
  apply integral_mono
    (((continuous_frozenLocalizedField c (fun i ↦ regularizedGap (T i) delta) modes w).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (hiz.add hie)
  intro x
  exact norm_weighted_gap_sum_sq_le_unfrozen (fun i ↦ quadraticWeight (c i) x) T (S x) (W x) C delta
    (fun _ ↦ Complex.normSq_nonneg _) (hC x)

end Mettapedia.FluidDynamics.NavierStokes.PancakeBoundaryFreezingError
