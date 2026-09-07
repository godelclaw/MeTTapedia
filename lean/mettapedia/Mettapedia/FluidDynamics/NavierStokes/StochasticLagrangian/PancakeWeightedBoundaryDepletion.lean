import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeWeightedBoundaryAssembly
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSpectralResidualDepletion

/-!
# Count-free boundary assembly retaining the strain action

Nonnegative weighted Cauchy--Schwarz controls the complete frozen field
by the sum of the actual squared operator actions on vorticity. No cell
count or lower spectral gap is introduced. The action is not replaced
by an operator norm times the full vorticity norm.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeWeightedBoundaryDepletion

open MeasureTheory
open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeTransverseEnergyFreezing
open PancakeDyadicDirectionEvolution PancakeQuadraticFourierSupport
open PancakeQuadraticProjectionLocalization PancakeWeightedBoundaryAssembly
open PancakeRegularizedDiffusion PancakeRegularizedMaterialRate PancakeSpectralDefectEvolution
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralResidualDepletion

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem norm_weighted_sum_sq_le {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (rho : ι → ℝ) (v : ι → E) (hr : ∀ i, 0 ≤ rho i) :
    ‖∑ i : ι, rho i • v i‖ ^ 2 ≤ (∑ i : ι, rho i) * (∑ i : ι, rho i * ‖v i‖ ^ 2) := by
  have hn : ‖∑ i : ι, rho i • v i‖ ≤ ∑ i : ι, rho i * ‖v i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hr _)] using
      (norm_sum_le Finset.univ (fun i ↦ rho i • v i))
  have hs : 0 ≤ ∑ i : ι, rho i * ‖v i‖ := Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hr i) (norm_nonneg _))
  have hsq : ‖∑ i : ι, rho i • v i‖ ^ 2 ≤ (∑ i : ι, rho i * ‖v i‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ i : ι, rho i • v i)]
  apply hsq.trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ (fun i _ ↦ hr i)
    (fun i _ ↦ mul_nonneg (hr i) (sq_nonneg ‖v i‖))
  intro i _
  nlinarith

theorem norm_weighted_sum_sq_le_coverage {ι E : Type*} [Fintype ι]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (rho : ι → ℝ) (v : ι → E) (C : ℝ) (hr : ∀ i, 0 ≤ rho i) (hC : ∑ i : ι, rho i ≤ C) :
    ‖∑ i : ι, rho i • v i‖ ^ 2 ≤ C * (∑ i : ι, rho i * ‖v i‖ ^ 2) :=
  (norm_weighted_sum_sq_le rho v hr).trans (mul_le_mul_of_nonneg_right hC
    (Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hr i) (sq_nonneg _))))

theorem norm_frozenLocalizedField_sq_le {ι : Type*} [Fintype ι] (c : ι → FourierCoeff (Fin 3))
    (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector) (w : FourierVelocity) (C : ℝ) (x : T3)
    (hC : ∑ i : ι, quadraticWeight (c i) x ≤ C) :
    ‖frozenLocalizedField c A modes w x‖ ^ 2 ≤ C * ∑ i : ι, quadraticWeight (c i) x *
      ‖A i (complexRealPartEuclidean (finiteFourierReconstruction modes w x))‖ ^ 2 :=
  norm_weighted_sum_sq_le_coverage _ _ C (fun _ ↦ Complex.normSq_nonneg _) hC

theorem integral_assembled_boundary_energy_depleted {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (A : ι → R3 →L[ℝ] R3) (modes : Finset Wavevector)
    (w : FourierVelocity) (C : ℝ) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hC : ∀ x : T3, ∑ i : ι, quadraticWeight (c i) x ≤ C) :
    (∫ x : T3, ‖assembledBoundaryField c A modes w x‖ ^ 2) ≤
      C * ∫ x : T3, ∑ i : ι, quadraticWeight (c i) x *
        ‖A i (complexRealPartEuclidean (finiteFourierReconstruction modes w x))‖ ^ 2 := by
  have hw : Continuous (fun x : T3 ↦ complexRealPartEuclidean (finiteFourierReconstruction modes w x)) :=
    complexRealPartEuclideanCLM.continuous.comp (continuous_finiteFourierReconstruction _ _)
  have hc : Continuous (fun x : T3 ↦ C * ∑ i : ι, quadraticWeight (c i) x *
      ‖A i (complexRealPartEuclidean (finiteFourierReconstruction modes w x))‖ ^ 2) :=
    (continuous_finsetSum _ (fun i _ ↦ (continuous_quadraticWeight (c i)).mul
      (((A i).continuous.comp hw).norm.pow 2))).const_mul C
  apply (integral_assembled_boundary_energy_le c A modes w hs).trans
  rw [← integral_const_mul]
  exact integral_mono
    (((continuous_frozenLocalizedField c A modes w).norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun x ↦ norm_frozenLocalizedField_sq_le c A modes w C x (hC x))

theorem integral_gapBoundary_energy_depleted {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (S : ι → SymmetricStrain) (modes : Finset Wavevector)
    (w : FourierVelocity) (C : ℝ) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hC : ∀ x : T3, ∑ i : ι, quadraticWeight (c i) x ≤ C) :
    (∫ x : T3, ‖assembledBoundaryField c (fun i ↦ regularizedGap (S i) 0) modes w x‖ ^ 2) ≤
      C * ∫ x : T3, ∑ i : ι, quadraticWeight (c i) x *
        ‖spectralResidual (S i).1 (topEigenvalue (S i))
          (complexRealPartEuclidean (finiteFourierReconstruction modes w x))‖ ^ 2 := by
  have h := integral_assembled_boundary_energy_depleted c (fun i ↦ regularizedGap (S i) 0) modes w C hs hC
  simpa only [regularizedGap_apply_eq, zero_smul, add_zero] using h

theorem integral_gapBoundary_energy_le_width_defect {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (S : ι → SymmetricStrain) (modes : Finset Wavevector)
    (w : FourierVelocity) (C : ℝ) (hs : ∀ q, -q ∈ modes ↔ q ∈ modes)
    (hC : ∀ x : T3, ∑ i : ι, quadraticWeight (c i) x ≤ C) :
    (∫ x : T3, ‖assembledBoundaryField c (fun i ↦ regularizedGap (S i) 0) modes w x‖ ^ 2) ≤
      C * ∫ x : T3, ∑ i : ι, quadraticWeight (c i) x * spectralWidth (S i) *
        topSpectralDefect (S i) (complexRealPartEuclidean (finiteFourierReconstruction modes w x)) := by
  let W := fun x : T3 ↦ complexRealPartEuclidean (finiteFourierReconstruction modes w x)
  have hw : Continuous W :=
    complexRealPartEuclideanCLM.continuous.comp (continuous_finiteFourierReconstruction _ _)
  have hC0 : 0 ≤ C := (Finset.sum_nonneg (fun i _ ↦
    (show 0 ≤ quadraticWeight (c i) (0 : T3) from Complex.normSq_nonneg _))).trans (hC 0)
  have hz (i : ι) : Continuous (fun x : T3 ↦ spectralResidual (S i).1 (topEigenvalue (S i)) (W x)) :=
    (hw.const_smul _).sub ((S i).1.continuous.comp hw)
  have hd (i : ι) : Continuous (fun x : T3 ↦ topSpectralDefect (S i) (W x)) :=
    ((hw.norm.pow 2).const_mul _).sub (hw.inner ((S i).1.continuous.comp hw))
  apply (integral_gapBoundary_energy_depleted c S modes w C hs hC).trans
  apply mul_le_mul_of_nonneg_left _ hC0
  apply integral_mono
    ((continuous_finsetSum _ (fun i _ ↦ (continuous_quadraticWeight (c i)).mul ((hz i).norm.pow 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((continuous_finsetSum _ (fun i _ ↦ ((continuous_quadraticWeight (c i)).mul_const _).mul (hd i))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  intro x
  apply Finset.sum_le_sum
  intro i _
  simpa only [Pi.mul_apply, mul_assoc] using mul_le_mul_of_nonneg_left
    (norm_topSpectralResidual_sq_le_width_defect (S i) (W x))
    (show 0 ≤ quadraticWeight (c i) x from Complex.normSq_nonneg _)

end Mettapedia.FluidDynamics.NavierStokes.PancakeWeightedBoundaryDepletion
