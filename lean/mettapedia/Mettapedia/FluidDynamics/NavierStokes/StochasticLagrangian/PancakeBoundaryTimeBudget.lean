import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBoundaryEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeEulerianAlignmentBudget

/-!
# Time-integrated boundary energy for fixed quadratic Fourier weights

Continuity of the actual finite convolution supplies time integrability.
The physical retained kinetic-energy identity pays the sum of exterior
energies with no retained-mode count or cell count. The weights are fixed
in time here; neither moving-cutoff rates nor nonlinear projection forcing
are bounded by this result.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeBoundaryTimeBudget

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeDyadicDirectionEvolution
open PancakeFiniteFourierLocalization PancakeLocalizedProjectionBoundary
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization PancakeBoundaryEnergy
open PancakeGalerkinKineticEnergy PancakeBlockReality PancakeViscousMisalignmentAbsorption
open PancakeEulerianAlignmentBudget

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_cutoffConvolution_coefficient (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : ℝ → FourierVelocity)
    (hw : ∀ k ∈ modes, ∀ i, Continuous (fun t ↦ w t k i)) (q : Wavevector) (i : Fin 3) :
    Continuous (fun t ↦ finiteCutoffConvolutionCoeff cutoff modes c (w t) q i) := by
  simp only [finiteCutoffConvolutionCoeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply continuous_finsetSum
  intro pk hpk
  exact continuous_const.mul (hw pk.2 (Finset.mem_product.mp (Finset.mem_filter.mp hpk).1).2 i)

theorem continuous_parametric_boundaryField (cutoff modes : Finset Wavevector)
    (c : Wavevector → ℂ) (w : ℝ → FourierVelocity)
    (hw : ∀ k ∈ modes, ∀ i, Continuous (fun t ↦ w t k i)) :
    Continuous (fun z : ℝ × T3 ↦ localizedBoundaryField cutoff modes c (w z.1) z.2) := by
  apply complexRealPartEuclideanCLM.continuous.comp
  apply continuous_pi
  intro i
  simp only [finiteFourierReconstruction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply continuous_finsetSum
  intro q _
  exact ((UnitAddTorus.mFourier q).continuous.comp continuous_snd).mul
    ((continuous_cutoffConvolution_coefficient cutoff modes c w hw q i).comp continuous_fst)

def totalQuadraticBoundaryEnergy {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (modes : Finset Wavevector) (w : FourierVelocity) : ℝ :=
  ∑ i : ι, ∫ x : T3, ‖quadraticBoundaryField (c i) modes w x‖ ^ 2

theorem continuous_totalQuadraticBoundaryEnergy {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (modes : Finset Wavevector) (w : ℝ → FourierVelocity)
    (hw : ∀ k ∈ modes, ∀ i, Continuous (fun t ↦ w t k i)) :
    Continuous (fun t ↦ totalQuadraticBoundaryEnergy c modes (w t)) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_spatialMean _
    ((continuous_parametric_boundaryField (quadraticFourierCoeff (c i)).support modes
      (quadraticFourierCoeff (c i)) w hw).norm.pow 2)

theorem totalQuadraticBoundaryEnergy_integral_initial_paid {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (C nu T : ℝ) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hC : ∀ x : T3, ∑ i : ι, quadraticWeight (c i) x ≤ C)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    (∫ t in (0 : ℝ)..T, totalQuadraticBoundaryEnergy c modes (fourierCurl (u t))) ≤
      C ^ 2 * fullEnergy modes (u 0) / (2 * nu) := by
  have hc : ∀ q ∈ modes, ∀ i, Continuous (fun t ↦ fourierCurl (u t) q i) := by
    intro q hq i
    apply continuousOn_univ.mp
    exact continuousOn_fourierCurl_coefficient u Set.univ q
      (fun j ↦ (continuous_iff_continuousAt.mpr (fun t ↦ (he t q hq j).continuousAt)).continuousOn) i
  have hB := (continuous_totalQuadraticBoundaryEnergy c modes (fun t ↦ fourierCurl (u t)) hc).intervalIntegrable
    (μ := volume) 0 T
  have hE : IntervalIntegrable (fun t ↦ fullEnergy modes (fourierCurl (u t))) volume 0 T :=
    (continuousOn_enstrophy_of_velocityRHS modes u nu (Set.Icc 0 T)
      (fun t _ ↦ he t)).intervalIntegrable_of_Icc hT
  have h := intervalIntegral.integral_mono_on hT hB (hE.const_mul (C ^ 2)) (fun t _ ↦
    sum_quadratic_boundary_energy_le_coefficients c modes (fourierCurl (u t)) C hs hC)
  rw [intervalIntegral.integral_const_mul] at h
  have hpaid := enstrophy_integral_le_initial modes u nu T hT hs hr hu (fun t _ ↦ he t)
  have hden : 0 < 2 * nu := by positivity
  have hEpaid : (∫ t in (0 : ℝ)..T, fullEnergy modes (fourierCurl (u t))) ≤ fullEnergy modes (u 0) / (2 * nu) :=
    (le_div_iff₀ hden).mpr (by linarith)
  calc
    _ ≤ C ^ 2 * (∫ t in (0 : ℝ)..T, fullEnergy modes (fourierCurl (u t))) := h
    _ ≤ C ^ 2 * (fullEnergy modes (u 0) / (2 * nu)) := mul_le_mul_of_nonneg_left hEpaid (sq_nonneg _)
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.PancakeBoundaryTimeBudget
