import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputLocalization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianRootOperatorBudget

/-!
# Gaussian localization with one fixed pressure output filter

Matched dyadic indices retain the fixed-output gain through the actual
kernel integral, the output-band series, and the high-input tail. The
spatial cost is explicit in the vorticity supremum and squared-root patch
gradient energy. No time-integrated control of either cost is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianRootFixedOutputBudget

open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open LocalLowDiffusionBudget LocalGaussianPressurePartition GaussianSquaredRootTranslation
open GaussianRootSpatialBudget GaussianRootOperatorBudget PressureFixedOutputSymbol
open PressureFixedOutputEnvelope PressureFixedOutputLocalization PressureLowOutputDyadicBudget

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def sumAction (N : ℝ) (hN : 0 < N) (j : ℕ) (gamma : ℝ)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) (x : T3) (i : ↑centers) : C3 :=
  ∑' m : ℕ, rootLocalizationAction (inputScale N j) (inputScale_pos N hN j)
    (dyadicParameter (j + m)) gamma chi modes u centers tau x i

def sumActionNorm (N : ℝ) (hN : 0 < N) (j : ℕ) (gamma : ℝ)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (centers : Finset T3) (tau : ℝ) : ℝ :=
  Real.sqrt (∫ x : T3, ∑ i : ↑centers, ‖sumAction N hN j gamma chi modes u centers tau x i‖ ^ 2)

theorem sumAction_eq (N : ℝ) (hN : 0 < N) (j : ℕ) (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (x : T3) (i : ↑centers) :
    sumAction N hN j gamma chi modes u centers tau x i =
      localization N hN j (localDirection chi modes u i.1)
        (complexVorticityField u hu) (complexVorticityField u hu)
        (complexRootPatch gamma hg chi modes u hu centers hc tau i)
        (complexRootPatch gamma hg chi modes u hu centers hc tau i) x := by
  have h := (ContinuousMap.evalCLM ℂ x).hasSum (hasSum_localization N hN j
    (localDirection chi modes u i.1)
    (PancakeSpectralFiniteDifference.topVector_norm _)
    (complexVorticityField u hu) (complexVorticityField u hu)
    (complexRootPatch gamma hg chi modes u hu centers hc tau i)
    (complexRootPatch gamma hg chi modes u hu centers hc tau i))
  exact h.tsum_eq

theorem sumActionNorm_le (N : ℝ) (hN : 0 < N) (j : ℕ) (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (hs : Summable (fun m : ℕ ↦ rootLocalizationActionNorm
      (inputScale N j) (inputScale_pos N hN j) (dyadicParameter (j + m))
        gamma chi modes u centers tau)) :
    sumActionNorm N hN j gamma chi modes u centers tau ≤
      ∑' m : ℕ, rootLocalizationActionNorm (inputScale N j) (inputScale_pos N hN j)
        (dyadicParameter (j + m)) gamma chi modes u centers tau := by
  unfold sumActionNorm
  simp_rw [sumAction_eq N hN j gamma hg chi modes u hu centers hc tau]
  exact finite_localization_spatial_norm_le N hN j
    (fun i : ↑centers ↦ localDirection chi modes u i.1)
    (fun _ ↦ PancakeSpectralFiniteDifference.topVector_norm _)
    (complexVorticityField u hu) (complexVorticityField u hu)
    (complexRootPatch gamma hg chi modes u hu centers hc tau)
    (complexRootPatch gamma hg chi modes u hu centers hc tau) hs

theorem exists_uniform_band_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N, ∀ j : ℕ,
      ∀ gamma : ℝ, 0 < gamma → ∀ chi : Wavevector → ℂ, ∀ modes : Finset Wavevector,
      ∀ u : FourierVelocity, Summable (fourierMoment 2 u) →
      ∀ centers : Finset T3, centers.Nonempty → ∀ tau W : ℝ,
      (∀ x : T3, ‖fullVorticity u x‖ ≤ W) →
      Summable (fun m : ℕ ↦ rootLocalizationActionNorm (inputScale N j) (inputScale_pos N hN j)
        (dyadicParameter (j + m)) gamma chi modes u centers tau) ∧
      (∑' m : ℕ, rootLocalizationActionNorm (inputScale N j) (inputScale_pos N hN j)
        (dyadicParameter (j + m)) gamma chi modes u centers tau) ≤
        ((C / N) * (1 / 4 : ℝ) ^ j) * (W ^ 2 * Real.sqrt (6 *
          ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x)) := by
  obtain ⟨C0, C1, hC0, hC1, M, hb⟩ := exists_uniform_envelope
  refine ⟨C1, hC1, ?_⟩
  intro N hN j gamma hg chi modes u hu centers hc tau W hW
  obtain ⟨hM, hK, hbudget⟩ := hb N hN
  let B := W ^ 2 * Real.sqrt (6 * ∫ x : T3,
    squaredRootGradientSquare gamma chi modes u centers tau x)
  have hB : 0 ≤ B := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hle (m : ℕ) : rootLocalizationActionNorm (inputScale N j) (inputScale_pos N hN j)
      (dyadicParameter (j + m)) gamma chi modes u centers tau ≤
      (∫ q : T6, ‖q‖ * M N hN j m q) * B := by
    have hKm : ∀ᵐ q : T6, ∀ e : R3, ‖e‖ = 1 →
        ‖PressureDyadicPeriodization.periodicKernel (inputScale N j) (inputScale_pos N hN j)
          (dyadicParameter (j + m)) e q‖ ≤ M N hN j m q :=
      hK.mono (fun _ h ↦ h j m)
    exact (rootLocalizationActionNorm_le _ _ _ gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau).trans
        (integrable_rootLocalizationSpatialNorm_and_integral_le _ _ _ (M N hN j m)
          (hM j m).1 (hM j m).2.2.2 hKm gamma hg chi modes u hu centers hc tau W hW).2
  have hs := (hbudget j).2.2.1.mul_right B
  have ha := hs.of_nonneg_of_le (fun _ ↦ Real.sqrt_nonneg _) hle
  refine ⟨ha, ?_⟩
  calc
    _ ≤ ∑' m : ℕ, (∫ q : T6, ‖q‖ * M N hN j m q) * B := ha.tsum_le_tsum hle hs
    _ = (∑' m : ℕ, ∫ q : T6, ‖q‖ * M N hN j m q) * B := tsum_mul_right
    _ ≤ _ := mul_le_mul_of_nonneg_right (hbudget j).2.2.2 hB

/-- The complete fixed-output localization operators are summable over
every high-input tail, retaining the quarter-geometric decay. -/
theorem exists_uniform_tail_budget :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
      ∀ gamma : ℝ, 0 < gamma → ∀ chi : Wavevector → ℂ, ∀ modes : Finset Wavevector,
      ∀ u : FourierVelocity, Summable (fourierMoment 2 u) →
      ∀ centers : Finset T3, centers.Nonempty → ∀ tau W : ℝ,
      (∀ x : T3, ‖fullVorticity u x‖ ≤ W) → ∀ J : ℕ,
      Summable (fun j : ℕ ↦ sumActionNorm N hN (J + j) gamma chi modes u centers tau) ∧
      (∑' j : ℕ, sumActionNorm N hN (J + j) gamma chi modes u centers tau) ≤
        ((C / N) * (1 / 4 : ℝ) ^ J) * (W ^ 2 * Real.sqrt (6 *
          ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x)) := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_band_budget
  refine ⟨4 * C / 3, by positivity, ?_⟩
  intro N hN gamma hg chi modes u hu centers hc tau W hW J
  let B := ((C / N) * (1 / 4 : ℝ) ^ J) * (W ^ 2 * Real.sqrt (6 *
    ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x))
  have hle (j : ℕ) : sumActionNorm N hN (J + j) gamma chi modes u centers tau ≤
      B * (1 / 4 : ℝ) ^ j := by
    obtain ⟨hs, ht⟩ := hb N hN (J + j) gamma hg chi modes u hu centers hc tau W hW
    exact ((sumActionNorm_le N hN (J + j) gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau hs).trans ht).trans_eq
        (by rw [pow_add]; dsimp [B]; ring)
  have hs := hasSum_quarter.mul_left B
  have ha := hs.summable.of_nonneg_of_le (fun _ ↦ Real.sqrt_nonneg _) hle
  refine ⟨ha, ?_⟩
  exact (ha.tsum_le_tsum hle hs.summable).trans_eq (by rw [hs.tsum_eq]; dsimp [B]; ring)

end Mettapedia.FluidDynamics.NavierStokes.GaussianRootFixedOutputBudget
