import Mettapedia.Analysis.WeightedSeries
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureHighInputFourier
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureFixedOutputReconstruction

/-!
# The finite low-input complement of the complete pressure tail

Summing all high-input annuli leaves a low-pass input weight supported in
the ball of radius twice the initial input scale. The complement is a
concrete finite sum, even when the original velocity has infinite Fourier
support. It is retained with its exact physical sign.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureHighInputComplement

open MeasureTheory PeriodicFourierTriad FourierPressureCommutator FourierPressureTraceSymbol
open PressureFixedOutputSymbol PressureHighInputAction PressureHighInputFourier
open PressureDyadicPhysicalIdentification PressureFixedOutputReconstruction PancakeArbitraryDataBlocks
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeFourierTranslationCurve PancakeInfiniteFourierDerivative PancakeBlockReality
open PancakeGalerkinKineticEnergy ComplexPressurePair GaussianRootOperatorBudget FourierPressureTiltEnergy
open Mettapedia.Analysis.WeightedSeries

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def lowInputMultiplier (N : ℝ) (J : ℕ) (k : Wavevector) : ℝ := 1 - inputMultiplier N J k

theorem inputMultiplier_nonneg (N : ℝ) (J : ℕ) (k : Wavevector) : 0 ≤ inputMultiplier N J k :=
  Mettapedia.Analysis.DyadicHighPass.multiplier_nonneg _

theorem inputMultiplier_le_one (N : ℝ) (J : ℕ) (k : Wavevector) : inputMultiplier N J k ≤ 1 :=
  Mettapedia.Analysis.DyadicHighPass.multiplier_le_one _

theorem lowInputMultiplier_eq_lowPass (N : ℝ) (J : ℕ) (k : Wavevector) :
    lowInputMultiplier N J k = Mettapedia.Analysis.DyadicLowPass.multiplier
      ((2 : ℝ) • ((inputScale N J)⁻¹ • realFrequency k)) := by
  unfold lowInputMultiplier inputMultiplier Mettapedia.Analysis.DyadicHighPass.multiplier
  ring

theorem lowInputMultiplier_nonneg (N : ℝ) (J : ℕ) (k : Wavevector) :
    0 ≤ lowInputMultiplier N J k := sub_nonneg.mpr (inputMultiplier_le_one N J k)

theorem lowInputMultiplier_eq_zero_of_le_norm (N : ℝ) (hN : 0 < N) (J : ℕ) (k : Wavevector)
    (hk : 2 * inputScale N J ≤ ‖realFrequency k‖) : lowInputMultiplier N J k = 0 := by
  have hi := inputScale_pos N hN J
  unfold lowInputMultiplier inputMultiplier
  rw [Mettapedia.Analysis.DyadicHighPass.multiplier_eq_one_of_le_norm]
  · ring
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hi.le)]
    calc
      (2 : ℝ) = (inputScale N J)⁻¹ * (2 * inputScale N J) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hk (inv_nonneg.mpr hi.le)

def lowInputModes (N : ℝ) (J : ℕ) : Finset Wavevector := wavevectorBox ⌈2 * inputScale N J⌉₊

theorem lowInputMultiplier_eq_zero_of_not_mem (N : ℝ) (hN : 0 < N) (J : ℕ)
    (k : Wavevector) (hk : k ∉ lowInputModes N J) : lowInputMultiplier N J k = 0 := by
  apply lowInputMultiplier_eq_zero_of_le_norm N hN J k
  by_contra hn
  apply hk
  rw [lowInputModes, mem_wavevectorBox_iff]
  intro i
  have hi := (PiLp.norm_apply_le (realFrequency k) i).trans
    ((le_of_lt (lt_of_not_ge hn)).trans (Nat.le_ceil (2 * inputScale N J)))
  change ‖(k i : ℝ)‖ ≤ (⌈2 * inputScale N J⌉₊ : ℝ) at hi
  rw [Real.norm_eq_abs] at hi
  exact_mod_cast hi

def lowInputCoefficient (N : ℝ) (J : ℕ) (e : R3) (u : FourierVelocity) (q : Wavevector) : C3 :=
  ∑ k ∈ lowInputModes N J, (lowInputMultiplier N J k : ℂ) •
    tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k))

theorem lowInputCoefficient_eq_tsum (N : ℝ) (hN : 0 < N) (J : ℕ)
    (e : R3) (u : FourierVelocity) (q : Wavevector) :
    lowInputCoefficient N J e u q = ∑' k, (lowInputMultiplier N J k : ℂ) •
      tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) := by
  symm
  apply tsum_eq_sum
  intro k hk
  rw [lowInputMultiplier_eq_zero_of_not_mem N hN J k hk, Complex.ofReal_zero, zero_smul]

theorem high_add_low_coefficient (N : ℝ) (hN : 0 < N) (J : ℕ) (e : R3) (he : ‖e‖ = 1)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (q : Wavevector) :
    (∑' k, (inputMultiplier N J k : ℂ) •
      tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k))) +
        lowInputCoefficient N J e u q =
      ∑' k, tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) := by
  have hw (k : Wavevector) : ‖(inputMultiplier N J k : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inputMultiplier_nonneg N J k)]
    exact inputMultiplier_le_one N J k
  have hc (k : Wavevector) : ‖1 - (inputMultiplier N J k : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (inputMultiplier_le_one N J k))]
    exact sub_le_self _ (inputMultiplier_nonneg N J k)
  rw [lowInputCoefficient_eq_tsum N hN J e u q]
  simp only [lowInputMultiplier, Complex.ofReal_sub, Complex.ofReal_one]
  exact tsum_smul_add_complement _ _ (summable_norm_curlTiltPair e he u hu q) 1 1 hw hc

theorem mFourierCoeff_tailOperator_vorticity (N : ℝ) (hN : 0 < N) (J : ℕ)
    (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (q : Wavevector) :
    UnitAddTorus.mFourierCoeff (tailOperator N hN J e
      (complexVorticityField u hu1) (complexVorticityField u hu1)) q =
      (outputMultiplier N q : ℂ) • ∑' k, (inputMultiplier N J k : ℂ) •
        tiltPair e k (q - k) (fourierCurl u k) (fourierCurl u (q - k)) := by
  rw [complexVorticityField_eq_fullFourierField u hu hu1 hr]
  rw [mFourierCoeff_tailOperator N hN J e he _ _
    (PhysicalPressurePair.summable_norm_fourierCurl u hu)
    (PhysicalPressurePair.summable_norm_fourierCurl u hu) q]
  exact tsum_const_smul'' _

theorem tiltCoefficient_eq_tail_add_low (N : ℝ) (hN : 0 < N) (J : ℕ)
    (e : R3) (he : ‖e‖ = 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hu1 : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (q : Wavevector) :
    coefficientVec (tiltCoefficient (fun q ↦ (outputMultiplier N q : ℂ)) u e q) =
      -UnitAddTorus.mFourierCoeff (tailOperator N hN J e
        (complexVorticityField u hu1) (complexVorticityField u hu1)) q -
          (outputMultiplier N q : ℂ) • lowInputCoefficient N J e u q := by
  rw [PhysicalPressurePair.tiltCoefficient_eq_tsum_pairs _ u hd hu e q,
    mFourierCoeff_tailOperator_vorticity N hN J e he u hu hu1 hr q,
    ← high_add_low_coefficient N hN J e he u hu q]
  simp only [neg_smul, smul_add, sub_eq_add_neg]

end Mettapedia.FluidDynamics.NavierStokes.PressureHighInputComplement
