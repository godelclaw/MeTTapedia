import Mettapedia.Analysis.AngularCurlSourceBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularSourceWork

/-!
# Cutoff-uniform corrected work for a bounded differentiable source

The source and its derivative are tested against the actual finite field.
Integration by parts and the quartic tensor Bernstein estimate remove
vorticity derivative norms from the final growth coefficient. Bounds for
the source operator and its derivative remain explicit hypotheses; they
are not inferred for the full nonlinear strain.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteAngularSourceBound

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis AngularCurlDecomposition
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeHaarTransportRate
open PancakeFourierTranslationCurve LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalVorticityEighthMoment FourierFiniteSupport FiniteVorticityMixedJets
open FiniteAngularSourceWork FiniteBandProjectionEnergy
local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (P : Finset Wavevector) (u : FourierVelocity) (hs : ∀ q, q ∉ P → u q = 0)
  (f : T3 → R3) (E : Fin 3 → T3 → R3) (hf : Continuous f) (hE : ∀ j, Continuous (E j))
  (hdf : ∀ j x h, HasDerivAt (fun t ↦ f (x + coordinateShift j t)) (E j (x + coordinateShift j h)) h)
  (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
  (hfv : ∀ x, ‖f x‖ ≤ M * ‖fullVorticity u x‖)
  (hEv : ∀ j x, ‖E j x‖ ≤ M * ‖fullCurlGradient u j x‖ + N * ‖fullVorticity u x‖)

include hs hf hE hdf hM hN hfv hEv

theorem abs_integral_angularGradient_source_le :
    |∫ x : T3, ⟪angularGradient u x, f x⟫| ≤
      (384 * M + 144 * N) * weightedPalinstrophy u + 48 * N * meanEnergy u := by
  have hu := summable_fourierMoment P u hs 3
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  have he := integral_angularCurlDensityRate_eq (fullVorticity u) f (fullCurlGradient u) E
    (fun j k ↦ mixed u k j) coordinateShift ha hf hD hE (fun _ _ ↦ continuous_mappedField _)
    continuous_coordinateShift coordinateShift_zero (hasDerivAt_fullVorticity_shift u hu) hdf
    (fun j k ↦ hasDerivAt_gradient_shift P u hs k j)
  change _ = ∫ x : T3, ⟪angularGradient u x, f x⟫ at he
  have hi := (continuous_angularCurlDensityRate (fullVorticity u) f (fullCurlGradient u) E
    ha hf hD hE).integrable_of_hasCompactSupport (μ := volume) (HasCompactSupport.of_compactSpace _)
  have hG := (continuous_weightedPalinstrophyDensity u hu).integrable_of_hasCompactSupport
    (μ := volume) (HasCompactSupport.of_compactSpace _)
  have h₈ := (ha.norm.pow 8).integrable_of_hasCompactSupport
    (μ := volume) (HasCompactSupport.of_compactSpace _)
  rw [← he]
  apply abs_integral_le_integral_abs.trans
  have hb := integral_mono hi.abs ((hG.const_mul (384 * M + 144 * N)).add (h₈.const_mul (48 * N)))
    (fun x ↦ abs_angularCurlDensityRate_le_of_source_bounds _ _ _ _ M N hM hN (hfv x) (fun j ↦ hEv j x))
  simp only [Pi.add_apply] at hb
  rw [integral_add (hG.const_mul _) (h₈.const_mul _), integral_const_mul, integral_const_mul] at hb
  simpa only [meanEnergy, energy_eq_norm_pow, weightedPalinstrophy,
    GaussianRootWeightedIncrement.weightedPalinstrophyDensity] using hb

/-- One fixed numerical coefficient works for every retained support and
radius. The hypotheses concern the incoming source, not unknown vorticity norms. -/
theorem abs_integral_correctedGradient_source_le (κ R : ℝ) (hκ : 0 < κ)
    (hP : ∀ q ∈ P, ‖PancakeFrequencyProjectorCommutator.frequencyVec q‖ ≤ R)
    (hscale : 1 + (8 * Real.pi * R) ^ 2 ≤ κ) :
    |∫ x : T3, ⟪correctedGradient κ u x, f x⟫| ≤ (577 * M + 360 * N) * meanEnergy u := by
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hi : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x, f x⟫) :=
    ((ha.norm.pow 6).mul (ha.inner hf)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hA : Integrable (fun x : T3 ↦ ⟪angularGradient u x, f x⟫) :=
    ((continuous_angularGradient P u hs).inner hf).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h₈ := (ha.norm.pow 8).integrable_of_hasCompactSupport
    (μ := volume) (HasCompactSupport.of_compactSpace _)
  have hbase : |∫ x : T3, ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x, f x⟫| ≤ M * meanEnergy u := by
    apply abs_integral_le_integral_abs.trans
    have h := integral_mono hi.abs (h₈.const_mul M) (fun x ↦ ?_)
    · simpa only [integral_const_mul, meanEnergy, energy_eq_norm_pow] using h
    · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖fullVorticity u x‖ ^ 6)]
      calc
        _ ≤ ‖fullVorticity u x‖ ^ 6 * (‖fullVorticity u x‖ * ‖f x‖) := by
          gcongr; exact abs_real_inner_le_norm _ _
        _ ≤ ‖fullVorticity u x‖ ^ 6 * (‖fullVorticity u x‖ * (M * ‖fullVorticity u x‖)) := by
          gcongr; exact hfv x
        _ = _ := by ring
  have hb := abs_integral_angularGradient_source_le P u hs f E hf hE hdf M N hM hN hfv hEv
  have hG := tensorGradientEnergy_le P u hs R hP
  rw [tensorGradientEnergy_eq u (summable_fourierMoment P u hs 3)] at hG
  have hGn : 2 * weightedPalinstrophy u ≤ κ * meanEnergy u := by
    have hh := mul_le_mul_of_nonneg_right hscale (meanEnergy_nonneg u)
    nlinarith only [hG, hh, radialDissipation_nonneg u, meanEnergy_nonneg u]
  have hκone : 1 ≤ κ := by nlinarith only [hscale, sq_nonneg (8 * Real.pi * R)]
  simp only [correctedGradient, inner_sub_left, real_inner_smul_left]
  rw [integral_sub hi (hA.const_mul _), integral_const_mul]
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3 / κ)]
  have hc := add_le_add hbase (mul_le_mul_of_nonneg_left hb (show 0 ≤ 3 / κ by positivity))
  apply hc.trans
  apply (le_of_mul_le_mul_right (a := κ) ?_ hκ)
  have hp := mul_le_mul_of_nonneg_left hGn (show 0 ≤ 192 * M + 72 * N by positivity)
  have henergy := meanEnergy_nonneg u
  have hn := mul_le_mul_of_nonneg_left hκone (show 0 ≤ 144 * N * meanEnergy u by positivity)
  field_simp
  nlinarith only [hp, hn]

end Mettapedia.FluidDynamics.NavierStokes.FiniteAngularSourceBound
