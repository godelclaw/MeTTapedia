import Mettapedia.Analysis.RegularizedProjectionParameter
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredCoherentProjectionBudget

/-!
# The signed cost of changing the projection normalization

This is a cost of changing the scalar normalization on a fixed filtered
field. Moving the Fourier multiplier itself would add another source.
The crude bound charges the relative normalization speed to corrected
energy; it does not prove that this speed has finite time integral.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalProjectionScaleMotion

open MeasureTheory Mettapedia.Analysis RegularizedProjectionParameter
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open LocalLowDiffusionBudget LocalWeightedProjectionEvolution LocalHelicityProjectionEvolution
open LocalHelicityProjectionDiffusion LocalVariableHelicityCenter LocalVorticityEighthMoment
open LocalWeightedCurlCancellation
open FiniteBandProjectionAbsorption FourierFiniteSupport
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def scaleDensity (ν κ dκ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  scaleRate ν κ dκ (fullVorticity u x) (fullVorticity (fourierCurl u) x)

def scaleWork (ν κ dκ : ℝ) (u : FourierVelocity) : ℝ := ∫ x : T3, scaleDensity ν κ dκ u x

theorem continuous_scaleDensity (ν κ dκ : ℝ) (hν : 0 < ν) (hκ : 0 < κ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) : Continuous (scaleDensity ν κ dκ u) := by
  have ha := continuous_fullVorticity u (summable_firstMoment_of_second u hu)
  have hb := continuous_fullVorticity (fourierCurl u) (summable_fourierMoment_curl 1 u hu)
  unfold scaleDensity scaleRate RegularizedProjection.residual RegularizedProjection.coefficient
  fun_prop (disch := intro x; positivity)

theorem abs_scaleDensity_le (ν κ dκ : ℝ) (u : FourierVelocity) (x : T3) :
    |scaleDensity ν κ dκ u x| ≤
      (3 * |dκ| / κ ^ 2) * weightedProjectionDensity (ν ^ 2 * κ ^ 2 / 3) u x :=
  abs_scaleRate_le ν κ dκ _ _

theorem abs_scaleWork_le (ν κ dκ : ℝ) (hν : 0 < ν) (hκ : 0 < κ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    |scaleWork ν κ dκ u| ≤ (3 * |dκ| / κ ^ 2) * weightedProjectionEnergy (ν ^ 2 * κ ^ 2 / 3) u := by
  have hδ : 0 < ν ^ 2 * κ ^ 2 / 3 := by positivity
  have hs : Integrable (scaleDensity ν κ dκ u) :=
    (continuous_scaleDensity ν κ dκ hν hκ u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hW : Integrable (weightedProjectionDensity (ν ^ 2 * κ ^ 2 / 3) u) :=
    (continuous_weightedProjectionDensity _ hδ u hu).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact (abs_integral_le_integral_abs.trans
    (integral_mono hs.abs (hW.const_mul _) (abs_scaleDensity_le ν κ dκ u))).trans_eq
      (integral_const_mul _ _)

/-- Coercivity supplies a multiplicative bound, not a bound on the time
integral of the logarithmic scale speed. -/
theorem abs_scaleWork_le_logarithmic_rate (ν R dκ : ℝ) (hν : 0 < ν)
    (P : Finset Wavevector) (u : FourierVelocity) (hs : ∀ q, q ∉ P → u q = 0)
    (hP : ∀ q ∈ P, ‖PancakeFrequencyProjectorCommutator.frequencyVec q‖ ≤ R) :
    |scaleWork ν (normalization R) dκ u| ≤
      (|dκ| / normalization R) * correctedEnergy ν R u := by
  have hκ := normalization_pos R
  have hb := (correctedEnergy_bounds P u hs R hP ν hν).1
  have h := abs_scaleWork_le ν (normalization R) dκ hν hκ u (summable_fourierMoment P u hs 2)
  have he : (3 * |dκ| / normalization R ^ 2) *
      weightedProjectionEnergy (ν ^ 2 * normalization R ^ 2 / 3) u =
      (|dκ| / normalization R) * (meanEnergy u / 8 - correctedEnergy ν R u) := by
    unfold correctedEnergy regularization
    field_simp
    ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith only [hb]) (by positivity))

/-- Retaining a fixed support radius improves the relative-speed bound
to inverse-square speed. The radius is not a count of Fourier modes. -/
theorem abs_scaleWork_le_fixed_band (ν R R₀ dκ : ℝ) (hν : 0 < ν)
    (P : Finset Wavevector) (u : FourierVelocity) (hs : ∀ q, q ∉ P → u q = 0)
    (hP₀ : ∀ q ∈ P, ‖PancakeFrequencyProjectorCommutator.frequencyVec q‖ ≤ R₀)
    (hP : ∀ q ∈ P, ‖PancakeFrequencyProjectorCommutator.frequencyVec q‖ ≤ R) :
    |scaleWork ν (normalization R) dκ u| ≤
      (48 * (8 * Real.pi * R₀) ^ 2 * (|dκ| / normalization R ^ 2)) * correctedEnergy ν R u := by
  have h := abs_scaleWork_le ν (normalization R) dκ hν (normalization_pos R) u
    (summable_fourierMoment P u hs 2)
  have hK := FiniteBandProjectionEnergy.weightedProjectionEnergy_le_meanEnergy
    P u hs R₀ hP₀ (regularization ν R) (regularization_pos ν R hν)
  have hE : meanEnergy u ≤ 16 * correctedEnergy ν R u := by
    linarith only [(correctedEnergy_bounds P u hs R hP ν hν).1]
  have hKE := hK.trans (mul_le_mul_of_nonneg_left hE (sq_nonneg _))
  have hc : 0 ≤ 3 * |dκ| / normalization R ^ 2 := by positivity
  exact h.trans ((mul_le_mul_of_nonneg_left hKE hc).trans_eq (by ring))

def normalizationRate (R : ℝ) : ℝ :=
  96 * (8 * Real.pi) ^ 2 * R + 24 * curvatureConstant * (2 * Real.pi) ^ 2 * R

theorem hasDerivAt_normalization (R : ℝ) : HasDerivAt normalization (normalizationRate R) R := by
  have h1 := (((hasDerivAt_id R).const_mul (8 * Real.pi)).pow 2).const_mul 48
  have h2 := (((hasDerivAt_id R).const_mul (2 * Real.pi)).pow 2).const_mul (12 * curvatureConstant)
  have h := (h1.add h2).add_const 1
  change HasDerivAt normalization _ R at h
  apply h.congr_deriv
  simp only [normalizationRate, Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, mul_one]
  ring

end Mettapedia.FluidDynamics.NavierStokes.LocalProjectionScaleMotion
