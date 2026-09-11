import Mettapedia.Analysis.TruncatedKernelMoment
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FrequencyPairPeriodization

/-!
# Wrapped first moments from truncated Euclidean moments

The frequency-pair torus has the product supremum norm. Its wrapped norm
is at most one half and at most the norm of every Euclidean lift. The
weighted periodization inequality therefore uses `min (1/2) ‖x‖`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization

open MeasureTheory PancakeBilinearPeriodization
open Mettapedia.Analysis.FundamentalDomainPeriodization
open Mettapedia.Analysis.TruncatedKernelMoment
open scoped ENNReal SchwartzMap

local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T6" => UnitAddTorus (Fin 6)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem norm_frequencyPairTorus_le_half (q : T6) : ‖q‖ ≤ (1 / 2 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
  intro i
  simpa only [abs_one] using (AddCircle.norm_le_half_period (p := (1 : ℝ))
    (x := q i) (by norm_num))

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem lintegral_firstMoment_periodize_le_truncated (K : E6 → E) (hK : Measurable K) :
    (∫⁻ q : T6, ‖q‖ₑ * ‖periodize K q‖ₑ) ≤
      ∫⁻ x : E6, ENNReal.ofReal (min (1 / 2 : ℝ) ‖x‖) * ‖K x‖ₑ := by
  let w : E6 → ℝ≥0∞ := fun x ↦ ‖torusProjection x‖ₑ
  have hw : Measurable w := continuous_torusProjection.measurable.enorm
  calc
    _ = ∫⁻ x in standardFrequencyPairCell,
        w x * ‖addPeriodization (G := StandardFrequencyPairLattice) K x‖ₑ := by
      have h := lintegral_representative
        (fun x ↦ w x * ‖addPeriodization (G := StandardFrequencyPairLattice) K x‖ₑ)
        (hw.mul (measurable_addPeriodization K hK).enorm)
      simpa [w, periodize] using h
    _ ≤ ∫⁻ x, w x * ‖K x‖ₑ :=
      setLIntegral_weight_mul_enorm_addPeriodization_le standardFrequencyPairCell_isAddFundamentalDomain
        K hK w hw (fun g x ↦ by simp [w, torusProjection_vadd])
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      apply mul_le_mul_left _ _
      change ‖torusProjection x‖ₑ ≤ ENNReal.ofReal (min (1 / 2 : ℝ) ‖x‖)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal
        (le_min (norm_frequencyPairTorus_le_half _) (norm_torusProjection_le x))

variable [NormedSpace ℂ E]

theorem integral_firstMoment_periodize_le_truncated (K : 𝓢(E6, E)) :
    (∫ q : T6, ‖q‖ * ‖periodize K q‖) ≤ moment (1 / 2) K volume := by
  have hbound := lintegral_firstMoment_periodize_le_truncated K K.continuous.measurable
  have ht (q : T6) : ‖q‖ₑ * ‖periodize K q‖ₑ = ENNReal.ofReal (‖q‖ * ‖periodize K q‖) := by
    rw [ENNReal.ofReal_mul (norm_nonneg _)]
    simp only [ofReal_norm]
  have hx (x : E6) : ENNReal.ofReal (min (1 / 2 : ℝ) ‖x‖) * ‖K x‖ₑ =
      ENNReal.ofReal (min (1 / 2 : ℝ) ‖x‖ * ‖K x‖) := by
    rw [ENNReal.ofReal_mul (le_min (by norm_num) (norm_nonneg _)), ofReal_norm]
  apply (ENNReal.ofReal_le_ofReal_iff (moment_nonneg (by norm_num) K)).mp
  rw [moment, ofReal_integral_eq_lintegral_ofReal
    (by simpa only [pow_one] using integrable_moment_periodize K 1)
    (Filter.Eventually.of_forall (fun q ↦ by positivity)),
    ofReal_integral_eq_lintegral_ofReal (integrable_min_mul_norm (by norm_num) K.integrable)
    (Filter.Eventually.of_forall (fun x ↦ by positivity))]
  simpa only [ht, hx] using hbound

end Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization
