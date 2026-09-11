import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FrequencyPairPeriodization

/-!
# Common envelopes on the frequency-pair torus

An integrable nonnegative envelope gives a single full-measure set on
which periodization preserves domination for every member of a family.
No countability of the parameter family is required.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FrequencyPairEnvelope

open MeasureTheory Set FrequencyPairPeriodization PancakeBilinearPeriodization
open Mettapedia.Analysis.FundamentalDomainPeriodization
open scoped ENNReal

local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T6" => UnitAddTorus (Fin 6)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem periodize_nonneg (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x) (q : T6) :
    0 ≤ periodize H q := tsum_nonneg (fun _ ↦ hH _)

theorem ae_summable_envelope_orbit (H : E6 → ℝ) (hH : Measurable H) (hHi : Integrable H) :
    ∀ᵐ q : T6, Summable (fun g : StandardFrequencyPairLattice ↦
      ‖H (g +ᵥ unitTorusFrequencyPairRepresentative q)‖) := by
  let F : E6 → ℝ≥0∞ := fun x ↦ ∑' g : StandardFrequencyPairLattice, ‖H (g +ᵥ x)‖ₑ
  have hm : Measurable F := Measurable.tsum (fun g ↦ (hH.comp (measurable_const_vadd g)).enorm)
  have he : (∫⁻ q : T6, F (unitTorusFrequencyPairRepresentative q)) = ∫⁻ x : E6, ‖H x‖ₑ := by
    rw [lintegral_representative F hm]
    unfold F
    rw [lintegral_tsum]
    · exact (standardFrequencyPairCell_isAddFundamentalDomain.lintegral_eq_tsum'' (fun x ↦ ‖H x‖ₑ)).symm
    · intro g
      exact (hH.comp (measurable_const_vadd g)).enorm.aemeasurable
  have hf := ae_lt_top (hm.comp measurable_unitTorusFrequencyPairRepresentative)
    (he.trans_ne (hasFiniteIntegral_iff_enorm.mp hHi.hasFiniteIntegral).ne)
  filter_upwards [hf] with q hq
  exact tsum_enorm_ne_top_iff_summable_norm.mp hq.ne

theorem ae_norm_periodize_family_le {A E : Type*} [NormedAddCommGroup E]
    (K : A → E6 → E) (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x)
    (hHm : Measurable H) (hHi : Integrable H) (hK : ∀ a x, ‖K a x‖ ≤ H x) :
    ∀ᵐ q : T6, ∀ a, ‖periodize (K a) q‖ ≤ periodize H q := by
  filter_upwards [ae_summable_envelope_orbit H hHm hHi] with q hq a
  have hs : Summable (fun g : StandardFrequencyPairLattice ↦
      H (g +ᵥ unitTorusFrequencyPairRepresentative q)) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hH _)] using hq
  have hkn : Summable (fun g : StandardFrequencyPairLattice ↦
      ‖K a (g +ᵥ unitTorusFrequencyPairRepresentative q)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ hK a _) hs
  exact (norm_tsum_le_tsum_norm hkn).trans (hkn.tsum_le_tsum (fun _ ↦ hK a _) hs)

theorem integrable_moment_periodize (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x)
    (hHm : Measurable H) (m : ℕ) (hHi : Integrable (fun x ↦ ‖x‖ ^ m * H x)) :
    Integrable (fun q : T6 ↦ ‖q‖ ^ m * periodize H q) := by
  have hbound := lintegral_moment_periodize_le H hHm m
  have hfinite : (∫⁻ x : E6, ‖x‖ₑ ^ m * ‖H x‖ₑ) < ∞ := by
    have hnorm : Integrable (fun x : E6 ↦ ‖x‖ ^ m * ‖H x‖) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hH _)] using hHi
    simpa only [enorm_mul, enorm_pow, enorm_norm] using
      (hasFiniteIntegral_iff_enorm.mp hnorm.hasFiniteIntegral)
  refine ⟨((continuous_norm.pow m).measurable.mul (measurable_periodize H hHm)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [enorm_mul, enorm_pow, enorm_norm] using hbound.trans_lt hfinite

theorem integral_moment_periodize_le (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x)
    (hHm : Measurable H) (m : ℕ) (hHi : Integrable (fun x ↦ ‖x‖ ^ m * H x)) :
    (∫ q : T6, ‖q‖ ^ m * periodize H q) ≤ ∫ x : E6, ‖x‖ ^ m * H x := by
  have hbound := lintegral_moment_periodize_le H hHm m
  have ht (q : T6) : ‖q‖ₑ ^ m * ‖periodize H q‖ₑ =
      ENNReal.ofReal (‖q‖ ^ m * periodize H q) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _), ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (periodize_nonneg H hH q)]
  have hx (x : E6) : ‖x‖ₑ ^ m * ‖H x‖ₑ = ENNReal.ofReal (‖x‖ ^ m * H x) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _), ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hH x)]
  apply (ENNReal.ofReal_le_ofReal_iff
    (MeasureTheory.integral_nonneg (fun x ↦ mul_nonneg (pow_nonneg (norm_nonneg _) _) (hH x)))).mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_moment_periodize H hH hHm m hHi)
    (Filter.Eventually.of_forall (fun q ↦ mul_nonneg (pow_nonneg (norm_nonneg _) _) (periodize_nonneg H hH q))),
    ofReal_integral_eq_lintegral_ofReal hHi
    (Filter.Eventually.of_forall (fun x ↦ mul_nonneg (pow_nonneg (norm_nonneg _) _) (hH x)))]
  simpa only [ht, hx] using hbound

end Mettapedia.FluidDynamics.NavierStokes.FrequencyPairEnvelope
