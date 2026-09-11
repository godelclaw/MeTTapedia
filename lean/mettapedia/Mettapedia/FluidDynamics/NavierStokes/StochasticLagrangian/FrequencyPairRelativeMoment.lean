import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FrequencyPairEnvelope
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureLowOutputSymbol

/-!
# Periodization preserves relative displacement moments

The difference of the two input displacements is measured after taking the
torus quotient. Its norm is bounded by the Euclidean relative displacement
on every lattice translate, independently of any common translation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization

open MeasureTheory PancakeBilinearPeriodization FrequencyPairEnvelope
open Mettapedia.Analysis.FundamentalDomainPeriodization
open PressureLowOutputSymbol (pairEquiv pairLinearEquiv)
open scoped ENNReal NNReal

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)
local instance relativeMomentCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance relativeMomentCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance relativeMomentCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def relativeDisplacement (x : E6) : R3 := (pairEquiv x).1 - (pairEquiv x).2

def relativeTorusDisplacement (q : T6) : T3 :=
  firstTorusDisplacement q - secondTorusDisplacement q

@[fun_prop] theorem continuous_relativeDisplacement : Continuous relativeDisplacement := by
  unfold relativeDisplacement
  fun_prop

@[fun_prop] theorem continuous_relativeTorusDisplacement : Continuous relativeTorusDisplacement :=
  continuous_firstTorusDisplacement.sub continuous_secondTorusDisplacement

theorem relativeTorusDisplacement_projection (x : E6) :
    relativeTorusDisplacement (torusProjection x) = fun i ↦ (relativeDisplacement x i : UnitAddCircle) := by
  ext i
  fin_cases i <;>
    simp [relativeTorusDisplacement, relativeDisplacement, firstTorusDisplacement,
      secondTorusDisplacement, torusProjection, pairEquiv, pairLinearEquiv]

theorem norm_relativeTorusDisplacement_projection_le (x : E6) :
    ‖relativeTorusDisplacement (torusProjection x)‖ ≤ ‖relativeDisplacement x‖ := by
  rw [relativeTorusDisplacement_projection]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ))).trans
    (PiLp.norm_apply_le (relativeDisplacement x) i)

theorem norm_relativeTorusDisplacement_le_half (q : T6) :
    ‖relativeTorusDisplacement q‖ ≤ (1 / 2 : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
  intro i
  simpa only [abs_one] using (AddCircle.norm_le_half_period (p := (1 : ℝ))
    (x := relativeTorusDisplacement q i) (by norm_num))

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem lintegral_relativeMoment_periodize_le (K : E6 → E) (hK : Measurable K) (m : ℕ) :
    (∫⁻ q : T6, ‖relativeTorusDisplacement q‖ₑ ^ m * ‖periodize K q‖ₑ) ≤
      ∫⁻ x : E6, ‖relativeDisplacement x‖ₑ ^ m * ‖K x‖ₑ := by
  let w : E6 → ℝ≥0∞ := fun x ↦ ‖relativeTorusDisplacement (torusProjection x)‖ₑ ^ m
  have hw : Measurable w :=
    (continuous_relativeTorusDisplacement.comp continuous_torusProjection).measurable.enorm.pow_const m
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
      have hn : ‖relativeTorusDisplacement (torusProjection x)‖ₑ ≤ ‖relativeDisplacement x‖ₑ := by
        simpa only [← ofReal_norm] using
          ENNReal.ofReal_le_ofReal (norm_relativeTorusDisplacement_projection_le x)
      exact mul_le_mul_left (pow_le_pow_left' hn m) _

theorem integrable_relativeMoment_periodize (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x)
    (hHm : Measurable H) (m : ℕ)
    (hHi : Integrable (fun x ↦ ‖relativeDisplacement x‖ ^ m * H x)) :
    Integrable (fun q : T6 ↦ ‖relativeTorusDisplacement q‖ ^ m * periodize H q) := by
  have hbound := lintegral_relativeMoment_periodize_le H hHm m
  have hfinite : (∫⁻ x : E6, ‖relativeDisplacement x‖ₑ ^ m * ‖H x‖ₑ) < ∞ := by
    have hnorm : Integrable (fun x : E6 ↦ ‖relativeDisplacement x‖ ^ m * ‖H x‖) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hH _)] using hHi
    simpa only [enorm_mul, enorm_pow, enorm_norm] using
      (hasFiniteIntegral_iff_enorm.mp hnorm.hasFiniteIntegral)
  refine ⟨((continuous_relativeTorusDisplacement.norm.pow m).measurable.mul
    (measurable_periodize H hHm)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [enorm_mul, enorm_pow, enorm_norm] using hbound.trans_lt hfinite

theorem integral_relativeMoment_periodize_le (H : E6 → ℝ) (hH : ∀ x, 0 ≤ H x)
    (hHm : Measurable H) (m : ℕ)
    (hHi : Integrable (fun x ↦ ‖relativeDisplacement x‖ ^ m * H x)) :
    (∫ q : T6, ‖relativeTorusDisplacement q‖ ^ m * periodize H q) ≤
      ∫ x : E6, ‖relativeDisplacement x‖ ^ m * H x := by
  have hbound := lintegral_relativeMoment_periodize_le H hHm m
  have ht (q : T6) : ‖relativeTorusDisplacement q‖ₑ ^ m * ‖periodize H q‖ₑ =
      ENNReal.ofReal (‖relativeTorusDisplacement q‖ ^ m * periodize H q) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _), ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (periodize_nonneg H hH q)]
  have hx (x : E6) : ‖relativeDisplacement x‖ₑ ^ m * ‖H x‖ₑ =
      ENNReal.ofReal (‖relativeDisplacement x‖ ^ m * H x) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _), ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hH x)]
  apply (ENNReal.ofReal_le_ofReal_iff
    (MeasureTheory.integral_nonneg (fun x ↦ mul_nonneg (pow_nonneg (norm_nonneg _) _) (hH x)))).mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_relativeMoment_periodize H hH hHm m hHi)
    (Filter.Eventually.of_forall (fun q ↦ mul_nonneg (pow_nonneg (norm_nonneg _) _) (periodize_nonneg H hH q))),
    ofReal_integral_eq_lintegral_ofReal hHi
    (Filter.Eventually.of_forall (fun x ↦ mul_nonneg (pow_nonneg (norm_nonneg _) _) (hH x)))]
  simpa only [ht, hx] using hbound

variable {F : Type*} [NormedAddCommGroup F]

theorem norm_translated_field_sub_le {L : ℝ≥0} (P : T3 → F) (hP : LipschitzWith L P)
    (x : T3) (q : T6) :
    ‖P (x - firstTorusDisplacement q) - P (x - secondTorusDisplacement q)‖ ≤
      L * ‖relativeTorusDisplacement q‖ := by
  have h := hP.dist_le_mul (x - firstTorusDisplacement q) (x - secondTorusDisplacement q)
  have he : (x - firstTorusDisplacement q) - (x - secondTorusDisplacement q) =
      -relativeTorusDisplacement q := by dsimp [relativeTorusDisplacement]; abel
  simpa only [dist_eq_norm, he, norm_neg] using h

/-- Squared field separation is integrable whenever the envelope has a finite
relative second moment. The Lipschitz constant is an explicit spatial cost. -/
theorem integrable_and_integral_translated_field_sub_sq_le (M : T6 → ℝ)
    (hn : ∀ q, 0 ≤ M q) (hm : Measurable M)
    (hi : Integrable (fun q ↦ ‖relativeTorusDisplacement q‖ ^ 2 * M q))
    {L : ℝ≥0} (P : T3 → F) (hP : LipschitzWith L P) (x : T3) :
    Integrable (fun q ↦ ‖P (x - firstTorusDisplacement q) - P (x - secondTorusDisplacement q)‖ ^ 2 * M q) ∧
      (∫ q : T6, ‖P (x - firstTorusDisplacement q) - P (x - secondTorusDisplacement q)‖ ^ 2 * M q) ≤
        (L : ℝ) ^ 2 * ∫ q : T6, ‖relativeTorusDisplacement q‖ ^ 2 * M q := by
  have hb (q : T6) :
      ‖P (x - firstTorusDisplacement q) - P (x - secondTorusDisplacement q)‖ ^ 2 * M q ≤
        (L : ℝ) ^ 2 * (‖relativeTorusDisplacement q‖ ^ 2 * M q) := by
    have h := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (norm_translated_field_sub_le P hP x q) 2) (hn q)
    simpa only [mul_pow, mul_assoc] using h
  have hc : Continuous (fun q ↦
      ‖P (x - firstTorusDisplacement q) - P (x - secondTorusDisplacement q)‖ ^ 2) :=
    ((hP.continuous.comp (continuous_const.sub continuous_firstTorusDisplacement)).sub
      (hP.continuous.comp (continuous_const.sub continuous_secondTorusDisplacement))).norm.pow 2
  have hg : Integrable (fun q ↦
      ‖P (x - firstTorusDisplacement q) - P (x - secondTorusDisplacement q)‖ ^ 2 * M q) := by
    apply (hi.const_mul ((L : ℝ) ^ 2)).mono' (hc.measurable.mul hm).aestronglyMeasurable
    filter_upwards [] with q
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hn q))]
    exact hb q
  refine ⟨hg, ?_⟩
  exact (integral_mono hg (hi.const_mul _) hb).trans_eq (integral_const_mul _ _)

end Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization
