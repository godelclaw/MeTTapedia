import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBilinearPeriodization
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Kernel-independent transfer on the frequency-pair torus

The standard lattice geometry transfers arbitrary kernels, not only coherent
stretching kernels. Spatial weights use the torus norm, which measures wrapped
distance and is bounded by the Euclidean norm on every lattice translate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization

open MeasureTheory Set PancakeBilinearPeriodization
open Mettapedia.Analysis.FundamentalDomainPeriodization
open scoped ENNReal FourierTransform SchwartzMap

local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "T6" => UnitAddTorus (Fin 6)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusProjection (x : E6) : T6 := fun i ↦ (x i : UnitAddCircle)

@[fun_prop] theorem continuous_torusProjection : Continuous torusProjection := by
  unfold torusProjection
  fun_prop

@[simp] theorem torusProjection_representative (q : T6) :
    torusProjection (unitTorusFrequencyPairRepresentative q) = q := by
  ext i
  exact AddCircle.coe_equivIoc

theorem torusProjection_vadd (g : StandardFrequencyPairLattice) (x : E6) :
    torusProjection (g +ᵥ x) = torusProjection x := by
  obtain ⟨z, hz⟩ := exists_integerCoordinates_standardFrequencyPairLattice g
  ext i
  change (((g : E6) i + x i : ℝ) : UnitAddCircle) = (x i : UnitAddCircle)
  rw [hz, AddCircle.coe_add]
  have hi : ((z i : ℝ) : UnitAddCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨z i, by simp⟩
  exact (congrArg (fun q : UnitAddCircle ↦ q + (x i : UnitAddCircle)) hi).trans (zero_add _)

theorem norm_torusProjection_le (x : E6) : ‖torusProjection x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ))).trans
    (PiLp.norm_apply_le x i)

theorem norm_firstTorusDisplacement_le (q : T6) : ‖firstTorusDisplacement q‖ ≤ ‖q‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
  intro i
  exact norm_le_pi_norm q _

theorem norm_secondTorusDisplacement_le (q : T6) : ‖secondTorusDisplacement q‖ ≤ ‖q‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
  intro i
  exact norm_le_pi_norm q _

theorem integral_representative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E6 → F) :
    (∫ q : T6, f (unitTorusFrequencyPairRepresentative q)) =
      ∫ x in standardFrequencyPairCell, f x := by
  calc
    _ = ∫ x : Fin 6 → ℝ in rawFrequencyPairCellIoc,
        f (unitTorusFrequencyPairRepresentative (fun i ↦ (x i : UnitAddCircle))) := by
      simpa [rawFrequencyPairCellIoc] using UnitAddTorus.integral_preimage
        (fun q : T6 ↦ f (unitTorusFrequencyPairRepresentative q)) (fun _ ↦ (0 : ℝ))
    _ = ∫ x : Fin 6 → ℝ in rawFrequencyPairCellIoc, f (WithLp.toLp 2 x) := by
      apply setIntegral_congr_fun
        (show MeasurableSet rawFrequencyPairCellIoc from MeasurableSet.univ_pi' (fun _ ↦ measurableSet_Ioc))
      intro x hx
      dsimp only
      rw [unitTorusFrequencyPairRepresentative_coe x hx]
    _ = ∫ x : Fin 6 → ℝ in rawFrequencyPairCellIco, f (WithLp.toLp 2 x) :=
      setIntegral_congr_set rawFrequencyPairCellIco_ae_eq_Ioc.symm
    _ = _ := by
      have h := (PiLp.volume_preserving_toLp (Fin 6)).setIntegral_preimage_emb
        (MeasurableEquiv.toLp 2 (Fin 6 → ℝ)).measurableEmbedding f standardFrequencyPairCell
      rwa [preimage_standardFrequencyPairCell_toLp] at h

theorem lintegral_representative (f : E6 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q : T6, f (unitTorusFrequencyPairRepresentative q)) =
      ∫⁻ x in standardFrequencyPairCell, f x := by
  calc
    _ = ∫⁻ x : Fin 6 → ℝ in rawFrequencyPairCellIoc,
        f (unitTorusFrequencyPairRepresentative (fun i ↦ (x i : UnitAddCircle))) := by
      simpa [rawFrequencyPairCellIoc] using UnitAddTorus.lintegral_preimage
        (fun q : T6 ↦ f (unitTorusFrequencyPairRepresentative q)) (fun _ ↦ (0 : ℝ))
    _ = ∫⁻ x : Fin 6 → ℝ in rawFrequencyPairCellIoc, f (WithLp.toLp 2 x) := by
      apply setLIntegral_congr_fun
        (show MeasurableSet rawFrequencyPairCellIoc from MeasurableSet.univ_pi' (fun _ ↦ measurableSet_Ioc))
      intro x hx
      dsimp only
      rw [unitTorusFrequencyPairRepresentative_coe x hx]
    _ = ∫⁻ x : Fin 6 → ℝ in rawFrequencyPairCellIco, f (WithLp.toLp 2 x) :=
      setLIntegral_congr rawFrequencyPairCellIco_ae_eq_Ioc.symm
    _ = _ := by
      have h := (PiLp.volume_preserving_toLp (Fin 6)).setLIntegral_comp_preimage
        (ZSpan.fundamentalDomain_measurableSet standardFrequencyPairBasis) hf
      change (∫⁻ x in (WithLp.toLp 2 : (Fin 6 → ℝ) → E6) ⁻¹' standardFrequencyPairCell,
        f (WithLp.toLp 2 x)) = ∫⁻ x in standardFrequencyPairCell, f x at h
      rwa [preimage_standardFrequencyPairCell_toLp] at h

variable {E : Type*} [NormedAddCommGroup E]

def periodize (K : E6 → E) (q : T6) : E :=
  addPeriodization (G := StandardFrequencyPairLattice) K (unitTorusFrequencyPairRepresentative q)

variable [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

theorem measurable_periodize (K : E6 → E) (hK : Measurable K) : Measurable (periodize K) :=
  (measurable_addPeriodization K hK).comp measurable_unitTorusFrequencyPairRepresentative

theorem lintegral_moment_periodize_le (K : E6 → E) (hK : Measurable K) (m : ℕ) :
    (∫⁻ q : T6, ‖q‖ₑ ^ m * ‖periodize K q‖ₑ) ≤ ∫⁻ x : E6, ‖x‖ₑ ^ m * ‖K x‖ₑ := by
  let w : E6 → ℝ≥0∞ := fun x ↦ ‖torusProjection x‖ₑ ^ m
  have hw : Measurable w := continuous_torusProjection.measurable.enorm.pow_const m
  calc
    _ = ∫⁻ x in standardFrequencyPairCell, w x * ‖addPeriodization (G := StandardFrequencyPairLattice) K x‖ₑ := by
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
      change ‖torusProjection x‖ₑ ^ m * ‖K x‖ₑ ≤ ‖x‖ₑ ^ m * ‖K x‖ₑ
      have hn : ‖torusProjection x‖ₑ ≤ ‖x‖ₑ := by
        simpa only [← ofReal_norm] using (ENNReal.ofReal_le_ofReal (norm_torusProjection_le x))
      exact mul_le_mul_left (pow_le_pow_left' hn m) _

variable [NormedSpace ℂ E]

theorem mFourierCoeff_periodize (K : E6 → E) (hK : Measurable K) (hKi : Integrable K)
    (n : Fin 6 → ℤ) :
    UnitAddTorus.mFourierCoeff (periodize K) n = (𝓕 K) (euclideanFrequencyPairOfWavevector n) := by
  have hchar (x : E6) : UnitAddTorus.mFourier (-n) (torusProjection x) =
      euclideanFrequencyPairCharacter n x :=
    mFourier_neg_coe_eq_euclideanFrequencyPairCharacter n (WithLp.ofLp x)
  calc
    _ = ∫ q : T6, euclideanFrequencyPairCharacter n (unitTorusFrequencyPairRepresentative q) •
        addPeriodization (G := StandardFrequencyPairLattice) K (unitTorusFrequencyPairRepresentative q) := by
      apply integral_congr_ae
      filter_upwards with q
      rw [← hchar, torusProjection_representative]
      rfl
    _ = ∫ x in standardFrequencyPairCell,
        euclideanFrequencyPairCharacter n x • addPeriodization (G := StandardFrequencyPairLattice) K x :=
      integral_representative (fun x ↦ euclideanFrequencyPairCharacter n x •
        addPeriodization (G := StandardFrequencyPairLattice) K x)
    _ = ∫ x, euclideanFrequencyPairCharacter n x • K x :=
      setIntegral_character_smul_addPeriodization_eq standardFrequencyPairCell_isAddFundamentalDomain
        K hK hKi (euclideanFrequencyPairCharacter n)
        (continuous_euclideanFrequencyPairCharacter n).measurable
        (norm_euclideanFrequencyPairCharacter n) (euclideanFrequencyPairCharacter_vadd n)
    _ = _ := by rw [Real.fourier_eq]; rfl

theorem integrable_moment_periodize (K : 𝓢(E6, E)) (m : ℕ) :
    Integrable (fun q : T6 ↦ ‖q‖ ^ m * ‖periodize K q‖) := by
  have hbound := lintegral_moment_periodize_le K K.continuous.measurable m
  have hfinite : (∫⁻ x : E6, ‖x‖ₑ ^ m * ‖K x‖ₑ) < ∞ := by
    simpa only [enorm_mul, enorm_pow, enorm_norm] using
      (hasFiniteIntegral_iff_enorm.mp (K.integrable_pow_mul volume m).hasFiniteIntegral)
  refine ⟨((continuous_norm.pow m).measurable.mul
    (measurable_periodize K K.continuous.measurable).norm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [enorm_mul, enorm_pow, enorm_norm] using hbound.trans_lt hfinite

theorem integral_moment_periodize_le (K : 𝓢(E6, E)) (m : ℕ) :
    (∫ q : T6, ‖q‖ ^ m * ‖periodize K q‖) ≤ ∫ x : E6, ‖x‖ ^ m * ‖K x‖ := by
  have hbound := lintegral_moment_periodize_le K K.continuous.measurable m
  have ht (q : T6) : ‖q‖ₑ ^ m * ‖periodize K q‖ₑ = ENNReal.ofReal (‖q‖ ^ m * ‖periodize K q‖) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _), ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ofReal_norm]
  have hx (x : E6) : ‖x‖ₑ ^ m * ‖K x‖ₑ = ENNReal.ofReal (‖x‖ ^ m * ‖K x‖) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _), ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ofReal_norm]
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun x ↦ by positivity))).mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_moment_periodize K m)
    (Filter.Eventually.of_forall (fun q ↦ by positivity)),
    ofReal_integral_eq_lintegral_ofReal (K.integrable_pow_mul volume m)
    (Filter.Eventually.of_forall (fun x ↦ by positivity))]
  simpa only [ht, hx] using hbound

theorem integrable_periodize (K : 𝓢(E6, E)) : Integrable (periodize K) := by
  apply (integrable_norm_iff (measurable_periodize K K.continuous.measurable).aestronglyMeasurable).mp
  simpa only [pow_zero, one_mul] using integrable_moment_periodize K 0

theorem integral_twoInputMoment_periodize_le (K : 𝓢(E6, E)) :
    (∫ q : T6, (‖firstTorusDisplacement q‖ + ‖secondTorusDisplacement q‖) * ‖periodize K q‖) ≤
      2 * ∫ x : E6, ‖x‖ * ‖K x‖ := by
  have hpoint (q : T6) : (‖firstTorusDisplacement q‖ + ‖secondTorusDisplacement q‖) *
      ‖periodize K q‖ ≤ 2 * (‖q‖ * ‖periodize K q‖) := by
    have h := mul_le_mul_of_nonneg_right
      (add_le_add (norm_firstTorusDisplacement_le q) (norm_secondTorusDisplacement_le q))
      (norm_nonneg (periodize K q))
    nlinarith
  have hi : Integrable (fun q : T6 ↦ 2 * (‖q‖ * ‖periodize K q‖)) := by
    simpa only [pow_one] using (integrable_moment_periodize K 1).const_mul 2
  have hm : AEStronglyMeasurable (fun q : T6 ↦
      (‖firstTorusDisplacement q‖ + ‖secondTorusDisplacement q‖) * ‖periodize K q‖) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul _ (measurable_periodize K K.continuous.measurable).norm
    exact (continuous_firstTorusDisplacement.norm.add continuous_secondTorusDisplacement.norm).measurable
  have hi' := hi.mono' hm (Filter.Eventually.of_forall (fun q ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (norm_nonneg _))] using hpoint q))
  calc
    _ ≤ ∫ q : T6, 2 * (‖q‖ * ‖periodize K q‖) := integral_mono hi' hi hpoint
    _ = 2 * ∫ q : T6, ‖q‖ * ‖periodize K q‖ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [pow_one] using integral_moment_periodize_le K 1)
      (by norm_num)

end Mettapedia.FluidDynamics.NavierStokes.FrequencyPairPeriodization
