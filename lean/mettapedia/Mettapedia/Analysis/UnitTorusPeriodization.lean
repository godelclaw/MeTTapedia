import Mettapedia.Analysis.UnitTorusLattice
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Weighted periodization on arbitrary finite-dimensional unit tori

The actual lattice orbit sum transfers Euclidean Fourier coefficients and
does not increase any nonnegative integer spatial moment. Wrapped torus
distance is bounded by Euclidean distance on every lattice translate.
-/

set_option autoImplicit false
noncomputable section
namespace Mettapedia.Analysis.UnitTorusPeriodization
open MeasureTheory Set UnitTorusLattice FundamentalDomainPeriodization
open scoped ENNReal FourierTransform SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "Rd" => EuclideanSpace ℝ ι
local notation "Td" => UnitAddTorus ι

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusProjection (x : Rd) : Td := fun i ↦ (x i : UnitAddCircle)

omit [Fintype ι] [DecidableEq ι] in
@[fun_prop] theorem continuous_torusProjection : Continuous (torusProjection (ι := ι)) := by
  unfold torusProjection
  fun_prop

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem torusProjection_representative (q : Td) :
    torusProjection (representative q) = q := by
  ext i
  exact AddCircle.coe_equivIoc

theorem torusProjection_vadd (g : Lattice (ι := ι)) (x : Rd) :
    torusProjection (g +ᵥ x) = torusProjection x := by
  obtain ⟨z, hz⟩ := exists_integerCoordinates g
  ext i
  change (((g : Rd) i + x i : ℝ) : UnitAddCircle) = (x i : UnitAddCircle)
  rw [hz, AddCircle.coe_add]
  have hi : ((z i : ℝ) : UnitAddCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨z i, by simp⟩
  exact (congrArg (fun q : UnitAddCircle ↦ q + (x i : UnitAddCircle)) hi).trans (zero_add _)

omit [DecidableEq ι] in
theorem norm_torusProjection_le (x : Rd) : ‖torusProjection x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  exact (QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ))).trans
    (PiLp.norm_apply_le x i)

omit [DecidableEq ι] in
theorem integral_representative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Rd → F) :
    (∫ q : Td, f (representative q)) =
      ∫ x in cell, f x := by
  calc
    _ = ∫ x : ι → ℝ in rawCellIoc,
        f (representative (fun i ↦ (x i : UnitAddCircle))) := by
      simpa [rawCellIoc] using UnitAddTorus.integral_preimage
        (fun q : Td ↦ f (representative q)) (fun _ ↦ (0 : ℝ))
    _ = ∫ x : ι → ℝ in rawCellIoc, f (WithLp.toLp 2 x) := by
      apply setIntegral_congr_fun
        (show MeasurableSet rawCellIoc from MeasurableSet.univ_pi' (fun _ ↦ measurableSet_Ioc))
      intro x hx
      dsimp only
      rw [representative_coe x hx]
    _ = ∫ x : ι → ℝ in rawCellIco, f (WithLp.toLp 2 x) :=
      setIntegral_congr_set rawCellIco_ae_eq_Ioc.symm
    _ = _ := by
      have h := (PiLp.volume_preserving_toLp (ι)).setIntegral_preimage_emb
        (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding f cell
      rwa [preimage_cell_toLp] at h

omit [DecidableEq ι] in
theorem lintegral_representative (f : Rd → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q : Td, f (representative q)) =
      ∫⁻ x in cell, f x := by
  calc
    _ = ∫⁻ x : ι → ℝ in rawCellIoc,
        f (representative (fun i ↦ (x i : UnitAddCircle))) := by
      simpa [rawCellIoc] using UnitAddTorus.lintegral_preimage
        (fun q : Td ↦ f (representative q)) (fun _ ↦ (0 : ℝ))
    _ = ∫⁻ x : ι → ℝ in rawCellIoc, f (WithLp.toLp 2 x) := by
      apply setLIntegral_congr_fun
        (show MeasurableSet rawCellIoc from MeasurableSet.univ_pi' (fun _ ↦ measurableSet_Ioc))
      intro x hx
      dsimp only
      rw [representative_coe x hx]
    _ = ∫⁻ x : ι → ℝ in rawCellIco, f (WithLp.toLp 2 x) :=
      setLIntegral_congr rawCellIco_ae_eq_Ioc.symm
    _ = _ := by
      have h := (PiLp.volume_preserving_toLp (ι)).setLIntegral_comp_preimage
        (ZSpan.fundamentalDomain_measurableSet standardBasis) hf
      change (∫⁻ x in (WithLp.toLp 2 : (ι → ℝ) → Rd) ⁻¹' cell,
        f (WithLp.toLp 2 x)) = ∫⁻ x in cell, f x at h
      rwa [preimage_cell_toLp] at h

variable {E : Type*} [NormedAddCommGroup E]

def periodize (K : Rd → E) (q : Td) : E :=
  addPeriodization (G := Lattice (ι := ι)) K (representative q)

variable [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

omit [DecidableEq ι] in
theorem measurable_periodize (K : Rd → E) (hK : Measurable K) : Measurable (periodize K) :=
  (measurable_addPeriodization K hK).comp measurable_representative

theorem lintegral_moment_periodize_le (K : Rd → E) (hK : Measurable K) (m : ℕ) :
    (∫⁻ q : Td, ‖q‖ₑ ^ m * ‖periodize K q‖ₑ) ≤ ∫⁻ x : Rd, ‖x‖ₑ ^ m * ‖K x‖ₑ := by
  let w : Rd → ℝ≥0∞ := fun x ↦ ‖torusProjection x‖ₑ ^ m
  have hw : Measurable w := (continuous_torusProjection (ι := ι)).measurable.enorm.pow_const m
  calc
    _ = ∫⁻ x in cell, w x * ‖addPeriodization (G := Lattice (ι := ι)) K x‖ₑ := by
      have h := lintegral_representative
        (fun x ↦ w x * ‖addPeriodization (G := Lattice (ι := ι)) K x‖ₑ)
        (hw.mul (measurable_addPeriodization K hK).enorm)
      simpa [w, periodize] using h
    _ ≤ ∫⁻ x, w x * ‖K x‖ₑ :=
      setLIntegral_weight_mul_enorm_addPeriodization_le cell_isAddFundamentalDomain
        K hK w hw (fun g x ↦ by simp [w, torusProjection_vadd])
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      change ‖torusProjection x‖ₑ ^ m * ‖K x‖ₑ ≤ ‖x‖ₑ ^ m * ‖K x‖ₑ
      have hn : ‖torusProjection x‖ₑ ≤ ‖x‖ₑ := by
        simpa only [← ofReal_norm] using (ENNReal.ofReal_le_ofReal (norm_torusProjection_le x))
      exact mul_le_mul_left (pow_le_pow_left' hn m) _

/-- Periodization preserves integrability; no Schwartz regularity is needed. -/
theorem integrable_periodize_of_integrable (K : Rd → E) (hK : Measurable K)
    (hKi : Integrable K) : Integrable (periodize K) := by
  refine ⟨(measurable_periodize K hK).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hbound := lintegral_moment_periodize_le K hK 0
  simp only [pow_zero, one_mul] at hbound
  exact hbound.trans_lt (hasFiniteIntegral_iff_enorm.mp hKi.hasFiniteIntegral)

variable [NormedSpace ℂ E]

/-- A continuous periodic test can be paired before or after periodization.
This is the same weighted unfolding used for Fourier coefficients. -/
theorem integral_smul_periodize (K : Rd → E) (hK : Measurable K) (hKi : Integrable K)
    (f : C(Td, ℂ)) :
    (∫ q : Td, f q • periodize K q) = ∫ x : Rd, f (torusProjection x) • K x := by
  have hm : Measurable (fun x : Rd ↦ f (torusProjection x)) :=
    (f.continuous.comp continuous_torusProjection).measurable
  calc
    _ = ∫ x in cell, f (torusProjection x) •
        addPeriodization (G := Lattice (ι := ι)) K x := by
      simpa only [torusProjection_representative, periodize] using
        integral_representative (fun x : Rd ↦ f (torusProjection x) •
          addPeriodization (G := Lattice (ι := ι)) K x)
    _ = _ := setIntegral_smul_addPeriodization_eq cell_isAddFundamentalDomain K hK
      (fun x ↦ f (torusProjection x)) hm (fun g x ↦ by rw [torusProjection_vadd])
      (hKi.bdd_smul ‖f‖ hm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm _))

theorem mFourierCoeff_periodize (K : Rd → E) (hK : Measurable K) (hKi : Integrable K)
    (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (periodize K) n = (𝓕 K) (frequency n) := by
  have hchar (x : Rd) : UnitAddTorus.mFourier (-n) (torusProjection x) =
      character n x :=
    mFourier_neg_coe_eq_character n (WithLp.ofLp x)
  calc
    _ = ∫ q : Td, character n (representative q) •
        addPeriodization (G := Lattice (ι := ι)) K (representative q) := by
      apply integral_congr_ae
      filter_upwards with q
      rw [← hchar, torusProjection_representative]
      rfl
    _ = ∫ x in cell,
        character n x • addPeriodization (G := Lattice (ι := ι)) K x :=
      integral_representative (fun x ↦ character n x •
        addPeriodization (G := Lattice (ι := ι)) K x)
    _ = ∫ x, character n x • K x :=
      setIntegral_character_smul_addPeriodization_eq cell_isAddFundamentalDomain
        K hK hKi (character n)
        (continuous_character n).measurable
        (norm_character n) (character_vadd n)
    _ = _ := by rw [Real.fourier_eq]; rfl

theorem integrable_moment_periodize (K : 𝓢(Rd, E)) (m : ℕ) :
    Integrable (fun q : Td ↦ ‖q‖ ^ m * ‖periodize K q‖) := by
  have hbound := lintegral_moment_periodize_le K K.continuous.measurable m
  have hfinite : (∫⁻ x : Rd, ‖x‖ₑ ^ m * ‖K x‖ₑ) < ∞ := by
    simpa only [enorm_mul, enorm_pow, enorm_norm] using
      (hasFiniteIntegral_iff_enorm.mp (K.integrable_pow_mul volume m).hasFiniteIntegral)
  refine ⟨((continuous_norm.pow m).measurable.mul
    (measurable_periodize K K.continuous.measurable).norm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa only [enorm_mul, enorm_pow, enorm_norm] using hbound.trans_lt hfinite

theorem integral_moment_periodize_le (K : 𝓢(Rd, E)) (m : ℕ) :
    (∫ q : Td, ‖q‖ ^ m * ‖periodize K q‖) ≤ ∫ x : Rd, ‖x‖ ^ m * ‖K x‖ := by
  have hbound := lintegral_moment_periodize_le K K.continuous.measurable m
  have ht (q : Td) : ‖q‖ₑ ^ m * ‖periodize K q‖ₑ = ENNReal.ofReal (‖q‖ ^ m * ‖periodize K q‖) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _), ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ofReal_norm]
  have hx (x : Rd) : ‖x‖ₑ ^ m * ‖K x‖ₑ = ENNReal.ofReal (‖x‖ ^ m * ‖K x‖) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _), ENNReal.ofReal_pow (norm_nonneg _)]
    simp only [ofReal_norm]
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun x ↦ by positivity))).mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_moment_periodize K m)
    (Filter.Eventually.of_forall (fun q ↦ by positivity)),
    ofReal_integral_eq_lintegral_ofReal (K.integrable_pow_mul volume m)
    (Filter.Eventually.of_forall (fun x ↦ by positivity))]
  simpa only [ht, hx] using hbound

theorem integrable_periodize (K : 𝓢(Rd, E)) : Integrable (periodize K) :=
  integrable_periodize_of_integrable K K.continuous.measurable K.integrable


end Mettapedia.Analysis.UnitTorusPeriodization
