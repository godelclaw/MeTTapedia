import Mettapedia.Analysis.PeriodicRadialCorrelationEnergy

/-!
# A uniform bound for the mixed-gradient correlation term

The first variations of both quartic factors have magnitude at most
`4 |a|^3 |v|`. Fourier contraction bounds their signed convolution pairing
by weighted palinstrophy. The pure second-variation terms are not included
in this bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.PeriodicRadialRiesz

open MeasureTheory UnitTorusConvolutionEnergy
open scoped RealInnerProductSpace
variable {d : ℕ}
local notation "Rd" => EuclideanSpace ℝ (Fin d)
local notation "Td" => UnitAddTorus (Fin d)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def quarticTensorRate (a v : Rd) (i j : Fin d) : ℝ :=
  2 * ⟪a, v⟫ * a i * a j + ‖a‖ ^ 2 * v i * a j + ‖a‖ ^ 2 * a i * v j

def quarticAmplitudeRate (a v : Rd) : ℝ := 4 * ‖a‖ ^ 2 * ⟪a, v⟫

theorem hasDerivAt_quarticTensorEntry {a : ℝ → Rd} {v : Rd} {t : ℝ}
    (ha : HasDerivAt a v t) (i j : Fin d) :
    HasDerivAt (fun τ ↦ quarticTensorEntry (a τ) i j) (quarticTensorRate (a t) v i j) t := by
  have hi := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d ↦ ℝ) i).hasFDerivAt.comp_hasDerivAt t ha
  have hj := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d ↦ ℝ) j).hasFDerivAt.comp_hasDerivAt t ha
  apply ((ha.norm_sq.mul hi).mul hj).congr_deriv
  simp only [quarticTensorRate, PiLp.proj_apply, Function.comp_def, Pi.mul_apply]
  ring

theorem hasDerivAt_quarticAmplitude {a : ℝ → Rd} {v : Rd} {t : ℝ}
    (ha : HasDerivAt a v t) :
    HasDerivAt (fun τ ↦ ‖a τ‖ ^ 4) (quarticAmplitudeRate (a t) v) t := by
  have h := ha.norm_sq.fun_pow 2
  simp only [← pow_mul] at h
  apply h.congr_deriv
  simp only [quarticAmplitudeRate, Nat.cast_ofNat]
  ring

theorem abs_quarticAmplitudeRate_le (a v : Rd) :
    |quarticAmplitudeRate a v| ≤ 4 * ‖a‖ ^ 3 * ‖v‖ := by
  rw [quarticAmplitudeRate, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_pow, abs_norm]
  calc
    _ ≤ 4 * ‖a‖ ^ 2 * (‖a‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm a v) (by positivity)
    _ = _ := by ring

theorem abs_quarticTensorRate_le (a v : Rd) (i j : Fin d) :
    |quarticTensorRate a v i j| ≤ 4 * ‖a‖ ^ 3 * ‖v‖ := by
  have ha (k : Fin d) : |a k| ≤ ‖a‖ := PiLp.norm_apply_le a k
  have hv (k : Fin d) : |v k| ≤ ‖v‖ := PiLp.norm_apply_le v k
  have h₁ : |2 * ⟪a, v⟫ * a i * a j| ≤ 2 * ‖a‖ ^ 3 * ‖v‖ := by
    simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ ≤ 2 * (‖a‖ * ‖v‖) * ‖a‖ * ‖a‖ := by
        gcongr
        · exact abs_real_inner_le_norm a v
        · exact ha i
        · exact ha j
      _ = _ := by ring
  have h₂ : |‖a‖ ^ 2 * v i * a j| ≤ ‖a‖ ^ 3 * ‖v‖ := by
    simp only [abs_mul, abs_pow, abs_norm]
    calc
      _ ≤ ‖a‖ ^ 2 * ‖v‖ * ‖a‖ := by gcongr; exacts [hv i, ha j]
      _ = _ := by ring
  have h₃ : |‖a‖ ^ 2 * a i * v j| ≤ ‖a‖ ^ 3 * ‖v‖ := by
    simp only [abs_mul, abs_pow, abs_norm]
    calc
      _ ≤ ‖a‖ ^ 2 * ‖a‖ * ‖v‖ := by gcongr; exacts [ha i, hv j]
      _ = _ := by ring
  unfold quarticTensorRate
  calc
    _ ≤ |2 * ⟪a, v⟫ * a i * a j| + |‖a‖ ^ 2 * v i * a j| + |‖a‖ ^ 2 * a i * v j| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

theorem continuous_quarticTensorRate (a v : Td → Rd) (ha : Continuous a) (hv : Continuous v)
    (i j : Fin d) : Continuous (fun x ↦ quarticTensorRate (a x) (v x) i j) := by
  have hac (k : Fin d) := (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) k).comp ha
  have hvc (k : Fin d) := (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) k).comp hv
  exact ((((ha.inner hv).const_mul 2).mul (hac i)).mul (hac j)).add
    (((ha.norm.pow 2).mul (hvc i)).mul (hac j)) |>.add
      (((ha.norm.pow 2).mul (hac i)).mul (hvc j))

theorem continuous_quarticAmplitudeRate (a v : Td → Rd) (ha : Continuous a) (hv : Continuous v) :
    Continuous (fun x ↦ quarticAmplitudeRate (a x) (v x)) :=
  ((ha.norm.pow 2).const_mul 4).mul (ha.inner hv)

def mixedGradientEntry (N : ℕ) (a v : Td → Rd) (i j : Fin d) : ℝ :=
  ∫ x : Td, quarticTensorRate (a x) (v x) i j *
    realConvolution (fun h ↦ (entry N i j h).re) (fun y ↦ quarticAmplitudeRate (a y) (v y)) x

theorem abs_mixedGradientEntry_le (N : ℕ) (a v : Td → Rd)
    (ha : Continuous a) (hv : Continuous v) (i j : Fin d) :
    |mixedGradientEntry N a v i j| ≤ 16 * ∫ x : Td, ‖a x‖ ^ 6 * ‖v x‖ ^ 2 := by
  have ht := continuous_quarticTensorRate a v ha hv i j
  have hr := continuous_quarticAmplitudeRate a v ha hv
  have hi (f : Td → ℝ) (hf : Continuous f) : Integrable f :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb (f : Td → ℝ) (hf : Continuous f) (h : ∀ x, |f x| ≤ 4 * ‖a x‖ ^ 3 * ‖v x‖) :
      (∫ x : Td, f x ^ 2) ≤ 16 * ∫ x : Td, ‖a x‖ ^ 6 * ‖v x‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono (hi _ (hf.pow 2)) (hi _ (((ha.norm.pow 6).mul (hv.norm.pow 2)).const_mul 16))
    intro x
    change f x ^ 2 ≤ 16 * (‖a x‖ ^ 6 * ‖v x‖ ^ 2)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) (h x) 2
    rw [sq_abs] at hsq
    exact hsq.trans_eq (by ring)
  have h₁ := hb _ ht (fun x ↦ abs_quarticTensorRate_le (a x) (v x) i j)
  have h₂ := hb _ hr (fun x ↦ abs_quarticAmplitudeRate_le (a x) (v x))
  have h := abs_integral_mul_realConvolution_le _ _ _
    (Complex.continuous_re.comp (continuous_entry N i j)) hr ht
    (norm_mFourierCoeff_re_entry_le_one N i j)
  change |mixedGradientEntry N a v i j| ≤ _ at h
  linarith

def mixedGradientSum (N : ℕ) (a v : Td → Rd) : ℝ :=
  2 * ∑ i : Fin d, ∑ j : Fin d, mixedGradientEntry N a v i j

theorem abs_mixedGradientSum_le (N : ℕ) (a v : Td → Rd)
    (ha : Continuous a) (hv : Continuous v) :
    |mixedGradientSum N a v| ≤
      32 * (d : ℝ) ^ 2 * ∫ x : Td, ‖a x‖ ^ 6 * ‖v x‖ ^ 2 := by
  have h : |∑ i : Fin d, ∑ j : Fin d, mixedGradientEntry N a v i j| ≤
      ∑ i : Fin d, ∑ j : Fin d, 16 * ∫ x : Td, ‖a x‖ ^ 6 * ‖v x‖ ^ 2 := by
    apply ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ ↦ Finset.abs_sum_le_sum_abs _ _))).trans
    exact Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ abs_mixedGradientEntry_le N a v ha hv i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold mixedGradientSum
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [h]

theorem sourceRate_tensor_eq_sum (N : ℕ) (q : Td) (a v : Rd) :
    OcticKernelCorrelation.sourceRate (tensor N q) a v =
      ∑ i : Fin d, ∑ j : Fin d, quarticTensorRate a v i j * (entry N i j q).re := by
  simp only [OcticKernelCorrelation.sourceRate, bilinear_tensor_eq_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold quarticTensorRate
  ring

theorem mixedGradientSum_eq_pairIntegral (N : ℕ) (a v : Td → Rd)
    (ha : Continuous a) (hv : Continuous v) :
    mixedGradientSum N a v = ∫ x : Td, ∫ y : Td,
      OcticKernelCorrelation.mixedCurvature (tensor N (x - y)) (a x) (a y) (v x) (v y) := by
  have hi (f : Td → ℝ) (hf : Continuous f) : Integrable f :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr := continuous_quarticAmplitudeRate a v ha hv
  have ht (i j : Fin d) := continuous_quarticTensorRate a v ha hv i j
  have hentry (i j : Fin d) : Continuous (fun x : Td ↦ quarticTensorRate (a x) (v x) i j *
      realConvolution (fun h ↦ (entry N i j h).re) (fun y ↦ quarticAmplitudeRate (a y) (v y)) x) :=
    (ht i j).mul (continuous_realConvolution _ _ (Complex.continuous_re.comp (continuous_entry N i j)) hr)
  unfold mixedGradientSum mixedGradientEntry
  simp_rw [← integral_finsetSum _ (fun j _ ↦ hi _ (hentry _ j))]
  rw [← integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi _ (hentry i j))),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hre (i j : Fin d) :
      realConvolution (fun h ↦ (entry N i j h).re) (fun y ↦ quarticAmplitudeRate (a y) (v y)) x =
        ∫ y : Td, (entry N i j (x - y)).re * quarticAmplitudeRate (a y) (v y) := by
    unfold realConvolution
    rw [← integral_sub_left_eq_self (fun h : Td ↦
      (entry N i j h).re * quarticAmplitudeRate (a (x - h)) (v (x - h))) volume x]
    simp only [sub_sub_cancel]
  simp_rw [hre, ← integral_const_mul]
  have hterm (i j : Fin d) : Integrable (fun y : Td ↦ quarticTensorRate (a x) (v x) i j *
      ((entry N i j (x - y)).re * quarticAmplitudeRate (a y) (v y))) :=
    hi _ (continuous_const.mul (((Complex.continuous_re.comp (continuous_entry N i j)).comp
      (continuous_const.sub continuous_id)).mul hr))
  simp_rw [← integral_finsetSum _ (fun j _ ↦ hterm _ j)]
  rw [← integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hterm i j)),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [OcticKernelCorrelation.mixedCurvature, sourceRate_tensor_eq_sum,
    Finset.mul_sum, Finset.sum_mul, quarticAmplitudeRate, OcticKernelCorrelation.amplitudeRate,
    mul_assoc]

end Mettapedia.Analysis.PeriodicRadialRiesz
