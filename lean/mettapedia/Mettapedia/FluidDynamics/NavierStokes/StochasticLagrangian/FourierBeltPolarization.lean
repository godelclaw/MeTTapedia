import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierSingleConeStretch
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierBeltKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.NormalizedPressureTrace

/-!
# Polarization of transverse modes in a Fourier belt

The component along the real vector `n × k` is the planar polarization of a
mode. Transversality expresses the remainder through the axial velocity
component. The algebra is complex bilinear, so Fourier phases are retained.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierBeltPolarization

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
  PancakeFrequencyProjectorCommutator FourierVorticitySource FourierPancakePairDepletion
  FourierPairedStretchIdentity FourierSingleConeStretch FourierBeltKernel
  NormalizedPressureTrace

theorem norm_axisCoefficient_sq (n : Fin 3 → ℝ) :
    ‖coefficientVec (axisCoefficient n)‖ ^ 2 = ∑ i : Fin 3, (n i) ^ 2 := by
  rw [norm_coefficientVec_sq]
  simp [coefficientEnergy, axisCoefficient, Complex.normSq_apply, pow_two]

theorem norm_axisCoefficient_eq_one (n : Fin 3 → ℝ)
    (hn : ∑ i : Fin 3, (n i) ^ 2 = 1) : ‖coefficientVec (axisCoefficient n)‖ = 1 := by
  have h := norm_axisCoefficient_sq n
  rw [hn] at h
  nlinarith [norm_nonneg (coefficientVec (axisCoefficient n))]

/-- A real vector perpendicular to the axis and the mode. -/
def axisCross (n : Fin 3 → ℝ) (k : Wavevector) : VelocityCoefficient :=
  coefficientCross (axisCoefficient n) (wavevectorCoefficient k)

@[simp] theorem conj_axisCross (n : Fin 3 → ℝ) (k : Wavevector) (i : Fin 3) :
    conj (axisCross n k i) = axisCross n k i := by
  fin_cases i <;> simp [axisCross, coefficientCross, axisCoefficient, wavevectorCoefficient]

theorem axisCross_dot_self (n : Fin 3 → ℝ) (k : Wavevector) :
    coefficientDot (axisCross n k) (axisCross n k) =
      ((‖coefficientVec (axisCross n k)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_pow, ← complex_inner_self, inner_coefficientVec]
  simp [coefficientHermitian, coefficientDot]

/-- Lagrange's identity for a real axis and an integer frequency. -/
theorem norm_axisCross_sq (n : Fin 3 → ℝ) (k : Wavevector) :
    ‖coefficientVec (axisCross n k)‖ ^ 2 =
      ‖coefficientVec (axisCoefficient n)‖ ^ 2 * ‖frequencyVec k‖ ^ 2 -
        ‖coefficientDot (axisCoefficient n) (wavevectorCoefficient k)‖ ^ 2 := by
  have h := FourierPairedStretchIdentity.cross_coefficientEnergy
    (axisCoefficient n) (wavevectorCoefficient k)
  simp only [axisCoefficient, Complex.conj_ofReal] at h
  simpa only [axisCross, ← norm_coefficientVec_sq, Complex.normSq_eq_norm_sq,
    coefficientDot, axisCoefficient, frequencyVec] using h

theorem axis_mode_dot_norm (n : Fin 3 → ℝ) (k : Wavevector) :
    ‖coefficientDot (axisCoefficient n) (wavevectorCoefficient k)‖ =
      |∑ i : Fin 3, (k i : ℝ) * n i| := by
  have he : coefficientDot (axisCoefficient n) (wavevectorCoefficient k) =
      ((∑ i : Fin 3, (k i : ℝ) * n i : ℝ) : ℂ) := by
    simp [coefficientDot, axisCoefficient, wavevectorCoefficient, mul_comm]
  rw [he, Complex.norm_real, Real.norm_eq_abs]

/-- A mode in a belt of width at most one half has a nondegenerate planar direction. -/
theorem half_norm_le_axisCross {n : Fin 3 → ℝ}
    (hn : ∑ i : Fin 3, (n i) ^ 2 = 1) {k : Wavevector}
    (hk : ‖coefficientDot (axisCoefficient n) (wavevectorCoefficient k)‖ ≤
      ‖frequencyVec k‖ / 2) :
    ‖frequencyVec k‖ / 2 ≤ ‖coefficientVec (axisCross n k)‖ := by
  have he := norm_axisCross_sq n k
  rw [norm_axisCoefficient_eq_one n hn] at he
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hk
  nlinarith [norm_nonneg (frequencyVec k), norm_nonneg (coefficientVec (axisCross n k))]

/-- The algebraic projection identity, before dividing by the squared planar length. -/
theorem cross_projection_identity (n k a : VelocityCoefficient) :
    coefficientDot (coefficientCross n k) (coefficientCross n k) • a =
      coefficientDot a (coefficientCross n k) • coefficientCross n k +
      coefficientDot a n • coefficientCross k (coefficientCross n k) -
      coefficientDot a k • coefficientCross n (coefficientCross n k) := by
  ext i
  fin_cases i <;> simp [coefficientCross, coefficientDot, Fin.sum_univ_three] <;> ring

/-- The planar part of a velocity coefficient. -/
def planarPart (n : Fin 3 → ℝ) (k : Wavevector) (a : VelocityCoefficient) : VelocityCoefficient :=
  (coefficientDot a (axisCross n k) / ((‖coefficientVec (axisCross n k)‖ ^ 2 : ℝ) : ℂ)) •
    axisCross n k

theorem norm_planarPart_le (n : Fin 3 → ℝ) (k : Wavevector) (a : VelocityCoefficient)
    (hP : 0 < ‖coefficientVec (axisCross n k)‖) :
    ‖coefficientVec (planarPart n k a)‖ ≤ ‖coefficientVec a‖ := by
  rw [planarPart, norm_cv_smul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ ((‖coefficientVec a‖ * ‖coefficientVec (axisCross n k)‖) /
        ‖coefficientVec (axisCross n k)‖ ^ 2) * ‖coefficientVec (axisCross n k)‖ := by
      gcongr
      exact norm_coefficientDot_le_product a _
    _ = _ := by field_simp

/-- Transversality leaves only an axial-velocity remainder after planar projection. -/
theorem planar_remainder_eq (n : Fin 3 → ℝ) (k : Wavevector) (a : VelocityCoefficient)
    (hka : modeDot k a = 0) (hP : 0 < ‖coefficientVec (axisCross n k)‖) :
    a - planarPart n k a =
      (coefficientDot a (axisCoefficient n) /
        ((‖coefficientVec (axisCross n k)‖ ^ 2 : ℝ) : ℂ)) •
          coefficientCross (wavevectorCoefficient k) (axisCross n k) := by
  have hak : coefficientDot a (wavevectorCoefficient k) = 0 := by
    rw [coefficientDot_wavevector_right, hka]
  have h := cross_projection_identity (axisCoefficient n) (wavevectorCoefficient k) a
  change coefficientDot (axisCross n k) (axisCross n k) • a = _ at h
  rw [axisCross_dot_self, hak, zero_smul, sub_zero] at h
  have hden : ((‖coefficientVec (axisCross n k)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (sq_pos_of_pos hP).ne'
  ext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hi
  simp only [planarPart, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  dsimp only [axisCross] at hi ⊢
  linear_combination hi

/-- The transverse remainder is bounded by twice the axial velocity component. -/
theorem norm_planar_remainder_le (n : Fin 3 → ℝ) (k : Wavevector) (a : VelocityCoefficient)
    (hka : modeDot k a = 0) (hk : 0 < ‖frequencyVec k‖)
    (hhalf : ‖frequencyVec k‖ / 2 ≤ ‖coefficientVec (axisCross n k)‖) :
    ‖coefficientVec (a - planarPart n k a)‖ ≤
      2 * ‖coefficientDot a (axisCoefficient n)‖ := by
  have hP : 0 < ‖coefficientVec (axisCross n k)‖ := lt_of_lt_of_le (by positivity) hhalf
  rw [planar_remainder_eq n k a hka hP, norm_cv_smul, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (‖coefficientDot a (axisCoefficient n)‖ / ‖coefficientVec (axisCross n k)‖ ^ 2) *
        (‖frequencyVec k‖ * ‖coefficientVec (axisCross n k)‖) := by
      gcongr
      exact norm_coefficientCross_le _ _
    _ = ‖coefficientDot a (axisCoefficient n)‖ *
        (‖frequencyVec k‖ / ‖coefficientVec (axisCross n k)‖) := by field_simp
    _ ≤ ‖coefficientDot a (axisCoefficient n)‖ * 2 := by
      gcongr
      rw [div_le_iff₀ hP]
      linarith
    _ = _ := by ring

/-- The scalar coefficient of the planar direction has the expected inverse-frequency bound. -/
theorem planar_scalar_le (n : Fin 3 → ℝ) (k : Wavevector) (a : VelocityCoefficient)
    (hk : 0 < ‖frequencyVec k‖)
    (hhalf : ‖frequencyVec k‖ / 2 ≤ ‖coefficientVec (axisCross n k)‖) :
    ‖coefficientDot a (axisCross n k) /
      ((‖coefficientVec (axisCross n k)‖ ^ 2 : ℝ) : ℂ)‖ ≤
        2 * ‖coefficientVec a‖ / ‖frequencyVec k‖ := by
  have hP : 0 < ‖coefficientVec (axisCross n k)‖ := lt_of_lt_of_le (by positivity) hhalf
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (‖coefficientVec a‖ * ‖coefficientVec (axisCross n k)‖) /
        ‖coefficientVec (axisCross n k)‖ ^ 2 := by
      gcongr
      exact norm_coefficientDot_le_product _ _
    _ = ‖coefficientVec a‖ / ‖coefficientVec (axisCross n k)‖ := by field_simp
    _ ≤ _ := by
      rw [div_le_div_iff₀ hP hk]
      nlinarith [mul_le_mul_of_nonneg_left hhalf (norm_nonneg (coefficientVec a))]

theorem cross_cross_axis (k l n : VelocityCoefficient) :
    coefficientCross (coefficientCross k l) n =
      coefficientDot k n • l - coefficientDot l n • k := by
  ext i
  fin_cases i <;> simp [coefficientCross, coefficientDot, Fin.sum_univ_three] <;> ring

theorem cross_axisCross (n k l : VelocityCoefficient) :
    coefficientCross (coefficientCross n k) (coefficientCross n l) =
      coefficientDot n (coefficientCross k l) • n := by
  ext i
  fin_cases i <;> simp [coefficientCross, coefficientDot, Fin.sum_univ_three] <;> ring

theorem norm_cross_cross_axis_le (k l n : VelocityCoefficient) (δ : ℝ)
    (hk : ‖coefficientDot k n‖ ≤ δ * ‖coefficientVec k‖)
    (hl : ‖coefficientDot l n‖ ≤ δ * ‖coefficientVec l‖) :
    ‖coefficientVec (coefficientCross (coefficientCross k l) n)‖ ≤
      2 * δ * ‖coefficientVec k‖ * ‖coefficientVec l‖ := by
  rw [cross_cross_axis]
  have he : coefficientVec (coefficientDot k n • l - coefficientDot l n • k) =
      coefficientVec (coefficientDot k n • l) - coefficientVec (coefficientDot l n • k) := rfl
  rw [he]
  calc
    _ ≤ ‖coefficientVec (coefficientDot k n • l)‖ +
        ‖coefficientVec (coefficientDot l n • k)‖ := norm_sub_le _ _
    _ = ‖coefficientDot k n‖ * ‖coefficientVec l‖ +
        ‖coefficientDot l n‖ * ‖coefficientVec k‖ := by rw [norm_cv_smul, norm_cv_smul]
    _ ≤ (δ * ‖coefficientVec k‖) * ‖coefficientVec l‖ +
        (δ * ‖coefficientVec l‖) * ‖coefficientVec k‖ := by gcongr
    _ = _ := by ring

/-- The two exactly planar polarizations combine into the common real axis. -/
theorem doubleCross_planar (k l n : VelocityCoefficient) (c d : ℂ) :
    coefficientCross (coefficientCross k l)
      (coefficientCross (c • coefficientCross n k) (d • coefficientCross n l)) =
        (c * d * coefficientDot n (coefficientCross k l)) •
          coefficientCross (coefficientCross k l) n := by
  have he : coefficientCross (c • coefficientCross n k) (d • coefficientCross n l) =
      (c * d) • coefficientCross (coefficientCross n k) (coefficientCross n l) := by
    ext i
    fin_cases i <;> simp [coefficientCross] <;> ring
  rw [he, cross_axisCross, smul_smul, coefficientCross_smul_right]

/-- The planar-pair bound retains the input cross product and hence the low-output gain. -/
theorem norm_planar_pair_le (n : Fin 3 → ℝ) (hn : ∑ i : Fin 3, (n i) ^ 2 = 1)
    (p r : Wavevector) (a b : VelocityCoefficient) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hp : 0 < ‖frequencyVec p‖) (hr : 0 < ‖frequencyVec r‖)
    (hpHalf : ‖frequencyVec p‖ / 2 ≤ ‖coefficientVec (axisCross n p)‖)
    (hrHalf : ‖frequencyVec r‖ / 2 ≤ ‖coefficientVec (axisCross n r)‖)
    (hpdot : ‖coefficientDot (wavevectorCoefficient p) (axisCoefficient n)‖ ≤
      δ * ‖frequencyVec p‖)
    (hrdot : ‖coefficientDot (wavevectorCoefficient r) (axisCoefficient n)‖ ≤
      δ * ‖frequencyVec r‖) :
    ‖coefficientVec (coefficientCross
      (coefficientCross (wavevectorCoefficient p) (wavevectorCoefficient r))
      (coefficientCross (planarPart n p a) (planarPart n r b)))‖ ≤
        8 * δ * ‖coefficientVec (coefficientCross (wavevectorCoefficient p) (wavevectorCoefficient r))‖ *
          ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
  have hdot : ‖coefficientDot (axisCoefficient n)
      (coefficientCross (wavevectorCoefficient p) (wavevectorCoefficient r))‖ ≤
        ‖coefficientVec (coefficientCross (wavevectorCoefficient p) (wavevectorCoefficient r))‖ := by
    simpa only [norm_axisCoefficient_eq_one n hn, one_mul] using
      norm_coefficientDot_le_product (axisCoefficient n)
        (coefficientCross (wavevectorCoefficient p) (wavevectorCoefficient r))
  unfold planarPart axisCross
  rw [doubleCross_planar, norm_cv_smul, norm_mul, norm_mul]
  calc
    _ ≤ ((2 * ‖coefficientVec a‖ / ‖frequencyVec p‖) *
        (2 * ‖coefficientVec b‖ / ‖frequencyVec r‖) *
          ‖coefficientVec (coefficientCross (wavevectorCoefficient p) (wavevectorCoefficient r))‖) *
            (2 * δ * ‖frequencyVec p‖ * ‖frequencyVec r‖) := by
      gcongr
      · exact planar_scalar_le n p a hp hpHalf
      · exact planar_scalar_le n r b hr hrHalf
      · exact norm_cross_cross_axis_le _ _ _ δ hpdot hrdot
    _ = _ := by field_simp; ring

theorem doubleCross_decompose (k l a b A B : VelocityCoefficient) :
    coefficientCross (coefficientCross k l) (coefficientCross a b) =
      coefficientCross (coefficientCross k l) (coefficientCross A B) +
      coefficientCross (coefficientCross k l) (coefficientCross A (b - B)) +
      coefficientCross (coefficientCross k l) (coefficientCross (a - A) b) := by
  ext i
  fin_cases i <;> simp [coefficientCross] <;> ring

/-- Approximate planar polarization depletes the pair while preserving its output-frequency gain. -/
theorem norm_doubleCross_le_polarized (n : Fin 3 → ℝ)
    (hn : ∑ i : Fin 3, (n i) ^ 2 = 1) (p r : Wavevector) (a b : VelocityCoefficient)
    (δ α β : ℝ) (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hp : 0 < ‖frequencyVec p‖) (hr : 0 < ‖frequencyVec r‖)
    (hpa : modeDot p a = 0) (hrb : modeDot r b = 0)
    (hpdot : ‖coefficientDot (wavevectorCoefficient p) (axisCoefficient n)‖ ≤
      δ * ‖frequencyVec p‖)
    (hrdot : ‖coefficientDot (wavevectorCoefficient r) (axisCoefficient n)‖ ≤
      δ * ‖frequencyVec r‖)
    (_hα : 0 ≤ α) (_hβ : 0 ≤ β)
    (ha : ‖coefficientDot a (axisCoefficient n)‖ ≤ α * ‖coefficientVec a‖)
    (hb : ‖coefficientDot b (axisCoefficient n)‖ ≤ β * ‖coefficientVec b‖) :
    ‖coefficientVec (coefficientCross
      (coefficientCross (wavevectorCoefficient p) (wavevectorCoefficient r))
      (coefficientCross a b))‖ ≤
        (8 * δ + 2 * α + 2 * β) *
          ‖coefficientVec (coefficientCross (wavevectorCoefficient p) (wavevectorCoefficient r))‖ *
            ‖coefficientVec a‖ * ‖coefficientVec b‖ := by
  have hpHalf : ‖frequencyVec p‖ / 2 ≤ ‖coefficientVec (axisCross n p)‖ := by
    apply half_norm_le_axisCross hn
    rw [coefficientDot_comm]
    refine hpdot.trans ?_
    linarith only [mul_le_mul_of_nonneg_right hδhalf hp.le]
  have hrHalf : ‖frequencyVec r‖ / 2 ≤ ‖coefficientVec (axisCross n r)‖ := by
    apply half_norm_le_axisCross hn
    rw [coefficientDot_comm]
    refine hrdot.trans ?_
    linarith only [mul_le_mul_of_nonneg_right hδhalf hr.le]
  have hP : 0 < ‖coefficientVec (axisCross n p)‖ := lt_of_lt_of_le (by positivity) hpHalf
  have hR : 0 < ‖coefficientVec (axisCross n r)‖ := lt_of_lt_of_le (by positivity) hrHalf
  have hA := norm_planarPart_le n p a hP
  have hB := norm_planarPart_le n r b hR
  have harem : ‖coefficientVec (a - planarPart n p a)‖ ≤ 2 * α * ‖coefficientVec a‖ :=
    (norm_planar_remainder_le n p a hpa hp hpHalf).trans
      (by linarith only [ha])
  have hbrem : ‖coefficientVec (b - planarPart n r b)‖ ≤ 2 * β * ‖coefficientVec b‖ :=
    (norm_planar_remainder_le n r b hrb hr hrHalf).trans
      (by linarith only [hb])
  let C := coefficientCross (wavevectorCoefficient p) (wavevectorCoefficient r)
  have hleft : ‖coefficientVec (coefficientCross C
      (coefficientCross (planarPart n p a) (b - planarPart n r b)))‖ ≤
        ‖coefficientVec C‖ * (‖coefficientVec a‖ * (2 * β * ‖coefficientVec b‖)) := by
    refine (norm_coefficientCross_le _ _).trans ?_
    gcongr
    exact (norm_coefficientCross_le _ _).trans (by gcongr)
  have hright : ‖coefficientVec (coefficientCross C
      (coefficientCross (a - planarPart n p a) b))‖ ≤
        ‖coefficientVec C‖ * ((2 * α * ‖coefficientVec a‖) * ‖coefficientVec b‖) := by
    refine (norm_coefficientCross_le _ _).trans ?_
    gcongr
    exact (norm_coefficientCross_le _ _).trans (by gcongr)
  change ‖coefficientVec (coefficientCross C (coefficientCross a b))‖ ≤
    (8 * δ + 2 * α + 2 * β) * ‖coefficientVec C‖ * ‖coefficientVec a‖ * ‖coefficientVec b‖
  rw [doubleCross_decompose _ _ a b (planarPart n p a) (planarPart n r b)]
  calc
    _ ≤ (‖coefficientVec (coefficientCross C
          (coefficientCross (planarPart n p a) (planarPart n r b)))‖ +
        ‖coefficientVec (coefficientCross C
          (coefficientCross (planarPart n p a) (b - planarPart n r b)))‖) +
        ‖coefficientVec (coefficientCross C
          (coefficientCross (a - planarPart n p a) b))‖ := by
      have h1 := norm_cv_add_le
        (coefficientCross C (coefficientCross (planarPart n p a) (planarPart n r b)))
        (coefficientCross C (coefficientCross (planarPart n p a) (b - planarPart n r b)))
      have h2 := norm_cv_add_le
        (coefficientCross C (coefficientCross (planarPart n p a) (planarPart n r b)) +
          coefficientCross C (coefficientCross (planarPart n p a) (b - planarPart n r b)))
        (coefficientCross C (coefficientCross (a - planarPart n p a) b))
      exact h2.trans (add_le_add h1 le_rfl)
    _ ≤ (8 * δ * ‖coefficientVec C‖ * ‖coefficientVec a‖ * ‖coefficientVec b‖ +
        ‖coefficientVec C‖ * (‖coefficientVec a‖ * (2 * β * ‖coefficientVec b‖))) +
        ‖coefficientVec C‖ * ((2 * α * ‖coefficientVec a‖) * ‖coefficientVec b‖) :=
      add_le_add (add_le_add
        (norm_planar_pair_le n hn p r a b δ hδ hp hr hpHalf hrHalf hpdot hrdot) hleft) hright
    _ = _ := by ring

end Mettapedia.FluidDynamics.NavierStokes.FourierBeltPolarization
