import Mettapedia.Analysis.SignedRadialStretchEvolution

/-!
# Coherent radial stretching controlled by plane and normal defects

The vorticity-normal pairings and the failure of the separation to be a
strain eigenvector are retained explicitly. Common rotation cancels.
The estimates concern only the coherent kernel/common-deformation channel;
unequal-gradient, velocity-remainder and viscous channels are not omitted
from the full rate and are not estimated by this file.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.RadialPancakeCoherence

open RadialPower SignedRadialStretch EuclideanCrossProduct
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "Op" => R3 →L[ℝ] R3

def normalMoment (p : ℕ) (a b h : R3) : ℝ :=
  ‖a‖ ^ p * |⟪h, a⟫| + ‖b‖ ^ p * |⟪h, b⟫|

theorem normalMoment_nonneg (p : ℕ) (a b h : R3) : 0 ≤ normalMoment p a b h := by
  unfold normalMoment
  positivity

theorem abs_amplitudePair_le (p : ℕ) (a b h : R3) :
    |amplitudePair p a b h| ≤ normalMoment p a b h := by
  simpa only [amplitudePair, radialPower, inner_sub_right, real_inner_smul_right,
    abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), normalMoment] using
    abs_sub (‖a‖ ^ p * ⟪h, a⟫) (‖b‖ ^ p * ⟪h, b⟫)

theorem normalMoment_le_of_tilt (p : ℕ) (a b h : R3) (δ : ℝ)
    (ha : |⟪h, a⟫| ≤ δ * ‖h‖ * ‖a‖) (hb : |⟪h, b⟫| ≤ δ * ‖h‖ * ‖b‖) :
    normalMoment p a b h ≤ δ * ‖h‖ * (‖a‖ ^ (p + 1) + ‖b‖ ^ (p + 1)) := by
  have h := add_le_add (mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ ‖a‖ ^ p))
    (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ ‖b‖ ^ p))
  simpa only [normalMoment, pow_succ] using h.trans_eq (by ring)

theorem normalMoment_eq_zero_of_orthogonal (p : ℕ) (a b h : R3)
    (ha : ⟪h, a⟫ = 0) (hb : ⟪h, b⟫ = 0) : normalMoment p a b h = 0 := by
  simp [normalMoment, ha, hb]

theorem normalPairRate_eq (A : Op) (a h r ra rh : R3) (σ : ℝ)
    (hA : ∀ v, ⟪A h, v⟫ + ⟪h, A v⟫ = 2 * ⟪σ • h + r, v⟫) :
    ⟪A h + rh, a⟫ + ⟪h, A a + ra⟫ =
      2 * σ * ⟪h, a⟫ + 2 * ⟪r, a⟫ + ⟪rh, a⟫ + ⟪h, ra⟫ := by
  have he := hA a
  simp only [inner_add_left, real_inner_smul_left] at he
  simp only [inner_add_left, inner_add_right]
  linarith only [he]

/-- A compressive normal damps its squared pairing, up to the explicit forcing cost. -/
theorem squareRate_le_of_compressive (σ κ z f : ℝ) (hκ : 0 < κ) (hσ : σ ≤ -κ) :
    2 * z * (2 * σ * z + f) ≤ -2 * κ * z ^ 2 + f ^ 2 / (2 * κ) := by
  have hs := mul_le_mul_of_nonneg_right hσ (sq_nonneg z)
  have hsq := sq_nonneg (2 * κ * z - f)
  have hd : 0 < 2 * κ := by positivity
  apply (mul_le_mul_iff_left₀ hd).mp
  have he : (-2 * κ * z ^ 2 + f ^ 2 / (2 * κ)) * (2 * κ) =
      -4 * κ ^ 2 * z ^ 2 + f ^ 2 := by field_simp; ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 8 * κ)]

/-- A signed endpoint contribution to the radial amplitude pair. -/
def weightedHeight (n : ℕ) (a h : R3) : ℝ := ⟪h, radialPower (2 * (n + 1)) a⟫

def weightedHeightRate (n : ℕ) (a h va vh : R3) : ℝ :=
  ⟪vh, radialPower (2 * (n + 1)) a⟫ + ⟪h, evenRadialRate n a va⟫

theorem hasDerivAt_weightedHeight (n : ℕ) {a h : ℝ → R3} {va vh : R3} {t : ℝ}
    (ha : HasDerivAt a va t) (hh : HasDerivAt h vh t) :
    HasDerivAt (fun τ ↦ weightedHeight n (a τ) (h τ))
      (weightedHeightRate n (a t) (h t) va vh) t := by
  simpa only [weightedHeight, weightedHeightRate, add_comm] using
    hh.inner ℝ (hasDerivAt_radialPower_even n ha)

/-- The extra radial amplitude rate must not be dropped when using normal damping. -/
theorem weightedHeightRate_eq (n : ℕ) (a h va vh : R3) :
    weightedHeightRate n a h va vh =
      ‖a‖ ^ (2 * (n + 1)) * (⟪vh, a⟫ + ⟪h, va⟫) +
      (2 * (n + 1) : ℝ) * ‖a‖ ^ (2 * n) * ⟪a, va⟫ * ⟪h, a⟫ := by
  simp only [weightedHeightRate, radialPower, evenRadialRate, inner_add_right,
    real_inner_smul_right]
  ring

/-- Compression competes with amplitude stretching even in a common affine field. -/
theorem weightedHeightRate_common (n : ℕ) (A : Op) (a h r : R3) (σ α : ℝ)
    (hA : ∀ v, ⟪A h, v⟫ + ⟪h, A v⟫ = 2 * ⟪σ • h + r, v⟫)
    (ha : ⟪a, A a⟫ = α * ‖a‖ ^ 2) :
    weightedHeightRate n a h (A a) (A h) =
      (2 * σ + (2 * (n + 1) : ℝ) * α) * weightedHeight n a h +
      2 * ‖a‖ ^ (2 * (n + 1)) * ⟪r, a⟫ := by
  rw [weightedHeightRate_eq, hA, ha]
  simp only [weightedHeight, radialPower, inner_add_left, real_inner_smul_left,
    real_inner_smul_right, show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
  ring

/-- The hypothesis specifies the symmetric action of the full gradient on the normal. -/
theorem commonAmplitudeRate_eq_normal_defects (n : ℕ) (A : Op) (a b h r : R3) (σ : ℝ)
    (hA : ∀ v, ⟪A h, v⟫ + ⟪h, A v⟫ = 2 * ⟪σ • h + r, v⟫) :
    commonAmplitudeRate n A a b h =
      2 * σ * amplitudePair (2 * (n + 1)) a b h +
      2 * ⟪r, radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b⟫ +
      (2 * (n + 1) : ℝ) *
        (‖a‖ ^ (2 * n) * ⟪a, A a⟫ * ⟪h, a⟫ - ‖b‖ ^ (2 * n) * ⟪b, A b⟫ * ⟪h, b⟫) := by
  unfold commonAmplitudeRate
  rw [hA]
  simp only [amplitudePair, radialStrainExcess, inner_add_left, real_inner_smul_left,
    inner_sub_right, real_inner_smul_right]
  ring

theorem abs_radialStrainHeight_le (n : ℕ) (A : Op) (a h : R3) (L : ℝ)
    (ha : |⟪a, A a⟫| ≤ L * ‖a‖ ^ 2) :
    |‖a‖ ^ (2 * n) * ⟪a, A a⟫ * ⟪h, a⟫| ≤ L * (‖a‖ ^ (2 * (n + 1)) * |⟪h, a⟫|) := by
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖a‖ ^ (2 * n))]
  have hb := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ ‖a‖ ^ (2 * n))) (abs_nonneg ⟪h, a⟫)
  apply hb.trans_eq
  rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
  ring

theorem abs_commonAmplitudeRate_le (n : ℕ) (A : Op) (a b h r : R3) (σ L : ℝ)
    (hA : ∀ v, ⟪A h, v⟫ + ⟪h, A v⟫ = 2 * ⟪σ • h + r, v⟫)
    (ha : |⟪a, A a⟫| ≤ L * ‖a‖ ^ 2) (hb : |⟪b, A b⟫| ≤ L * ‖b‖ ^ 2) :
    |commonAmplitudeRate n A a b h| ≤
      (2 * |σ| + (2 * (n + 1) : ℝ) * L) * normalMoment (2 * (n + 1)) a b h +
      2 * ‖r‖ * ‖radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b‖ := by
  rw [commonAmplitudeRate_eq_normal_defects n A a b h r σ hA]
  have hfirst : |2 * σ * amplitudePair (2 * (n + 1)) a b h| ≤
      2 * |σ| * normalMoment (2 * (n + 1)) a b h := by
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      mul_le_mul_of_nonneg_left (abs_amplitudePair_le (2 * (n + 1)) a b h)
        (by positivity : 0 ≤ 2 * |σ|)
  have hsecond : |2 * ⟪r, radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b⟫| ≤
      2 * ‖r‖ * ‖radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b‖ := by
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc] using
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm r
        (radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b)) (by norm_num : (0 : ℝ) ≤ 2)
  have hthird := (abs_sub (‖a‖ ^ (2 * n) * ⟪a, A a⟫ * ⟪h, a⟫)
    (‖b‖ ^ (2 * n) * ⟪b, A b⟫ * ⟪h, b⟫)).trans
      (add_le_add (abs_radialStrainHeight_le n A a h L ha) (abs_radialStrainHeight_le n A b h L hb))
  have hm := mul_le_mul_of_nonneg_left hthird (by positivity : 0 ≤ (2 * (n + 1) : ℝ))
  have htadd (x y z : ℝ) : |x + y + z| ≤ |x| + |y| + |z| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have hall := htadd (2 * σ * amplitudePair (2 * (n + 1)) a b h)
    (2 * ⟪r, radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b⟫)
    ((2 * (n + 1) : ℝ) *
      (‖a‖ ^ (2 * n) * ⟪a, A a⟫ * ⟪h, a⟫ - ‖b‖ ^ (2 * n) * ⟪b, A b⟫ * ⟪h, b⟫))
  have ht := add_le_add (add_le_add hfirst hsecond) hm
  simp only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 * (n + 1) : ℝ)),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hall ht
  apply hall.trans
  exact ht.trans_eq (by unfold normalMoment; ring)

theorem commonAmplitudeRate_eq_zero_of_plane (n : ℕ) (A : Op) (a b h : R3) (σ : ℝ)
    (hA : ∀ v, ⟪A h, v⟫ + ⟪h, A v⟫ = 2 * ⟪σ • h, v⟫)
    (ha : ⟪h, a⟫ = 0) (hb : ⟪h, b⟫ = 0) : commonAmplitudeRate n A a b h = 0 := by
  rw [commonAmplitudeRate_eq_normal_defects n A a b h 0 σ (by simpa only [add_zero] using hA)]
  simp [amplitudePair, radialPower, inner_sub_right, real_inner_smul_right, ha, hb]

def coherentRate (n : ℕ) (A : Op) (k dk : ℝ) (a b h : R3) : ℝ :=
  dk * tripleProduct a b h * amplitudePair (2 * (n + 1)) a b h +
    k * tripleProduct a b h * commonAmplitudeRate n A a b h

theorem abs_coherentRate_le (n : ℕ) (A : Op) (k dk : ℝ) (a b h r : R3) (σ L : ℝ)
    (hA : ∀ v, ⟪A h, v⟫ + ⟪h, A v⟫ = 2 * ⟪σ • h + r, v⟫)
    (ha : |⟪a, A a⟫| ≤ L * ‖a‖ ^ 2) (hb : |⟪b, A b⟫| ≤ L * ‖b‖ ^ 2) :
    |coherentRate n A k dk a b h| ≤ |tripleProduct a b h| *
      ((|dk| + |k| * (2 * |σ| + (2 * (n + 1) : ℝ) * L)) * normalMoment (2 * (n + 1)) a b h +
        2 * |k| * ‖r‖ * ‖radialPower (2 * (n + 1)) a - radialPower (2 * (n + 1)) b‖) := by
  have he : coherentRate n A k dk a b h = tripleProduct a b h *
      (dk * amplitudePair (2 * (n + 1)) a b h + k * commonAmplitudeRate n A a b h) := by
    unfold coherentRate
    ring
  rw [he, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h := (abs_add_le (dk * amplitudePair (2 * (n + 1)) a b h)
    (k * commonAmplitudeRate n A a b h)).trans (by
      simp only [abs_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (abs_amplitudePair_le (2 * (n + 1)) a b h) (abs_nonneg dk))
        (mul_le_mul_of_nonneg_left (abs_commonAmplitudeRate_le n A a b h r σ L hA ha hb) (abs_nonneg k)))
  exact h.trans_eq (by ring)

theorem coherentRate_eq_zero_of_plane (n : ℕ) (A : Op) (k dk : ℝ) (a b h : R3) (σ : ℝ)
    (hA : ∀ v, ⟪A h, v⟫ + ⟪h, A v⟫ = 2 * ⟪σ • h, v⟫)
    (ha : ⟪h, a⟫ = 0) (hb : ⟪h, b⟫ = 0) : coherentRate n A k dk a b h = 0 := by
  rw [coherentRate, commonAmplitudeRate_eq_zero_of_plane n A a b h σ hA ha hb]
  simp [amplitudePair, radialPower, inner_sub_right, real_inner_smul_right, ha, hb]

end Mettapedia.Analysis.RadialPancakeCoherence
