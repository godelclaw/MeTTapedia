import Mathlib.Tactic

/-!
# A global initial bound for a gradient-corrected stretching rate

For the periodic datum
`u = a (-sin x cos z - 2 sin y, 2 sin x, cos x sin z)` and the
original-data regularizer `δ = 16a²`, the lab's corrected rate is
`qκ = (2 ω·∇u ω + 2κν |∇ω|²) / (|ω|² + δ)`.

This file certifies its scalar whole-domain maximum, with the three inputs
representing coordinate cosines. The identification with the actual field,
its unforced NS initial tangent and the positive-time passage are analytic
in the companion lab. In particular, this is not a PDE comparison theorem.
-/

set_option autoImplicit false
noncomputable section

namespace MettapediaNS.SignedReactionRenewal

def denominator (x y z : ℝ) : ℝ :=
  (1 - x ^ 2) * (1 - z ^ 2) + (x + y) ^ 2 + 4

def gradientShape (x y z : ℝ) : ℝ :=
  2 + z ^ 2 - y ^ 2 - 2 * x ^ 2 * z ^ 2

def maximumGap (x y z : ℝ) : ℝ :=
  denominator x y z - 2 * x * z * (x + y) ^ 2

def correctedRate (ν κ a x y z : ℝ) : ℝ :=
  (2 * a * x * z * (x + y) ^ 2 + 2 * κ * ν * gradientShape x y z) /
    denominator x y z

theorem denominator_pos (x y z : ℝ) (hx : x ^ 2 ≤ 1) (hz : z ^ 2 ≤ 1) :
    0 < denominator x y z := by
  have hp := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hz)
  unfold denominator
  nlinarith [sq_nonneg (x + y)]

theorem gradientShape_nonneg (x y z : ℝ)
    (hx : x ^ 2 ≤ 1) (hy : y ^ 2 ≤ 1) (hz : z ^ 2 ≤ 1) :
    0 ≤ gradientShape x y z := by
  have h₁ := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hz)
  have h₂ := mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg z)
  unfold gradientShape
  nlinarith

/-- Two polynomial certificates cover the entire cube, including its
boundary and all points attaining the maximum. -/
theorem gradientShape_le_maximumGap (x y z : ℝ)
    (hx : x ^ 2 ≤ 1) (hy : y ^ 2 ≤ 1) (hz : z ^ 2 ≤ 1) :
    gradientShape x y z ≤ maximumGap x y z := by
  have hxz : 0 ≤ 1 - x * z := by nlinarith [sq_nonneg (x - z)]
  have ht := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hz)
  by_cases hw : (x + y) ^ 2 ≤ 1
  · have h₁ := mul_nonneg hxz (sq_nonneg (x + y))
    have h₂ := mul_nonneg (sq_nonneg x) (sq_nonneg z)
    have hid : maximumGap x y z - gradientShape x y z =
        (1 - x ^ 2) * (1 - z ^ 2) + (1 - (x + y) ^ 2) +
        (1 - z ^ 2) + y ^ 2 + 2 * x ^ 2 * z ^ 2 +
        2 * (1 - x * z) * (x + y) ^ 2 := by
      unfold maximumGap denominator gradientShape
      ring
    nlinarith [sq_nonneg y]
  · have h₁ := mul_nonneg hxz (sub_nonneg.mpr (le_of_not_ge hw))
    have hid : maximumGap x y z - gradientShape x y z =
        3 * ((1 - x ^ 2) * (1 - z ^ 2)) + (x - y) ^ 2 +
        (x - z) ^ 2 + (2 - x ^ 2 - y ^ 2) +
        2 * (1 - x * z) * ((x + y) ^ 2 - 1) := by
      unfold maximumGap denominator gradientShape
      ring
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - z)]

theorem correctedRate_le_amplitude (ν κ a x y z : ℝ)
    (ha : 0 ≤ a) (hκ : 2 * κ * ν ≤ a)
    (hx : x ^ 2 ≤ 1) (hy : y ^ 2 ≤ 1) (hz : z ^ 2 ≤ 1) :
    correctedRate ν κ a x y z ≤ a := by
  have hj := gradientShape_nonneg x y z hx hy hz
  have hg := gradientShape_le_maximumGap x y z hx hy hz
  have h₁ := mul_nonneg (sub_nonneg.mpr hκ) hj
  have h₂ := mul_nonneg ha (sub_nonneg.mpr hg)
  unfold correctedRate
  apply (div_le_iff₀ (denominator_pos x y z hx hz)).mpr
  unfold maximumGap at h₂
  nlinarith

theorem correctedRate_at_origin (ν κ a : ℝ) :
    correctedRate ν κ a 1 1 1 = a := by
  unfold correctedRate denominator gradientShape
  ring

/-- For every fixed nonnegative correction coefficient there is an
amplitude whose certified initial maximum has the positive rate computed
by the unforced PDE in the lab. The rate's PDE identification is separate. -/
theorem parameters_with_positive_initial_rate (ν κ : ℝ) (hν : 0 < ν) (hκ : 0 ≤ κ) :
    ∃ a : ℝ, 0 < a ∧ 2 * κ * ν ≤ a ∧ 0 < a * (a - 3 * ν) ∧
      correctedRate ν κ a 1 1 1 = a ∧
      ∀ x y z : ℝ, x ^ 2 ≤ 1 → y ^ 2 ≤ 1 → z ^ 2 ≤ 1 →
        correctedRate ν κ a x y z ≤ a := by
  let a := (2 * κ + 4) * ν
  have hκν := mul_nonneg hκ hν.le
  have ha : 0 < a := by dsimp [a]; nlinarith
  have hbound : 2 * κ * ν ≤ a := by dsimp [a]; nlinarith
  have hgap : 0 < a - 3 * ν := by dsimp [a]; nlinarith
  exact ⟨a, ha, hbound, mul_pos ha hgap, correctedRate_at_origin ν κ a,
    fun x y z hx hy hz ↦ correctedRate_le_amplitude ν κ a x y z ha.le hbound hx hy hz⟩

end MettapediaNS.SignedReactionRenewal
