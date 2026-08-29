import KrennSparseCertificate

/-!
The small algebraic core found in one gauge-fixed non-collapse C6 slot.

This is deliberately an abstract ring lemma: it records the elementary
``minor is a unit, but the balanced equations force it to vanish'' argument
behind the strict eleven-generator certificate.  It is not a claim that the
same eleven equations cover every C6 slot.
-/

namespace Krenn.C6NoncollapseElevenRow

/-- An inverted two-by-two minor kills two cofactors once both rows of the
minor annihilate them.  This is the reusable first stage of the C6
non-collapse argument; the chart audit supplies the four annihilation rows
from balanced amplitudes and the two adjugate P-kills. -/
theorem cofactor_kills
    {R : Type*} [CommRing R]
    {a b c d x y t : R}
    (hax : a * x = 0)
    (hbx : b * x = 0)
    (hcy : c * y = 0)
    (hdy : d * y = 0)
    (hunit : t * (a * d - b * c) = 1) : x = 0 ∧ y = 0 := by
  have hxminor : x * (a * d - b * c) = 0 := by
    calc
      x * (a * d - b * c) = d * (a * x) - c * (b * x) := by ring
      _ = 0 := by rw [hax, hbx]; ring
  have hyminor : y * (a * d - b * c) = 0 := by
    calc
      y * (a * d - b * c) = a * (d * y) - b * (c * y) := by ring
      _ = 0 := by rw [hdy, hcy]; ring
  constructor
  · calc
      x = x * 1 := by ring
      _ = x * (t * (a * d - b * c)) := by rw [hunit]
      _ = t * (x * (a * d - b * c)) := by ring
      _ = 0 := by rw [hxminor]; ring
  · calc
      y = y * 1 := by ring
      _ = y * (t * (a * d - b * c)) := by rw [hunit]
      _ = t * (y * (a * d - b * c)) := by ring
      _ = 0 := by rw [hyminor]; ring

/-- The generic non-collapse minor argument has a finite domain frontier.

When its two cofactors are products, their vanishing splits into the four
ordinary factor-zero cases.  This is the formal algebra behind the finite
chart frontier recorded by the non-collapse audit; it deliberately does not
claim that those factor cases are already contradictory. -/
theorem cofactor_product_factor_cases
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    {a b c d x₀ x₁ y₀ y₁ t : R}
    (hax : a * (x₀ * x₁) = 0)
    (hbx : b * (x₀ * x₁) = 0)
    (hcy : c * (y₀ * y₁) = 0)
    (hdy : d * (y₀ * y₁) = 0)
    (hunit : t * (a * d - b * c) = 1) :
    (x₀ = 0 ∨ x₁ = 0) ∧ (y₀ = 0 ∨ y₁ = 0) := by
  rcases cofactor_kills hax hbx hcy hdy hunit with ⟨hx, hy⟩
  exact ⟨mul_eq_zero.mp hx, mul_eq_zero.mp hy⟩

/-- Eleven equations of the profile signature
`2 × (4,2) + 2 × (4,1,1) + 5 × (3,2,1)`, together with two P-kills and a
unit minor, are inconsistent over any nontrivial commutative ring. -/
theorem contradiction
    {R : Type*} [CommRing R] [Nontrivial R]
    {a b c d x y q r t p s akill bkill e f g h i j k l m : R}
    (hax0 : a * x + p * bkill = 0)
    (hcy0 : s * akill + c * y = 0)
    (hbx0 : b * x + q * bkill = 0)
    (hdy0 : r * akill + d * y = 0)
    (hb0 : b * y * e + b + q * y * f + q * g = 0)
    (hr0 : r * y * h + r + q * y * i = 0)
    (hd0 : r * x * j + r * k + d * x * l + d = 0)
    (hq0 : r * x * m + q * x * l + q = 0)
    (hakill : akill = 0)
    (hbkill : bkill = 0)
    (hunit : t * (a * d - b * c) = 1) : False := by
  have hax : a * x = 0 := by
    calc
      a * x = a * x + p * bkill := by rw [hbkill]; ring
      _ = 0 := hax0
  have hcy : c * y = 0 := by
    calc
      c * y = s * akill + c * y := by rw [hakill]; ring
      _ = 0 := hcy0
  have hbx : b * x = 0 := by
    calc
      b * x = b * x + q * bkill := by rw [hbkill]; ring
      _ = 0 := hbx0
  have hdy : d * y = 0 := by
    calc
      d * y = r * akill + d * y := by rw [hakill]; ring
      _ = 0 := hdy0
  have hxminor : x * (a * d - b * c) = 0 := by
    calc
      x * (a * d - b * c) = d * (a * x) - c * (b * x) := by ring
      _ = 0 := by rw [hax, hbx]; ring
  have hyminor : y * (a * d - b * c) = 0 := by
    calc
      y * (a * d - b * c) = a * (d * y) - b * (c * y) := by ring
      _ = 0 := by rw [hdy, hcy]; ring
  have hx : x = 0 := by
    calc
      x = x * 1 := by ring
      _ = x * (t * (a * d - b * c)) := by rw [hunit]
      _ = t * (x * (a * d - b * c)) := by ring
      _ = 0 := by rw [hxminor]; ring
  have hy : y = 0 := by
    calc
      y = y * 1 := by ring
      _ = y * (t * (a * d - b * c)) := by rw [hunit]
      _ = t * (y * (a * d - b * c)) := by ring
      _ = 0 := by rw [hyminor]; ring
  have hr : r = 0 := by
    calc
      r = r * y * h + r + q * y * i := by rw [hy]; ring
      _ = 0 := hr0
  have hd : d = 0 := by
    calc
      d = r * x * j + r * k + d * x * l + d := by rw [hr, hx]; ring
      _ = 0 := hd0
  have hq : q = 0 := by
    calc
      q = r * x * m + q * x * l + q := by rw [hr, hx]; ring
      _ = 0 := hq0
  have hb : b = 0 := by
    calc
      b = b * y * e + b + q * y * f + q * g := by rw [hy, hq]; ring
      _ = 0 := hb0
  have hminorzero : a * d - b * c = 0 := by rw [hd, hb]; ring
  have hzeroone : (0 : R) = 1 := by
    calc
      (0 : R) = t * (a * d - b * c) := by rw [hminorzero]; ring
      _ = 1 := hunit
  exact zero_ne_one hzeroone

end Krenn.C6NoncollapseElevenRow

#print axioms Krenn.C6NoncollapseElevenRow.contradiction
#print axioms Krenn.C6NoncollapseElevenRow.cofactor_kills
#print axioms Krenn.C6NoncollapseElevenRow.cofactor_product_factor_cases
