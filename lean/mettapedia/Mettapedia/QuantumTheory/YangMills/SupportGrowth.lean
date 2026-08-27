import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-!
# Yang-Mills Support-Growth Recurrence Dichotomy

The manuscript's glue lemma asserts both that the RG remainder is "supported
in a fixed `O(1)`-block collar" and that after `J` steps it lives "in an
`O(J)` collar ... still `O(1)` in physical units".  Those correspond to two
*different* recurrences for the support radius `r j` (in blocks at scale `j`):

* **coarsen-then-thicken** (`good`): each step first coarsens by the block
  factor `b` and then thickens by an `O(1)` collar `A`, giving
  `r (j+1) ≤ r j / b + A`.  This recurrence has the uniform envelope
  `r J ≤ r 0 / b^J + A * b / (b - 1)` — bounded in `J`.
* **thicken-only** (`bad`): each step only thickens, `r (j+1) ≤ r j + A`,
  giving `r J ≤ r 0 + A * J` — and that linear envelope is *achieved* (with
  equality) by an explicit sequence, so it grows past every bound.

The dichotomy theorem records the binary checkpoint: under the good
recurrence the support stays within a fixed collar uniformly in the number of
RG steps; under the bad recurrence the tight envelope diverges.  Which
recurrence the glue construction actually satisfies is a property of the RG
map that is **not** proven here; this module only pins the arithmetic
consequences of each reading.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- **Good (coarsen-then-thicken) recurrence: uniform envelope.**  If
`r (j+1) ≤ r j / b + A` with block factor `b > 1` and collar `A ≥ 0`, then
`r J ≤ r 0 / b^J + A * b / (b - 1)` for every `J`.  The additive term is
independent of `J`: the support collar stays `O(1)`. -/
theorem good_support_recurrence_uniform_bound
    {r : ℕ → ℝ} {b A : ℝ} (hb : 1 < b) (hA : 0 ≤ A)
    (hrec : ∀ j, r (j + 1) ≤ r j / b + A) :
    ∀ J, r J ≤ r 0 / b ^ J + A * b / (b - 1) := by
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  have hb1 : (0 : ℝ) < b - 1 := sub_pos.mpr hb
  intro J
  induction J with
  | zero =>
      have hcollar : 0 ≤ A * b / (b - 1) := by positivity
      simp only [pow_zero, div_one]
      linarith
  | succ J ih =>
      have hinv : (0 : ℝ) ≤ b⁻¹ := inv_nonneg.mpr hb0.le
      have hmul := mul_le_mul_of_nonneg_right ih hinv
      have hstep := hrec J
      have halg :
          (r 0 / b ^ J + A * b / (b - 1)) / b + A
            = r 0 / b ^ (J + 1) + A * b / (b - 1) := by
        field_simp
        ring
      calc r (J + 1) ≤ r J / b + A := hstep
        _ ≤ (r 0 / b ^ J + A * b / (b - 1)) / b + A := by
            simp only [div_eq_mul_inv]
            simp only [div_eq_mul_inv] at hmul
            linarith
        _ = r 0 / b ^ (J + 1) + A * b / (b - 1) := halg

/-- The good envelope at the manuscript's block factor `b = 2`:
`r J ≤ r 0 / 2^J + 2 A`. -/
theorem good_support_recurrence_uniform_bound_two
    {r : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hrec : ∀ j, r (j + 1) ≤ r j / 2 + A) :
    ∀ J, r J ≤ r 0 / 2 ^ J + 2 * A := by
  intro J
  have h := good_support_recurrence_uniform_bound (b := 2)
    (by norm_num) hA hrec J
  have h2 : (A : ℝ) * 2 / (2 - 1) = 2 * A := by ring
  linarith [h, h2.le]

/-- **Bad (thicken-only) recurrence: linear envelope.**  If
`r (j+1) ≤ r j + A`, then only `r J ≤ r 0 + A * J` follows: the collar
budget grows with the number of RG steps. -/
theorem bad_support_recurrence_linear_bound
    {r : ℕ → ℝ} {A : ℝ}
    (hrec : ∀ j, r (j + 1) ≤ r j + A) :
    ∀ J : ℕ, r J ≤ r 0 + A * J := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
      calc r (J + 1) ≤ r J + A := hrec J
        _ ≤ r 0 + A * J + A := by linarith
        _ = r 0 + A * ((J : ℕ) + 1 : ℕ) := by push_cast; ring

/-- The tight thicken-only envelope: `j ↦ r0 + A * j`. -/
def badSupportEnvelope (r0 A : ℝ) (j : ℕ) : ℝ :=
  r0 + A * j

/-- The bad envelope satisfies the thicken-only recurrence with equality, so
the linear bound of `bad_support_recurrence_linear_bound` cannot be
improved. -/
theorem badSupportEnvelope_step (r0 A : ℝ) (j : ℕ) :
    badSupportEnvelope r0 A (j + 1) = badSupportEnvelope r0 A j + A := by
  unfold badSupportEnvelope
  push_cast
  ring

/-- For any positive collar, the bad envelope eventually exceeds every
bound. -/
theorem badSupportEnvelope_unbounded
    {r0 A : ℝ} (hA : 0 < A) (M : ℝ) :
    ∃ J : ℕ, M < badSupportEnvelope r0 A J := by
  obtain ⟨J, hJ⟩ := exists_nat_gt ((M - r0) / A)
  refine ⟨J, ?_⟩
  unfold badSupportEnvelope
  have h := (div_lt_iff₀ hA).mp hJ
  linarith

/-- **Support-growth dichotomy (the binary checkpoint).**  With block factor
`b > 1`, positive collar `A`, and nonnegative initial support radius `r0`:

* every sequence satisfying the coarsen-then-thicken recurrence stays below
  the `J`-independent bound `r0 + A * b / (b - 1)`;
* the tight thicken-only envelope starting at `r0` exceeds every bound at
  some finite step.

The two readings of the manuscript's glue-support claim are therefore not
interchangeable: one gives a uniform `O(1)` collar, the other diverges
linearly in the number of RG steps. -/
theorem support_growth_dichotomy
    {b A r0 : ℝ} (hb : 1 < b) (hA : 0 < A) (hr0 : 0 ≤ r0) :
    (∀ r : ℕ → ℝ, r 0 = r0 →
      (∀ j, r (j + 1) ≤ r j / b + A) →
      ∀ J, r J ≤ r0 + A * b / (b - 1)) ∧
    (∀ M : ℝ, ∃ J : ℕ, M < badSupportEnvelope r0 A J) := by
  constructor
  · intro r h0 hrec J
    have h := good_support_recurrence_uniform_bound hb hA.le hrec J
    have hpow : (1 : ℝ) ≤ b ^ J := one_le_pow₀ hb.le
    have hshrink : r 0 / b ^ J ≤ r0 := by
      rw [h0]
      exact div_le_self hr0 hpow
    linarith [hshrink, h]
  · exact badSupportEnvelope_unbounded hA

end YangMills
end QuantumTheory
end Mettapedia
