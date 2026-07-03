import Mettapedia.QuantumTheory.YangMills.RGBootstrap
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Yang-Mills Extraction Constant: Displayed Sum Audit and Majorant Norm

The manuscript bounds the extraction-projection operator norm (Appendix O,
factor `(d)` of the `C1` budget) by the displayed sum

  `‖P≤dmax‖ ≤ Σ_{d=0}^{dmax} C(n, d) * (r1/r0)^(-d)`,

with `n` the number of indices, and asserts `‖P≤dmax‖ ≤ 2` at `r1/r0 = 1/2`,
`dmax = 16`.  This module machine-checks the three readings of that display
and then develops the repaired route:

* **Literal reading** (`(r1/r0)^(-d) = 2^d` as printed): the sum is
  `≥ 2n + 1 ≥ 3` for every `n ≥ 1`, so it never certifies `≤ 2`.
* **Sign-corrected reading** (`(r1/r0)^(+d) = 2^(-d)`): the full binomial sum
  equals `(3/2)^n`, and even the `d ≤ 16` truncation exceeds `2` for every
  `n ≥ 2`.  The corrected display therefore also fails to certify `≤ 2` as
  soon as there is more than one index.
* **Weightless reading** (no binomial factors): `Σ_{d≤16} 2^(-d) = 2 - 2^(-16)
  < 2` — the only reading under which the asserted `≤ 2` is true.

* **Majorant-norm repair** (the proposed fix: change the norm, not the
  argument): on the weighted-ℓ¹ coefficient norm `‖c‖_r = Σ_i |c_i| r^(Δ i)`,
  monomial truncation to canonical dimension `≤ D` is literally contractive
  (extraction constant `≤ 1`, better than the advertised `2`); the tail gains
  `(r1/r0)^(D+1)` under radius restriction; and the canonical RG rescaling
  `c_i ↦ b^(4 - Δ i) c_i` contracts the tail by `b^(3-D) = irrelevantScale`.

Scope: the coefficient model is finite (finitely many monomials, arbitrary
dimension map `Δ`), so these are exact finite-sum inequalities, not statements
about the actual infinite-dimensional space of lattice gauge observables.
Nothing here derives `C1 = 2224` or touches the continuum Yang-Mills endpoint.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-! ## Part 1: the three readings of the displayed extraction sum -/

/-- The manuscript's displayed extraction-operator sum at `ρ = r1/r0 = 1/2`
and `dmax = 16`, read literally with the printed inverted exponent
`ρ^(-d) = 2^d`, for `n` indices. -/
def literalExtractionOperatorSum (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.range 17, n.choose d * 2 ^ d

/-- The literal displayed sum dominates its two lowest-order terms
`1 + 2n`. -/
theorem literalExtractionOperatorSum_ge (n : ℕ) :
    2 * n + 1 ≤ literalExtractionOperatorSum n := by
  unfold literalExtractionOperatorSum
  have hsub : Finset.range 2 ⊆ Finset.range 17 := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hle :
      ∑ d ∈ Finset.range 2, n.choose d * 2 ^ d
        ≤ ∑ d ∈ Finset.range 17, n.choose d * 2 ^ d :=
    Finset.sum_le_sum_of_subset hsub
  have hval : ∑ d ∈ Finset.range 2, n.choose d * 2 ^ d = 2 * n + 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one,
      Nat.choose_zero_right, Nat.choose_one_right]
    ring
  omega

/-- **Literal reading fails.**  For every positive number of indices, the
literal displayed sum is at least `3`; in particular it never certifies the
asserted bound `≤ 2`. -/
theorem three_le_literalExtractionOperatorSum {n : ℕ} (hn : 1 ≤ n) :
    3 ≤ literalExtractionOperatorSum n := by
  have h := literalExtractionOperatorSum_ge n
  omega

/-- The literal displayed sum is never `≤ 2` for `n ≥ 1`. -/
theorem not_literalExtractionOperatorSum_le_two {n : ℕ} (hn : 1 ≤ n) :
    ¬ literalExtractionOperatorSum n ≤ 2 := by
  have h := three_le_literalExtractionOperatorSum hn
  omega

/-- Even a single index already saturates the failure: at `n = 1` the literal
sum is exactly `3`. -/
theorem literalExtractionOperatorSum_one :
    literalExtractionOperatorSum 1 = 3 := by
  decide

/-- The binomial-free literal growth pin: `Σ_{d=0}^{16} 2^d = 131071`.  Read
with the printed exponent the display grows geometrically even without any
index combinatorics. -/
theorem literalWeightlessExtractionSum_eq :
    ∑ d ∈ Finset.range 17, 2 ^ d = 131071 := by
  norm_num [Finset.sum_range_succ]

/-- **Sign-corrected reading, exact value.**  With the intended exponent
`(r1/r0)^(+d)` at `ρ = 1/2`, the full binomial sum collapses by the binomial
theorem: `Σ_{d=0}^{n} C(n,d) 2^(-d) = (3/2)^n`. -/
theorem signCorrectedExtractionSum_eq (n : ℕ) :
    ∑ d ∈ Finset.range (n + 1), (n.choose d : ℝ) * ((1 : ℝ) / 2) ^ d
      = ((3 : ℝ) / 2) ^ n := by
  calc
    ∑ d ∈ Finset.range (n + 1), (n.choose d : ℝ) * ((1 : ℝ) / 2) ^ d
        = ∑ d ∈ Finset.range (n + 1),
            ((1 : ℝ) / 2) ^ d * (1 : ℝ) ^ (n - d) * (n.choose d : ℝ) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [one_pow]
          ring
    _ = ((1 : ℝ) / 2 + 1) ^ n := (add_pow ((1 : ℝ) / 2) 1 n).symm
    _ = ((3 : ℝ) / 2) ^ n := by norm_num

/-- `(3/2)^n > 2` for every `n ≥ 2`. -/
theorem two_lt_three_half_pow {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) < ((3 : ℝ) / 2) ^ n :=
  calc (2 : ℝ) < ((3 : ℝ) / 2) ^ 2 := by norm_num
    _ ≤ ((3 : ℝ) / 2) ^ n := pow_le_pow_right₀ (by norm_num) hn

/-- The manuscript's sign-corrected truncated sum: the display's `d ≤ 16`
cutoff with the intended decaying weight `2^(-d)`. -/
def signCorrectedTruncatedExtractionSum (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.range 17, (n.choose d : ℝ) * ((1 : ℝ) / 2) ^ d

/-- **Sign-corrected reading also fails for `n ≥ 2`.**  Already the three
lowest-order terms give `1 + n/2 + C(n,2)/4 > 2` for every `n ≥ 2`, so the
corrected display exceeds the asserted bound `2` whenever there is more than
one index. -/
theorem two_lt_signCorrectedTruncatedExtractionSum {n : ℕ} (hn : 2 ≤ n) :
    (2 : ℝ) < signCorrectedTruncatedExtractionSum n := by
  unfold signCorrectedTruncatedExtractionSum
  have hsub : Finset.range 3 ⊆ Finset.range 17 := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hnonneg :
      ∀ d ∈ Finset.range 17, d ∉ Finset.range 3 →
        0 ≤ (n.choose d : ℝ) * ((1 : ℝ) / 2) ^ d := by
    intro d _ _
    positivity
  have hle :
      ∑ d ∈ Finset.range 3, (n.choose d : ℝ) * ((1 : ℝ) / 2) ^ d
        ≤ ∑ d ∈ Finset.range 17, (n.choose d : ℝ) * ((1 : ℝ) / 2) ^ d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have h3 :
      ∑ d ∈ Finset.range 3, (n.choose d : ℝ) * ((1 : ℝ) / 2) ^ d
        = 1 + (n : ℝ) / 2 + (n.choose 2 : ℝ) / 4 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      Nat.choose_zero_right, Nat.choose_one_right]
    push_cast
    ring
  have hchoose : 1 ≤ n.choose 2 := Nat.choose_pos hn
  have hchooseR : (1 : ℝ) ≤ (n.choose 2 : ℝ) := by exact_mod_cast hchoose
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- **Weightless reading, exact value.**  Dropping the binomial factors
entirely, `Σ_{d=0}^{16} 2^(-d) = 2 - 2^(-16)`. -/
theorem weightlessExtractionSum_eq :
    ∑ d ∈ Finset.range 17, ((1 : ℝ) / 2) ^ d = 2 - ((1 : ℝ) / 2) ^ 16 := by
  rw [geom_sum_eq (by norm_num : ((1 : ℝ) / 2) ≠ 1) 17]
  norm_num

/-- The weightless geometric series is the only reading of the display under
which the asserted `≤ 2` (in fact `< 2`) holds. -/
theorem weightlessExtractionSum_lt_two :
    ∑ d ∈ Finset.range 17, ((1 : ℝ) / 2) ^ d < 2 := by
  rw [weightlessExtractionSum_eq]
  norm_num

/-! ## Part 2: the coefficient-majorant (weighted ℓ¹) norm repair

A finite family of monomials is indexed by `ι`, with canonical dimension map
`Δ : ι → ℕ` and coefficient vector `c : ι → ℝ`.  The majorant norm at radius
`r` is `‖c‖_r = Σ_i |c i| * r^(Δ i)`. -/

variable {ι : Type*} [Fintype ι]

/-- Weighted-ℓ¹ coefficient-majorant norm at radius `r`. -/
def majorantNorm (r : ℝ) (Δ : ι → ℕ) (c : ι → ℝ) : ℝ :=
  ∑ i, |c i| * r ^ Δ i

/-- Monomial truncation to canonical dimension `≤ D`: the coefficient model of
the extraction projection `P≤D`. -/
def dimTruncate (Δ : ι → ℕ) (D : ℕ) (c : ι → ℝ) : ι → ℝ :=
  fun i => if Δ i ≤ D then c i else 0

/-- The complementary tail, supported in canonical dimension `> D`. -/
def dimTail (Δ : ι → ℕ) (D : ℕ) (c : ι → ℝ) : ι → ℝ :=
  fun i => if D < Δ i then c i else 0

/-- Canonical RG rescaling on coefficients: a dimension-`Δ i` monomial scales
by `b^(4 - Δ i)` under one blocking step in four dimensions. -/
def rgDimScale (b : ℝ) (Δ : ι → ℕ) (c : ι → ℝ) : ι → ℝ :=
  fun i => b ^ ((4 : ℤ) - (Δ i : ℤ)) * c i

omit [Fintype ι] in
/-- Truncation and tail decompose the coefficient vector exactly. -/
theorem dimTruncate_add_dimTail (Δ : ι → ℕ) (D : ℕ) (c : ι → ℝ) :
    dimTruncate Δ D c + dimTail Δ D c = c := by
  funext i
  by_cases h : Δ i ≤ D
  · simp [dimTruncate, dimTail, h, not_lt.mpr h]
  · simp [dimTruncate, dimTail, h, Nat.lt_of_not_le h]

/-- The majorant norm is nonnegative at nonnegative radius. -/
theorem majorantNorm_nonneg {r : ℝ} (hr : 0 ≤ r) (Δ : ι → ℕ) (c : ι → ℝ) :
    0 ≤ majorantNorm r Δ c :=
  Finset.sum_nonneg fun _ _ =>
    mul_nonneg (abs_nonneg _) (pow_nonneg hr _)

/-- The majorant norm splits exactly along the truncation/tail decomposition
(the two pieces have disjoint monomial support). -/
theorem majorantNorm_split (r : ℝ) (Δ : ι → ℕ) (D : ℕ) (c : ι → ℝ) :
    majorantNorm r Δ c
      = majorantNorm r Δ (dimTruncate Δ D c)
        + majorantNorm r Δ (dimTail Δ D c) := by
  unfold majorantNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : Δ i ≤ D
  · simp [dimTruncate, dimTail, h, not_lt.mpr h]
  · simp [dimTruncate, dimTail, h, Nat.lt_of_not_le h]

/-- **Truncation is contractive in the majorant norm.**  The extraction
constant of `P≤D` on the weighted-ℓ¹ coefficient norm is `≤ 1`, improving the
manuscript's advertised Cauchy-estimate bound `≤ 2` and bypassing the broken
displayed sum of Part 1 entirely. -/
theorem majorantNorm_dimTruncate_le {r : ℝ} (hr : 0 ≤ r)
    (Δ : ι → ℕ) (D : ℕ) (c : ι → ℝ) :
    majorantNorm r Δ (dimTruncate Δ D c) ≤ majorantNorm r Δ c := by
  unfold majorantNorm
  refine Finset.sum_le_sum fun i _ => ?_
  have habs : |dimTruncate Δ D c i| ≤ |c i| := by
    by_cases h : Δ i ≤ D <;> simp [dimTruncate, h, abs_nonneg]
  exact mul_le_mul_of_nonneg_right habs (pow_nonneg hr _)

/-- **Tail radius-restriction gain.**  Restricting the tail (dimension `> D`)
from radius `r0` to radius `r1 ≤ r0` gains the factor `(r1/r0)^(D+1)`. -/
theorem majorantNorm_dimTail_le_shrink
    (Δ : ι → ℕ) (D : ℕ) (c : ι → ℝ) {r0 r1 : ℝ}
    (hr1 : 0 ≤ r1) (hr0 : 0 < r0) (hle : r1 ≤ r0) :
    majorantNorm r1 Δ (dimTail Δ D c)
      ≤ (r1 / r0) ^ (D + 1) * majorantNorm r0 Δ c := by
  unfold majorantNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hratio0 : 0 ≤ r1 / r0 := div_nonneg hr1 hr0.le
  have hterm0 : 0 ≤ |c i| * r0 ^ Δ i :=
    mul_nonneg (abs_nonneg _) (pow_nonneg hr0.le _)
  by_cases h : D < Δ i
  · have hratio1 : r1 / r0 ≤ 1 := (div_le_one hr0).mpr hle
    have hpow : (r1 / r0) ^ Δ i ≤ (r1 / r0) ^ (D + 1) :=
      pow_le_pow_of_le_one hratio0 hratio1 h
    have hr1pow : r1 ^ Δ i = (r1 / r0) ^ Δ i * r0 ^ Δ i := by
      rw [div_pow, div_mul_cancel₀]
      exact pow_ne_zero _ hr0.ne'
    simp only [dimTail, if_pos h]
    calc |c i| * r1 ^ Δ i
        = (r1 / r0) ^ Δ i * (|c i| * r0 ^ Δ i) := by rw [hr1pow]; ring
      _ ≤ (r1 / r0) ^ (D + 1) * (|c i| * r0 ^ Δ i) :=
          mul_le_mul_of_nonneg_right hpow hterm0
  · simp only [dimTail, if_neg h, abs_zero, zero_mul]
    exact mul_nonneg (pow_nonneg hratio0 _) hterm0

/-- **RG rescaling contracts the tail by the irrelevant factor.**  On
coefficients supported in dimension `> D`, the canonical rescaling
`c_i ↦ b^(4 - Δ i) c_i` is bounded by `b^(3-D)` in the majorant norm. -/
theorem majorantNorm_rgDimScale_dimTail_le
    (Δ : ι → ℕ) (D : ℕ) (c : ι → ℝ) {b r : ℝ}
    (hb : 1 ≤ b) (hr : 0 ≤ r) :
    majorantNorm r Δ (rgDimScale b Δ (dimTail Δ D c))
      ≤ b ^ ((3 : ℤ) - (D : ℤ)) * majorantNorm r Δ (dimTail Δ D c) := by
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le one_pos hb
  unfold majorantNorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have habs : |rgDimScale b Δ (dimTail Δ D c) i|
      = b ^ ((4 : ℤ) - (Δ i : ℤ)) * |dimTail Δ D c i| := by
    unfold rgDimScale
    rw [abs_mul, abs_of_pos (zpow_pos hb0 _)]
  rw [habs]
  rcases eq_or_ne (dimTail Δ D c i) 0 with h0 | h0
  · simp [h0]
  · have hlt : D < Δ i := by
      by_contra hcon
      apply h0
      simp [dimTail, hcon]
    have hcast : (D : ℤ) < (Δ i : ℤ) := by exact_mod_cast hlt
    have hexp : (4 : ℤ) - (Δ i : ℤ) ≤ 3 - (D : ℤ) := by omega
    have hzpow : b ^ ((4 : ℤ) - (Δ i : ℤ)) ≤ b ^ ((3 : ℤ) - (D : ℤ)) :=
      zpow_le_zpow_right₀ hb hexp
    calc b ^ ((4 : ℤ) - (Δ i : ℤ)) * |dimTail Δ D c i| * r ^ Δ i
        = b ^ ((4 : ℤ) - (Δ i : ℤ)) * (|dimTail Δ D c i| * r ^ Δ i) := by
          ring
      _ ≤ b ^ ((3 : ℤ) - (D : ℤ)) * (|dimTail Δ D c i| * r ^ Δ i) :=
          mul_le_mul_of_nonneg_right hzpow
            (mul_nonneg (abs_nonneg _) (pow_nonneg hr _))

/-- **Majorant-route irrelevant-tail contraction.**  Chaining the RG
rescaling bound with the radius-restriction gain: one blocking step applied to
the dimension-`> D` tail is bounded by `b^(3-D) * (r1/r0)^(D+1) * ‖c‖_{r0}` in
the majorant norm at the restricted radius.  This is the advertised
`λ_irr = b^(3-D)` with the extraction constant `≤ 1`. -/
theorem majorant_irrelevant_tail_contraction
    (Δ : ι → ℕ) (D : ℕ) (c : ι → ℝ) {b r0 r1 : ℝ}
    (hb : 1 ≤ b) (hr1 : 0 ≤ r1) (hr0 : 0 < r0) (hle : r1 ≤ r0) :
    majorantNorm r1 Δ (rgDimScale b Δ (dimTail Δ D c))
      ≤ b ^ ((3 : ℤ) - (D : ℤ))
        * ((r1 / r0) ^ (D + 1) * majorantNorm r0 Δ c) := by
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le one_pos hb
  have hbpow : 0 ≤ b ^ ((3 : ℤ) - (D : ℤ)) := (zpow_pos hb0 _).le
  calc majorantNorm r1 Δ (rgDimScale b Δ (dimTail Δ D c))
      ≤ b ^ ((3 : ℤ) - (D : ℤ)) * majorantNorm r1 Δ (dimTail Δ D c) :=
        majorantNorm_rgDimScale_dimTail_le Δ D c hb hr1
    _ ≤ b ^ ((3 : ℤ) - (D : ℤ))
          * ((r1 / r0) ^ (D + 1) * majorantNorm r0 Δ c) :=
        mul_le_mul_of_nonneg_left
          (majorantNorm_dimTail_le_shrink Δ D c hr1 hr0 hle) hbpow

/-- The majorant-route contraction expressed through `irrelevantScale`, the
factor budgeted by `HasExtendedExtractionContraction` and
`HasTwoSourceBootstrapSlack`: for a natural block factor `b ≥ 1` the tail
bound is exactly `irrelevantScale b D` times the radius gain. -/
theorem majorant_irrelevant_tail_contraction_irrelevantScale
    (Δ : ι → ℕ) (D : ℕ) (c : ι → ℝ) {bN : ℕ} {r0 r1 : ℝ}
    (hb : 1 ≤ bN) (hr1 : 0 ≤ r1) (hr0 : 0 < r0) (hle : r1 ≤ r0) :
    majorantNorm r1 Δ (rgDimScale (bN : ℝ) Δ (dimTail Δ D c))
      ≤ irrelevantScale bN D
        * ((r1 / r0) ^ (D + 1) * majorantNorm r0 Δ c) := by
  have hbR : (1 : ℝ) ≤ (bN : ℝ) := by exact_mod_cast hb
  have h := majorant_irrelevant_tail_contraction Δ D c hbR hr1 hr0 hle
  simpa [irrelevantScale] using h

end YangMills
end QuantumTheory
end Mettapedia
