import Mettapedia.UniversalAI.UniversalHyperprior.DyadicRealization
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Exact dyadic arithmetic and accuracy-controlled limits

Dyadic addition aligns denominators without rounding, and multiplication is
also exact. Their real realizations therefore give genuine error propagation
bounds. A sequence converges when its certified errors shrink with an accuracy
parameter tending to infinity; increasing the stored denominator alone is not
an accuracy certificate.

This leaf uses the completed realization layer and Mathlib. It does not import
the unfinished posterior arithmetic or assert that a fixed precision-free
posterior routine converges. The legacy posterior approximation obligation
remains separate in `ApproximationBounds`.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.UniversalHyperprior.Dyadic

open DyadicValue
open Mettapedia.UniversalAI.UniversalHyperprior

theorem dyadicValue_toReal_correct (num : ℤ) (denom_pow : ℕ) :
    (DyadicValue.mk num denom_pow).toReal = (num : ℝ) / (2 : ℝ) ^ denom_pow := rfl

theorem dyadicContext_toReal_τ₀_sq (k : ℤ) (σ_sq_num : ℕ) (σ_sq_denom_pow : ℕ)
    (positive : 0 < σ_sq_num) :
    (DyadicContext.atK k σ_sq_num σ_sq_denom_pow positive).toReal.τ₀_sq = (2 : ℝ) ^ k := rfl

namespace DyadicValue

/-- Aligning denominator exponents preserves the exact sum. -/
@[simp] theorem toReal_add (first second : DyadicValue) :
    (first + second).toReal = first.toReal + second.toReal := by
  change (add first second).toReal = _
  unfold add
  split_ifs with same less
  · simp [toReal, same, add_div]
  · have exponent : first.denom_pow + (second.denom_pow - first.denom_pow) =
        second.denom_pow := Nat.add_sub_of_le less.le
    have powers : (2 : ℝ) ^ second.denom_pow =
        (2 : ℝ) ^ first.denom_pow * (2 : ℝ) ^ (second.denom_pow - first.denom_pow) := by
      rw [← pow_add, exponent]
    simp only [toReal, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    rw [powers]
    field_simp
  · have greater : second.denom_pow ≤ first.denom_pow := Nat.le_of_not_gt less
    have exponent : second.denom_pow + (first.denom_pow - second.denom_pow) =
        first.denom_pow := Nat.add_sub_of_le greater
    have powers : (2 : ℝ) ^ first.denom_pow =
        (2 : ℝ) ^ second.denom_pow * (2 : ℝ) ^ (first.denom_pow - second.denom_pow) := by
      rw [← pow_add, exponent]
    simp only [toReal, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    rw [powers]
    field_simp

@[simp] theorem toReal_mul (first second : DyadicValue) :
    (first * second).toReal = first.toReal * second.toReal := by
  change ((first.num * second.num : ℤ) : ℝ) / (2 : ℝ) ^
    (first.denom_pow + second.denom_pow) = _
  rw [Int.cast_mul, pow_add, mul_div_mul_comm]
  rfl

end DyadicValue

/-- Addition introduces no rounding error of its own. -/
theorem add_error_bound (a b : DyadicValue) (a_real b_real : ℝ)
    (ha : |a.toReal - a_real| ≤ 2 ^ (-(a.denom_pow : ℤ)))
    (hb : |b.toReal - b_real| ≤ 2 ^ (-(b.denom_pow : ℤ))) :
    |(a + b).toReal - (a_real + b_real)| ≤
      2 ^ (-(min a.denom_pow b.denom_pow : ℤ)) +
        2 ^ (-(max a.denom_pow b.denom_pow : ℤ)) := by
  have error : |(a + b).toReal - (a_real + b_real)| ≤
      2 ^ (-(a.denom_pow : ℤ)) + 2 ^ (-(b.denom_pow : ℤ)) := by
    rw [toReal_add]
    calc
      |a.toReal + b.toReal - (a_real + b_real)| =
          |(a.toReal - a_real) + (b.toReal - b_real)| := by congr 1; ring
      _ ≤ |a.toReal - a_real| + |b.toReal - b_real| := abs_add_le _ _
      _ ≤ _ := add_le_add ha hb
  rcases le_total a.denom_pow b.denom_pow with first | second
  · have order : (a.denom_pow : ℤ) ≤ b.denom_pow := by exact_mod_cast first
    simpa only [min_eq_left order, max_eq_right order] using error
  · have order : (b.denom_pow : ℤ) ≤ a.denom_pow := by exact_mod_cast second
    simpa only [min_eq_right order, max_eq_left order, add_comm] using error

/-- Bounded target magnitudes control the two linear error terms; the product
of the input errors supplies the remaining term. -/
theorem mul_error_bound (a b : DyadicValue) (a_real b_real : ℝ)
    (ha : |a.toReal - a_real| ≤ 2 ^ (-(a.denom_pow : ℤ)))
    (hb : |b.toReal - b_real| ≤ 2 ^ (-(b.denom_pow : ℤ)))
    (ha_bound : |a_real| ≤ 1) (hb_bound : |b_real| ≤ 1) :
    |(a * b).toReal - (a_real * b_real)| ≤
      2 ^ (-(a.denom_pow : ℤ)) + 2 ^ (-(b.denom_pow : ℤ)) +
        2 ^ (-(a.denom_pow + b.denom_pow : ℤ)) := by
  have radius_a : 0 ≤ (2 : ℝ) ^ (-(a.denom_pow : ℤ)) := (zpow_pos (by norm_num) _).le
  have first_term : |a.toReal - a_real| * |b_real| ≤ 2 ^ (-(a.denom_pow : ℤ)) := by
    calc
      _ ≤ |a.toReal - a_real| * 1 := mul_le_mul_of_nonneg_left hb_bound (abs_nonneg _)
      _ ≤ _ := by simpa using ha
  have second_term : |a_real| * |b.toReal - b_real| ≤ 2 ^ (-(b.denom_pow : ℤ)) := by
    calc
      _ ≤ 1 * |b.toReal - b_real| := mul_le_mul_of_nonneg_right ha_bound (abs_nonneg _)
      _ ≤ _ := by simpa using hb
  have product_term : |a.toReal - a_real| * |b.toReal - b_real| ≤
      (2 : ℝ) ^ (-(a.denom_pow : ℤ)) * (2 : ℝ) ^ (-(b.denom_pow : ℤ)) :=
    mul_le_mul ha hb (abs_nonneg _) radius_a
  have product_radius : (2 : ℝ) ^ (-(a.denom_pow : ℤ)) * (2 : ℝ) ^ (-(b.denom_pow : ℤ)) =
      2 ^ (-(a.denom_pow + b.denom_pow : ℤ)) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [product_radius] at product_term
  rw [toReal_mul]
  calc
    |a.toReal * b.toReal - a_real * b_real| =
        |((a.toReal - a_real) * b_real + a_real * (b.toReal - b_real)) +
          (a.toReal - a_real) * (b.toReal - b_real)| := by congr 1; ring
    _ ≤ |(a.toReal - a_real) * b_real + a_real * (b.toReal - b_real)| +
        |(a.toReal - a_real) * (b.toReal - b_real)| := abs_add_le _ _
    _ ≤ (|(a.toReal - a_real) * b_real| + |a_real * (b.toReal - b_real)|) +
        |(a.toReal - a_real) * (b.toReal - b_real)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = _ := by simp only [abs_mul]
    _ ≤ _ := add_le_add (add_le_add first_term second_term) product_term

/-- The usual epsilon definition for the realized dyadic sequence. -/
def ApproximatesAt (seq : ℕ → DyadicValue) (r : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |(seq n).toReal - r| < ε

theorem approximatesAt_iff_tendsto (seq : ℕ → DyadicValue) (r : ℝ) :
    ApproximatesAt seq r ↔ Filter.Tendsto (fun n => (seq n).toReal) Filter.atTop (nhds r) := by
  simpa only [ApproximatesAt, Real.dist_eq] using
    (Metric.tendsto_atTop : Filter.Tendsto (fun n => (seq n).toReal) Filter.atTop (nhds r) ↔ _).symm

theorem accuracy_grid_tendsto_zero :
    Filter.Tendsto (fun precision : ℕ => (2 : ℝ) ^ (-(precision : ℤ)))
      Filter.atTop (nhds 0) := by
  simpa only [zpow_neg, zpow_natCast, inv_pow] using
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)

/-- The error certificate, rather than the numeric representation alone,
connects increasing accuracy to a real limit. Arbitrary index filters are allowed. -/
theorem tendsto_of_grid_error {Index : Type*} {along : Filter Index}
    (values : Index → ℝ) (limit : ℝ) (precision : Index → ℕ)
    (increases : Filter.Tendsto precision along Filter.atTop)
    (bound : ∀ index, |values index - limit| ≤ (2 : ℝ) ^ (-(precision index : ℤ))) :
    Filter.Tendsto values along (nhds limit) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (accuracy_grid_tendsto_zero.comp increases)
  intro index
  simpa only [Real.norm_eq_abs, Function.comp_apply] using bound index

theorem dyadic_convergence_of_precision_tendsto (r : ℝ) (seq : ℕ → DyadicValue)
    (increases : Filter.Tendsto (fun n => (seq n).denom_pow) Filter.atTop Filter.atTop)
    (bound : ∀ n, |(seq n).toReal - r| ≤ 2 ^ (-((seq n).denom_pow : ℤ))) :
    ApproximatesAt seq r :=
  (approximatesAt_iff_tendsto seq r).mpr
    (tendsto_of_grid_error _ r _ increases bound)

/-- Strictly growing denominator exponents suffice when accompanied by the
stated, independently required accuracy bounds. -/
theorem dyadic_convergence (r : ℝ) (seq : ℕ → DyadicValue)
    (h_precision : ∀ n, (seq n.succ).denom_pow > (seq n).denom_pow)
    (h_bound : ∀ n, |(seq n).toReal - r| ≤ 2 ^ (-((seq n).denom_pow : ℤ))) :
    ApproximatesAt seq r :=
  dyadic_convergence_of_precision_tendsto r seq
    (strictMono_nat_of_lt_succ h_precision).tendsto_atTop h_bound

/-- The mean and observation-variance limits use only their own error bounds.
No exactness premise about the unrelated prior variance is necessary. -/
theorem context_sequence_convergence (ctx_limit : NormalNormalContext)
    (ctx_seq : ℕ → DyadicContext)
    (h_μ₀_conv : ∀ n, |(ctx_seq n).toReal.μ₀ - ctx_limit.μ₀| ≤ 2 ^ (-n : ℤ))
    (h_σ_sq_conv : ∀ n, |(ctx_seq n).toReal.σ_sq - ctx_limit.σ_sq| ≤ 2 ^ (-n : ℤ)) :
    Filter.Tendsto (fun n => (ctx_seq n).toReal.μ₀) Filter.atTop (nhds ctx_limit.μ₀) ∧
    Filter.Tendsto (fun n => (ctx_seq n).toReal.σ_sq) Filter.atTop (nhds ctx_limit.σ_sq) :=
  ⟨tendsto_of_grid_error _ _ id Filter.tendsto_id h_μ₀_conv,
    tendsto_of_grid_error _ _ id Filter.tendsto_id h_σ_sq_conv⟩

namespace ApproximationExamples

theorem exact_signed_operations :
    ((⟨-1, 3⟩ : DyadicValue) + ⟨3, 1⟩).toReal = 11 / 8 ∧
      ((⟨-1, 3⟩ : DyadicValue) * ⟨3, 1⟩).toReal = -3 / 16 := by
  constructor
  · change (DyadicValue.add ⟨-1, 3⟩ ⟨3, 1⟩).toReal = 11 / 8
    norm_num [DyadicValue.add, DyadicValue.toReal]
  · change (DyadicValue.mul ⟨-1, 3⟩ ⟨3, 1⟩).toReal = -3 / 16
    norm_num [DyadicValue.mul, DyadicValue.toReal]

/-- The actual accuracy-parameterized division can converge to a non-dyadic real. -/
theorem thirds_approximated :
    ApproximatesAt (fun precision => DyadicValue.div DyadicValue.one ⟨3, 0⟩ precision) (1 / 3) := by
  apply (approximatesAt_iff_tendsto _ _).mpr
  simpa [DyadicValue.one, DyadicValue.toReal] using
    DyadicValue.tendsto_div DyadicValue.one ⟨3, 0⟩ (by decide)

/-- A changing representation can retain the same inaccurate value forever. -/
theorem denominator_growth_alone_insufficient :
    (∀ n : ℕ, (⟨0, n + 1⟩ : DyadicValue).denom_pow > (⟨0, n⟩ : DyadicValue).denom_pow) ∧
      ¬ ApproximatesAt (fun n => (⟨0, n⟩ : DyadicValue)) 1 := by
  constructor
  · intro n; exact Nat.lt_succ_self n
  · intro converges
    obtain ⟨index, after⟩ := converges 1 (by norm_num)
    have impossible := after index le_rfl
    norm_num [DyadicValue.toReal] at impossible

end ApproximationExamples

end Mettapedia.UniversalAI.UniversalHyperprior.Dyadic
