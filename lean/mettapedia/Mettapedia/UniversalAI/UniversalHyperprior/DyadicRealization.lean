import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mettapedia.UniversalAI.UniversalHyperprior
import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGamma

/-!
# Dyadic contexts, evidence, and certified division

`DyadicValue` represents integer numerators over powers of two. Contexts embed
prior means, power-of-two prior variances, and positive dyadic observation
variances into the existing real-valued normal model. Evidence embeds a sample
count, mean, and nonnegative variance into valid reconstructed moments; the
Cauchy–Schwarz law follows from that variance constraint. These moment
inequalities do not assert that a dataset with exactly that sample count
realizes the supplied moments.

Division uses a fixed output grid and integer Euclidean division. Its absolute
error is smaller than one grid interval for every nonzero divisor, including
signed inputs. The stronger one-sided error law applies to positive divisors.
Zero division has the explicit total integer-division convention.

Power-of-two prior variances are represented exactly. This does not imply that
posterior means, precisions, or marginal likelihoods are dyadic: those separate
algorithms still require approximation and accuracy proofs in the accompanying
arithmetic and approximation modules. This file establishes neither their
implementation nor convergence of the full hyperprior procedure.
-/

namespace Mettapedia.UniversalAI.UniversalHyperprior.Dyadic

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGamma
open Mettapedia.UniversalAI.UniversalHyperprior

/-! ## Dyadic Value Type

A dyadic rational is a number of the form `num / 2^denom_pow`.

We store:
- `num : ℤ` - the numerator (can be negative)
- `denom_pow : ℕ` - the power of 2 in the denominator

This represents: `num / 2^denom_pow`
-/

structure DyadicValue where
  num : ℤ
  denom_pow : ℕ

namespace DyadicValue

/-- Convert a dyadic value to a real number -/
noncomputable def toReal (d : DyadicValue) : ℝ :=
  (d.num : ℝ) / (2 : ℝ) ^ d.denom_pow

/-- Zero as a dyadic -/
def zero : DyadicValue := ⟨0, 0⟩

/-- One as a dyadic -/
def one : DyadicValue := ⟨1, 0⟩

/-- Addition of dyadic values (aligns to common denominator) -/
def add (a b : DyadicValue) : DyadicValue :=
  if a.denom_pow = b.denom_pow then
    ⟨a.num + b.num, a.denom_pow⟩
  else if a.denom_pow < b.denom_pow then
    let shift := b.denom_pow - a.denom_pow
    ⟨a.num * (2 ^ shift) + b.num, b.denom_pow⟩
  else
    let shift := a.denom_pow - b.denom_pow
    ⟨a.num + b.num * (2 ^ shift), a.denom_pow⟩

/-- Multiplication of dyadic values -/
def mul (a b : DyadicValue) : DyadicValue :=
  ⟨a.num * b.num, a.denom_pow + b.denom_pow⟩

/-- Division on the fixed grid with denominator `2 ^ precision`.
For a positive divisor numerator, integer Euclidean division rounds down and
the error is strictly smaller than one grid interval (`div_error`).  A zero
divisor numerator returns zero by the total integer-division convention. -/
def div (a b : DyadicValue) (precision : ℕ) : DyadicValue :=
  ⟨(a.num * (2 : ℤ) ^ (b.denom_pow + precision)) /
    (b.num * (2 : ℤ) ^ a.denom_pow), precision⟩

/-- The error contract excludes zero and negative divisor numerators.  The
dividend numerator may have either sign. -/
theorem div_error (a b : DyadicValue) (precision : ℕ) (positive : 0 < b.num) :
    0 ≤ a.toReal / b.toReal - (div a b precision).toReal ∧
      a.toReal / b.toReal - (div a b precision).toReal <
        1 / (2 : ℝ) ^ precision := by
  let numerator : ℤ := a.num * (2 : ℤ) ^ (b.denom_pow + precision)
  let denominator : ℤ := b.num * (2 : ℤ) ^ a.denom_pow
  have denominator_pos : 0 < denominator :=
    mul_pos positive (pow_pos (by norm_num) _)
  have denominator_real_pos : (0 : ℝ) < denominator := by exact_mod_cast denominator_pos
  have grid_pos : (0 : ℝ) < 2 ^ precision := pow_pos (by norm_num) _
  have remainder_nonneg : (0 : ℝ) ≤ (numerator % denominator : ℤ) := by
    exact_mod_cast Int.emod_nonneg numerator (ne_of_gt denominator_pos)
  have remainder_small : ((numerator % denominator : ℤ) : ℝ) < denominator := by
    exact_mod_cast Int.emod_lt_of_pos numerator denominator_pos
  have division_identity :
      ((numerator % denominator : ℤ) : ℝ) +
        (denominator : ℝ) * ((numerator / denominator : ℤ) : ℝ) = numerator := by
    exact_mod_cast Int.emod_add_mul_ediv numerator denominator
  have scaled_quotient :
      a.toReal / b.toReal = (numerator : ℝ) / denominator / (2 : ℝ) ^ precision := by
    dsimp [numerator, denominator, toReal]
    push_cast
    rw [pow_add]
    have bn : (b.num : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt positive
    field_simp
  have error_eq :
      a.toReal / b.toReal - (div a b precision).toReal =
        ((numerator % denominator : ℤ) : ℝ) / denominator / (2 : ℝ) ^ precision := by
    rw [scaled_quotient]
    change (numerator : ℝ) / denominator / (2 : ℝ) ^ precision -
        ((numerator / denominator : ℤ) : ℝ) / (2 : ℝ) ^ precision = _
    field_simp
    nlinarith [division_identity]
  rw [error_eq]
  constructor
  · exact div_nonneg (div_nonneg remainder_nonneg denominator_real_pos.le) grid_pos.le
  · exact (div_lt_div_iff_of_pos_right grid_pos).2
      ((div_lt_one denominator_real_pos).2 remainder_small)

/-- The absolute grid-error bound holds for every nonzero divisor numerator.
With a negative divisor, Euclidean division reverses the directed rounding error. -/
theorem div_abs_error (a b : DyadicValue) (precision : ℕ) (nonzero : b.num ≠ 0) :
    |a.toReal / b.toReal - (div a b precision).toReal| <
      1 / (2 : ℝ) ^ precision := by
  rcases lt_or_gt_of_ne nonzero with negative | positive
  · let positiveDivisor : DyadicValue := ⟨-b.num, b.denom_pow⟩
    have numerator_pos : 0 < positiveDivisor.num := neg_pos.mpr negative
    have bound := div_error a positiveDivisor precision numerator_pos
    have exact_negative :
        a.toReal / b.toReal = -(a.toReal / positiveDivisor.toReal) := by
      have value_negative : positiveDivisor.toReal = -b.toReal := by
        simp [positiveDivisor, toReal, neg_div]
      rw [value_negative, div_neg, neg_neg]
    have result_negative :
        (div a b precision).toReal = -(div a positiveDivisor precision).toReal := by
      simp [div, toReal, positiveDivisor, neg_mul, Int.ediv_neg, neg_div]
    have difference_negative :
        a.toReal / b.toReal - (div a b precision).toReal =
          -(a.toReal / positiveDivisor.toReal - (div a positiveDivisor precision).toReal) := by
      rw [exact_negative, result_negative]
      ring
    rw [difference_negative, abs_neg, abs_of_nonneg bound.1]
    exact bound.2
  · have bound := div_error a b precision positive
    simpa only [abs_of_nonneg bound.1] using bound.2

@[simp] theorem div_zero_num (a b : DyadicValue) (precision : ℕ) (zero_num : b.num = 0) :
    div a b precision = ⟨0, precision⟩ := by
  simp [div, zero_num]

/-- An explicit accuracy parameter tending to infinity gives genuine convergence. -/
theorem tendsto_div (a b : DyadicValue) (nonzero : b.num ≠ 0) :
    Filter.Tendsto (fun precision : ℕ => (DyadicValue.div a b precision).toReal)
      Filter.atTop (nhds (a.toReal / b.toReal)) := by
  have grid_limit : Filter.Tendsto (fun precision : ℕ => 1 / (2 : ℝ) ^ precision)
      Filter.atTop (nhds 0) := by
    simpa only [one_div, inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ grid_limit
  intro precision
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact (DyadicValue.div_abs_error a b precision nonzero).le

/-- The same limit holds for any index/filter whose requested precision tends to infinity. -/
theorem tendsto_div_of_precision_tendsto {Index : Type*} {along : Filter Index}
    (a b : DyadicValue) (nonzero : b.num ≠ 0) (precision : Index → ℕ)
    (increases : Filter.Tendsto precision along Filter.atTop) :
    Filter.Tendsto (fun index => (DyadicValue.div a b (precision index)).toReal)
      along (nhds (a.toReal / b.toReal)) :=
  (tendsto_div a b nonzero).comp increases

instance : Add DyadicValue := ⟨add⟩
instance : Mul DyadicValue := ⟨mul⟩

end DyadicValue

/-! ## Dyadic Context

A `NormalNormalContext` represented with dyadic rationals.

Key insight: Since τ₀² = 2^k in the Universal Hyperprior, it's EXACTLY
representable as a dyadic (no approximation!).
-/

structure DyadicContext where
  /-- Prior mean μ₀ as dyadic: μ₀_num / 2^μ₀_denom_pow -/
  μ₀_num : ℤ
  μ₀_denom_pow : ℕ

  /-- Prior variance τ₀² as a POWER of 2: τ₀² = 2^τ₀_sq_pow

  This is EXACT for the Universal Hyperprior family! -/
  τ₀_sq_pow : ℤ

  /-- Observation variance σ² as dyadic: σ_sq_num / 2^σ_sq_denom_pow -/
  σ_sq_num : ℕ
  σ_sq_denom_pow : ℕ

  /-- Positivity constraint: σ² > 0 -/
  σ_sq_num_pos : 0 < σ_sq_num

namespace DyadicContext

/-- Convert dyadic context to real-valued context -/
noncomputable def toReal (ctx : DyadicContext) : NormalNormalContext where
  μ₀ := (ctx.μ₀_num : ℝ) / (2 : ℝ) ^ ctx.μ₀_denom_pow
  τ₀_sq := (2 : ℝ) ^ ctx.τ₀_sq_pow
  σ_sq := (ctx.σ_sq_num : ℝ) / (2 : ℝ) ^ ctx.σ_sq_denom_pow
  τ₀_sq_pos := by
    apply zpow_pos
    norm_num
  σ_sq_pos := by
    apply div_pos
    · exact Nat.cast_pos.mpr ctx.σ_sq_num_pos
    · apply pow_pos; norm_num

/-- Create a context for Universal Hyperprior at index k
    Uses τ₀² = 2^k (exact!), μ₀ = 0, σ² provided as dyadic -/
def atK (k : ℤ) (σ_sq_num : ℕ) (σ_sq_denom_pow : ℕ) (h : 0 < σ_sq_num) : DyadicContext where
  μ₀_num := 0
  μ₀_denom_pow := 0
  τ₀_sq_pow := k
  σ_sq_num := σ_sq_num
  σ_sq_denom_pow := σ_sq_denom_pow
  σ_sq_num_pos := h

end DyadicContext

/-! ## Dyadic BinaryEvidence

BinaryEvidence represented with dyadic rationals for sample mean and variance.
-/

structure DyadicEvidence where
  /-- Sample count (exact) -/
  n : ℕ

  /-- Sample mean as dyadic: mean_num / 2^mean_denom_pow -/
  mean_num : ℤ
  mean_denom_pow : ℕ

  /-- Sample variance as dyadic: var_num / 2^var_denom_pow -/
  var_num : ℕ
  var_denom_pow : ℕ

namespace DyadicEvidence

/-- Convert dyadic evidence to real-valued evidence -/
noncomputable def toReal (ev : DyadicEvidence) : NormalGammaEvidence where
  n := ev.n
  sum := ev.n * ((ev.mean_num : ℝ) / (2 : ℝ) ^ ev.mean_denom_pow)
  sumSq := ev.n * (((ev.mean_num : ℝ) / (2 : ℝ) ^ ev.mean_denom_pow) ^ 2
                   + (ev.var_num : ℝ) / (2 : ℝ) ^ ev.var_denom_pow)
  sumSq_nonneg := by
    apply mul_nonneg
    · exact Nat.cast_nonneg _
    · apply add_nonneg
      · apply sq_nonneg
      · apply div_nonneg
        · exact Nat.cast_nonneg _
        · apply pow_nonneg; norm_num
  cauchy_schwarz := by
    have variance_nonneg :
        0 ≤ (ev.var_num : ℝ) / (2 : ℝ) ^ ev.var_denom_pow :=
      div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
    calc
      ((ev.n : ℝ) * ((ev.mean_num : ℝ) / (2 : ℝ) ^ ev.mean_denom_pow)) ^ 2 ≤
          ((ev.n : ℝ) * ((ev.mean_num : ℝ) / (2 : ℝ) ^ ev.mean_denom_pow)) ^ 2 +
            (ev.n : ℝ) ^ 2 * ((ev.var_num : ℝ) / (2 : ℝ) ^ ev.var_denom_pow) :=
        le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) variance_nonneg)
      _ = _ := by ring

/-- Extract sample mean as dyadic value -/
def toMean (ev : DyadicEvidence) : DyadicValue :=
  ⟨ev.mean_num, ev.mean_denom_pow⟩

end DyadicEvidence

end Mettapedia.UniversalAI.UniversalHyperprior.Dyadic
