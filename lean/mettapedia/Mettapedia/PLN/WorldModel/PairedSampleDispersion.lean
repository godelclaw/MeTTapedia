import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Pairs of samples are not samples

Pairing every sample of one bag with every sample of another gives the paired
product of `Mettapedia.PLN.WorldModel.EvidenceSpaces.ofSamples_product`: `a⁺ b⁺`
positive pairs among `n m`.  Its strength is the product of the two strengths,
the right point estimate of the conjunction of two independent propositions.
Its total `n m` is a number of pairs, and the pairs are not independent: two
pairs that share a sample are correlated.  This module derives that from the
sampling model, with no probability theory beyond finite sums.

* `expect p n f` is the expectation of `f` over `n` independent Bernoulli(`p`)
  samples, defined by conditioning on the first sample.  Over any commutative
  ring it gives the binomial moments `n p` and `n p (1 - p) + n² p²`
  (`expect_count`, `expect_count_sq`).
* **The paired count is overdispersed** (`paired_variance`): for independent
  bags of sizes `n`, `m` with success probabilities `p`, `q`, the variance of the
  number of positive pairs is
  `n m · p q (1 - p q) + n m · p q · ((m - 1) q (1 - p) + (n - 1) p (1 - q))`.
  The first term is the variance of the count of positives among `n m`
  independent samples of the conjunction (`joint_variance`), computed by the
  same expectation.
* **The paired total is an effective sample size only for single samples**
  (`paired_variance_eq_joint_iff`): for `0 < p, q < 1` the two variances agree
  exactly when `n = m = 1`.
* A small exact witness (`Controls.all_pairs_positive`): with two fair samples
  on each side, all four pairs are positive with probability `1/16`; four
  independent samples of the conjunction are all positive with probability
  `1/256`.

So a readout of confidence from the total of a paired product overstates the
evidence for a conjunction: for `n = m` and `p = q = 1/2` the effective number of
independent joint samples is `3 n² / (2 n + 1)`, below `3 n / 2`
(`Controls.effective_size_half`), not `n²`.  The confidence of a conjunction is
derived from the factors through their credal intervals
(`Mettapedia.PLN.WorldModel.EvidenceContracts.product_interval`,
`Mettapedia.PLN.WorldModel.EvidenceContracts.Controls.conjunction_through_intervals`),
not from the paired total.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.PairedSampleDispersion

universe u

section Ring

variable {R : Type u} [CommRing R]

/-- **Expectation over independent samples**: condition on the first sample. -/
def expect (p : R) : ℕ → (List Bool → R) → R
  | 0, f => f []
  | n + 1, f => p * expect p n (fun s => f (true :: s)) + (1 - p) * expect p n (fun s => f (false :: s))

/-- The number of positive samples. -/
def positives (s : List Bool) : ℕ := s.count true

@[simp] theorem positives_true (s : List Bool) : positives (true :: s) = positives s + 1 := by
  simp [positives]

@[simp] theorem positives_false (s : List Bool) : positives (false :: s) = positives s := by
  simp [positives]

theorem expect_add (p : R) (n : ℕ) (f g : List Bool → R) :
    expect p n (fun s => f s + g s) = expect p n f + expect p n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
      simp only [expect]
      rw [ih (fun s => f (true :: s)) (fun s => g (true :: s)),
        ih (fun s => f (false :: s)) (fun s => g (false :: s))]
      ring

theorem expect_mul_left (p c : R) (n : ℕ) (f : List Bool → R) :
    expect p n (fun s => c * f s) = c * expect p n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [expect]
      rw [ih (fun s => f (true :: s)), ih (fun s => f (false :: s))]
      ring

theorem expect_const (p c : R) (n : ℕ) : expect p n (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [expect, ih]
      ring

theorem expect_congr (p : R) (n : ℕ) {f g : List Bool → R} (same : ∀ s, f s = g s) :
    expect p n f = expect p n g := by
  rw [funext same]

/-- **Mean of the binomial count.** -/
theorem expect_count (p : R) (n : ℕ) : expect p n (fun s => (positives s : R)) = n * p := by
  induction n with
  | zero => simp [expect, positives]
  | succ n ih =>
      simp only [expect, positives_true, positives_false, Nat.cast_add, Nat.cast_one]
      rw [expect_add, expect_const, ih]
      ring

/-- **Second moment of the binomial count.** -/
theorem expect_count_sq (p : R) (n : ℕ) :
    expect p n (fun s => (positives s : R) ^ 2) = n * p * (1 - p) + n ^ 2 * p ^ 2 := by
  induction n with
  | zero => simp [expect, positives]
  | succ n ih =>
      simp only [expect, positives_true, positives_false, Nat.cast_add, Nat.cast_one]
      have square : ∀ s : List Bool, ((positives s : R) + 1) ^ 2 =
          (positives s : R) ^ 2 + (2 * (positives s : R) + 1) := fun s => by ring
      rw [expect_congr p n square, expect_add, expect_add, expect_const, expect_mul_left,
        expect_count, ih]
      ring

/-- The count of positive pairs, from two independent bags. -/
def pairedMoment (p q : R) (n m : ℕ) (k : ℕ) : R :=
  expect p n fun s => expect q m fun t => ((positives s * positives t : ℕ) : R) ^ k

theorem pairedMoment_eq (p q : R) (n m k : ℕ) :
    pairedMoment p q n m k =
      expect p n (fun s => (positives s : R) ^ k) * expect q m (fun t => (positives t : R) ^ k) := by
  unfold pairedMoment
  have inner : ∀ s : List Bool, expect q m (fun t => ((positives s * positives t : ℕ) : R) ^ k) =
      (positives s : R) ^ k * expect q m (fun t => (positives t : R) ^ k) := by
    intro s
    rw [← expect_mul_left]
    exact expect_congr q m fun t => by push_cast; ring
  rw [expect_congr p n inner]
  rw [show (fun s : List Bool => (positives s : R) ^ k * expect q m (fun t => (positives t : R) ^ k)) =
      fun s => expect q m (fun t => (positives t : R) ^ k) * (positives s : R) ^ k from
    funext fun s => mul_comm _ _, expect_mul_left, mul_comm]

/-- The variance of the number of positive pairs. -/
def pairedVariance (p q : R) (n m : ℕ) : R := pairedMoment p q n m 2 - pairedMoment p q n m 1 ^ 2

/-- The variance of the number of positives among `N` independent samples of a
proposition of probability `r`. -/
def jointVariance (r : R) (N : ℕ) : R :=
  expect r N (fun s => (positives s : R) ^ 2) - expect r N (fun s => (positives s : R)) ^ 2

/-- **Variance of independent joint samples**: `N r (1 - r)`. -/
theorem joint_variance (r : R) (N : ℕ) : jointVariance r N = N * r * (1 - r) := by
  rw [jointVariance, expect_count_sq, expect_count]
  ring

/-- **The paired count is overdispersed.** -/
theorem paired_variance (p q : R) (n m : ℕ) :
    pairedVariance p q n m =
      jointVariance (p * q) (n * m) +
        n * m * (p * q) * ((m - 1) * q * (1 - p) + (n - 1) * p * (1 - q)) := by
  rw [pairedVariance, pairedMoment_eq, pairedMoment_eq, joint_variance]
  simp only [pow_one]
  rw [expect_count_sq, expect_count_sq, expect_count, expect_count]
  push_cast
  ring

end Ring

section Field

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- **The paired total is an effective sample size only for single samples.** -/
theorem paired_variance_eq_joint_iff {p q : F} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hq1 : q < 1) {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    pairedVariance p q n m = jointVariance (p * q) (n * m) ↔ n = 1 ∧ m = 1 := by
  rw [paired_variance]
  constructor
  · intro same
    have excess : (n : F) * m * (p * q) * ((m - 1) * q * (1 - p) + (n - 1) * p * (1 - q)) = 0 := by
      linarith
    have nPos : (0 : F) < n := by exact_mod_cast hn
    have mPos : (0 : F) < m := by exact_mod_cast hm
    have factor : (0 : F) < n * m * (p * q) := by positivity
    have inner : ((m : F) - 1) * q * (1 - p) + ((n : F) - 1) * p * (1 - q) = 0 := by
      rcases mul_eq_zero.1 excess with h | h
      · exact absurd h factor.ne'
      · exact h
    have m1 : (0 : F) ≤ (m : F) - 1 := by
      have : (1 : F) ≤ m := by exact_mod_cast hm
      linarith
    have n1 : (0 : F) ≤ (n : F) - 1 := by
      have : (1 : F) ≤ n := by exact_mod_cast hn
      linarith
    have a : 0 ≤ ((m : F) - 1) * q * (1 - p) := by
      have : 0 < 1 - p := by linarith
      positivity
    have b : 0 ≤ ((n : F) - 1) * p * (1 - q) := by
      have : 0 < 1 - q := by linarith
      positivity
    have aZero : ((m : F) - 1) * q * (1 - p) = 0 := by linarith
    have bZero : ((n : F) - 1) * p * (1 - q) = 0 := by linarith
    have mEq : (m : F) - 1 = 0 := by
      rcases mul_eq_zero.1 aZero with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · exact h'
        · exact absurd h' hq.ne'
      · exact absurd h (by linarith)
    have nEq : (n : F) - 1 = 0 := by
      rcases mul_eq_zero.1 bZero with h | h
      · rcases mul_eq_zero.1 h with h' | h'
        · exact h'
        · exact absurd h' hp.ne'
      · exact absurd h (by linarith)
    constructor
    · exact_mod_cast (sub_eq_zero.1 nEq)
    · exact_mod_cast (sub_eq_zero.1 mEq)
  · rintro ⟨rfl, rfl⟩
    simp

end Field

/-! ## Controls -/

namespace Controls

/-- **All four pairs positive**: probability `1/16` from two fair samples on each
side, against `1/256` for four independent samples of the conjunction. -/
theorem all_pairs_positive :
    expect (1 / 2 : ℚ) 2 (fun s => expect (1 / 2 : ℚ) 2
        (fun t => if positives s * positives t = 4 then 1 else 0)) = 1 / 16 ∧
      expect (1 / 4 : ℚ) 4 (fun s => if positives s = 4 then 1 else 0) = 1 / 256 := by
  constructor <;> norm_num [expect, positives]

/-- **The effective sample size at `p = q = 1/2`**: the number `N` of independent
joint samples with the variance of the paired estimator satisfies
`N · pairedVariance = n⁴ · (1/4) (3/4)`, and `N = 3 n² / (2 n + 1)`. -/
theorem effective_size_half (n : ℕ) :
    (3 * n ^ 2 / (2 * n + 1) : ℚ) * pairedVariance (1 / 2) (1 / 2) n n =
      (n * n : ℚ) ^ 2 * ((1 / 4) * (1 - 1 / 4)) := by
  rw [paired_variance, joint_variance]
  have : (0 : ℚ) < 2 * n + 1 := by positivity
  push_cast
  field_simp
  ring

end Controls

end Mettapedia.PLN.WorldModel.PairedSampleDispersion
