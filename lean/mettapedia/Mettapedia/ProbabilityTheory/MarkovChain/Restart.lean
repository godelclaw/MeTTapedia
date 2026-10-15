import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Personalized PageRank for associative recall

HippoRAG (arXiv 2405.14831) and HippoRAG 2 (arXiv 2502.14802) answer a query by
running Personalized PageRank over a memory graph. The seed puts mass on the
nodes the query mentions. In HippoRAG these are phrase nodes weighted by node
specificity. HippoRAG 2 adds passage nodes weighted by dense similarity. Both
papers use a damping factor of 0.5. Passages are then ranked by the mass the walk
leaves on them.

Here `P i j` is the probability of a step from node `j` to node `i`. Columns may
sum to less than one, which models mass lost at dangling nodes. With restart
probability `α ∈ (0, 1]` and seed `s`, one step maps `x` to `α s + (1 - α) P x`.

Main results:
* `step_contract`: one step contracts ℓ¹ distance by the factor `1 - α`.
* `ppr_fixed` and `ppr_unique`: the PPR vector is the unique fixed point.
* `ppr_add` and `ppr_smul`: it is linear in the seed.
* `iterate_error` and `iterate_error_dist` (quantitative): after `k` steps of
  power iteration the ℓ¹ error is at most `(1 - α)^k` times the initial error,
  and at most `2 (1 - α)^k` when seed and start are distributions. With
  `α = 1/2`, ten sparse matrix-vector products give an error below `0.002`.
* `ppr_nonneg`, `ppr_mono` and `passage_scores_mono`: a nonnegative seed gives
  nonnegative scores, a larger seed gives larger node scores, and passage scores
  aggregated with nonnegative weights follow.
* `ppr_mass` and `ppr_mass_le`: a stochastic walk conserves the seed's mass, and
  a substochastic walk does not increase it.
* `mass_outside_reach` (quantitative locality): the mass on nodes that the walk
  cannot reach from the seed within `k` steps is at most `(1 - α)^(k+1)` times
  the seed's mass. A bounded-hop computation therefore loses a controlled amount.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.MarkovChain.Restart

open Finset Matrix

variable {ι : Type*} [Fintype ι]

/-- A restarting random walk on a finite memory graph. -/
structure RestartWalk (ι : Type*) [Fintype ι] where
  /-- `P i j` is the probability of a step from node `j` to node `i`. -/
  P : Matrix ι ι ℝ
  nonneg : ∀ i j, 0 ≤ P i j
  col_le : ∀ j, ∑ i, P i j ≤ 1
  /-- The restart probability. -/
  α : ℝ
  α_pos : 0 < α
  α_le : α ≤ 1

/-- Total absolute mass, the ℓ¹ norm. -/
def l1 (x : ι → ℝ) : ℝ := ∑ i, |x i|

/-- Total signed mass. -/
def mass (x : ι → ℝ) : ℝ := ∑ i, x i

theorem l1_nonneg (x : ι → ℝ) : 0 ≤ l1 x := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem l1_eq_zero {x : ι → ℝ} : l1 x = 0 ↔ x = 0 := by
  unfold l1
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg _]
  simp [funext_iff]

theorem l1_smul (c : ℝ) (x : ι → ℝ) : l1 (c • x) = |c| * l1 x := by
  simp [l1, abs_mul, Finset.mul_sum]

theorem l1_sub_le (x y : ι → ℝ) : l1 (x - y) ≤ l1 x + l1 y := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => abs_sub _ _

theorem l1_of_nonneg {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) : l1 x = mass x := by
  simp [l1, mass, abs_of_nonneg (hx _)]

namespace RestartWalk

variable (W : RestartWalk ι)

theorem one_sub_α_nonneg : 0 ≤ 1 - W.α := by linarith [W.α_le]

/-- One step: restart at the seed with probability `α`, otherwise follow the walk. -/
def step (s x : ι → ℝ) : ι → ℝ := W.α • s + (1 - W.α) • (W.P *ᵥ x)

theorem mulVec_apply (x : ι → ℝ) (i : ι) : (W.P *ᵥ x) i = ∑ j, W.P i j * x j := rfl

/-- The walk does not increase ℓ¹ mass. -/
theorem l1_mulVec_le (x : ι → ℝ) : l1 (W.P *ᵥ x) ≤ l1 x := by
  unfold l1
  calc ∑ i, |(W.P *ᵥ x) i| = ∑ i, |∑ j, W.P i j * x j| := rfl
    _ ≤ ∑ i, ∑ j, W.P i j * |x j| := by
        apply Finset.sum_le_sum
        intro i _
        calc |∑ j, W.P i j * x j| ≤ ∑ j, |W.P i j * x j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j, W.P i j * |x j| := by
              apply Finset.sum_congr rfl
              intro j _
              rw [abs_mul, abs_of_nonneg (W.nonneg i j)]
    _ = ∑ j, (∑ i, W.P i j) * |x j| := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
    _ ≤ ∑ j, |x j| := by
        apply Finset.sum_le_sum
        intro j _
        calc (∑ i, W.P i j) * |x j| ≤ 1 * |x j| :=
              mul_le_mul_of_nonneg_right (W.col_le j) (abs_nonneg _)
          _ = |x j| := one_mul _

/-- On nonnegative vectors the walk does not increase mass. -/
theorem mass_mulVec_le {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) : mass (W.P *ᵥ x) ≤ mass x := by
  have hP : ∀ i, 0 ≤ (W.P *ᵥ x) i := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (W.nonneg i j) (hx j)
  rw [← l1_of_nonneg hx, ← l1_of_nonneg hP]
  exact W.l1_mulVec_le x

theorem mulVec_nonneg {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (i : ι) : 0 ≤ (W.P *ᵥ x) i :=
  Finset.sum_nonneg fun j _ => mul_nonneg (W.nonneg i j) (hx j)

/-- A stochastic walk conserves mass. -/
theorem mass_mulVec_of_stochastic (hcol : ∀ j, ∑ i, W.P i j = 1) (x : ι → ℝ) :
    mass (W.P *ᵥ x) = mass x := by
  unfold mass
  calc ∑ i, (W.P *ᵥ x) i = ∑ i, ∑ j, W.P i j * x j := rfl
    _ = ∑ j, (∑ i, W.P i j) * x j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
    _ = ∑ j, x j := by simp [hcol]

/-! ## Contraction and convergence -/

theorem step_sub (s x y : ι → ℝ) :
    W.step s x - W.step s y = (1 - W.α) • (W.P *ᵥ (x - y)) := by
  simp only [step, mulVec_sub, smul_sub]
  abel

/-- One step contracts ℓ¹ distance by the factor `1 - α`. -/
theorem step_contract (s x y : ι → ℝ) :
    l1 (W.step s x - W.step s y) ≤ (1 - W.α) * l1 (x - y) := by
  rw [step_sub, l1_smul, abs_of_nonneg W.one_sub_α_nonneg]
  exact mul_le_mul_of_nonneg_left (W.l1_mulVec_le _) W.one_sub_α_nonneg

theorem iterate_contract (s : ι → ℝ) (k : ℕ) (x y : ι → ℝ) :
    l1 ((W.step s)^[k] x - (W.step s)^[k] y) ≤ (1 - W.α) ^ k * l1 (x - y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc l1 (W.step s ((W.step s)^[k] x) - W.step s ((W.step s)^[k] y))
        ≤ (1 - W.α) * l1 ((W.step s)^[k] x - (W.step s)^[k] y) := W.step_contract s _ _
      _ ≤ (1 - W.α) * ((1 - W.α) ^ k * l1 (x - y)) :=
          mul_le_mul_of_nonneg_left ih W.one_sub_α_nonneg
      _ = (1 - W.α) ^ (k + 1) * l1 (x - y) := by ring

/-! ## The fixed point -/

/-- The linear operator `x ↦ x - (1 - α) P x`. -/
def resolvent : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := LinearMap.id - (1 - W.α) • W.P.mulVecLin

theorem resolvent_apply (x : ι → ℝ) : W.resolvent x = x - (1 - W.α) • (W.P *ᵥ x) := rfl

theorem resolvent_injective : Function.Injective W.resolvent := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [resolvent_apply, sub_eq_zero] at hx
  have hle : l1 x ≤ (1 - W.α) * l1 x := by
    calc l1 x = l1 ((1 - W.α) • (W.P *ᵥ x)) := by rw [← hx]
      _ = (1 - W.α) * l1 (W.P *ᵥ x) := by rw [l1_smul, abs_of_nonneg W.one_sub_α_nonneg]
      _ ≤ (1 - W.α) * l1 x := mul_le_mul_of_nonneg_left (W.l1_mulVec_le x) W.one_sub_α_nonneg
  have hzero : l1 x = 0 := by
    by_contra hne
    have hpos : 0 < l1 x := lt_of_le_of_ne (l1_nonneg x) (Ne.symm hne)
    have := mul_pos W.α_pos hpos
    linarith
  exact l1_eq_zero.mp hzero

/-- The resolvent is invertible on the finite-dimensional space of scores. -/
noncomputable def resolventEquiv : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.ofInjectiveEndo W.resolvent W.resolvent_injective

/-- The personalized PageRank vector of seed `s`. -/
noncomputable def ppr (s : ι → ℝ) : ι → ℝ := W.resolventEquiv.symm (W.α • s)

theorem resolvent_ppr (s : ι → ℝ) : W.resolvent (W.ppr s) = W.α • s :=
  W.resolventEquiv.apply_symm_apply (W.α • s)

theorem step_eq_self_iff (s x : ι → ℝ) : W.step s x = x ↔ W.resolvent x = W.α • s := by
  rw [resolvent_apply, step]
  constructor
  · intro h
    nth_rewrite 1 [← h]
    abel
  · intro h
    rw [← h]
    abel

/-- The PPR vector is a fixed point of the step. -/
theorem ppr_fixed (s : ι → ℝ) : W.step s (W.ppr s) = W.ppr s :=
  (W.step_eq_self_iff s _).mpr (W.resolvent_ppr s)

/-- The fixed point is unique. -/
theorem ppr_unique {s x : ι → ℝ} (hx : W.step s x = x) : x = W.ppr s :=
  W.resolvent_injective (((W.step_eq_self_iff s x).mp hx).trans (W.resolvent_ppr s).symm)

theorem ppr_add (s t : ι → ℝ) : W.ppr (s + t) = W.ppr s + W.ppr t := by
  simp [ppr, smul_add]

theorem ppr_smul (c : ℝ) (s : ι → ℝ) : W.ppr (c • s) = c • W.ppr s := by
  simp [ppr, smul_comm W.α c s]

theorem ppr_sub (s t : ι → ℝ) : W.ppr (s - t) = W.ppr s - W.ppr t := by
  simp [ppr, smul_sub]

/-- Convergence of power iteration: the ℓ¹ error shrinks by `1 - α` per step. -/
theorem iterate_error (s x₀ : ι → ℝ) (k : ℕ) :
    l1 ((W.step s)^[k] x₀ - W.ppr s) ≤ (1 - W.α) ^ k * l1 (x₀ - W.ppr s) := by
  have h := W.iterate_contract s k x₀ (W.ppr s)
  rwa [Function.iterate_fixed (W.ppr_fixed s)] at h

/-! ## Positivity and mass -/

theorem ppr_apply (s : ι → ℝ) (i : ι) :
    W.ppr s i = W.α * s i + (1 - W.α) * ∑ j, W.P i j * W.ppr s j := by
  have h := congrFun (W.ppr_fixed s) i
  simp only [step, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [← h]
  rfl

/-- A nonnegative seed gives nonnegative scores. -/
theorem ppr_nonneg {s : ι → ℝ} (hs : ∀ i, 0 ≤ s i) (i : ι) : 0 ≤ W.ppr s i := by
  set x := W.ppr s with hx
  by_contra hneg
  rw [not_le] at hneg
  set N := Finset.univ.filter (fun i => x i < 0) with hN
  have hiN : i ∈ N := by simp [N, hneg]
  have hsum : ∑ j ∈ N, x j < 0 :=
    Finset.sum_neg (fun j hj => (Finset.mem_filter.mp hj).2) ⟨i, hiN⟩
  have hβ := W.one_sub_α_nonneg
  have key : (1 - W.α) * ∑ j ∈ N, x j ≤ ∑ j ∈ N, x j := by
    calc (1 - W.α) * ∑ j ∈ N, x j
        ≤ (1 - W.α) * ∑ j ∈ N, x j * ∑ i ∈ N, W.P i j := by
          apply mul_le_mul_of_nonneg_left _ hβ
          apply Finset.sum_le_sum
          intro j hj
          have hxj : x j < 0 := (Finset.mem_filter.mp hj).2
          have hcol : ∑ i ∈ N, W.P i j ≤ 1 :=
            le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ N)
              fun i _ _ => W.nonneg i j) (W.col_le j)
          nlinarith
      _ = (1 - W.α) * ∑ i ∈ N, ∑ j ∈ N, W.P i j * x j := by
          congr 1
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ ≤ (1 - W.α) * ∑ i ∈ N, ∑ j, W.P i j * x j := by
          apply mul_le_mul_of_nonneg_left _ hβ
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ N)
          intro j _ hjN
          have : 0 ≤ x j := by
            simp only [N, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hjN
            exact hjN
          exact mul_nonneg (W.nonneg i j) this
      _ = ∑ i ∈ N, (1 - W.α) * ∑ j, W.P i j * x j := by rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ N, x i := by
          apply Finset.sum_le_sum
          intro i _
          rw [hx, W.ppr_apply s i]
          have := mul_nonneg W.α_pos.le (hs i)
          linarith
  have := mul_neg_of_pos_of_neg W.α_pos hsum
  linarith

/-- A larger seed gives larger scores everywhere. -/
theorem ppr_mono {s t : ι → ℝ} (h : ∀ i, s i ≤ t i) (i : ι) : W.ppr s i ≤ W.ppr t i := by
  have := W.ppr_nonneg (s := t - s) (fun i => sub_nonneg.mpr (h i)) i
  rw [W.ppr_sub, Pi.sub_apply] at this
  linarith

/-- HippoRAG ranks passages by `M π`, where `M p i` counts the occurrences of
node `i` in passage `p`. Any nonnegative aggregation of this kind keeps the
ranking monotone in the seed. -/
theorem passage_scores_mono {π : Type*} (M : Matrix π ι ℝ) (hM : ∀ p i, 0 ≤ M p i)
    {s t : ι → ℝ} (h : ∀ i, s i ≤ t i) (p : π) : (M *ᵥ W.ppr s) p ≤ (M *ᵥ W.ppr t) p :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (W.ppr_mono h i) (hM p i)

theorem mass_ppr_eq (s : ι → ℝ) :
    mass (W.ppr s) = W.α * mass s + (1 - W.α) * mass (W.P *ᵥ W.ppr s) := by
  have h := W.ppr_fixed s
  unfold mass
  conv_lhs => rw [← h]
  simp [step, Finset.sum_add_distrib, Finset.mul_sum]

/-- A stochastic walk conserves the seed's mass. -/
theorem ppr_mass (hcol : ∀ j, ∑ i, W.P i j = 1) (s : ι → ℝ) : mass (W.ppr s) = mass s := by
  have h := W.mass_ppr_eq s
  rw [W.mass_mulVec_of_stochastic hcol] at h
  have : W.α * mass (W.ppr s) = W.α * mass s := by linarith
  exact mul_left_cancel₀ W.α_pos.ne' this

/-- A substochastic walk does not increase the mass of a nonnegative seed. -/
theorem ppr_mass_le {s : ι → ℝ} (hs : ∀ i, 0 ≤ s i) : mass (W.ppr s) ≤ mass s := by
  have h := W.mass_ppr_eq s
  have hle := W.mass_mulVec_le (W.ppr_nonneg hs)
  have : W.α * mass (W.ppr s) ≤ W.α * mass s := by
    nlinarith [W.one_sub_α_nonneg]
  exact le_of_mul_le_mul_left this W.α_pos

/-- When the seed and the starting vector are distributions, `k` steps of power
iteration leave an ℓ¹ error of at most `2 (1 - α)^k`. -/
theorem iterate_error_dist {s x₀ : ι → ℝ} (hs : ∀ i, 0 ≤ s i) (hs1 : mass s = 1)
    (hx : ∀ i, 0 ≤ x₀ i) (hx1 : mass x₀ = 1) (k : ℕ) :
    l1 ((W.step s)^[k] x₀ - W.ppr s) ≤ 2 * (1 - W.α) ^ k := by
  have h0 : l1 (x₀ - W.ppr s) ≤ 2 := by
    calc l1 (x₀ - W.ppr s) ≤ l1 x₀ + l1 (W.ppr s) := l1_sub_le _ _
      _ = mass x₀ + mass (W.ppr s) := by
          rw [l1_of_nonneg hx, l1_of_nonneg (W.ppr_nonneg hs)]
      _ ≤ 1 + 1 := by rw [hx1]; linarith [W.ppr_mass_le hs]
      _ = 2 := by norm_num
  calc l1 ((W.step s)^[k] x₀ - W.ppr s) ≤ (1 - W.α) ^ k * l1 (x₀ - W.ppr s) :=
        W.iterate_error s x₀ k
    _ ≤ (1 - W.α) ^ k * 2 :=
        mul_le_mul_of_nonneg_left h0 (pow_nonneg W.one_sub_α_nonneg k)
    _ = 2 * (1 - W.α) ^ k := mul_comm _ _

/-! ## Locality -/

variable [DecidableEq ι]

theorem pow_mulVec_nonneg {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (t : ℕ) (i : ι) :
    0 ≤ ((W.P ^ t) *ᵥ x) i := by
  induction t generalizing i with
  | zero => simpa using hx i
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec]
    exact W.mulVec_nonneg (fun j => ih j) i

theorem mass_pow_mulVec_le {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (t : ℕ) :
    mass ((W.P ^ t) *ᵥ x) ≤ mass x := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← mulVec_mulVec]
    exact le_trans (W.mass_mulVec_le (W.pow_mulVec_nonneg hx t)) ih

/-- One more step of unrolling: the remainder after `n` steps splits into the
walk's `n`-th step from the seed and a remainder after `n + 1` steps. -/
theorem ppr_tail (s : ι → ℝ) (n : ℕ) :
    (1 - W.α) ^ n • ((W.P ^ n) *ᵥ W.ppr s) =
      (W.α * (1 - W.α) ^ n) • ((W.P ^ n) *ᵥ s) +
        (1 - W.α) ^ (n + 1) • ((W.P ^ (n + 1)) *ᵥ W.ppr s) := by
  have hx : W.ppr s = W.α • s + (1 - W.α) • (W.P *ᵥ W.ppr s) := (W.ppr_fixed s).symm
  conv_lhs => rw [hx]
  rw [mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec, ← pow_succ, smul_add, smul_smul,
    smul_smul, mul_comm ((1 - W.α) ^ n) W.α, ← pow_succ]

/-- Unrolling the fixed point `k + 1` times: the walk's first `k` steps from the
seed, plus a remainder weighted by `(1 - α)^(k+1)`. -/
theorem ppr_unroll (s : ι → ℝ) (k : ℕ) :
    W.ppr s = ∑ t ∈ range (k + 1), (W.α * (1 - W.α) ^ t) • ((W.P ^ t) *ᵥ s) +
      (1 - W.α) ^ (k + 1) • ((W.P ^ (k + 1)) *ᵥ W.ppr s) := by
  induction k with
  | zero => simpa [Finset.sum_range_one] using W.ppr_tail s 0
  | succ k ih =>
    rw [Finset.sum_range_succ, add_assoc, ← W.ppr_tail s (k + 1)]
    exact ih

/-- The nodes that a walk from the seed reaches with nonzero mass within `k` steps. -/
noncomputable def reach (s : ι → ℝ) (k : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => ∃ t ∈ range (k + 1), ((W.P ^ t) *ᵥ s) i ≠ 0)

theorem not_mem_reach {s : ι → ℝ} {k : ℕ} {i : ι} (h : i ∉ W.reach s k) :
    ∀ t ∈ range (k + 1), ((W.P ^ t) *ᵥ s) i = 0 := by
  classical
  intro t ht
  by_contra hne
  apply h
  simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and]
  convert (⟨t, ht, hne⟩ : ∃ t ∈ range (k + 1), ((W.P ^ t) *ᵥ s) i ≠ 0)

/-- Locality: the mass of the PPR vector outside the `k`-step reach of the seed
is at most `(1 - α)^(k+1)` times the seed's mass. -/
theorem mass_outside_reach {s : ι → ℝ} (hs : ∀ i, 0 ≤ s i) (k : ℕ) :
    ∑ i ∈ (W.reach s k)ᶜ, W.ppr s i ≤ (1 - W.α) ^ (k + 1) * mass s := by
  set x := W.ppr s
  have hx : ∀ i, 0 ≤ x i := W.ppr_nonneg hs
  have hout : ∀ i ∈ (W.reach s k)ᶜ,
      x i = (1 - W.α) ^ (k + 1) * ((W.P ^ (k + 1)) *ᵥ x) i := by
    intro i hi
    have hz := W.not_mem_reach (Finset.mem_compl.mp hi)
    have h := congrFun (W.ppr_unroll s k) i
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    rw [Finset.sum_eq_zero (fun t ht => by rw [hz t ht, mul_zero])] at h
    simpa using h
  calc ∑ i ∈ (W.reach s k)ᶜ, x i
      = ∑ i ∈ (W.reach s k)ᶜ, (1 - W.α) ^ (k + 1) * ((W.P ^ (k + 1)) *ᵥ x) i :=
        Finset.sum_congr rfl hout
    _ = (1 - W.α) ^ (k + 1) * ∑ i ∈ (W.reach s k)ᶜ, ((W.P ^ (k + 1)) *ᵥ x) i := by
        rw [Finset.mul_sum]
    _ ≤ (1 - W.α) ^ (k + 1) * mass ((W.P ^ (k + 1)) *ᵥ x) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg W.one_sub_α_nonneg _)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun i _ _ => W.pow_mulVec_nonneg hx (k + 1) i
    _ ≤ (1 - W.α) ^ (k + 1) * mass x :=
        mul_le_mul_of_nonneg_left (W.mass_pow_mulVec_le hx (k + 1))
          (pow_nonneg W.one_sub_α_nonneg _)
    _ ≤ (1 - W.α) ^ (k + 1) * mass s :=
        mul_le_mul_of_nonneg_left (W.ppr_mass_le hs) (pow_nonneg W.one_sub_α_nonneg _)

end RestartWalk

end Mettapedia.ProbabilityTheory.MarkovChain.Restart
