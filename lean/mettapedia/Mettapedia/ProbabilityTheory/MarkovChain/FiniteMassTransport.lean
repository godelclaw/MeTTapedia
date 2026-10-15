import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mettapedia.ProbabilityTheory.MarkovChain.Restart

/-!
# Finite conservative transport over nonnegative kernels

A normalized outgoing row redistributes attention; a dangling row keeps its
attention. Every iteration applies the complete supplied kernel. Reachability expands
monotonically with iteration count, while individual scores need not.

These are exact-real laws. They neither certify floating-point arithmetic nor
identify attention with probability, evidential confidence or proof validity.
Conservation does not imply immunity to duplicate-edge bias: a canary below
exhibits two conservative kernels with different routing.
-/

noncomputable section

namespace Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport

open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι]

/-- Mathlib's row-stochastic submonoid is the canonical kernel representation. -/
abbrev Kernel (ι : Type*) [Fintype ι] := ↥(Matrix.rowStochastic ℝ ι)

def Kernel.share (P : Kernel ι) : Matrix ι ι ℝ := P.val

theorem Kernel.nonneg (P : Kernel ι) (i j : ι) : 0 ≤ Kernel.share P i j :=
  Matrix.nonneg_of_mem_rowStochastic P.property

theorem Kernel.row_sum (P : Kernel ι) (i : ι) : ∑ j, Kernel.share P i j = 1 :=
  Matrix.sum_row_of_mem_rowStochastic P.property i

/-- Composed rounds remain stochastic by the existing submonoid laws. -/
theorem Kernel.power_stochastic (P : Kernel ι) (n : ℕ) :
    ((P ^ n : Kernel ι) : Matrix ι ι ℝ) ∈ Matrix.rowStochastic ℝ ι := (P ^ n).property

def normalize (w : ι → ι → ℝ) (i j : ι) : ℝ :=
  if (∑ k, w i k) = 0 then (if i = j then 1 else 0)
  else w i j / ∑ k, w i k

theorem normalize_nonneg (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j) (i j : ι) :
    0 ≤ normalize w i j := by
  unfold normalize
  split
  · split <;> norm_num
  · exact div_nonneg (hw i j) (Finset.sum_nonneg fun k _ => hw i k)

theorem normalize_row_sum (w : ι → ι → ℝ) (i : ι) :
    ∑ j, normalize w i j = 1 := by
  by_cases h : (∑ k, w i k) = 0
  · simp [normalize, h]
  · simp only [normalize, h, if_false]
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ h

def kernel (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j) : Kernel ι :=
  ⟨normalize w, Matrix.mem_rowStochastic_iff_sum.mpr
    ⟨normalize_nonneg w hw, normalize_row_sum w⟩⟩

def mass (s : ι → ℝ) : ℝ := ∑ i, s i

def transport (P : Kernel ι) (s : ι → ℝ) (j : ι) : ℝ :=
  ∑ i, s i * Kernel.share P i j

theorem transport_mass (P : Kernel ι) (s : ι → ℝ) :
    mass (transport P s) = mass s := by
  unfold mass transport
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, Kernel.row_sum P, mul_one]

theorem transport_nonneg (P : Kernel ι) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) :
    ∀ j, 0 ≤ transport P s j := by
  intro j
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hs i) (Kernel.nonneg P i j)

theorem transport_mono (P : Kernel ι) (s t : ι → ℝ) (h : ∀ i, s i ≤ t i) :
    ∀ j, transport P s j ≤ transport P t j := by
  intro j
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (Kernel.nonneg P i j)

def step (P : Kernel ι) (d : ℝ) (s : ι → ℝ) (j : ι) : ℝ :=
  (1 - d) * s j + d * transport P s j

@[simp] theorem step_disabled (P : Kernel ι) (s : ι → ℝ) : step P 0 s = s := by
  funext j
  simp [step]

theorem step_mass (P : Kernel ι) (d : ℝ) (s : ι → ℝ) :
    mass (step P d s) = mass s := by
  simp only [mass, step, Finset.sum_add_distrib, ← Finset.mul_sum]
  change (1 - d) * mass s + d * mass (transport P s) = mass s
  rw [transport_mass]
  ring

theorem step_nonneg (P : Kernel ι) (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) : ∀ j, 0 ≤ step P d s j := by
  intro j
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hd1) (hs j))
    (mul_nonneg hd0 (transport_nonneg P s hs j))

def rounds (P : Kernel ι) (d : ℝ) : ℕ → (ι → ℝ) → (ι → ℝ)
  | 0, s => s
  | n + 1, s => step P d (rounds P d n s)

theorem rounds_mass (P : Kernel ι) (d : ℝ) (n : ℕ) (s : ι → ℝ) :
    mass (rounds P d n s) = mass s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rounds, step_mass, ih]

theorem rounds_nonneg (P : Kernel ι) (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (n : ℕ) (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) :
    ∀ j, 0 ≤ rounds P d n s j := by
  induction n with
  | zero => exact hs
  | succ n ih => exact step_nonneg P d hd0 hd1 _ ih

/-- The discovered set is cumulative; ranking is a separate, revisable view. -/
def reachable (P : Kernel ι) (seed : Set ι) : ℕ → Set ι
  | 0 => seed
  | n + 1 => reachable P seed n ∪ {j | ∃ i ∈ reachable P seed n, Kernel.share P i j ≠ 0}

theorem reachable_mono (P : Kernel ι) (seed : Set ι) (n : ℕ) :
    reachable P seed n ⊆ reachable P seed (n + 1) := Set.subset_union_left

theorem rounds_zero_outside_reachable (P : Kernel ι) (d : ℝ)
    (seed : Set ι) (s : ι → ℝ) (hs : ∀ i, i ∉ seed → s i = 0) (n : ℕ) :
    ∀ j, j ∉ reachable P seed n → rounds P d n s j = 0 := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    intro j hj
    have hprev : j ∉ reachable P seed n := fun h => hj (Or.inl h)
    have hin : ¬ ∃ i ∈ reachable P seed n, Kernel.share P i j ≠ 0 :=
      fun h => hj (Or.inr h)
    have hz : transport P (rounds P d n s) j = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i ∈ reachable P seed n
      · have hshare : Kernel.share P i j = 0 := by
          by_contra h
          exact hin ⟨i, hi, h⟩
        simp [hshare]
      · simp [ih i hi]
    simp [rounds, step, ih j hprev, hz]

/-- Explicit finite l1 distance; the default function norm would be the sup norm. -/
def distance (s t : ι → ℝ) : ℝ := ∑ i, |s i - t i|

theorem transport_distance (P : Kernel ι) (s t : ι → ℝ) :
    distance (transport P s) (transport P t) ≤ distance s t := by
  have hpoint : ∀ j, |transport P s j - transport P t j| ≤
      ∑ i, |s i - t i| * Kernel.share P i j := by
    intro j
    have heq : transport P s j - transport P t j =
        ∑ i, (s i - t i) * Kernel.share P i j := by
      simp [transport, sub_mul, Finset.sum_sub_distrib]
    rw [heq]
    calc
      |∑ i, (s i - t i) * Kernel.share P i j| ≤ ∑ i, |(s i - t i) * Kernel.share P i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |s i - t i| * Kernel.share P i j := by
        simp_rw [abs_mul, abs_of_nonneg (Kernel.nonneg P _ _)]
  calc
    distance (transport P s) (transport P t) ≤ ∑ j, ∑ i, |s i - t i| * Kernel.share P i j :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = distance s t := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, Kernel.row_sum P, mul_one]
      rfl

/-- `a` is continuation mass; restart mass is `1-a`. This is a scoring process. -/
def restart (P : Kernel ι) (a : ℝ) (u s : ι → ℝ) (j : ι) : ℝ :=
  (1 - a) * u j + a * transport P s j

theorem restart_distance (P : Kernel ι) (a : ℝ) (ha : 0 ≤ a) (u s t : ι → ℝ) :
    distance (restart P a u s) (restart P a u t) ≤ a * distance s t := by
  have heq : distance (restart P a u s) (restart P a u t) =
      a * distance (transport P s) (transport P t) := by
    unfold distance
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have h : restart P a u s j - restart P a u t j =
        a * (transport P s j - transport P t j) := by unfold restart; ring
    rw [h, abs_mul, abs_of_nonneg ha]
  rw [heq]
  exact mul_le_mul_of_nonneg_left (transport_distance P s t) ha

def restartRounds (P : Kernel ι) (a : ℝ) (u : ι → ℝ) : ℕ → (ι → ℝ) → (ι → ℝ)
  | 0, s => s
  | n + 1, s => restart P a u (restartRounds P a u n s)

/-- A finite-round bound conditional on the supplied target being a fixed point.
This is not an assertion that an arbitrary observed candidate is a fixed point. -/
theorem restart_error_bound (P : Kernel ι) (a : ℝ) (ha : 0 ≤ a) (u s target : ι → ℝ)
    (hfixed : restart P a u target = target) (n : ℕ) :
    distance (restartRounds P a u n s) target ≤ a ^ n * distance s target := by
  induction n with
  | zero => simp [restartRounds]
  | succ n ih =>
    calc
      distance (restartRounds P a u (n + 1) s) target =
          distance (restart P a u (restartRounds P a u n s)) (restart P a u target) := by
            rw [hfixed]; rfl
      _ ≤ a * distance (restartRounds P a u n s) target := restart_distance P a ha _ _ _
      _ ≤ a * (a ^ n * distance s target) := mul_le_mul_of_nonneg_left ih ha
      _ = a ^ (n + 1) * distance s target := by rw [pow_succ]; ring

/-- Adapt outgoing rows to the existing column-oriented restarting-walk theory.
`a` denotes continuation mass here, so the walk's restart probability is `1-a`. -/
def restartingWalk (P : Kernel ι) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Mettapedia.ProbabilityTheory.MarkovChain.Restart.RestartWalk ι where
  P j i := Kernel.share P i j
  nonneg j i := Kernel.nonneg P i j
  col_le i := (Kernel.row_sum P i).le
  α := 1 - a
  α_pos := sub_pos.mpr ha1
  α_le := by linarith

theorem restart_eq_walk_step (P : Kernel ι) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (u s : ι → ℝ) : restart P a u s = (restartingWalk P a ha0 ha1).step u s := by
  funext j
  simp [restart, restartingWalk, Restart.RestartWalk.step, transport,
    Matrix.mulVec, dotProduct, mul_comm]

/-- Existence and uniqueness reuse the established finite-dimensional resolvent proof. -/
theorem restart_has_unique_fixed_point (P : Kernel ι) (a : ℝ) (ha0 : 0 ≤ a)
    (ha1 : a < 1) (u : ι → ℝ) : ∃! s, restart P a u s = s := by
  let W := restartingWalk P a ha0 ha1
  refine ⟨W.ppr u, ?_, ?_⟩
  · change restart P a u (W.ppr u) = W.ppr u
    rw [restart_eq_walk_step P a ha0 ha1]
    exact W.ppr_fixed u
  · intro s hs
    rw [restart_eq_walk_step P a ha0 ha1] at hs
    exact W.ppr_unique hs

/-- Idempotent edge replacement belongs to the keyed store, not conservation. -/
def setEdge (w : (ι × ι) → ℝ) (edge : ι × ι) (value : ℝ) : (ι × ι) → ℝ :=
  Function.update w edge value

omit [Fintype ι] in
theorem setEdge_idempotent (w : (ι × ι) → ℝ) (edge : ι × ι) (value : ℝ) :
    setEdge (setEdge w edge value) edge value = setEdge w edge value := by
  simp [setEdge]

/-- Adding a duplicate changes normalized routing even though both rows sum to one. -/
theorem duplicate_edge_bias :
    normalize (fun (_ : Fin 2) (_ : Fin 2) => 1) 0 0 = (1 / 2 : ℝ) ∧
    normalize (fun (_ : Fin 2) j => if j = 0 then 2 else 1) 0 0 = (2 / 3 : ℝ) := by
  norm_num [normalize, Fin.sum_univ_two]


end Mettapedia.ProbabilityTheory.MarkovChain.FiniteMassTransport
