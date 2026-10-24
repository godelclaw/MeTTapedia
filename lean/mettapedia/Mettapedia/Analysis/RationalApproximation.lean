import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Ordered rational approximation

A monotone sequence and its limit are analytic data. No algorithm for producing the
sequence is assumed. Lower and upper rational approximations are instances of the
same ordered carrier, using ordinary and dual orders respectively. Their endpoint
bounds and one-sided error specifications follow from monotone convergence.

Arithmetic constructions retain their supplied stage values. Nonnegative products
clip each factor at zero; no uniform bound on the functions is needed.
-/

namespace Mettapedia.Analysis

open Filter Topology

noncomputable section

/-- Approximation through an order-preserving interpretation, with its actual stages. -/
structure OrderApproximation {α Q R : Type*} [Preorder Q] [Preorder R]
    [TopologicalSpace R] (interpret : Q →o R) (f : α → R) where
  approx : α → ℕ → Q
  monotone : ∀ x, Monotone (approx x)
  tendsto : ∀ x, Tendsto (fun n => interpret (approx x n)) atTop (𝓝 (f x))

/-- Increasing rational stages converging to a real-valued function. -/
abbrev LowerApproximation {α : Type*} (f : α → ℝ) :=
  OrderApproximation (Rat.castOrderEmbedding (K := ℝ)).toOrderHom f

/-- Decreasing rational stages: the same construction in the dual orders. -/
noncomputable def UpperApproximation {α : Type*} (f : α → ℝ) :=
  OrderApproximation (Rat.castOrderEmbedding (K := ℝ)).toOrderHom.dual
    (OrderDual.toDual ∘ f)

@[simp] theorem rational_interpret (q : ℚ) :
    (Rat.castOrderEmbedding (K := ℝ)).toOrderHom q = (q : ℝ) := rfl

@[simp] theorem rational_interpret_dual (q : ℚᵒᵈ) :
    (Rat.castOrderEmbedding (K := ℝ)).toOrderHom.dual q =
      OrderDual.toDual ((OrderDual.ofDual q : ℚ) : ℝ) := rfl

/-- The bound-plus-error specification characterizes convergence of increasing stages. -/
theorem lower_spec_iff {a : ℕ → ℚ} {r : ℝ} (ha : Monotone a) :
    Tendsto (fun n => (a n : ℝ)) atTop (𝓝 r) ↔
      (∀ n, (a n : ℝ) ≤ r) ∧
        ∀ ε > 0, ∃ N, ∀ n ≥ N, r - (a n : ℝ) < ε := by
  constructor
  · intro h
    refine ⟨(Rat.castOrderEmbedding (K := ℝ)).monotone.comp ha |>.ge_of_tendsto h, ?_⟩
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 h).1 (r - ε) (sub_lt_self r hε))
    exact ⟨N, fun n hn => by linarith [hN n hn]⟩
  · rintro ⟨hb, hc⟩
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro l hl
      obtain ⟨N, hN⟩ := hc (r - l) (sub_pos.2 hl)
      exact eventually_atTop.2 ⟨N, fun n hn => by linarith [hN n hn]⟩
    · intro u hu
      exact Eventually.of_forall (fun n => lt_of_le_of_lt (hb n) hu)

/-- The dual bound-plus-error specification, without replacing the supplied stages. -/
theorem upper_spec_iff {a : ℕ → ℚ} {r : ℝ} (ha : Antitone a) :
    Tendsto (fun n => (a n : ℝ)) atTop (𝓝 r) ↔
      (∀ n, r ≤ (a n : ℝ)) ∧
        ∀ ε > 0, ∃ N, ∀ n ≥ N, (a n : ℝ) - r < ε := by
  constructor
  · intro h
    refine ⟨(Rat.castOrderEmbedding (K := ℝ)).monotone.comp_antitone ha |>.le_of_tendsto h, ?_⟩
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 h).2 (r + ε) (lt_add_of_pos_right r hε))
    exact ⟨N, fun n hn => by linarith [hN n hn]⟩
  · rintro ⟨hb, hc⟩
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro l hl
      exact Eventually.of_forall (fun n => lt_of_lt_of_le hl (hb n))
    · intro u hu
      obtain ⟨N, hN⟩ := hc (u - r) (sub_pos.2 hu)
      exact eventually_atTop.2 ⟨N, fun n hn => by linarith [hN n hn]⟩

namespace LowerApproximation

variable {α β : Type*} {f g : α → ℝ}

theorem approx_mono (hf : LowerApproximation f) (x : α) (n : ℕ) :
    hf.approx x n ≤ hf.approx x (n + 1) := hf.monotone x (Nat.le_succ n)

theorem approx_le (hf : LowerApproximation f) (x : α) (n : ℕ) :
    (hf.approx x n : ℝ) ≤ f x := (lower_spec_iff (hf.monotone x)).1 (hf.tendsto x) |>.1 n

theorem approx_converges (hf : LowerApproximation f) (x : α) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, f x - (hf.approx x n : ℝ) < ε :=
  (lower_spec_iff (hf.monotone x)).1 (hf.tendsto x) |>.2

/-- Construct analytic data from the equivalent one-sided specification. -/
noncomputable def of_bounds (a : α → ℕ → ℚ) (hm : ∀ x n, a x n ≤ a x (n + 1))
    (hb : ∀ x n, (a x n : ℝ) ≤ f x)
    (hc : ∀ x ε, 0 < ε → ∃ N, ∀ n ≥ N, f x - (a x n : ℝ) < ε) :
    LowerApproximation f where
  approx := a
  monotone x := monotone_nat_of_le_succ (hm x)
  tendsto x := (lower_spec_iff (monotone_nat_of_le_succ (hm x))).2 ⟨hb x, hc x⟩

end LowerApproximation

namespace UpperApproximation

variable {α : Type*} {f g : α → ℝ}

def approx (hf : UpperApproximation f) (x : α) (n : ℕ) : ℚ :=
  OrderDual.ofDual (OrderApproximation.approx hf x n)

theorem antitone (hf : UpperApproximation f) (x : α) : Antitone (hf.approx x) :=
  hf.monotone x

theorem converges (hf : UpperApproximation f) (x : α) :
    Tendsto (fun n => (hf.approx x n : ℝ)) atTop (𝓝 (f x)) := hf.tendsto x

theorem approx_anti (hf : UpperApproximation f) (x : α) (n : ℕ) :
    hf.approx x (n + 1) ≤ hf.approx x n := hf.antitone x (Nat.le_succ n)

theorem approx_ge (hf : UpperApproximation f) (x : α) (n : ℕ) :
    f x ≤ (hf.approx x n : ℝ) := (upper_spec_iff (hf.antitone x)).1 (hf.tendsto x) |>.1 n

theorem approx_converges (hf : UpperApproximation f) (x : α) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, (hf.approx x n : ℝ) - f x < ε :=
  (upper_spec_iff (hf.antitone x)).1 (hf.tendsto x) |>.2

noncomputable def of_bounds (a : α → ℕ → ℚ) (hm : ∀ x n, a x (n + 1) ≤ a x n)
    (hb : ∀ x n, f x ≤ (a x n : ℝ))
    (hc : ∀ x ε, 0 < ε → ∃ N, ∀ n ≥ N, (a x n : ℝ) - f x < ε) :
    UpperApproximation f where
  approx := a
  monotone x := antitone_nat_of_succ_le (hm x)
  tendsto x := (upper_spec_iff (antitone_nat_of_succ_le (hm x))).2 ⟨hb x, hc x⟩

end UpperApproximation

namespace LowerApproximation

variable {α β : Type*} {f g : α → ℝ}

/-- An exact rational constant, including signed constants. -/
noncomputable def const_rat (q : ℚ) : LowerApproximation (fun _ : α => (q : ℝ)) where
  approx _ _ := q
  monotone _ := monotone_const
  tendsto _ := tendsto_const_nhds

noncomputable def const_zero : LowerApproximation (fun _ : α => (0 : ℝ)) where
  approx _ _ := 0
  monotone _ := monotone_const
  tendsto _ := by simp

/-- Same-stage addition; no stage selection or change of approximation data. -/
noncomputable def add (hf : LowerApproximation f) (hg : LowerApproximation g) :
    LowerApproximation (f + g) where
  approx x n := hf.approx x n + hg.approx x n
  monotone x := (hf.monotone x).add (hg.monotone x)
  tendsto x := by simpa using (hf.tendsto x).add (hg.tendsto x)

noncomputable def const_smul_rat (c : ℚ) (hc : 0 ≤ c) (hf : LowerApproximation f) :
    LowerApproximation (fun x => (c : ℝ) * f x) where
  approx x n := c * hf.approx x n
  monotone x _ _ h := mul_le_mul_of_nonneg_left (hf.monotone x h) hc
  tendsto x := by simpa using (hf.tendsto x).const_mul (c : ℝ)

/-- Clipping is essential: two negative lower estimates can have an excessive product. -/
noncomputable def mul (hf : LowerApproximation f) (hg : LowerApproximation g)
    (hf_nn : ∀ x, 0 ≤ f x) (hg_nn : ∀ x, 0 ≤ g x) :
    LowerApproximation (fun x => f x * g x) where
  approx x n := max 0 (hf.approx x n) * max 0 (hg.approx x n)
  monotone x _ _ h := mul_le_mul
    (max_le_max le_rfl (hf.monotone x h)) (max_le_max le_rfl (hg.monotone x h))
    (le_max_left _ _) (le_max_left _ _)
  tendsto x := by
    simpa only [rational_interpret, Rat.cast_mul, Rat.cast_max, Rat.cast_zero, max_eq_right (hf_nn x),
      max_eq_right (hg_nn x)] using
      ((tendsto_const_nhds (x := (0 : ℝ))).max (hf.tendsto x)).mul
        ((tendsto_const_nhds (x := (0 : ℝ))).max (hg.tendsto x))

/-- Arbitrary precomposition preserves analytic approximation, without an effectivity claim. -/
noncomputable def comp {β : Type*} (hf : LowerApproximation f) (g : β → α) :
    LowerApproximation (f ∘ g) where
  approx x := hf.approx (g x)
  monotone x := hf.monotone (g x)
  tendsto x := hf.tendsto (g x)

/-- Negation exchanges lower and upper approximation. -/
noncomputable def neg (hf : LowerApproximation f) : UpperApproximation (-f) where
  approx x n := -hf.approx x n
  monotone x _ _ h := neg_le_neg (hf.monotone x h)
  tendsto x := by
    change Tendsto (fun n => ((-hf.approx x n : ℚ) : ℝ)) atTop (𝓝 (-f x))
    simpa using (hf.tendsto x).neg

/-- Lower stages minus upper stages converge from below. -/
noncomputable def sub (hf : LowerApproximation f) (hg : UpperApproximation g) :
    LowerApproximation (fun x => f x - g x) where
  approx x n := hf.approx x n - hg.approx x n
  monotone x _ _ h := sub_le_sub (hf.monotone x h) (hg.antitone x h)
  tendsto x := by simpa using (hf.tendsto x).sub (hg.converges x)

/-- Finite minima retain the minimum of the supplied rational stages. -/
noncomputable def finset_inf {ι : Type*} [Fintype ι] {f : ι → α → ℝ}
    (hf : ∀ i, LowerApproximation (f i)) (hne : Nonempty ι) :
    LowerApproximation (fun x => Finset.univ.inf' Finset.univ_nonempty (fun i => f i x)) where
  approx x n := Finset.univ.inf' Finset.univ_nonempty (fun i => (hf i).approx x n)
  monotone x _ _ h := Finset.le_inf' _ _ fun i hi =>
    (Finset.inf'_le _ hi).trans ((hf i).monotone x h)
  tendsto x := by
    have hcast (n : ℕ) := Finset.apply_inf'_eq_inf'_comp Finset.univ_nonempty
      (fun q : ℚ => (q : ℝ)) (fun p q => Rat.cast_min (K := ℝ) p q)
      (f := fun i => (hf i).approx x n)
    simp only [rational_interpret]
    simp_rw [hcast]
    exact Tendsto.finset_inf'_nhds_apply _ (fun i _ => (hf i).tendsto x)

noncomputable def list_sum {ι : Type*} {f : ι → α → ℝ}
    (hf : ∀ i, LowerApproximation (f i)) :
    (l : List ι) → LowerApproximation (fun x => (l.map (f · x)).sum)
  | [] => const_zero
  | i :: is => add (hf i) (list_sum hf is)

/-- Finite aggregation uses the same stage in every summand. -/
noncomputable def finset_sum_finset {ι : Type*} (s : Finset ι)
    {f : ι → α → ℝ} (hf : ∀ i, LowerApproximation (f i)) :
    LowerApproximation (fun x => ∑ i ∈ s, f i x) where
  approx x n := ∑ i ∈ s, (hf i).approx x n
  monotone x _ _ h := Finset.sum_le_sum fun i _ => (hf i).monotone x h
  tendsto x := by
    simpa using tendsto_finsetSum s (fun i _ => (hf i).tendsto x)

noncomputable def finset_sum {ι : Type*} [Fintype ι] {f : ι → α → ℝ}
    (hf : ∀ i, LowerApproximation (f i)) :
    LowerApproximation (fun x => ∑ i, f i x) := finset_sum_finset Finset.univ hf

/-- Analytic approximation of a nonnegative real constant. The rational candidates
are chosen between `max 0 (c - 1/(n+1))` and `c`, then accumulated by maxima.
This retains those candidates; it does not assert that they are computable. -/
noncomputable def const_nonneg (c : ℝ) (hc : 0 ≤ c) :
    LowerApproximation (fun _ : α => c) := by
  classical
  by_cases hc0 : c = 0
  · subst hc0
    exact const_zero
  have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  let lower (n : ℕ) : ℝ := max 0 (c - 1 / (n + 1 : ℝ))
  have hlower_lt (n : ℕ) : lower n < c := by
    exact max_lt hc_pos (sub_lt_self c (by positivity))
  let cand (n : ℕ) : ℚ := Classical.choose (exists_rat_btwn (hlower_lt n))
  have cand_spec (n : ℕ) : lower n < (cand n : ℝ) ∧ (cand n : ℝ) < c :=
    Classical.choose_spec (exists_rat_btwn (hlower_lt n))
  let q (n : ℕ) : ℚ :=
    Nat.rec (max 0 (cand 0)) (fun n qn => max qn (max 0 (cand (n + 1)))) n
  have hm (n : ℕ) : q n ≤ q (n + 1) := by
    simpa only [q, Nat.rec_add_one] using le_max_left (q n) (max 0 (cand (n + 1)))
  have hq_cand (n : ℕ) : cand n ≤ q n := by
    cases n with
    | zero => exact le_max_right _ _
    | succ n => exact (le_max_right 0 (cand (n + 1))).trans (le_max_right _ _)
  have hq_lt (n : ℕ) : (Rat.cast (q n) : ℝ) < c := by
    induction n with
    | zero => simpa [q] using max_lt hc_pos (cand_spec 0).2
    | succ n ih => simpa [q] using max_lt ih (max_lt hc_pos (cand_spec (n + 1)).2)
  refine
    { approx := fun _ => q
      monotone := fun _ => monotone_nat_of_le_succ hm
      tendsto := fun _ => ?_ }
  have hl : Tendsto (fun n : ℕ => c - 1 / (n + 1 : ℝ)) atTop (𝓝 c) := by
    simpa using (tendsto_const_nhds (x := c)).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    (fun n => (le_max_right 0 _).trans
      ((cand_spec n).1.le.trans (Rat.cast_le.2 (hq_cand n))))
    (fun n => (hq_lt n).le)

theorem const_nonneg_nonneg (c : ℝ) (hc : 0 ≤ c) (x : α) (n : ℕ) :
    0 ≤ (const_nonneg c hc).approx x n := by
  classical
  by_cases hc0 : c = 0
  · subst hc0
    simp [const_nonneg, const_zero]
  · simp only [const_nonneg, dif_neg hc0]
    cases n with
    | zero => exact le_max_left _ _
    | succ n => exact (le_max_left 0 _).trans (le_max_right _ _)

/-- Scalar multiplication reuses the constant's actual rational sequence. -/
noncomputable def const_smul (c : ℝ) (hc : 0 ≤ c) (hf : LowerApproximation f)
    (hf_nn : ∀ x, 0 ≤ f x) : LowerApproximation (fun x => c * f x) :=
  mul (const_nonneg c hc) hf (fun _ => hc) hf_nn

theorem const_smul_approx (c : ℝ) (hc : 0 ≤ c) (hf : LowerApproximation f)
    (hf_nn : ∀ x, 0 ≤ f x) (x : α) (n : ℕ) :
    (const_smul c hc hf hf_nn).approx x n =
      (const_nonneg c hc).approx x n * max 0 (hf.approx x n) := by
  simp only [const_smul, mul, max_eq_right (const_nonneg_nonneg c hc x n)]

/-- Diagonal envelope of supplied approximations. Family monotonicity is unnecessary:
an upper bound and one-sided convergence of the family suffice. -/
noncomputable def diagonal_envelope {f_n : ℕ → α → ℝ}
    (hf_n : ∀ n, LowerApproximation (f_n n))
    (h_conv : ∀ x ε, 0 < ε → ∃ N, ∀ n ≥ N, f x - f_n n x < ε)
    (h_bound : ∀ n x, f_n n x ≤ f x) : LowerApproximation f :=
  of_bounds
    (fun x m => (Finset.range (m + 1)).sup' Finset.nonempty_range_add_one
      (fun n => (hf_n n).approx x m))
    (by
      intro x m
      apply Finset.sup'_le
      intro n hn
      exact ((hf_n n).approx_mono x m).trans
        (Finset.le_sup' (fun i => (hf_n i).approx x (m + 1))
          (by simp only [Finset.mem_range] at hn ⊢; omega)))
    (by
      intro x m
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
        (fun n => (hf_n n).approx x m)
      rw [hi]
      exact ((hf_n i).approx_le x m).trans (h_bound i x))
    (by
      intro x ε hε
      obtain ⟨N, hN⟩ := h_conv x (ε / 2) (half_pos hε)
      obtain ⟨M, hM⟩ := (hf_n N).approx_converges x (ε / 2) (half_pos hε)
      refine ⟨max N M, fun m hm => ?_⟩
      have hs := (Rat.cast_le (K := ℝ)).2 (Finset.le_sup' (fun i => (hf_n i).approx x m)
        (show N ∈ Finset.range (m + 1) by simp only [Finset.mem_range]; omega))
      have h1 := hN N le_rfl
      have h2 := hM m (le_of_max_le_right hm)
      linarith)

/-- Strict threshold observations stabilize along lower stages, even at equality.
The threshold is an arbitrary real parameter; this is an analytic construction. -/
noncomputable def indicator_lt (hf : LowerApproximation f) (t : ℝ) :
    LowerApproximation (fun x => if t < f x then (1 : ℝ) else 0) := by
  classical
  refine
    { approx := fun x n => if t < (hf.approx x n : ℝ) then 1 else 0
      monotone := ?_
      tendsto := ?_ }
  · intro x m n hmn
    by_cases hm : t < (hf.approx x m : ℝ)
    · have hn := hm.trans_le (Rat.cast_le.2 (hf.monotone x hmn))
      simp [hm, hn]
    · simp only [if_neg hm]
      split_ifs <;> norm_num
  · intro x
    change Tendsto (fun n => ((if t < (hf.approx x n : ℝ) then 1 else 0 : ℚ) : ℝ))
      atTop (𝓝 (if t < f x then 1 else 0))
    by_cases ht : t < f x
    · have he := (tendsto_order.1 (hf.tendsto x)).1 t ht
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      simp [ht, rational_interpret] at hn ⊢
      simp [hn]
    · have hn (n : ℕ) : ¬t < (hf.approx x n : ℝ) :=
        fun h => ht (h.trans_le (hf.approx_le x n))
      simpa only [if_neg ht, if_neg (hn _), Rat.cast_zero] using
        (tendsto_const_nhds (x := (0 : ℝ)))

end LowerApproximation

namespace UpperApproximation

variable {α β : Type*} {f g : α → ℝ}

noncomputable def add (hf : UpperApproximation f) (hg : UpperApproximation g) :
    UpperApproximation (fun x => f x + g x) where
  approx x n := hf.approx x n + hg.approx x n
  monotone x _ _ h := add_le_add (hf.antitone x h) (hg.antitone x h)
  tendsto x := by
    change Tendsto (fun n => ((hf.approx x n + hg.approx x n : ℚ) : ℝ))
      atTop (𝓝 (f x + g x))
    simpa using (hf.converges x).add (hg.converges x)

noncomputable def comp (hf : UpperApproximation f) (g : β → α) :
    UpperApproximation (f ∘ g) where
  approx x := hf.approx (g x)
  monotone x := hf.antitone (g x)
  tendsto x := hf.tendsto (g x)

noncomputable def neg (hf : UpperApproximation f) : LowerApproximation (-f) where
  approx x n := -hf.approx x n
  monotone x _ _ h := neg_le_neg (hf.antitone x h)
  tendsto x := by simpa using (hf.converges x).neg

end UpperApproximation

end

end Mettapedia.Analysis
