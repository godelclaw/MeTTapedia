import Mettapedia.Algorithms.Retrieval.RetrievalContract
import Mettapedia.ProbabilityTheory.MarkovChain.Restart
import Mathlib.Data.Finset.SymmDiff

/-!
# Top-k utility, approximation regret, and observable stopping certificates

The utility `q i` may be a probability of needing item `i`: then its sum is
expected useful hits, with no independence assumption. The algebra also holds
for arbitrary real utility. Calibration to utility is an explicit hypothesis,
not a consequence of convergence. Strict-gap certificates need not fire at ties.
-/

noncomputable section
namespace Mettapedia.Algorithms.Retrieval.TopKSelection
open scoped BigOperators symmDiff
open Mettapedia.ProbabilityTheory.MarkovChain.Restart
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact cardinality, using the existing retrieval top-k contract on all items. -/
def IsTopK (a : ι → ℝ) (T : Finset ι) (k : ℕ) : Prop :=
  T.card = k ∧ RetrievalContract.IsTopK a k Finset.univ T

omit [DecidableEq ι] in
theorem isTopK_iff (a : ι → ℝ) (T : Finset ι) (k : ℕ) :
    IsTopK a T k ↔ T.card = k ∧ ∀ i ∈ T, ∀ j ∉ T, a j ≤ a i := by
  constructor
  · rintro ⟨hc, _, _, hd⟩
    exact ⟨hc, fun i hi j hj => hd i hi j (Finset.mem_univ j) hj⟩
  · rintro ⟨hc, hd⟩
    refine ⟨hc, Finset.subset_univ _, ?_, fun i hi j _ hj => hd i hi j hj⟩
    have := Finset.card_le_card (Finset.subset_univ T)
    omega

omit [Fintype ι] [DecidableEq ι] in
/-- A coordinatewise perturbation smaller than half the separating margin
preserves every selected/unselected strict comparison. -/
theorem topk_frozen (x y : ι → ℝ) (T : Finset ι) (e : ℝ)
    (hmargin : ∀ i ∈ T, ∀ j ∉ T, 2 * e < x i - x j)
    (herr : ∀ i, |x i - y i| ≤ e) :
    ∀ i ∈ T, ∀ j ∉ T, y j < y i := by
  intro i hi j hj
  have h1 := abs_le.mp (herr i)
  have h2 := abs_le.mp (herr j)
  have hg := hmargin i hi j hj
  linarith

omit [DecidableEq ι] in
/-- The observed new-vector margin and last change certify its exact PPR top-k.
No theorem asserts finite termination without a separating gap. -/
theorem certified_topk (W : RestartWalk ι) (s x : ι → ℝ) (T : Finset ι) (k : ℕ)
    (hcard : T.card = k)
    (hmargin : ∀ i ∈ T, ∀ j ∉ T,
      2 * ((1 - W.α) / W.α * l1 (W.step s x - x)) < W.step s x i - W.step s x j) :
    IsTopK (W.ppr s) T k := by
  apply (isTopK_iff _ _ _).mpr
  refine ⟨hcard, fun i hi j hj => le_of_lt ?_⟩
  apply topk_frozen (W.step s x) (W.ppr s) T _ hmargin _ i hi j hj
  intro z
  exact (abs_coordinate_le_l1 (W.step s x - W.ppr s) z).trans (W.next_error_le s x)

omit [DecidableEq ι] in
/-- Positive score rescaling preserves the selection. -/
theorem topk_scale (a : ι → ℝ) (T : Finset ι) (k : ℕ) (c : ℝ) (hc : 0 < c)
    (h : IsTopK a T k) : IsTopK (c • a) T k := by
  rw [isTopK_iff] at h ⊢
  exact ⟨h.1, fun i hi j hj => mul_le_mul_of_nonneg_left (h.2 i hi j hj) hc.le⟩

private theorem sum_sdiff_score_le (a : ι → ℝ) (T O : Finset ι) (k : ℕ)
    (hT : IsTopK a T k) (hO : O.card = k) :
    ∑ i ∈ O \ T, a i ≤ ∑ i ∈ T \ O, a i := by
  have hc : (O \ T).card = (T \ O).card := Finset.card_sdiff_comm (hO.trans hT.1.symm)
  by_cases hn : (T \ O).Nonempty
  · obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image (T \ O) a hn
    calc
      ∑ i ∈ O \ T, a i ≤ ∑ _i ∈ O \ T, a z := by
        apply Finset.sum_le_sum
        intro i hi
        exact ((isTopK_iff _ _ _).mp hT).2 z (Finset.mem_sdiff.mp hz).1 i
          (Finset.mem_sdiff.mp hi).2
      _ = ∑ _i ∈ T \ O, a z := by simp [hc]
      _ ≤ ∑ i ∈ T \ O, a i := Finset.sum_le_sum fun i hi => hmin i hi
  · have he : T \ O = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have he' : O \ T = ∅ := Finset.card_eq_zero.mp (by simpa [he] using hc)
    simp [he, he']

/-- Only errors on exchanged items contribute to top-k regret. -/
theorem topk_regret_le_symmDiff (q a : ι → ℝ) (T O : Finset ι) (k : ℕ)
    (hT : IsTopK a T k) (hO : O.card = k) :
    (∑ i ∈ O, q i) - ∑ i ∈ T, q i ≤ ∑ i ∈ T ∆ O, |q i - a i| := by
  have hs := sum_sdiff_score_le a T O k hT hO
  have hq : (∑ i ∈ O, q i) - ∑ i ∈ T, q i =
      (∑ i ∈ O \ T, q i) - ∑ i ∈ T \ O, q i :=
    (Finset.sum_sdiff_sub_sum_sdiff (s₁ := T) (s₂ := O) (f := q)).symm
  have hd : Disjoint (T \ O) (O \ T) := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1)
  rw [hq, Finset.symmDiff_def, Finset.sum_union hd]
  have h1 : (∑ i ∈ O \ T, (q i - a i)) ≤ ∑ i ∈ O \ T, |q i - a i| :=
    Finset.sum_le_sum fun i _ => le_abs_self _
  have h2 : (∑ i ∈ T \ O, -(q i - a i)) ≤ ∑ i ∈ T \ O, |q i - a i| :=
    Finset.sum_le_sum fun i _ => neg_le_abs _
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at h1 h2
  linarith

/-- Utility mismatch in l1 bounds regret against every equal-size comparator. -/
theorem topk_regret_le_l1 (q a : ι → ℝ) (T O : Finset ι) (k : ℕ)
    (hT : IsTopK a T k) (hO : O.card = k) :
    (∑ i ∈ O, q i) - ∑ i ∈ T, q i ≤ l1 (q - a) := by
  exact (topk_regret_le_symmDiff q a T O k hT hO).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => abs_nonneg _))

theorem topk_regret_le_l1_scaled (q a : ι → ℝ) (T O : Finset ι) (k : ℕ)
    (c : ℝ) (hc : 0 < c) (hT : IsTopK a T k) (hO : O.card = k) :
    (∑ i ∈ O, q i) - ∑ i ∈ T, q i ≤ l1 (q - c • a) :=
  topk_regret_le_l1 q (c • a) T O k (topk_scale a T k c hc hT) hO

/-- Uniform error form; on a nonempty finite type take e to be the maximum error. -/
theorem topk_regret_le_uniform (q a : ι → ℝ) (T O : Finset ι) (k : ℕ)
    (e : ℝ) (he : 0 ≤ e) (herr : ∀ i, |q i - a i| ≤ e)
    (hT : IsTopK a T k) (hO : O.card = k) :
    (∑ i ∈ O, q i) - ∑ i ∈ T, q i ≤ 2 * k * e := by
  have hc : (T ∆ O).card ≤ 2 * k := by
    calc (T ∆ O).card ≤ (T ∪ O).card := Finset.card_le_card Finset.symmDiff_subset_union
      _ ≤ T.card + O.card := Finset.card_union_le _ _
      _ = 2 * k := by rw [hT.1, hO]; omega
  calc
    _ ≤ ∑ i ∈ T ∆ O, |q i - a i| := topk_regret_le_symmDiff q a T O k hT hO
    _ ≤ ∑ _i ∈ T ∆ O, e := Finset.sum_le_sum fun i _ => herr i
    _ = ((T ∆ O).card : ℝ) * e := by simp
    _ ≤ (2 * k : ℕ) * e := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) he
    _ = 2 * k * e := by push_cast; ring

/-- The explicit scaled l-infinity corollary. Nonemptiness is needed only to
write a finite maximum; the uniform-bound theorem also handles an empty type. -/
theorem topk_regret_le_max [Nonempty ι] (q a : ι → ℝ) (T O : Finset ι) (k : ℕ)
    (c : ℝ) (hc : 0 < c) (hT : IsTopK a T k) (hO : O.card = k) :
    (∑ i ∈ O, q i) - ∑ i ∈ T, q i ≤
      2 * k * Finset.univ.sup' Finset.univ_nonempty (fun i => |q i - c * a i|) := by
  let e := Finset.univ.sup' Finset.univ_nonempty (fun i => |q i - c * a i|)
  have he : 0 ≤ e := (abs_nonneg _).trans
    (Finset.le_sup' (fun i => |q i - c * a i|) (Finset.mem_univ (Classical.arbitrary ι)))
  exact topk_regret_le_uniform q (c • a) T O k e he
    (fun i => by simpa only [Pi.smul_apply, smul_eq_mul] using
      Finset.le_sup' (fun j => |q j - c * a j|) (Finset.mem_univ i))
    (topk_scale a T k c hc hT) hO

theorem calibrated_topk_optimal (a : ι → ℝ) (T O : Finset ι) (k : ℕ)
    (c : ℝ) (hc : 0 < c) (hT : IsTopK a T k) (hO : O.card = k) :
    ∑ i ∈ O, c * a i ≤ ∑ i ∈ T, c * a i := by
  have h := topk_regret_le_l1_scaled (c • a) a T O k c hc hT hO
  simp [l1] at h
  exact h

end Mettapedia.Algorithms.Retrieval.TopKSelection
