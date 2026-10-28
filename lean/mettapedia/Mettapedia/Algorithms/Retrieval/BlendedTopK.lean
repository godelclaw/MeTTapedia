import Mettapedia.Algorithms.Retrieval.TopKSelection

/-!
# Certified top-k for a similarity/attention blend

An attention reranker scores a candidate by `mix * sim + (1 - mix) * x / M`, where
`x` is restart-walk mass and `M` its largest value. From the walk's last observed
change this module bounds that score's error, so the reranker may stop as soon as
its selection is certified.

The reranker sees only a pool: the best similarity matches, plus every node the
walk has reached. A node outside the pool carries no mass yet, and when the pool
comes from an exact similarity search its similarity is at most the pool's
smallest one. One virtual competitor with that similarity therefore stands for
every unseen node, and the certificate covers the whole store.

The certificate concerns the supplied walk and similarities. It does not
establish that the selection is useful, and it need not fire at a tie.
-/

noncomputable section
namespace Mettapedia.Algorithms.Retrieval.BlendedTopK
open Mettapedia.ProbabilityTheory.MarkovChain.Restart
open Mettapedia.Algorithms.Retrieval.TopKSelection
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The reranker's score with an explicit normalizer. -/
def blend (mix : ℝ) (sim x : ι → ℝ) (M : ℝ) (j : ι) : ℝ :=
  mix * sim j + (1 - mix) * (x j / M)

/-- Normalizing by an approximate maximum costs at most `2e/M`. -/
theorem ratio_error (y p M Mp e : ℝ) (hM : 0 < M) (hMp : 0 < Mp)
    (hp0 : 0 ≤ p) (hpM : p ≤ Mp) (hy : |y - p| ≤ e) (hMe : |M - Mp| ≤ e) :
    |y / M - p / Mp| ≤ 2 * e / M := by
  have key : y / M - p / Mp = (y - p) / M + p / Mp * ((Mp - M) / M) := by
    field_simp
    ring
  have hr0 : 0 ≤ p / Mp := div_nonneg hp0 hMp.le
  have hr1 : p / Mp ≤ 1 := (div_le_one hMp).mpr hpM
  have hMe' : |Mp - M| ≤ e := by rwa [abs_sub_comm]
  rw [key]
  calc |(y - p) / M + p / Mp * ((Mp - M) / M)|
      ≤ |(y - p) / M| + |p / Mp * ((Mp - M) / M)| := abs_add_le _ _
    _ ≤ e / M + e / M := by
        apply add_le_add
        · rw [abs_div, abs_of_pos hM]
          exact div_le_div_of_nonneg_right hy hM.le
        · rw [abs_mul, abs_of_nonneg hr0, abs_div, abs_of_pos hM]
          calc p / Mp * (|Mp - M| / M) ≤ 1 * (|Mp - M| / M) :=
                mul_le_mul_of_nonneg_right hr1 (div_nonneg (abs_nonneg _) hM.le)
            _ ≤ e / M := by
                rw [one_mul]
                exact div_le_div_of_nonneg_right hMe' hM.le
    _ = 2 * e / M := by ring

omit [Fintype ι] [DecidableEq ι] in
/-- Attained maxima of coordinatewise `e`-close vectors are `e`-close. -/
theorem max_close (y p : ι → ℝ) (M Mp e : ℝ) (hMy : ∀ j, y j ≤ M) (hMyx : ∃ j, y j = M)
    (hMp : ∀ j, p j ≤ Mp) (hMpx : ∃ j, p j = Mp) (he : ∀ j, |y j - p j| ≤ e) :
    |M - Mp| ≤ e := by
  obtain ⟨a, ha⟩ := hMyx
  obtain ⟨b, hb⟩ := hMpx
  have h1 := abs_le.mp (he a)
  have h2 := abs_le.mp (he b)
  have h3 := hMp a
  have h4 := hMy b
  rw [abs_le]
  constructor <;> linarith

variable (W : RestartWalk ι)

omit [DecidableEq ι] in
/-- The observed blended score is within `(1-mix) * 2e/M` of the exact one, where
`e` is the restart walk's observable error bound. -/
theorem blend_error (mix : ℝ) (hmix1 : mix ≤ 1) (sim s x : ι → ℝ)
    (hs : ∀ i, 0 ≤ s i) (M Mp : ℝ) (hM : 0 < M) (hMp0 : 0 < Mp)
    (hMy : ∀ j, W.step s x j ≤ M) (hMyx : ∃ j, W.step s x j = M)
    (hMp : ∀ j, W.ppr s j ≤ Mp) (hMpx : ∃ j, W.ppr s j = Mp) (j : ι) :
    |blend mix sim (W.step s x) M j - blend mix sim (W.ppr s) Mp j| ≤
      (1 - mix) * (2 * ((1 - W.α) / W.α * l1 (W.step s x - x)) / M) := by
  set e := (1 - W.α) / W.α * l1 (W.step s x - x)
  have he : ∀ i, |W.step s x i - W.ppr s i| ≤ e := fun i =>
    (abs_coordinate_le_l1 (W.step s x - W.ppr s) i).trans (W.next_error_le s x)
  have hMe := max_close (W.step s x) (W.ppr s) M Mp e hMy hMyx hMp hMpx he
  have hr := ratio_error (W.step s x j) (W.ppr s j) M Mp e hM hMp0
    (W.ppr_nonneg hs j) (hMp j) (he j) hMe
  have hdiff : blend mix sim (W.step s x) M j - blend mix sim (W.ppr s) Mp j =
      (1 - mix) * (W.step s x j / M - W.ppr s j / Mp) := by
    unfold blend
    ring
  rw [hdiff, abs_mul, abs_of_nonneg (sub_nonneg.mpr hmix1)]
  exact mul_le_mul_of_nonneg_left hr (sub_nonneg.mpr hmix1)

/-- The reranker's stopping rule. `C` is the scored pool, containing the selection
`T` and every node the walk has reached; `σ` bounds the similarity of every node
outside it. If each selected score beats every other pooled score, and the
virtual unseen competitor `mix * σ`, by more than twice the error bound, then `T`
is the exact top-k of the converged blend over the whole store. -/
theorem certified_blend_topk (mix : ℝ) (hmix0 : 0 ≤ mix) (hmix1 : mix ≤ 1)
    (sim s x : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (M Mp : ℝ) (hM : 0 < M) (hMp0 : 0 < Mp)
    (hMy : ∀ j, W.step s x j ≤ M) (hMyx : ∃ j, W.step s x j = M)
    (hMp : ∀ j, W.ppr s j ≤ Mp) (hMpx : ∃ j, W.ppr s j = Mp)
    (C T : Finset ι) (k : ℕ) (hcard : T.card = k) (σ : ℝ)
    (hunseen : ∀ j, j ∉ C → W.step s x j = 0 ∧ sim j ≤ σ)
    (hmargin : ∀ i ∈ T, ∀ j ∈ C, j ∉ T →
      2 * ((1 - mix) * (2 * ((1 - W.α) / W.α * l1 (W.step s x - x)) / M)) <
        blend mix sim (W.step s x) M i - blend mix sim (W.step s x) M j)
    (hvirtual : ∀ i ∈ T,
      2 * ((1 - mix) * (2 * ((1 - W.α) / W.α * l1 (W.step s x - x)) / M)) <
        blend mix sim (W.step s x) M i - mix * σ) :
    IsTopK (blend mix sim (W.ppr s) Mp) T k := by
  apply (isTopK_iff _ _ _).mpr
  refine ⟨hcard, fun i hi j hj => le_of_lt ?_⟩
  have hall : ∀ i ∈ T, ∀ j ∉ T,
      2 * ((1 - mix) * (2 * ((1 - W.α) / W.α * l1 (W.step s x - x)) / M)) <
        blend mix sim (W.step s x) M i - blend mix sim (W.step s x) M j := by
    intro i hi j hj
    by_cases hjC : j ∈ C
    · exact hmargin i hi j hjC hj
    · obtain ⟨hzero, hsim⟩ := hunseen j hjC
      have hb : blend mix sim (W.step s x) M j ≤ mix * σ := by
        unfold blend
        rw [hzero, zero_div, mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_left hsim hmix0
      linarith [hvirtual i hi]
  exact topk_frozen _ _ T _ hall
    (fun z => blend_error W mix hmix1 sim s x hs M Mp hM hMp0 hMy hMyx hMp hMpx z) i hi j hj

end Mettapedia.Algorithms.Retrieval.BlendedTopK
