import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# One retrieval contract: sound candidates, exact refinement and fusion

The authoritative store holds the memory records. A vector index, keyword index
or graph search produces candidates. The index is not the truth. A query
re-checks candidates against the current store and the exact relation.
Correctness then rests on one property of the index: it must not miss a true
answer.

Zep's retrieval (arXiv 2501.13956) composes search, reranking and context
construction. Its searches use cosine similarity, BM25 and breadth-first graph
search, and reciprocal rank fusion is one of its rerankers. Mem0, A-MEM and
HippoRAG 2 all begin with dense top-k retrieval. This file states what each
stage must guarantee.

Main results:
* `refine_exact` and `sound_iff_refine_exact`: filter-and-refine returns exactly
  the true answers if and only if the index is sound. `refine_correct` holds for
  any index.
* `sound_of_abstraction` and `lower_bound_range_sound`: an index over an
  abstraction is sound when the abstraction never rejects a true answer. A
  projected distance that never exceeds the true distance is one such case.
* `sound_inter`, `sound_union` and `sound_mono`: soundness composes over
  conjunctions and disjunctions of filters.
* `lagging_sound` and `refine_lagging_card_le` (quantitative): an index built
  from an older store, plus a scan of the records written since, stays sound.
  Deleted records need no index update. The exact check runs on at most
  `|candidates| + |delta|` records.
* `exists_topK`, `rerank_exact` and `rerank_exact_of_bound`: reranking a
  candidate set by the exact score yields an exact top-k when the candidates
  contain some true top-k, or when every non-candidate is certified to score no
  higher than the selection.
* `rrf_perm`, `rrf_unanimous`, `rrf_pos_iff` and `rrf_le`: reciprocal rank
  fusion ignores the order of its input rankings and respects unanimous
  preferences. It gives positive score exactly to items that some ranking
  returned, and its scores are bounded.
-/

set_option autoImplicit false

namespace AgentMemory.Retrieval

/-! ## Filter and refine -/

section Filter

variable {Q X : Type*}

/-- An index is sound for the exact relation `R` over the store when it returns
every true answer. -/
def Sound (R : Q → X → Prop) (store : Finset X) (cand : Q → Finset X) : Prop :=
  ∀ q, ∀ x ∈ store, R q x → x ∈ cand q

section Compose

variable {R : Q → X → Prop} {store : Finset X} {cand : Q → Finset X}

/-- An index over an abstraction is sound when the abstraction never rejects a
true answer. -/
theorem sound_of_abstraction {A B : Type*} (α : X → A) (γ : Q → B) (RA : B → A → Prop)
    (hα : ∀ q x, R q x → RA (γ q) (α x))
    (hc : ∀ q, ∀ x ∈ store, RA (γ q) (α x) → x ∈ cand q) : Sound R store cand :=
  fun q x hx hr => hc q x hx (hα q x hr)

/-- No false dismissals: when a projected distance never exceeds the true one, a
range query in the projection keeps every true answer of the range query. -/
theorem lower_bound_range_sound {A β : Type*} [Preorder β] (d : X → X → β)
    (dA : A → A → β) (α : X → A) (hlb : ∀ x y, dA (α x) (α y) ≤ d x y) (r : β)
    (cand : X → Finset X) (hc : ∀ q, ∀ x ∈ store, dA (α q) (α x) ≤ r → x ∈ cand q) :
    Sound (fun q x => d q x ≤ r) store cand :=
  fun q x hx hr => hc q x hx (le_trans (hlb q x) hr)

theorem sound_mono {R' : Q → X → Prop} (h : Sound R store cand) (hR : ∀ q x, R' q x → R q x) :
    Sound R' store cand :=
  fun q x hx hr => h q x hx (hR q x hr)

variable [DecidableEq X]

theorem sound_inter {R₁ R₂ : Q → X → Prop} {c₁ c₂ : Q → Finset X} (h₁ : Sound R₁ store c₁)
    (h₂ : Sound R₂ store c₂) : Sound (fun q x => R₁ q x ∧ R₂ q x) store (fun q => c₁ q ∩ c₂ q) :=
  fun q x hx hr => Finset.mem_inter.mpr ⟨h₁ q x hx hr.1, h₂ q x hx hr.2⟩

theorem sound_union {R₁ R₂ : Q → X → Prop} {c₁ c₂ : Q → Finset X} (h₁ : Sound R₁ store c₁)
    (h₂ : Sound R₂ store c₂) : Sound (fun q x => R₁ q x ∨ R₂ q x) store (fun q => c₁ q ∪ c₂ q) :=
  fun q x hx hr => hr.elim (fun h => Finset.mem_union_left _ (h₁ q x hx h))
    (fun h => Finset.mem_union_right _ (h₂ q x hx h))

/-- An index built from an older store stays sound when the records written since
(new records and new versions of old ones) are scanned alongside it. Deleted
records need no index update, because refinement re-checks the current store. -/
theorem lagging_sound {old current delta : Finset X} (h : Sound R old cand)
    (hcur : current ⊆ old ∪ delta) : Sound R current (fun q => cand q ∪ delta) := by
  intro q x hx hr
  rcases Finset.mem_union.mp (hcur hx) with ho | hd
  · exact Finset.mem_union_left _ (h q x ho hr)
  · exact Finset.mem_union_right _ hd

end Compose

section Refine

variable [DecidableEq X]

/-- Filter and refine: keep the candidates that are still in the store and
satisfy the exact relation. -/
def refine (R : Q → X → Prop) [∀ q, DecidablePred (R q)] (store : Finset X)
    (cand : Q → Finset X) (q : Q) : Finset X :=
  (cand q ∩ store).filter (R q)

variable {R : Q → X → Prop} [∀ q, DecidablePred (R q)] {store : Finset X}
  {cand : Q → Finset X}

/-- Whatever the index returns, refinement never reports a false answer or a
record missing from the store. -/
theorem refine_correct (q : Q) {x : X} (hx : x ∈ refine R store cand q) :
    x ∈ store ∧ R q x := by
  simp only [refine, Finset.mem_filter, Finset.mem_inter] at hx
  exact ⟨hx.1.2, hx.2⟩

/-- With a sound index, refinement returns exactly the true answers. -/
theorem refine_exact (h : Sound R store cand) (q : Q) :
    refine R store cand q = store.filter (R q) := by
  ext x
  simp only [refine, Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨⟨_, hs⟩, hr⟩
    exact ⟨hs, hr⟩
  · rintro ⟨hs, hr⟩
    exact ⟨⟨h q x hs hr, hs⟩, hr⟩

/-- Soundness is also necessary for exact answers. -/
theorem sound_iff_refine_exact :
    Sound R store cand ↔ ∀ q, refine R store cand q = store.filter (R q) := by
  refine ⟨fun h q => refine_exact h q, fun h q x hx hr => ?_⟩
  have : x ∈ refine R store cand q := by
    rw [h q]
    exact Finset.mem_filter.mpr ⟨hx, hr⟩
  simp only [refine, Finset.mem_filter, Finset.mem_inter] at this
  exact this.1.1

/-- The exact relation is evaluated at most once per candidate. -/
theorem refine_card_le (q : Q) : (refine R store cand q).card ≤ (cand q).card :=
  le_trans (Finset.card_filter_le _ _) (Finset.card_le_card Finset.inter_subset_left)

/-- The exact check over a lagging index touches at most the index's candidates
plus the records written since the index was built. -/
theorem refine_lagging_card_le (delta : Finset X) (q : Q) :
    (refine R store (fun q => cand q ∪ delta) q).card ≤ (cand q).card + delta.card :=
  le_trans (refine_card_le (cand := fun q => cand q ∪ delta) q) (Finset.card_union_le _ _)

end Refine

end Filter

/-! ## Exact top-k by reranking -/

section TopK

variable {X β : Type*} [DecidableEq X] [LinearOrder β] (score : X → β)

/-- `T` is a top-`k` selection from `S`: as many elements as possible up to `k`,
and no unselected element scores higher than a selected one. Ties may be broken
either way. -/
def IsTopK (k : ℕ) (S T : Finset X) : Prop :=
  T ⊆ S ∧ T.card = min k S.card ∧ ∀ x ∈ T, ∀ y ∈ S, y ∉ T → score y ≤ score x

variable {score}

/-- Every finite set has a top-`k` selection. -/
theorem exists_topK (k : ℕ) (S : Finset X) : ∃ T, IsTopK score k S T := by
  induction k with
  | zero => exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hTS, hcard, hord⟩ := ih
    by_cases hne : (S \ T).Nonempty
    · obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (S \ T) score hne
      rw [Finset.mem_sdiff] at hm
      have hlt : T.card < S.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hTS, fun h => by rw [h] at hm; exact hm.2 hm.1⟩)
      refine ⟨insert m T, Finset.insert_subset hm.1 hTS, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hm.2]
        omega
      · intro x hx y hy hyn
        rw [Finset.mem_insert, not_or] at hyn
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hmax y (Finset.mem_sdiff.mpr ⟨hy, hyn.2⟩)
        · exact hord x hx y hy hyn.2
    · have hTeq : T = S := by
        apply Finset.Subset.antisymm hTS
        intro y hy
        by_contra hyT
        exact hne ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyT⟩⟩
      subst hTeq
      refine ⟨T, subset_rfl, ?_, fun x _ y hy hyn => absurd hy hyn⟩
      omega

/-- Reranking is exact when the candidates contain some true top-`k`: every
top-`k` of the candidates is a top-`k` of the store. -/
theorem rerank_exact {k : ℕ} {S C T₀ T : Finset X} (hT₀ : IsTopK score k S T₀)
    (hT₀C : T₀ ⊆ C) (hCS : C ⊆ S) (hT : IsTopK score k C T) : IsTopK score k S T := by
  obtain ⟨hT₀S, hT₀card, hT₀ord⟩ := hT₀
  obtain ⟨hTC, hTcard, hTord⟩ := hT
  have h1 := Finset.card_le_card hT₀C
  have h2 := Finset.card_le_card hCS
  have hcard : T.card = min k S.card := by omega
  refine ⟨hTC.trans hCS, hcard, fun x hx y hy hyT => ?_⟩
  by_cases hyC : y ∈ C
  · exact hTord x hx y hyC hyT
  · have hyT₀ : y ∉ T₀ := fun h => hyC (hT₀C h)
    by_cases hxT₀ : x ∈ T₀
    · exact hT₀ord x hxT₀ y hy hyT₀
    · have hsub : ¬ T₀ ⊆ T := fun hsub => hxT₀ (by
        rw [Finset.eq_of_subset_of_card_le hsub (by omega)]
        exact hx)
      obtain ⟨z, hzT₀, hzT⟩ := Finset.not_subset.mp hsub
      exact le_trans (hT₀ord z hzT₀ y hy hyT₀) (hTord x hx z (hT₀C hzT₀) hzT)

/-- Reranking is exact when every record left out of the candidates is certified
(for example by an upper bound on its score) to score no higher than the
selection, and there are at least `k` candidates. -/
theorem rerank_exact_of_bound {k : ℕ} {S C T : Finset X} (hCS : C ⊆ S) (hk : k ≤ C.card)
    (hT : IsTopK score k C T)
    (hbound : ∀ y ∈ S, y ∉ C → ∀ x ∈ T, score y ≤ score x) : IsTopK score k S T := by
  obtain ⟨hTC, hTcard, hTord⟩ := hT
  have h2 := Finset.card_le_card hCS
  refine ⟨hTC.trans hCS, by omega, fun x hx y hy hyT => ?_⟩
  by_cases hyC : y ∈ C
  · exact hTord x hx y hyC hyT
  · exact hbound y hy hyC x hx

end TopK

/-! ## Reciprocal rank fusion -/

section Fusion

variable {X : Type*} [DecidableEq X]

/-- The contribution of one ranking to reciprocal rank fusion (Cormack, Clarke
and Büttcher, SIGIR 2009): `1 / (c + rank)` with 1-based rank, and `0` when the
ranking does not contain the item. -/
def rrfTerm (c : ℚ) (r : List X) (x : X) : ℚ :=
  if x ∈ r then 1 / (c + ((r.idxOf x + 1 : ℕ) : ℚ)) else 0

/-- Fused score of `x` over the rankings `rs`. -/
def rrf (c : ℚ) (rs : List (List X)) (x : X) : ℚ := (rs.map fun r => rrfTerm c r x).sum

theorem rrf_nil (c : ℚ) (x : X) : rrf c [] x = 0 := rfl

theorem rrf_cons (c : ℚ) (r : List X) (rs : List (List X)) (x : X) :
    rrf c (r :: rs) x = rrfTerm c r x + rrf c rs x := by
  simp [rrf]

/-- Fusion does not depend on the order of its input rankings. -/
theorem rrf_perm (c : ℚ) {rs rs' : List (List X)} (h : rs.Perm rs') (x : X) :
    rrf c rs x = rrf c rs' x :=
  (h.map _).sum_eq

variable {c : ℚ}

theorem rank_pos (r : List X) (x : X) (hc : 0 ≤ c) : 0 < c + ((r.idxOf x + 1 : ℕ) : ℚ) := by
  have : (0 : ℚ) < ((r.idxOf x + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos _
  linarith

theorem rrfTerm_nonneg (hc : 0 ≤ c) (r : List X) (x : X) : 0 ≤ rrfTerm c r x := by
  unfold rrfTerm
  split_ifs
  · exact le_of_lt (one_div_pos.mpr (rank_pos r x hc))
  · exact le_rfl

theorem rrfTerm_pos_iff (hc : 0 ≤ c) (r : List X) (x : X) : 0 < rrfTerm c r x ↔ x ∈ r := by
  unfold rrfTerm
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => one_div_pos.mpr (rank_pos r x hc)⟩
  · exact ⟨fun h' => absurd h' (lt_irrefl 0), fun h' => absurd h' h⟩

theorem rrfTerm_le (hc : 0 ≤ c) (r : List X) (x : X) : rrfTerm c r x ≤ 1 / (c + 1) := by
  unfold rrfTerm
  split_ifs
  · apply one_div_le_one_div_of_le (by linarith)
    have : (1 : ℚ) ≤ ((r.idxOf x + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    linarith
  · exact le_of_lt (one_div_pos.mpr (by linarith))

/-- A better rank never earns a smaller contribution. -/
theorem rrfTerm_anti (hc : 0 ≤ c) {r : List X} {x y : X} (hx : x ∈ r)
    (hxy : y ∈ r → r.idxOf x ≤ r.idxOf y) : rrfTerm c r y ≤ rrfTerm c r x := by
  unfold rrfTerm
  rw [if_pos hx]
  split_ifs with hy
  · apply one_div_le_one_div_of_le (rank_pos r x hc)
    have : ((r.idxOf x + 1 : ℕ) : ℚ) ≤ ((r.idxOf y + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.succ_le_succ (hxy hy)
    linarith
  · exact le_of_lt (one_div_pos.mpr (rank_pos r x hc))

theorem rrf_nonneg (hc : 0 ≤ c) (rs : List (List X)) (x : X) : 0 ≤ rrf c rs x := by
  induction rs with
  | nil => exact le_rfl
  | cons r rs ih => rw [rrf_cons]; exact add_nonneg (rrfTerm_nonneg hc r x) ih

/-- Unanimity: if every ranking contains `x` and places it no lower than `y`,
fusion scores `x` at least as high as `y`. -/
theorem rrf_unanimous (hc : 0 ≤ c) {rs : List (List X)} {x y : X}
    (h : ∀ r ∈ rs, x ∈ r ∧ (y ∈ r → r.idxOf x ≤ r.idxOf y)) : rrf c rs y ≤ rrf c rs x := by
  induction rs with
  | nil => exact le_rfl
  | cons r rs ih =>
    rw [rrf_cons, rrf_cons]
    have hr := h r List.mem_cons_self
    exact add_le_add (rrfTerm_anti hc hr.1 hr.2)
      (ih fun r' hr' => h r' (List.mem_cons_of_mem r hr'))

/-- No fabrication and no loss: fusion gives positive score exactly to the items
that some ranking returned. -/
theorem rrf_pos_iff (hc : 0 ≤ c) (rs : List (List X)) (x : X) :
    0 < rrf c rs x ↔ ∃ r ∈ rs, x ∈ r := by
  induction rs with
  | nil => simp [rrf_nil]
  | cons r rs ih =>
    rw [rrf_cons]
    constructor
    · intro h
      by_cases hx : x ∈ r
      · exact ⟨r, List.mem_cons_self, hx⟩
      · have h0 : rrfTerm c r x = 0 := by simp [rrfTerm, hx]
        rw [h0, zero_add] at h
        obtain ⟨r', hr', hx'⟩ := ih.mp h
        exact ⟨r', List.mem_cons_of_mem r hr', hx'⟩
    · rintro ⟨r', hr', hx'⟩
      rcases List.mem_cons.mp hr' with rfl | hr'
      · exact add_pos_of_pos_of_nonneg ((rrfTerm_pos_iff hc r' x).mpr hx') (rrf_nonneg hc rs x)
      · exact add_pos_of_nonneg_of_pos (rrfTerm_nonneg hc r x) (ih.mpr ⟨r', hr', hx'⟩)

/-- Fused scores are bounded by the number of rankings. -/
theorem rrf_le (hc : 0 ≤ c) (rs : List (List X)) (x : X) :
    rrf c rs x ≤ rs.length * (1 / (c + 1)) := by
  induction rs with
  | nil => simp [rrf_nil]
  | cons r rs ih =>
    rw [rrf_cons, List.length_cons, Nat.cast_succ, add_mul, one_mul]
    linarith [rrfTerm_le hc r x]

/-- An item at 1-based rank at most `m` in one ranking scores at least
`1 / (c + m)` after fusion, whatever the other rankings say. -/
theorem rrf_ge_of_rank (hc : 0 ≤ c) {rs : List (List X)} {r : List X} (hr : r ∈ rs) {x : X}
    (hx : x ∈ r) {m : ℕ} (hm : r.idxOf x + 1 ≤ m) : 1 / (c + m) ≤ rrf c rs x := by
  induction rs with
  | nil => simp at hr
  | cons r' rs ih =>
    rw [rrf_cons]
    rcases List.mem_cons.mp hr with rfl | hr
    · have hterm : 1 / (c + m) ≤ rrfTerm c r x := by
        unfold rrfTerm
        rw [if_pos hx]
        apply one_div_le_one_div_of_le (rank_pos r x hc)
        have : ((r.idxOf x + 1 : ℕ) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
        linarith
      linarith [rrf_nonneg hc rs x]
    · linarith [ih hr, rrfTerm_nonneg hc r' x]

/-- With the usual constant `c = 60`, a top-ranked item from one retriever beats an
item that appears nowhere. -/
example : rrf 60 [[1, 2, 3], [3, 1]] (2 : ℕ) < rrf 60 [[1, 2, 3], [3, 1]] 1 ∧
    rrf 60 [[1, 2, 3], [3, 1]] (4 : ℕ) = 0 := by
  constructor <;> norm_num [rrf, rrfTerm]

end Fusion

end AgentMemory.Retrieval
