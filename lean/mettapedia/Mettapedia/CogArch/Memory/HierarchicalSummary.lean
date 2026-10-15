import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Tactic.NormNum

/-!
# Hierarchical summaries: when consolidation is exact

GraphRAG (arXiv 2404.16130) partitions its entity graph into nested Leiden
communities and summarizes them bottom-up with an LLM. When a community's
elements exceed the context window, it substitutes sub-community summaries for
them. Zep (arXiv 2501.13956) keeps a community tier, and Mem0 (arXiv 2504.19413)
refreshes a rolling conversation summary. An LLM summary is lossy, and
summarizing summaries need not agree with summarizing the members.

This file states when hierarchical consolidation is exact. It gives the cached
data a summary should carry alongside its text.

Main results:
* `hsum_eq_flat`: an additive aggregate (counts, sums, evidence totals)
  computed through any number of levels of disjoint sub-communities equals the
  aggregate over the members.
* `hsup_eq_flat`: an idempotent aggregate (the set of supporting episodes, the
  latest update time) is exact through any levels of covering sub-communities,
  even overlapping ones. Provenance and freshness therefore stay exact while
  the text of a summary is lossy.
* `mean_of_means_ne_mean`: an average is not such an aggregate. Averaging
  sub-community averages gives the wrong answer, so a summary should cache the
  sum and the count.
* `sum_update_of_not_mem` and `update_cost_le_levels` (quantitative): changing
  one member changes only the summaries of communities that contain it. That is
  at most one community per level of disjoint communities.
* `stale_iff`: a cached summary is stale exactly when a member was updated
  after the summary's recorded latest time. One comparison against an exact
  aggregate decides it.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.Memory.HierarchicalSummary

variable {ι M : Type*} [DecidableEq ι]

/-- `children` splits every community into sub-communities that cover it. -/
def Covers (children : Finset ι → Finset (Finset ι)) : Prop :=
  ∀ c, (children c).biUnion id = c

/-- `children` splits every community into disjoint sub-communities that cover it. -/
def Splits (children : Finset ι → Finset (Finset ι)) : Prop :=
  Covers children ∧ ∀ c, (children c : Set (Finset ι)).PairwiseDisjoint id

/-! ## Additive aggregates -/

section Additive

variable [AddCommMonoid M]

/-- A bottom-up summary through `n` levels: each community combines the summaries
of its sub-communities, and the lowest level combines its members directly. -/
def hsum (children : Finset ι → Finset (Finset ι)) (v : ι → M) : ℕ → Finset ι → M
  | 0, c => ∑ i ∈ c, v i
  | n + 1, c => ∑ d ∈ children c, hsum children v n d

/-- Hierarchical and flat aggregation agree for additive aggregates. -/
theorem hsum_eq_flat {children : Finset ι → Finset (Finset ι)} (h : Splits children)
    (v : ι → M) : ∀ (n : ℕ) (c : Finset ι), hsum children v n c = ∑ i ∈ c, v i
  | 0, _ => rfl
  | n + 1, c => by
    simp only [hsum]
    rw [Finset.sum_congr rfl fun d _ => hsum_eq_flat h v n d]
    conv_rhs => rw [← h.1 c]
    rw [Finset.sum_biUnion (h.2 c)]
    rfl

/-- Updating a member leaves the summary of every community without it unchanged. -/
theorem sum_update_of_not_mem {c : Finset ι} {x : ι} (hx : x ∉ c) (v : ι → M) (a : M) :
    ∑ i ∈ c, Function.update v x a i = ∑ i ∈ c, v i :=
  Finset.sum_congr rfl fun i hi =>
    Function.update_of_ne (fun (h : i = x) => hx (h ▸ hi)) a v

end Additive

/-! ## Idempotent aggregates -/

section Idempotent

variable [SemilatticeSup M] [OrderBot M]

/-- A bottom-up idempotent summary, such as a union of supporting episodes or a
latest update time. -/
def hsup (children : Finset ι → Finset (Finset ι)) (v : ι → M) : ℕ → Finset ι → M
  | 0, c => c.sup v
  | n + 1, c => (children c).sup fun d => hsup children v n d

/-- Idempotent aggregates are exact through any covering hierarchy, including
overlapping communities. -/
theorem hsup_eq_flat {children : Finset ι → Finset (Finset ι)} (h : Covers children)
    (v : ι → M) : ∀ (n : ℕ) (c : Finset ι), hsup children v n c = c.sup v
  | 0, _ => rfl
  | n + 1, c => by
    simp only [hsup]
    rw [show (fun d => hsup children v n d) = fun d => d.sup v from
      funext fun d => hsup_eq_flat h v n d]
    conv_rhs => rw [← h c]
    rw [Finset.sup_biUnion]
    rfl

/-- The provenance of a summary is exactly the union of its members' sources. -/
theorem provenance_exact {E : Type*} [DecidableEq E] {children : Finset ι → Finset (Finset ι)}
    (h : Covers children) (sources : ι → Finset E) (n : ℕ) (c : Finset ι) :
    hsup children sources n c = c.biUnion sources := by
  rw [hsup_eq_flat h sources n c, Finset.sup_eq_biUnion]

end Idempotent

/-! ## Averages are not aggregates -/

/-- The average of a list of values. -/
def mean (xs : List ℚ) : ℚ := xs.sum / xs.length

/-- Averaging sub-community averages differs from averaging the members. -/
theorem mean_of_means_ne_mean : mean [mean [1], mean [2, 3, 4]] ≠ mean [1, 2, 3, 4] := by
  norm_num [mean]

/-- Caching the sum and the count instead gives the exact average at any level. -/
example : let stats : List (ℚ × ℕ) := [((1 : ℚ), 1), (9, 3)]
    (stats.map Prod.fst).sum / (stats.map Prod.snd).sum = mean [1, 2, 3, 4] := by
  norm_num [mean]

/-! ## Update cost -/

/-- In a level of pairwise disjoint communities, at most one contains a member. -/
theorem card_containing_le_one {L : Finset (Finset ι)}
    (hL : (L : Set (Finset ι)).PairwiseDisjoint id) (x : ι) :
    (L.filter (x ∈ ·)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  by_contra hab
  exact Finset.disjoint_left.mp (hL ha.1 hb.1 hab) ha.2 hb.2

/-- An update to one member changes the summaries of at most one community per
level, so its cost is bounded by the number of levels. -/
theorem update_cost_le_levels (levels : List (Finset (Finset ι)))
    (hL : ∀ L ∈ levels, (L : Set (Finset ι)).PairwiseDisjoint id) (x : ι) :
    (levels.map fun L => (L.filter (x ∈ ·)).card).sum ≤ levels.length := by
  induction levels with
  | nil => simp
  | cons L levels ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := card_containing_le_one (hL L List.mem_cons_self) x
    have h2 := ih fun L' hL' => hL L' (List.mem_cons_of_mem L hL')
    omega

/-! ## Staleness -/

/-- A cached summary records the latest update time of its members when it was
built. It is stale when some member has been updated since. -/
def Stale (updated : ι → ℕ) (c : Finset ι) (cached : ℕ) : Prop := ∃ i ∈ c, cached < updated i

omit [DecidableEq ι] in
/-- The staleness check reduces to one comparison with the current latest time,
which is itself an exact idempotent aggregate. -/
theorem stale_iff (updated : ι → ℕ) (c : Finset ι) (cached : ℕ) :
    Stale updated c cached ↔ cached < c.sup updated := by
  unfold Stale
  constructor
  · rintro ⟨i, hi, hlt⟩
    exact lt_of_lt_of_le hlt (Finset.le_sup hi)
  · intro h
    by_contra hno
    push Not at hno
    exact absurd h (not_lt.mpr (Finset.sup_le fun i hi => hno i hi))

/-! ## Revision stamps, including changing membership

The timestamp theorem above fixes the member set. The native hierarchy also
allows links to be added or removed, and records node and child-summary
revisions. Its freshness test compares sets of dependency/revision pairs.
This model characterizes that test; it does not prove summary prose accurate,
or verify the evaluator, store transport, or native implementation.
-/

section Revisions

variable {D : Type*} [DecidableEq D]

def revisionStamp (members : Finset D) (revision : D → ℕ) : Finset (D × ℕ) :=
  members.image fun d => (d, revision d)

theorem mem_revisionStamp (members : Finset D) (revision : D → ℕ) (d : D) (r : ℕ) :
    (d, r) ∈ revisionStamp members revision ↔ d ∈ members ∧ r = revision d := by
  simp [revisionStamp, Prod.ext_iff, eq_comm]

theorem revisionStamp_eq_iff (a b : Finset D) (ra rb : D → ℕ) :
    revisionStamp a ra = revisionStamp b rb ↔ a = b ∧ ∀ d ∈ a, ra d = rb d := by
  constructor
  · intro h
    have hab : a = b := by
      ext d
      constructor
      · intro hd
        have hm : (d, ra d) ∈ revisionStamp b rb := h ▸ (mem_revisionStamp a ra d (ra d)).mpr ⟨hd, rfl⟩
        exact ((mem_revisionStamp b rb d (ra d)).mp hm).1
      · intro hd
        have hm : (d, rb d) ∈ revisionStamp a ra := h.symm ▸ (mem_revisionStamp b rb d (rb d)).mpr ⟨hd, rfl⟩
        exact ((mem_revisionStamp a ra d (rb d)).mp hm).1
    refine ⟨hab, ?_⟩
    intro d hd
    have hm : (d, ra d) ∈ revisionStamp b rb := h ▸ (mem_revisionStamp a ra d (ra d)).mpr ⟨hd, rfl⟩
    exact ((mem_revisionStamp b rb d (ra d)).mp hm).2
  · rintro ⟨rfl, h⟩
    apply Finset.image_congr
    intro d hd
    simp [h d hd]

theorem changed_membership_changes_stamp (a b : Finset D) (ra rb : D → ℕ)
    (h : a ≠ b) : revisionStamp a ra ≠ revisionStamp b rb := by
  intro heq
  exact h ((revisionStamp_eq_iff a b ra rb).mp heq).1

theorem changed_dependency_changes_stamp (a : Finset D) (ra rb : D → ℕ)
    (d : D) (hd : d ∈ a) (h : ra d ≠ rb d) :
    revisionStamp a ra ≠ revisionStamp a rb := by
  intro heq
  exact h (((revisionStamp_eq_iff a a ra rb).mp heq).2 d hd)

theorem unrelated_revision_does_not_change_stamp (a : Finset D) (ra rb : D → ℕ)
    (h : ∀ d ∈ a, ra d = rb d) : revisionStamp a ra = revisionStamp a rb :=
  (revisionStamp_eq_iff a a ra rb).mpr ⟨rfl, h⟩

theorem added_member_changes_stamp (a : Finset D) (r : D → ℕ) (d : D) (hd : d ∉ a) :
    revisionStamp a r ≠ revisionStamp (insert d a) r := by
  apply changed_membership_changes_stamp
  intro h
  exact hd (h.symm ▸ Finset.mem_insert_self d a)

theorem removed_member_changes_stamp (a : Finset D) (r : D → ℕ) (d : D) (hd : d ∈ a) :
    revisionStamp a r ≠ revisionStamp (a.erase d) r := by
  apply changed_membership_changes_stamp
  intro h
  have hm : d ∈ a.erase d := h ▸ hd
  simp at hm

/-- The latest timestamp can remain unchanged when an older member disappears. -/
theorem latest_time_misses_removed_membership :
    ({1, 2} : Finset ℕ).sup (fun d => if d = 1 then 5 else 4) =
      ({1} : Finset ℕ).sup (fun d => if d = 1 then 5 else 4) ∧
    revisionStamp ({1, 2} : Finset ℕ) (fun d => if d = 1 then 5 else 4) ≠
      revisionStamp ({1} : Finset ℕ) (fun d => if d = 1 then 5 else 4) := by
  decide

end Revisions


end Mettapedia.CogArch.Memory.HierarchicalSummary
