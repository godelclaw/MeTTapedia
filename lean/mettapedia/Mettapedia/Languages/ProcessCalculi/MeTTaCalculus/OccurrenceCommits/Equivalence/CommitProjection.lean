import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Basis
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.BorrowedSteps

/-!
# From commits over occurrences to rules over bags

The equivalences compare bags of labels; the commits of the occurrence model act on occurrences
with identities. This module relates the two.

* **Normal form** (`normalize`, `enabled_normalize_iff`, `fire_normalize`): keeping what a
  predicate query saw and the commit does not take changes neither enabling nor firing. In normal
  form every predicate query sees only what the commit takes or keeps (`QueriesUsed`), which is the
  shape of a bag rule's closed regions.
* **Projection** (`ruleOf`, `ruleOf_enabled`, `labels_fire_eq_result`): a commit in normal form,
  enabled at a store, gives a bag rule enabled at the store's labels, and firing the commit is
  firing the rule on labels. So every run of commits projects onto a run of the bag rules
  (`reduces_of_enabled`).
* **Waking contexts** (`bag_label_le`, `bag_label_eq_of_injOn`, `bag_label_le_arrival`): the
  bag-level least label of a commit's rule lies below the labels of the identity-level least waking
  context `(taken ∪ kept) \ S` of the reactive module (`minimal_wake`), and below the labels of
  every arrival that wakes the commit; it equals the former when labels are injective on the store
  and the commit's uses. With repeated labels it is strictly smaller
  (`Controls.bag_label_smaller`): the identity-level commit waits for one particular occurrence,
  the bag rule for any occurrence with that label, which is what a behavioural equivalence should
  compare.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} [DecidableEq O] {R : Type v}

/-! ## Normal form -/

/-- A commit's predicate queries see only what it takes or keeps. -/
def QueriesUsed (c : Commit O R) : Prop := ∀ read ∈ c.queries, read.seen ⊆ c.taken ∪ c.kept

/-- **The normal form**: keep, besides, what the predicate queries saw (`seenOf`) and the commit
does not take. -/
def normalize (c : Commit O R) : Commit O R := ⟨c.taken, c.kept ∪ (seenOf c.queries \ c.taken), c.made, c.queries⟩

theorem queriesUsed_normalize (c : Commit O R) : QueriesUsed (normalize c) := by
  intro read member o seen
  by_cases taken : o ∈ c.taken
  · exact Finset.mem_union_left _ taken
  · exact Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_sdiff.mpr ⟨mem_seenOf.mpr ⟨read, member, seen⟩, taken⟩))

variable {label : O → R}

/-- **Normalizing changes no enabling.** -/
theorem enabled_normalize_iff {S : Finset O} {c : Commit O R} :
    Enabled label S (normalize c) ↔ Enabled label S c := by
  constructor
  · intro e
    exact ⟨e.taken_subset, fun o k => e.kept_subset (Finset.mem_union_left _ k),
      Finset.disjoint_of_subset_right Finset.subset_union_left e.apart, e.fresh, e.queries_hold⟩
  · intro e
    refine ⟨e.taken_subset, ?_, ?_, e.fresh, e.queries_hold⟩
    · intro o member
      rcases Finset.mem_union.mp member with k | s
      · exact e.kept_subset k
      · obtain ⟨read, inQueries, seen⟩ := mem_seenOf.mp (Finset.mem_sdiff.mp s).1
        exact PredicateQuery.seen_subset (e.queries_hold read inQueries) seen
    · refine Finset.disjoint_union_right.mpr ⟨e.apart, ?_⟩
      exact Finset.disjoint_left.mpr fun o taken s => (Finset.mem_sdiff.mp s).2 taken

/-- **Normalizing changes no firing.** -/
theorem fire_normalize (S : Finset O) (c : Commit O R) : fire S (normalize c) = fire S c :=
  rfl

/-! ## Projection onto bag rules -/

variable [DecidableEq R]

variable (label) in
/-- The bag rule of a commit: its labels, and the union of the regions it queries. -/
def ruleOf (c : Commit O R) : Rule R :=
  ⟨labels label c.taken, labels label c.kept, labels label c.made,
    fun x => c.queries.any fun read => read.region x⟩

omit [DecidableEq R] in
theorem ruleOf_redex {c : Commit O R} (apart : Disjoint c.taken c.kept) :
    (ruleOf label c).redex = labels label (c.taken ∪ c.kept) :=
  (labels_union_of_disjoint label apart).symm

/-- **A commit in normal form, enabled at a store, projects onto an enabled bag rule.** -/
theorem ruleOf_enabled {S : Finset O} {c : Commit O R} (enabled : Enabled label S c)
    (used : QueriesUsed c) : (ruleOf label c).Enabled (labels label S) := by
  have uses : c.taken ∪ c.kept ⊆ S := Finset.union_subset enabled.taken_subset enabled.kept_subset
  refine ⟨?_, ?_⟩
  · rw [ruleOf_redex enabled.apart]
    exact labels_mono uses
  · rw [ruleOf_redex enabled.apart, ← labels_sdiff_of_subset label uses]
    intro x member
    obtain ⟨o, inFrame, rfl⟩ := Multiset.mem_map.mp member
    obtain ⟨inS, notUsed⟩ := Finset.mem_sdiff.mp (Finset.mem_val.mp inFrame)
    cases h : (ruleOf label c).closed (label o)
    · rfl
    · exfalso
      simp only [ruleOf, List.any_eq_true] at h
      obtain ⟨read, inQueries, inRegion⟩ := h
      have holds := enabled.queries_hold read inQueries
      have : o ∈ read.seen := by
        rw [← holds]; exact mem_regionOf.mpr ⟨inS, inRegion⟩
      exact notUsed (used read inQueries this)

/-- **Firing a commit is firing its rule on labels.** -/
theorem labels_fire_eq_result {S : Finset O} {c : Commit O R} (enabled : Enabled label S c) :
    labels label (fire S c) = (ruleOf label c).result (labels label S) :=
  labels_fire enabled

/-- **Every firing of a commit is a reduction of the projected rules.** -/
theorem reduces_of_enabled {Γc : Commit O R → Prop} {S : Finset O} {c : Commit O R} (member : Γc c)
    (used : QueriesUsed c) (enabled : Enabled label S c) :
    Reduces (fun ρ => ∃ c, Γc c ∧ QueriesUsed c ∧ ρ = ruleOf label c) (labels label S)
      (labels label (fire S c)) :=
  ⟨ruleOf label c, ⟨c, member, used, rfl⟩, ruleOf_enabled enabled used, labels_fire_eq_result enabled⟩

/-! ## Waking contexts -/

/-- **The bag label lies below the labels of the identity-level least waking context.** -/
theorem bag_label_le {S : Finset O} {c : Commit O R} (apart : Disjoint c.taken c.kept) :
    (ruleOf label c).redex - labels label S ≤ labels label ((c.taken ∪ c.kept) \ S) := by
  rw [ruleOf_redex apart]
  set U := c.taken ∪ c.kept
  have split : labels label (U \ S) = labels label U - labels label (U ∩ S) := by
    rw [← labels_sdiff_of_subset label Finset.inter_subset_left, Finset.sdiff_inter_self_left]
  rw [split]
  exact tsub_le_tsub_left (labels_mono Finset.inter_subset_right) _

omit [DecidableEq O] in
/-- Counting one label in the labels of a set on which labels are injective. -/
theorem count_labels_of_injOn {U X : Finset O} (inj : Set.InjOn label ↑U) (sub : X ⊆ U) (x : R) :
    Multiset.count x (labels label X) = if ∃ o ∈ X, label o = x then 1 else 0 := by
  unfold labels
  rw [Multiset.count_map]
  split_ifs with h
  · obtain ⟨o, inX, rfl⟩ := h
    have : X.val.filter (fun a => label o = label a) = {o} := by
      have eq : X.filter (fun a => label o = label a) = {o} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨inA, same⟩
          exact (inj (sub inA) (sub inX) same.symm)
        · rintro rfl; exact ⟨inX, rfl⟩
      have := congrArg Finset.val eq
      simpa [Finset.filter_val] using this
    rw [this]; rfl
  · rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro a inA same
    exact h ⟨a, Finset.mem_val.mp inA, same.symm⟩

/-- **With labels injective on the store and the commit's uses, the two labels agree.** -/
theorem bag_label_eq_of_injOn {S : Finset O} {c : Commit O R} (apart : Disjoint c.taken c.kept)
    (inj : Set.InjOn label ↑(S ∪ (c.taken ∪ c.kept))) :
    (ruleOf label c).redex - labels label S = labels label ((c.taken ∪ c.kept) \ S) := by
  rw [ruleOf_redex apart]
  set U := c.taken ∪ c.kept
  ext x
  rw [Multiset.count_sub, count_labels_of_injOn inj Finset.subset_union_right,
    count_labels_of_injOn inj Finset.subset_union_left,
    count_labels_of_injOn inj ((Finset.sdiff_subset).trans Finset.subset_union_right)]
  by_cases hU : ∃ o ∈ U, label o = x
  · obtain ⟨o, inU, rfl⟩ := hU
    by_cases inS : o ∈ S
    · have : ∃ o' ∈ S, label o' = label o := ⟨o, inS, rfl⟩
      have notDiff : ¬ ∃ o' ∈ U \ S, label o' = label o := by
        rintro ⟨o', inDiff, same⟩
        have := inj (Finset.mem_union_right _ (Finset.mem_sdiff.mp inDiff).1)
          (Finset.mem_union_right _ inU) same
        subst this
        exact (Finset.mem_sdiff.mp inDiff).2 inS
      rw [if_pos ⟨o, inU, rfl⟩, if_pos this, if_neg notDiff]
    · have notS : ¬ ∃ o' ∈ S, label o' = label o := by
        rintro ⟨o', inS', same⟩
        have := inj (Finset.mem_union_left _ inS') (Finset.mem_union_right _ inU) same
        subst this
        exact inS inS'
      have diff : ∃ o' ∈ U \ S, label o' = label o := ⟨o, Finset.mem_sdiff.mpr ⟨inU, inS⟩, rfl⟩
      rw [if_pos ⟨o, inU, rfl⟩, if_neg notS, if_pos diff]
  · have notDiff : ¬ ∃ o' ∈ U \ S, label o' = x := fun ⟨o', inDiff, same⟩ =>
      hU ⟨o', (Finset.mem_sdiff.mp inDiff).1, same⟩
    rw [if_neg hU, if_neg notDiff]
    simp

/-- **The bag label lies below the labels of every arrival that wakes a positive commit**, through
the identity-level least waking context of the reactive module. -/
theorem bag_label_le_arrival {S : Finset O} {c : Commit O R} (positive : c.Positive)
    (apart : Disjoint c.taken c.kept) (fresh : Disjoint c.made S) {arrival : Finset O}
    (avoids : Disjoint c.made arrival) (wakes : Enabled label (S ∪ arrival) c) :
    (ruleOf label c).redex - labels label S ≤ labels label arrival := by
  have least := (enabled_union_iff positive apart fresh avoids).mp wakes
  exact (bag_label_le apart).trans (labels_mono least)

/-! ## Controls -/

namespace Controls

/-- Occurrences `3` and `5` both carry the token. -/
def twoTokens : ℕ → Bool := fun _ => true

/-- Take occurrence `5`. -/
def takeFive : Commit ℕ Bool := ⟨{5}, ∅, ∅, []⟩

/-- **With repeated labels the bag label is strictly smaller.** At the store `{3}`, the commit that
takes occurrence `5` waits for occurrence `5`; its bag rule, "take a token", is enabled already. -/
theorem bag_label_smaller :
    (({5} : Finset ℕ) ∪ ∅) \ {3} = {5} ∧
      (ruleOf twoTokens takeFive).redex - labels twoTokens ({3} : Finset ℕ) = 0 ∧
      labels twoTokens ((({5} : Finset ℕ) ∪ ∅) \ {3}) = {true} := by
  refine ⟨by decide, ?_, by decide⟩
  simp [ruleOf, takeFive, Rule.redex, labels, twoTokens]

/-- Keep occurrence `5` and query every label, having seen `5`. -/
def keepAndQuery : Commit ℕ Bool := ⟨∅, {5}, ∅, [⟨fun _ => true, {5}⟩]⟩

/-- **Queries used, positive**: what the query saw, `5`, is kept. -/
theorem keepAndQuery_queriesUsed : QueriesUsed keepAndQuery := by
  unfold QueriesUsed keepAndQuery; decide

/-- Query every label, having seen `5`, and keep nothing. -/
def queryOnly : Commit ℕ Bool := ⟨∅, ∅, ∅, [⟨fun _ => true, {5}⟩]⟩

/-- **Queries used, negative**: the query saw `5`, which the commit neither takes nor keeps; its
normal form keeps it (`normalize`). -/
theorem queryOnly_not_queriesUsed : ¬ QueriesUsed queryOnly := by
  unfold QueriesUsed queryOnly; decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence
