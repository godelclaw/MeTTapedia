import Mettapedia.GSLT.Causality.FactLinearResources

/-!
# Double-pushout rewriting of a space of atom occurrences

A space is a finite set of atom *occurrences*, each labelled by its atom. A rule instance of a resource system
(`ResourceInteraction.System`) is a span `L ← K → R` over such spaces: `K` is what it reads and keeps, `L ∖ K` is
what it consumes, and `R ∖ K` is what it produces. A space has no edges between its occurrences, so the dangling
condition of double-pushout rewriting is empty, and only the identification condition remains: an occurrence the
rule consumes is not also one it keeps.

All spaces of a run are subsets of one supply of occurrences and every morphism is an inclusion, so the pushouts
along inclusions are unions whose intersection is the shared part.

## The direct derivation

A match (`Match`) picks the consumed and the kept occurrences, with the instance's labels, inside the state,
consumed and kept apart.
* **The two pushout squares** (`left_square`, `right_square`): the context `D` (the state without the consumed
  occurrences) and the rule's left side make up the state and meet in the kept part; `D` and the right side make
  up the result and meet in the kept part.
* **The context is unique** (`context_unique`): any set making up the state with the left side and meeting it in
  the kept part is `D`.
* **Counted, the derivation is one firing** (`labels_result`), and **a match exists exactly when the instance is
  enabled** (`exists_match_iff`).

## Parallel independence

Two matches are *parallel independent* when they overlap only in occurrences both keep (`Independent`).
* **Local Church–Rosser** (`Match.after`, `local_church_rosser`): each match survives the other's derivation,
  and the two orders reach one space.
* **Otherwise a derivation destroys the other's match** (`not_independent_destroys`).
* **Counted, independence is concurrency** (`concurrent_iff_exists_independent`): two instances are concurrent at
  a bag exactly when some state with that bag of labels has parallel independent matches for them. With a
  declaration of facts, two enabled instances with no independent matches are short of a linear resource
  (`exists_linear_shortfall_of_no_independent`): this is the double-pushout form of "every conflict is a linear
  shortage".

## A static test for conflicts

If the consumption of each of two instances avoids everything the other consumes or reads, they are concurrent
wherever both are enabled (`concurrent_of_consumptionApart`). A catalogue whose distinct instances are pairwise
like this is free of conflicts and confluent (`confluent_of_consumptionApart`), whether or not it consumes.
Keep-only catalogues are the case with no consumption at all.

## Controls

* Reading and consuming the same atom needs two occurrences of it: one occurrence admits no match
  (`readTake_one_copy_no_match`), two admit one (`readTake_two_copies_match`). Dropping the identification
  condition breaks the right square: the kept occurrence is not in the context (`unidentified_kept_vanishes`).
* Two readers of one token have independent matches (`readers_independent`); a reader and a consumer of one token
  have none (`reader_taker_not_independent`).
* Two consumers of different tokens and a reader of a third form a consuming catalogue that is confluent
  (`apart_catalogue_confluent`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

universe uRes uRule uOcc

namespace System

variable {R : Type uRes} [DecidableEq R] (S : System.{uRes, uRule} R)
variable {O : Type uOcc} [DecidableEq O] (label : O → R)

/-! ## Labels of occurrences -/

/-- The bag of atoms a set of occurrences carries. -/
def labels (X : Finset O) : Multiset R := X.val.map label

variable {label}

omit [DecidableEq R] [DecidableEq O] in
theorem labels_mono {X Y : Finset O} (sub : X ⊆ Y) : labels label X ≤ labels label Y :=
  Multiset.map_le_map (Finset.val_le_iff.mpr sub)

omit [DecidableEq R] in
theorem labels_union_of_disjoint {X Y : Finset O} (apart : Disjoint X Y) :
    labels label (X ∪ Y) = labels label X + labels label Y := by
  rw [← Finset.disjUnion_eq_union X Y apart]
  exact Multiset.map_add _ _ _

theorem labels_sdiff {X Y : Finset O} (sub : Y ⊆ X) :
    labels label (X \ Y) = labels label X - labels label Y := by
  have split : labels label X = labels label (X \ Y) + labels label Y := by
    rw [← labels_union_of_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_of_subset sub]
  rw [split, add_tsub_cancel_right]

theorem labels_erase {X : Finset O} {o : O} (member : o ∈ X) :
    labels label (X.erase o) = (labels label X).erase (label o) := by
  have whole : labels label X = label o ::ₘ labels label (X.erase o) := by
    unfold labels
    rw [Finset.erase_val, ← Multiset.map_cons, Multiset.cons_erase (Finset.mem_val.mpr member)]
  rw [whole, Multiset.erase_cons_head]

/-- **Any bag below the labels of a set is the labels of a subset.** -/
theorem exists_sub_labels (A : Multiset R) :
    ∀ {X : Finset O}, A ≤ labels label X → ∃ Y ⊆ X, labels label Y = A := by
  induction A using Multiset.induction_on with
  | empty => exact fun _ => ⟨∅, Finset.empty_subset _, rfl⟩
  | cons a A ih =>
      intro X le
      have present : a ∈ labels label X := Multiset.mem_of_le le (Multiset.mem_cons_self a A)
      obtain ⟨o, member, rfl⟩ := Multiset.mem_map.mp present
      have member' : o ∈ X := Finset.mem_val.mp member
      have rest : A ≤ labels label (X.erase o) := by
        rw [labels_erase member']
        rw [← Multiset.cons_erase present] at le
        exact (Multiset.cons_le_cons_iff _).mp le
      obtain ⟨Y, sub, labelsY⟩ := ih rest
      have notIn : o ∉ Y := fun inY => (Finset.notMem_erase o X) (sub inY)
      refine ⟨insert o Y, Finset.insert_subset member' (sub.trans (Finset.erase_subset o X)), ?_⟩
      unfold labels at labelsY ⊢
      rw [Finset.insert_val_of_notMem notIn, Multiset.map_cons, labelsY]

/-! ## Matches and the direct derivation -/

variable (label)

/-- **A match of an instance into a state**: the consumed and the kept occurrences, with the instance's labels,
inside the state, and apart (the identification condition). -/
structure Match (state : Finset O) {site : S.Site} (i : S.Instance site) where
  taken : Finset O
  kept : Finset O
  taken_sub : taken ⊆ state
  kept_sub : kept ⊆ state
  taken_labels : labels label taken = S.consume i
  kept_labels : labels label kept = S.read i
  identification : Disjoint taken kept

variable {S label}

namespace Match

variable {state : Finset O} {site : S.Site} {i : S.Instance site}

/-- The context: the state without the consumed occurrences. -/
def context (m : S.Match label state i) : Finset O := state \ m.taken

/-- The result of the derivation, with fresh occurrences `made` for the production. -/
def result (m : S.Match label state i) (made : Finset O) : Finset O := m.context ∪ made

omit [DecidableEq R] in
/-- **The left pushout square**: the context and the left side make up the state and meet in the kept part. -/
theorem left_square (m : S.Match label state i) :
    m.context ∪ (m.taken ∪ m.kept) = state ∧ m.context ∩ (m.taken ∪ m.kept) = m.kept := by
  have takenSub := m.taken_sub
  have keptSub := m.kept_sub
  have apart := m.identification
  constructor
  · ext o
    simp only [context, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨inState, -⟩ | inTaken | inKept)
      · exact inState
      · exact takenSub inTaken
      · exact keptSub inKept
    · intro inState
      by_cases inTaken : o ∈ m.taken
      · exact Or.inr (Or.inl inTaken)
      · exact Or.inl ⟨inState, inTaken⟩
  · ext o
    simp only [context, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨-, notTaken⟩, inTaken | inKept⟩
      · exact absurd inTaken notTaken
      · exact inKept
    · intro inKept
      exact ⟨⟨keptSub inKept, Finset.disjoint_right.mp apart inKept⟩, Or.inr inKept⟩

omit [DecidableEq R] in
/-- **The right pushout square**: the context and the right side make up the result and meet in the kept
part, when the produced occurrences are fresh. -/
theorem right_square (m : S.Match label state i) {made : Finset O} (fresh : Disjoint made state) :
    m.context ∪ (m.kept ∪ made) = m.result made ∧ m.context ∩ (m.kept ∪ made) = m.kept := by
  have keptSub := m.kept_sub
  have apart := m.identification
  constructor
  · ext o
    simp only [result, context, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (inContext | inKept | inMade)
      · exact Or.inl inContext
      · exact Or.inl ⟨keptSub inKept, Finset.disjoint_right.mp apart inKept⟩
      · exact Or.inr inMade
    · rintro (inContext | inMade)
      · exact Or.inl inContext
      · exact Or.inr (Or.inr inMade)
  · ext o
    simp only [context, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨inState, -⟩, inKept | inMade⟩
      · exact inKept
      · exact absurd inState (Finset.disjoint_left.mp fresh inMade)
    · intro inKept
      exact ⟨⟨keptSub inKept, Finset.disjoint_right.mp apart inKept⟩, Or.inl inKept⟩

omit [DecidableEq R] in
/-- **The pushout complement is unique**: any set making up the state with the left side, and meeting it in the
kept part, is the context. -/
theorem context_unique (m : S.Match label state i) {D : Finset O}
    (makesUp : D ∪ (m.taken ∪ m.kept) = state) (meets : D ∩ (m.taken ∪ m.kept) = m.kept) :
    D = m.context := by
  have apart := m.identification
  ext o
  simp only [context, Finset.mem_sdiff]
  constructor
  · intro inD
    refine ⟨makesUp ▸ Finset.mem_union_left _ inD, fun inTaken => ?_⟩
    have inKept : o ∈ m.kept := meets ▸ Finset.mem_inter.mpr ⟨inD, Finset.mem_union_left _ inTaken⟩
    exact Finset.disjoint_left.mp apart inTaken inKept
  · rintro ⟨inState, notTaken⟩
    rw [← makesUp] at inState
    rcases Finset.mem_union.mp inState with inD | inLeft
    · exact inD
    · rcases Finset.mem_union.mp inLeft with inTaken | inKept
      · exact absurd inTaken notTaken
      · exact (Finset.mem_inter.mp (meets.symm ▸ inKept : o ∈ D ∩ (m.taken ∪ m.kept))).1

/-- **Counted, the derivation is one firing.** -/
theorem labels_result (m : S.Match label state i) {made : Finset O} (fresh : Disjoint made state)
    (madeLabels : labels label made = S.produce i) :
    labels label (m.result made) = S.fire (labels label state) i := by
  have apart : Disjoint m.context made :=
    Finset.disjoint_of_subset_left Finset.sdiff_subset fresh.symm
  rw [result, labels_union_of_disjoint apart, context, labels_sdiff m.taken_sub, m.taken_labels,
    madeLabels]
  rfl

end Match

/-- **A match exists exactly when the instance is enabled.** -/
theorem exists_match_iff (state : Finset O) {site : S.Site} (i : S.Instance site) :
    Nonempty (S.Match label state i) ↔ S.Enables (labels label state) i := by
  constructor
  · rintro ⟨m⟩
    unfold Enables
    rw [← m.taken_labels, ← m.kept_labels, ← labels_union_of_disjoint m.identification]
    exact labels_mono (Finset.union_subset m.taken_sub m.kept_sub)
  · intro enabled
    obtain ⟨Y, sub, labelsY⟩ := exists_sub_labels _ enabled
    obtain ⟨T, subT, labelsT⟩ := exists_sub_labels (label := label) (S.consume i)
      (labelsY ▸ Multiset.le_add_right _ _ : S.consume i ≤ labels label Y)
    have keptLabels : labels label (Y \ T) = S.read i := by
      rw [labels_sdiff subT, labelsY, labelsT, add_tsub_cancel_left]
    exact ⟨⟨T, Y \ T, subT.trans sub, Finset.sdiff_subset.trans sub, labelsT, keptLabels,
      Finset.disjoint_sdiff⟩⟩

/-! ## Parallel independence -/

section Independence

variable {state : Finset O} {site₁ site₂ : S.Site} {i : S.Instance site₁} {j : S.Instance site₂}

/-- **Parallel independence**: the two matches overlap only in occurrences both keep. -/
def Independent (m₁ : S.Match label state i) (m₂ : S.Match label state j) : Prop :=
  (m₁.taken ∪ m₁.kept) ∩ (m₂.taken ∪ m₂.kept) ⊆ m₁.kept ∩ m₂.kept

omit [DecidableEq R] in
/-- Independence in its delete–use form: neither consumes what the other uses. -/
theorem independent_iff (m₁ : S.Match label state i) (m₂ : S.Match label state j) :
    Independent m₁ m₂ ↔
      Disjoint m₁.taken (m₂.taken ∪ m₂.kept) ∧ Disjoint m₂.taken (m₁.taken ∪ m₁.kept) := by
  have apart₁ := m₁.identification
  have apart₂ := m₂.identification
  constructor
  · intro indep
    constructor
    · refine Finset.disjoint_left.mpr fun o inTaken inUse => ?_
      have both := indep (Finset.mem_inter.mpr ⟨Finset.mem_union_left _ inTaken, inUse⟩)
      exact Finset.disjoint_left.mp apart₁ inTaken (Finset.mem_inter.mp both).1
    · refine Finset.disjoint_left.mpr fun o inTaken inUse => ?_
      have both := indep (Finset.mem_inter.mpr ⟨inUse, Finset.mem_union_left _ inTaken⟩)
      exact Finset.disjoint_left.mp apart₂ inTaken (Finset.mem_inter.mp both).2
  · rintro ⟨one, two⟩ o member
    obtain ⟨inUse₁, inUse₂⟩ := Finset.mem_inter.mp member
    rcases Finset.mem_union.mp inUse₁ with inTaken₁ | inKept₁
    · exact absurd inUse₂ (Finset.disjoint_left.mp one inTaken₁)
    · rcases Finset.mem_union.mp inUse₂ with inTaken₂ | inKept₂
      · exact absurd (Finset.mem_union_right _ inKept₁) (Finset.disjoint_left.mp two inTaken₂)
      · exact Finset.mem_inter.mpr ⟨inKept₁, inKept₂⟩

/-- **A match survives an independent derivation**: the same occurrences match in its result. -/
def Match.after (m₂ : S.Match label state j) (m₁ : S.Match label state i) {made₁ : Finset O}
    (indep : Independent m₁ m₂) : S.Match label (m₁.result made₁) j where
  taken := m₂.taken
  kept := m₂.kept
  taken_sub := fun o inTaken => by
    have avoid := ((independent_iff m₁ m₂).mp indep).1
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨m₂.taken_sub inTaken,
      fun inTaken₁ => Finset.disjoint_left.mp avoid inTaken₁ (Finset.mem_union_left _ inTaken)⟩)
  kept_sub := fun o inKept => by
    have avoid := ((independent_iff m₁ m₂).mp indep).1
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨m₂.kept_sub inKept,
      fun inTaken₁ => Finset.disjoint_left.mp avoid inTaken₁ (Finset.mem_union_right _ inKept)⟩)
  taken_labels := m₂.taken_labels
  kept_labels := m₂.kept_labels
  identification := m₂.identification

omit [DecidableEq R] in
/-- **Local Church–Rosser**: two independent derivations, with fresh productions, reach one space in either
order. -/
theorem local_church_rosser (m₁ : S.Match label state i) (m₂ : S.Match label state j)
    (indep : Independent m₁ m₂) {made₁ made₂ : Finset O} (fresh₁ : Disjoint made₁ state)
    (fresh₂ : Disjoint made₂ state) :
    (m₂.after m₁ (made₁ := made₁) indep).result made₂ =
      (m₁.after m₂ (made₁ := made₂) (by
        rw [independent_iff] at indep ⊢
        exact ⟨indep.2, indep.1⟩)).result made₁ := by
  ext o
  simp only [Match.result, Match.context, Match.after, Finset.mem_union, Finset.mem_sdiff]
  have notTaken₂ : o ∈ made₁ → o ∉ m₂.taken := fun inMade inTaken =>
    Finset.disjoint_left.mp fresh₁ inMade (m₂.taken_sub inTaken)
  have notTaken₁ : o ∈ made₂ → o ∉ m₁.taken := fun inMade inTaken =>
    Finset.disjoint_left.mp fresh₂ inMade (m₁.taken_sub inTaken)
  constructor
  · rintro (⟨⟨inState, notT₁⟩ | inMade₁, notT₂⟩ | inMade₂)
    · exact Or.inl ⟨Or.inl ⟨inState, notT₂⟩, notT₁⟩
    · exact Or.inr inMade₁
    · exact Or.inl ⟨Or.inr inMade₂, notTaken₁ inMade₂⟩
  · rintro (⟨⟨inState, notT₂⟩ | inMade₂, notT₁⟩ | inMade₁)
    · exact Or.inl ⟨Or.inl ⟨inState, notT₁⟩, notT₂⟩
    · exact Or.inr inMade₂
    · exact Or.inl ⟨Or.inr inMade₁, notTaken₂ inMade₁⟩

omit [DecidableEq R] in
/-- **Without independence, one derivation destroys the other's match**: an occurrence the other uses is
missing from its result. -/
theorem not_independent_destroys (m₁ : S.Match label state i) (m₂ : S.Match label state j)
    (dependent : ¬ Independent m₁ m₂) {made₁ made₂ : Finset O} (fresh₁ : Disjoint made₁ state)
    (fresh₂ : Disjoint made₂ state) :
    (∃ o ∈ m₂.taken ∪ m₂.kept, o ∉ m₁.result made₁) ∨
      (∃ o ∈ m₁.taken ∪ m₁.kept, o ∉ m₂.result made₂) := by
  rw [independent_iff, not_and_or] at dependent
  rcases dependent with one | two
  · obtain ⟨o, inTaken, inUse⟩ := Finset.not_disjoint_iff.mp one
    refine Or.inl ⟨o, inUse, ?_⟩
    simp only [Match.result, Match.context, Finset.mem_union, Finset.mem_sdiff, not_or, not_and,
      not_not]
    exact ⟨fun _ => inTaken, fun inMade => Finset.disjoint_left.mp fresh₁ inMade (m₁.taken_sub inTaken)⟩
  · obtain ⟨o, inTaken, inUse⟩ := Finset.not_disjoint_iff.mp two
    refine Or.inr ⟨o, inUse, ?_⟩
    simp only [Match.result, Match.context, Finset.mem_union, Finset.mem_sdiff, not_or, not_and,
      not_not]
    exact ⟨fun _ => inTaken, fun inMade => Finset.disjoint_left.mp fresh₂ inMade (m₂.taken_sub inTaken)⟩

/-- **Counted, parallel independence is concurrency**: two instances are concurrent at the labels of a state
exactly when they have parallel independent matches into it. -/
theorem concurrent_iff_exists_independent (state : Finset O) (i : S.Instance site₁)
    (j : S.Instance site₂) :
    S.Concurrent (labels label state) i j ↔
      ∃ (m₁ : S.Match label state i) (m₂ : S.Match label state j), Independent m₁ m₂ := by
  rw [concurrent_iff_union]
  constructor
  · intro fits
    obtain ⟨Y, subY, labelsY⟩ := exists_sub_labels _ fits
    obtain ⟨T₁, subT₁, labelsT₁⟩ := exists_sub_labels (label := label) (S.consume i)
      (by rw [labelsY, add_assoc]; exact Multiset.le_add_right _ _)
    have rest₁ : labels label (Y \ T₁) = S.consume j + (S.read i ∪ S.read j) := by
      rw [labels_sdiff subT₁, labelsY, labelsT₁, add_assoc, add_tsub_cancel_left]
    obtain ⟨T₂, subT₂, labelsT₂⟩ := exists_sub_labels (label := label) (S.consume j)
      (by rw [rest₁]; exact Multiset.le_add_right _ _)
    have rest₂ : labels label ((Y \ T₁) \ T₂) = S.read i ∪ S.read j := by
      rw [labels_sdiff subT₂, rest₁, labelsT₂, add_tsub_cancel_left]
    obtain ⟨K₁, subK₁, labelsK₁⟩ := exists_sub_labels (label := label) (S.read i)
      (by rw [rest₂]; exact Multiset.le_union_left)
    obtain ⟨K₂, subK₂, labelsK₂⟩ := exists_sub_labels (label := label) (S.read j)
      (by rw [rest₂]; exact Multiset.le_union_right)
    have inY : (Y \ T₁) \ T₂ ⊆ Y := Finset.sdiff_subset.trans Finset.sdiff_subset
    have avoid₁ : ∀ o ∈ (Y \ T₁) \ T₂, o ∉ T₁ := fun o member =>
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp member).1).2
    have avoid₂ : ∀ o ∈ (Y \ T₁) \ T₂, o ∉ T₂ := fun o member => (Finset.mem_sdiff.mp member).2
    have T₂avoid : ∀ o ∈ T₂, o ∉ T₁ := fun o member => (Finset.mem_sdiff.mp (subT₂ member)).2
    let m₁ : S.Match label state i :=
      ⟨T₁, K₁, subT₁.trans subY, (subK₁.trans inY).trans subY, labelsT₁, labelsK₁,
        Finset.disjoint_right.mpr fun o member => avoid₁ o (subK₁ member)⟩
    let m₂ : S.Match label state j :=
      ⟨T₂, K₂, (subT₂.trans Finset.sdiff_subset).trans subY, (subK₂.trans inY).trans subY, labelsT₂,
        labelsK₂, Finset.disjoint_right.mpr fun o member => avoid₂ o (subK₂ member)⟩
    refine ⟨m₁, m₂, ?_⟩
    rw [independent_iff]
    constructor
    · refine Finset.disjoint_left.mpr fun o inT₁ inUse => ?_
      rcases Finset.mem_union.mp inUse with inT₂ | inK₂
      · exact T₂avoid o inT₂ inT₁
      · exact avoid₁ o (subK₂ inK₂) inT₁
    · refine Finset.disjoint_left.mpr fun o inT₂ inUse => ?_
      rcases Finset.mem_union.mp inUse with inT₁ | inK₁
      · exact T₂avoid o inT₂ inT₁
      · exact avoid₂ o (subK₁ inK₁) inT₂
  · rintro ⟨m₁, m₂, indep⟩
    obtain ⟨one, two⟩ := (independent_iff m₁ m₂).mp indep
    have T₁T₂ : Disjoint m₁.taken m₂.taken := Finset.disjoint_of_subset_right Finset.subset_union_left one
    have T₁K : Disjoint m₁.taken (m₁.kept ∪ m₂.kept) := Finset.disjoint_union_right.mpr
      ⟨m₁.identification, Finset.disjoint_of_subset_right Finset.subset_union_right one⟩
    have T₂K : Disjoint m₂.taken (m₁.kept ∪ m₂.kept) := Finset.disjoint_union_right.mpr
      ⟨Finset.disjoint_of_subset_right Finset.subset_union_right two, m₂.identification⟩
    have readsLe : S.read i ∪ S.read j ≤ labels label (m₁.kept ∪ m₂.kept) := by
      rw [← m₁.kept_labels, ← m₂.kept_labels]
      exact Multiset.union_le (labels_mono Finset.subset_union_left)
        (labels_mono Finset.subset_union_right)
    have whole : labels label (m₁.taken ∪ (m₂.taken ∪ (m₁.kept ∪ m₂.kept))) =
        labels label m₁.taken + labels label m₂.taken + labels label (m₁.kept ∪ m₂.kept) := by
      rw [labels_union_of_disjoint (Finset.disjoint_union_right.mpr ⟨T₁T₂, T₁K⟩),
        labels_union_of_disjoint T₂K, add_assoc]
    have inside : m₁.taken ∪ (m₂.taken ∪ (m₁.kept ∪ m₂.kept)) ⊆ state :=
      Finset.union_subset m₁.taken_sub (Finset.union_subset m₂.taken_sub
        (Finset.union_subset m₁.kept_sub m₂.kept_sub))
    calc S.consume i + S.consume j + (S.read i ∪ S.read j)
        ≤ labels label m₁.taken + labels label m₂.taken + labels label (m₁.kept ∪ m₂.kept) := by
          rw [m₁.taken_labels, m₂.taken_labels]
          exact add_le_add le_rfl readsLe
      _ = labels label (m₁.taken ∪ (m₂.taken ∪ (m₁.kept ∪ m₂.kept))) := whole.symm
      _ ≤ labels label state := labels_mono inside

/-- **Every conflict is a linear shortage, in double-pushout form**: two enabled instances with no parallel
independent matches into a state are short of some linear resource there. -/
theorem exists_linear_shortfall_of_no_independent {fact : R → Prop} [DecidablePred fact] (respects : S.ConsumesNoFacts fact)
    (state : Finset O) {i : S.Instance site₁} {j : S.Instance site₂}
    (enabledI : S.Enables (labels label state) i) (enabledJ : S.Enables (labels label state) j)
    (none : ¬ ∃ (m₁ : S.Match label state i) (m₂ : S.Match label state j), Independent m₁ m₂) :
    ∃ r, ¬ fact r ∧ (labels label state).count r <
      (S.consume i + S.consume j + (S.read i ∪ S.read j)).count r :=
  S.exists_linear_shortfall respects enabledI enabledJ fun concurrent =>
    none ((concurrent_iff_exists_independent state i j).mp concurrent)

end Independence

/-! ## A static test for conflicts -/

/-- The consumption of `i` avoids everything `j` consumes or reads. -/
def ConsumptionAvoids {site₁ site₂ : S.Site} (i : S.Instance site₁) (j : S.Instance site₂) : Prop :=
  ∀ r ∈ S.consume i, r ∉ S.consume j ∧ r ∉ S.read j

/-- **Two instances whose consumptions avoid each other's footprints are concurrent wherever both are
enabled.** -/
theorem concurrent_of_consumptionApart {M : Multiset R} {site₁ site₂ : S.Site} {i : S.Instance site₁}
    {j : S.Instance site₂} (enabledI : S.Enables M i) (enabledJ : S.Enables M j)
    (avoidsIJ : S.ConsumptionAvoids i j) (avoidsJI : S.ConsumptionAvoids j i) : S.Concurrent M i j := by
  rw [concurrent_iff_union, Multiset.le_iff_count]
  unfold Enables at enabledI enabledJ
  rw [Multiset.le_iff_count] at enabledI enabledJ
  intro r
  have atI := enabledI r
  have atJ := enabledJ r
  simp only [Multiset.count_add, Multiset.count_union] at atI atJ ⊢
  by_cases inI : r ∈ S.consume i
  · obtain ⟨notJ, notReadJ⟩ := avoidsIJ r inI
    rw [Multiset.count_eq_zero.mpr notJ, Multiset.count_eq_zero.mpr notReadJ]
    omega
  · rw [Multiset.count_eq_zero.mpr inI]
    by_cases inJ : r ∈ S.consume j
    · rw [Multiset.count_eq_zero.mpr (avoidsJI r inJ).2]
      omega
    · rw [Multiset.count_eq_zero.mpr inJ]
      omega

/-- A catalogue whose distinct instances consume nothing the other uses. -/
def ConsumptionApart (catalogue : List S.Entry) : Prop :=
  ∀ first ∈ catalogue, ∀ second ∈ catalogue, first ≠ second → S.ConsumptionAvoids first.2 second.2

theorem conflictFree_of_consumptionApart {catalogue : List S.Entry}
    (apart : S.ConsumptionApart catalogue) : S.ConflictFree catalogue :=
  fun _ first second firstIn secondIn different enabledFirst enabledSecond =>
    S.concurrent_of_consumptionApart enabledFirst enabledSecond
      (apart first firstIn second secondIn different)
      (apart second secondIn first firstIn (Ne.symm different))

/-- **A catalogue whose consumptions avoid each other's footprints is confluent**, consuming or not. -/
theorem confluent_of_consumptionApart {catalogue : List S.Entry} (apart : S.ConsumptionApart catalogue)
    {M N₁ N₂ : Multiset R}
    (reach₁ : Relation.ReflTransGen (S.CatalogueStep catalogue) M N₁)
    (reach₂ : Relation.ReflTransGen (S.CatalogueStep catalogue) M N₂) :
    Relation.Join (Relation.ReflTransGen (S.CatalogueStep catalogue)) N₁ N₂ :=
  S.confluent_of_conflictFree catalogue (S.conflictFree_of_consumptionApart apart) reach₁ reach₂

end System

/-! ## Controls -/

namespace DoublePushoutControls

open Mettapedia.GSLT.Causality.ResourceInteraction.System

/-- Atoms of the controls. -/
inductive Atom where
  | tok | a | b | c | gotA | gotB | sawC | seen
  deriving DecidableEq, Repr

open Atom

/-- One rule instance that reads `tok` and consumes `tok`. -/
def readTake : System Atom where
  Site := Unit
  Instance := fun _ => Unit
  consume := fun _ => {tok}
  read := fun _ => {tok}
  produce := fun _ => {seen}

/-- **One occurrence admits no match for reading and consuming it**: the identification condition. -/
theorem readTake_one_copy_no_match :
    ¬ Nonempty (readTake.Match (fun _ : Fin 1 => tok) Finset.univ (site := ()) ()) := fun found =>
  absurd ((exists_match_iff _ _).mp found) (by unfold System.Enables labels; decide)

/-- **Two occurrences admit one.** -/
theorem readTake_two_copies_match :
    Nonempty (readTake.Match (fun _ : Fin 2 => tok) Finset.univ (site := ()) ()) :=
  (exists_match_iff _ _).mpr (by unfold System.Enables labels; decide)

/-- **Without the identification condition a kept occurrence vanishes.** With one occurrence of `tok`, using it
both as the consumed and as the kept item gives the right labels to both, but the two parts are not apart, and
the context (the state without the consumed item) no longer meets the right side in the kept part: the right
square of the derivation fails. -/
theorem unidentified_kept_vanishes :
    labels (fun _ : Fin 1 => tok) {0} = readTake.consume (site := ()) () ∧
      labels (fun _ : Fin 1 => tok) {0} = readTake.read (site := ()) () ∧
      ¬ Disjoint ({0} : Finset (Fin 1)) {0} ∧
      (Finset.univ \ {0} : Finset (Fin 1)) ∩ ({0} ∪ ∅) ≠ {0} := by
  refine ⟨rfl, rfl, by decide, by decide⟩

/-- One reader and one consumer of `tok`. -/
def readerTaker : System Atom where
  Site := Unit
  Instance := fun _ => Bool
  consume := fun (reader : Bool) => match reader with
    | true => 0
    | false => {tok}
  read := fun (reader : Bool) => match reader with
    | true => {tok}
    | false => 0
  produce := fun (reader : Bool) => match reader with
    | true => {sawC}
    | false => {gotA}

/-- **Two readers of one token have independent matches.** -/
theorem readers_independent :
    ∃ (m₁ : readerTaker.Match (fun _ : Fin 1 => tok) Finset.univ (site := ()) true)
      (m₂ : readerTaker.Match (fun _ : Fin 1 => tok) Finset.univ (site := ()) true),
      Independent m₁ m₂ :=
  (concurrent_iff_exists_independent _ _ _).mp (by unfold System.Concurrent labels; decide)

/-- **A reader and a consumer of one token have no independent matches.** -/
theorem reader_taker_not_independent :
    ¬ ∃ (m₁ : readerTaker.Match (fun _ : Fin 1 => tok) Finset.univ (site := ()) true)
      (m₂ : readerTaker.Match (fun _ : Fin 1 => tok) Finset.univ (site := ()) false),
      Independent m₁ m₂ := fun found =>
  absurd ((concurrent_iff_exists_independent _ _ _).mpr found)
    (by unfold System.Concurrent labels; decide)

/-- Two consumers of different tokens and a reader of a third. -/
def apart : System Atom where
  Site := Unit
  Instance := fun _ => Fin 3
  consume := fun (k : Fin 3) => match k with
    | 0 => {a}
    | 1 => {b}
    | 2 => 0
  read := fun (k : Fin 3) => match k with
    | 0 => 0
    | 1 => 0
    | 2 => {c}
  produce := fun (k : Fin 3) => match k with
    | 0 => {gotA}
    | 1 => {gotB}
    | 2 => {sawC}

def apartCatalogue : List apart.Entry := [⟨(), (0 : Fin 3)⟩, ⟨(), (1 : Fin 3)⟩, ⟨(), (2 : Fin 3)⟩]

theorem apart_consumptionApart : apart.ConsumptionApart apartCatalogue := by
  intro first firstIn second secondIn different r member
  simp only [apartCatalogue, List.mem_cons, List.mem_nil_iff, or_false] at firstIn secondIn
  rcases firstIn with rfl | rfl | rfl <;> rcases secondIn with rfl | rfl | rfl <;>
    first
    | exact absurd rfl different
    | (revert member r; decide)

/-- **A consuming catalogue whose consumptions avoid each other's footprints is confluent.** -/
theorem apart_catalogue_confluent {M N₁ N₂ : Multiset Atom}
    (reach₁ : Relation.ReflTransGen (apart.CatalogueStep apartCatalogue) M N₁)
    (reach₂ : Relation.ReflTransGen (apart.CatalogueStep apartCatalogue) M N₂) :
    Relation.Join (Relation.ReflTransGen (apart.CatalogueStep apartCatalogue)) N₁ N₂ :=
  apart.confluent_of_consumptionApart apart_consumptionApart reach₁ reach₂

/-- The catalogue consumes: it is not keep-only. -/
theorem apart_not_keepOnly : ¬ apart.KeepOnly := fun keep => by
  have empty := keep (site := ()) (0 : Fin 3)
  simp [apart] at empty

end DoublePushoutControls

end Mettapedia.GSLT.Causality.ResourceInteraction
