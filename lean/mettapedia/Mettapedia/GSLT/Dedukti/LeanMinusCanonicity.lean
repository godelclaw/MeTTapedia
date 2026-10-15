import Mettapedia.GSLT.Dedukti.LeanMinusLevelValues

/-!
# The computed sets of sublevels are canonical: Theorems 2 and 3 for all levels

`LeanMinusLevelValues` shows that the set of sublevels computed for a level
has the value of the level.  This module shows the converse that makes the
set a normal form of the semantics: **two levels with one value at every
valuation have one computed set**, with any number of level variables.

## The argument

A computed set is **canonical** (`Canonical`): its sublevels are sorted
strictly by the comparison `cmpS` of the rules, and no sublevel of the set is
below another one for the dominance test `leS`.  The corrected `Add` keeps
canonical sets canonical (`Canonical.addSub`), and so do the increment and the
guarded copies, so the set computed for every level is canonical
(`normalSetWith_canonical`).

A canonical set is determined by its values.

* **A sublevel whose value never exceeds the value of a set is below one
  sublevel of the set** (`exists_leSub_of_eval_le`).  Two valuations decide
  it.  For a constant `C G c`, the valuation that is `1` on the guard `G` and
  `0` elsewhere (`indicator`): the sublevels of the set that are alive there
  have their guards inside `G`, and one of them is at least `c`.  For a
  variable `V G x k`, the same valuation with a value at `x` above every
  constant and offset of the set (`spike`): only a `V G' x k'` with `k ≤ k'`
  reaches `x + k`.
* The dominance test is transitive and antisymmetric on sublevels whose guards
  are sorted (`leSub_trans`, `leSub_antisymm`).  So two canonical sets with
  one value at every valuation have the same sublevels
  (`Canonical.eq_of_dominations`), and being sorted for one strict order they
  are one list (`eq_of_pairwise_of_mem_iff`).

The comparison `cmpS` is a strict order because it is the lexicographic
comparison of a key of natural numbers (`cmpSub_eq_cmpList_key`,
`cmpSub_strict`).

## Consequences

* **Theorem 3, for all levels** (`theorem3_all_levels`): equivalent levels have
  convertible codes in the theory with explicit level substitution, also read
  in any frame (`theorem3_all_levels_in`).
* **Theorem 2, for all levels** (`theorem2_all_levels`): two levels have
  convertible codes exactly when they are equivalent; also inside a
  declaration (`theorem2_all_levels_in`).
* **The empty guard alone decides equivalence over the positive valuations**
  (`conv_paperCode_explicit_iff_positive`): with the rule on `Add` corrected,
  the paper's codes of two levels are convertible exactly when the levels have
  one value at every valuation that is positive everywhere.  The same argument
  applies, with the valuation `1` everywhere in the place of the indicator of a
  guard.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF

/-! ## Comparisons that are strict orders -/

/-- **A comparison whose "less" is a strict order**, and whose "greater" is its
converse. -/
structure StrictComparison {α : Type} (compare : α → α → Ordering) : Prop where
  irrefl : ∀ element, compare element element = .eq
  trans : ∀ {first second third}, compare first second = .lt → compare second third = .lt →
    compare first third = .lt
  swap : ∀ {first second}, compare first second = .gt → compare second first = .lt

theorem cmpNat_strict : StrictComparison cmpNat where
  irrefl := fun _ => cmpNat_eq_eq.mpr rfl
  trans := fun firstSecond secondThird =>
    cmpNat_eq_lt.mpr (Nat.lt_trans (cmpNat_eq_lt.mp firstSecond) (cmpNat_eq_lt.mp secondThird))
  swap := fun above => cmpNat_eq_lt.mpr (cmpNat_eq_gt.mp above)

theorem cmpList_cmpNat_self : ∀ list : List Nat, cmpList cmpNat list list = .eq
  | [] => rfl
  | head :: rest => by
      simp [cmpList, cmpNat_eq_eq.mpr (rfl : head = head), cmpList_cmpNat_self rest]

theorem cmpList_cmpNat_swap :
    ∀ {first second : List Nat}, cmpList cmpNat first second = .gt → cmpList cmpNat second first = .lt
  | [], [], above => by simp [cmpList] at above
  | [], _ :: _, above => by simp [cmpList] at above
  | _ :: _, [], _ => rfl
  | head :: rest, head' :: rest', above => by
      rcases outcome : cmpNat head head' with _ | _ | _
      · simp [cmpList, outcome] at above
      · simp only [cmpList, outcome] at above
        have same := cmpNat_eq_eq.mp outcome
        subst same
        simp [cmpList, outcome, cmpList_cmpNat_swap above]
      · have below := cmpNat_eq_lt.mpr (cmpNat_eq_gt.mp outcome)
        simp [cmpList, below]

theorem cmpList_cmpNat_trans :
    ∀ {first second third : List Nat}, cmpList cmpNat first second = .lt →
      cmpList cmpNat second third = .lt → cmpList cmpNat first third = .lt
  | [], [], _, firstSecond, _ => by simp [cmpList] at firstSecond
  | [], _ :: _, [], _, secondThird => by simp [cmpList] at secondThird
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, firstSecond, _ => by simp [cmpList] at firstSecond
  | _ :: _, _ :: _, [], _, secondThird => by simp [cmpList] at secondThird
  | head :: rest, head' :: rest', head'' :: rest'', firstSecond, secondThird => by
      rcases left : cmpNat head head' with _ | _ | _
      · rcases right : cmpNat head' head'' with _ | _ | _
        · simp [cmpList, cmpNat_strict.trans left right]
        · have same := cmpNat_eq_eq.mp right
          subst same
          simp [cmpList, left]
        · simp [cmpList, right] at secondThird
      · have same := cmpNat_eq_eq.mp left
        subst same
        simp only [cmpList, left] at firstSecond
        rcases right : cmpNat head head'' with _ | _ | _
        · simp [cmpList, right]
        · simp only [cmpList, right] at secondThird
          simp [cmpList, right, cmpList_cmpNat_trans firstSecond secondThird]
        · simp [cmpList, right] at secondThird
      · simp [cmpList, left] at firstSecond

/-- The comparison of lists of naturals is a strict order. -/
theorem cmpList_cmpNat_strict : StrictComparison (cmpList cmpNat) :=
  ⟨cmpList_cmpNat_self, cmpList_cmpNat_trans, cmpList_cmpNat_swap⟩

/-- A key of natural numbers for a sublevel: its kind, its guard with a
terminator below every member, and its numbers. -/
def sublevelKey : Sublevel → List Nat
  | .cst guard constant => 0 :: (guard.map (· + 1) ++ [0, constant])
  | .var guard index offset => 1 :: (guard.map (· + 1) ++ [0, index, offset])

theorem cmpList_guard_append :
    ∀ (guard guard' tail tail' : List Nat),
      cmpList cmpNat (guard.map (· + 1) ++ 0 :: tail) (guard'.map (· + 1) ++ 0 :: tail') =
        match cmpList cmpNat guard guard' with
        | .lt => .lt
        | .eq => cmpList cmpNat tail tail'
        | .gt => .gt
  | [], [], tail, tail' => by simp [cmpList, cmpNat]
  | [], head' :: rest', tail, tail' => by simp [cmpList, cmpNat]
  | head :: rest, [], tail, tail' => by simp [cmpList, cmpNat]
  | head :: rest, head' :: rest', tail, tail' => by
      have ih := cmpList_guard_append rest rest' tail tail'
      simp only [List.map_cons, List.cons_append, cmpList, cmpNat]
      rcases outcome : cmpNat head head' with _ | _ | _
      · rfl
      · exact ih
      · rfl

theorem cmpList_singleton (first second : Nat) :
    cmpList cmpNat [first] [second] = cmpNat first second := by
  rcases outcome : cmpNat first second with _ | _ | _ <;> simp [cmpList, outcome]

theorem cmpList_pair (index offset index' offset' : Nat) :
    cmpList cmpNat [index, offset] [index', offset'] =
      match cmpNat index index' with
      | .lt => .lt
      | .eq => cmpNat offset offset'
      | .gt => .gt := by
  rcases outcome : cmpNat index index' with _ | _ | _ <;>
    rcases inner : cmpNat offset offset' with _ | _ | _ <;> simp [cmpList, outcome, inner]

/-- **The comparison of sublevels is the lexicographic comparison of their
keys.** -/
theorem cmpSub_eq_cmpList_key (first second : Sublevel) :
    cmpSub first second = cmpList cmpNat (sublevelKey first) (sublevelKey second) := by
  cases first with
  | cst guard constant =>
      cases second with
      | cst guard' constant' =>
          simp only [cmpSub, sublevelKey, cmpList, cmpNat]
          rw [cmpList_guard_append, cmpList_singleton]
          cases cmpList cmpNat guard guard' <;> rfl
      | var guard' index' offset' => simp [cmpSub, sublevelKey, cmpList, cmpNat]
  | var guard index offset =>
      cases second with
      | cst guard' constant' => simp [cmpSub, sublevelKey, cmpList, cmpNat]
      | var guard' index' offset' =>
          simp only [cmpSub, sublevelKey, cmpList, cmpNat]
          rw [cmpList_guard_append, cmpList_pair]
          cases cmpList cmpNat guard guard' <;> rfl

/-- **The comparison of sublevels is a strict order.** -/
theorem cmpSub_strict : StrictComparison cmpSub where
  irrefl := fun sublevel => by
    rw [cmpSub_eq_cmpList_key]
    exact cmpList_cmpNat_self _
  trans := fun firstSecond secondThird => by
    rw [cmpSub_eq_cmpList_key] at firstSecond secondThird ⊢
    exact cmpList_cmpNat_trans firstSecond secondThird
  swap := fun above => by
    rw [cmpSub_eq_cmpList_key] at above ⊢
    exact cmpList_cmpNat_swap above

/-! ## Sorted lists -/

/-- **Sorted insertion keeps a list strictly sorted.** -/
theorem insertSorted_pairwise {α : Type} {compare : α → α → Ordering}
    (strict : StrictComparison compare) (element : α) :
    ∀ {list : List α}, list.Pairwise (fun first second => compare first second = .lt) →
      (insertSorted compare element list).Pairwise fun first second => compare first second = .lt
  | [], _ => List.pairwise_singleton _ _
  | head :: rest, sorted => by
      obtain ⟨headBefore, restSorted⟩ := List.pairwise_cons.mp sorted
      rcases outcome : compare element head with _ | _ | _
      · simp only [insertSorted, outcome]
        refine List.pairwise_cons.mpr ⟨fun other member => ?_, sorted⟩
        rcases List.mem_cons.mp member with same | inRest
        · rw [same]
          exact outcome
        · exact strict.trans outcome (headBefore other inRest)
      · simp only [insertSorted, outcome]
        exact sorted
      · simp only [insertSorted, outcome]
        refine List.pairwise_cons.mpr
          ⟨fun other member => ?_, insertSorted_pairwise strict element restSorted⟩
        rcases mem_insertSorted compare element rest other member with same | inRest
        · rw [same]
          exact strict.swap outcome
        · exact headBefore other inRest

/-- **Two lists sorted strictly for one strict order, with the same members,
are one list.** -/
theorem eq_of_pairwise_of_mem_iff {α : Type} {before : α → α → Prop}
    (irrefl : ∀ element, ¬ before element element)
    (trans : ∀ {first second third}, before first second → before second third → before first third) :
    ∀ {first second : List α}, first.Pairwise before → second.Pairwise before →
      (∀ element, element ∈ first ↔ element ∈ second) → first = second
  | [], [], _, _, _ => rfl
  | [], head :: _, _, _, same => absurd ((same head).mpr List.mem_cons_self) List.not_mem_nil
  | head :: _, [], _, _, same => absurd ((same head).mp List.mem_cons_self) List.not_mem_nil
  | head :: rest, head' :: rest', firstSorted, secondSorted, same => by
      obtain ⟨headBefore, restSorted⟩ := List.pairwise_cons.mp firstSorted
      obtain ⟨headBefore', restSorted'⟩ := List.pairwise_cons.mp secondSorted
      have heads : head = head' := by
        by_contra distinct
        have inSecond : head ∈ rest' := by
          rcases List.mem_cons.mp ((same head).mp List.mem_cons_self) with equal | inRest
          · exact absurd equal distinct
          · exact inRest
        have inFirst : head' ∈ rest := by
          rcases List.mem_cons.mp ((same head').mpr List.mem_cons_self) with equal | inRest
          · exact absurd equal.symm distinct
          · exact inRest
        exact irrefl head (trans (headBefore head' inFirst) (headBefore' head inSecond))
      subst heads
      have tails : ∀ element, element ∈ rest ↔ element ∈ rest' := fun element => by
        constructor
        · intro member
          rcases List.mem_cons.mp ((same element).mp (List.mem_cons_of_mem _ member)) with equal | inRest
          · subst equal
            exact absurd (headBefore _ member) (irrefl _)
          · exact inRest
        · intro member
          rcases List.mem_cons.mp ((same element).mpr (List.mem_cons_of_mem _ member)) with equal | inRest
          · subst equal
            exact absurd (headBefore' _ member) (irrefl _)
          · exact inRest
      rw [eq_of_pairwise_of_mem_iff irrefl trans restSorted restSorted' tails]

/-! ## Guards -/

/-- A guard whose variables are in strictly increasing order. -/
def SortedGuard (guard : List Nat) : Prop :=
  guard.Pairwise fun first second => cmpNat first second = .lt

theorem sortedGuard_union (first : List Nat) {second : List Nat} (sorted : SortedGuard second) :
    SortedGuard (unionSorted cmpNat first second) := by
  induction first with
  | nil => exact sorted
  | cons head rest ih => exact insertSorted_pairwise cmpNat_strict head ih

theorem inclNat_self : ∀ guard : List Nat, inclNat guard guard = true
  | [] => rfl
  | head :: rest => by
      simp [inclNat, cmpNat_eq_eq.mpr (rfl : head = head), inclNat_self rest]

/-- **On sorted guards, `incl` accepts every inclusion.** -/
theorem inclNat_of_subset {first : List Nat} :
    ∀ {second : List Nat}, SortedGuard first → SortedGuard second →
      (∀ index ∈ first, index ∈ second) → inclNat first second = true := by
  intro second
  induction second generalizing first with
  | nil =>
      intro _ _ included
      cases first with
      | nil => rfl
      | cons head rest => exact absurd (included head List.mem_cons_self) List.not_mem_nil
  | cons head' rest' ih =>
      intro firstSorted secondSorted included
      cases first with
      | nil => rfl
      | cons head rest =>
          obtain ⟨headBefore, restSorted⟩ := List.pairwise_cons.mp firstSorted
          obtain ⟨headBefore', restSorted'⟩ := List.pairwise_cons.mp secondSorted
          rcases outcome : cmpNat head head' with _ | _ | _
          · have below := cmpNat_eq_lt.mp outcome
            rcases List.mem_cons.mp (included head List.mem_cons_self) with same | inRest
            · omega
            · have above := cmpNat_eq_lt.mp (headBefore' head inRest)
              omega
          · have same := cmpNat_eq_eq.mp outcome
            subst same
            have inner : inclNat rest rest' = true := ih restSorted restSorted' fun index member => by
              rcases List.mem_cons.mp (included index (List.mem_cons_of_mem _ member)) with same | inRest
              · have above := cmpNat_eq_lt.mp (headBefore index member)
                omega
              · exact inRest
            simp [inclNat, outcome, inner]
          · have above := cmpNat_eq_gt.mp outcome
            have inner : inclNat (head :: rest) rest' = true :=
              ih firstSorted restSorted' fun index member => by
                rcases List.mem_cons.mp (included index member) with same | inRest
                · rcases List.mem_cons.mp member with isHead | inTail
                  · omega
                  · have later := cmpNat_eq_lt.mp (headBefore index inTail)
                    omega
                · exact inRest
            simp [inclNat, outcome, inner]

/-- Sorted guards with the same variables are one guard. -/
theorem sortedGuard_ext {first second : List Nat} (firstSorted : SortedGuard first)
    (secondSorted : SortedGuard second) (same : ∀ index, index ∈ first ↔ index ∈ second) :
    first = second :=
  eq_of_pairwise_of_mem_iff (before := fun first second => cmpNat first second = .lt)
    (fun element below => by
      rw [cmpNat_strict.irrefl element] at below
      cases below)
    cmpNat_strict.trans firstSorted secondSorted same

/-! ## The dominance test is an order on sublevels with sorted guards -/

/-- The guard of the sublevel is sorted. -/
def GuardSorted (sublevel : Sublevel) : Prop := SortedGuard (guardOfSub sublevel)

/-- **The dominance test is transitive.** -/
theorem leSub_trans {first second third : Sublevel} (firstSorted : GuardSorted first)
    (thirdSorted : GuardSorted third) (firstSecond : leSub first second = true)
    (secondThird : leSub second third = true) : leSub first third = true := by
  cases first with
  | cst guard constant =>
      cases second with
      | cst guard' constant' =>
          cases third with
          | cst guard'' constant'' =>
              simp only [leSub, Bool.and_eq_true, decide_eq_true_eq] at firstSecond secondThird ⊢
              exact ⟨inclNat_of_subset thirdSorted firstSorted fun index member =>
                inclNat_subset firstSecond.1 index (inclNat_subset secondThird.1 index member),
                Nat.le_trans firstSecond.2 secondThird.2⟩
          | var guard'' index'' offset'' =>
              simp only [leSub, Bool.and_eq_true, decide_eq_true_eq] at firstSecond secondThird ⊢
              exact ⟨inclNat_of_subset thirdSorted firstSorted fun index member =>
                inclNat_subset firstSecond.1 index (inclNat_subset secondThird.1 index member),
                Nat.le_trans firstSecond.2 secondThird.2⟩
      | var guard' index' offset' =>
          cases third with
          | cst guard'' constant'' => simp [leSub] at secondThird
          | var guard'' index'' offset'' =>
              simp only [leSub, Bool.and_eq_true, decide_eq_true_eq] at firstSecond secondThird ⊢
              exact ⟨inclNat_of_subset thirdSorted firstSorted fun index member =>
                inclNat_subset firstSecond.1 index (inclNat_subset secondThird.1 index member), by omega⟩
  | var guard index offset =>
      cases second with
      | cst guard' constant' => simp [leSub] at firstSecond
      | var guard' index' offset' =>
          cases third with
          | cst guard'' constant'' => simp [leSub] at secondThird
          | var guard'' index'' offset'' =>
              simp only [leSub, Bool.and_eq_true, decide_eq_true_eq] at firstSecond secondThird ⊢
              exact ⟨inclNat_of_subset thirdSorted firstSorted fun index member =>
                inclNat_subset firstSecond.1 index (inclNat_subset secondThird.1 index member),
                firstSecond.2.1.trans secondThird.2.1, Nat.le_trans firstSecond.2.2 secondThird.2.2⟩

/-- **The dominance test is antisymmetric.** -/
theorem leSub_antisymm {first second : Sublevel} (firstSorted : GuardSorted first)
    (secondSorted : GuardSorted second) (below : leSub first second = true)
    (above : leSub second first = true) : first = second := by
  cases first with
  | cst guard constant =>
      cases second with
      | cst guard' constant' =>
          simp only [leSub, Bool.and_eq_true, decide_eq_true_eq] at below above
          have guards : guard = guard' := sortedGuard_ext firstSorted secondSorted fun index =>
            ⟨inclNat_subset above.1 index, inclNat_subset below.1 index⟩
          have constants : constant = constant' := Nat.le_antisymm below.2 above.2
          rw [guards, constants]
      | var guard' index' offset' => simp [leSub] at above
  | var guard index offset =>
      cases second with
      | cst guard' constant' => simp [leSub] at below
      | var guard' index' offset' =>
          simp only [leSub, Bool.and_eq_true, decide_eq_true_eq] at below above
          have guards : guard = guard' := sortedGuard_ext firstSorted secondSorted fun other =>
            ⟨inclNat_subset above.1 other, inclNat_subset below.1 other⟩
          have offsets : offset = offset' := Nat.le_antisymm below.2.2 above.2.2
          rw [guards, below.2.1, offsets]

/-! ## Increments keep the two comparisons -/

theorem cmpSub_incrSub (first second : Sublevel) :
    cmpSub (incrSub first) (incrSub second) = cmpSub first second := by
  cases first <;> cases second <;> simp [incrSub, cmpSub, cmpNat]

theorem leSub_incrSub (first second : Sublevel) :
    leSub (incrSub first) (incrSub second) = leSub first second := by
  cases first <;> cases second <;> simp [incrSub, leSub]

theorem incrSub_injective {first second : Sublevel} (same : incrSub first = incrSub second) :
    first = second := by
  cases first <;> cases second <;> simp [incrSub] at same <;> simp [same]

/-! ## Canonical sets -/

/-- **A canonical set of sublevels**: its sublevels are of the kind `good`,
they are sorted strictly by the comparison of the rules, and none of them is
below another one for the dominance test. -/
structure Canonical (good : Sublevel → Prop) (set : List Sublevel) : Prop where
  good : ∀ sublevel ∈ set, good sublevel
  sorted : set.Pairwise fun first second => cmpSub first second = .lt
  antichain : ∀ first ∈ set, ∀ second ∈ set, leSub first second = true → first = second

namespace Canonical

variable {good : Sublevel → Prop}

theorem nil : Canonical good [] :=
  ⟨fun _ member => (by cases member), List.Pairwise.nil, fun _ member => (by cases member)⟩

theorem singleton {sublevel : Sublevel} (isGood : good sublevel) : Canonical good [sublevel] where
  good := fun other member => by
    rw [List.mem_singleton.mp member]
    exact isGood
  sorted := List.pairwise_singleton _ _
  antichain := fun first firstMember second secondMember _ => by
    rw [List.mem_singleton.mp firstMember, List.mem_singleton.mp secondMember]

theorem tail {head : Sublevel} {rest : List Sublevel} (canonical : Canonical good (head :: rest)) :
    Canonical good rest where
  good := fun sublevel member => canonical.good sublevel (List.mem_cons_of_mem _ member)
  sorted := (List.pairwise_cons.mp canonical.sorted).2
  antichain := fun first firstMember second secondMember =>
    canonical.antichain first (List.mem_cons_of_mem _ firstMember) second
      (List.mem_cons_of_mem _ secondMember)

/-- **The corrected `Add` keeps canonical sets canonical.** -/
theorem addSub {sublevel : Sublevel} (isGood : good sublevel) :
    ∀ {set : List Sublevel}, Canonical good set → Canonical good (addSub sublevel set)
  | [], _ => singleton isGood
  | head :: rest, canonical => by
      have inner := Canonical.addSub isGood canonical.tail
      simp only [LeanMinus.addSub]
      by_cases dominated : leSub sublevel head = true
      · rw [if_pos dominated]
        exact canonical
      · rw [if_neg dominated]
        by_cases dominates : leSub head sublevel = true
        · rw [if_pos dominates]
          exact inner
        · rw [if_neg dominates]
          have headGood := canonical.good head List.mem_cons_self
          have origin : ∀ other ∈ insertSorted cmpSub head (LeanMinus.addSub sublevel rest),
              other = head ∨ other = sublevel ∨ other ∈ rest := fun other member => by
            rcases mem_insertSorted cmpSub head _ other member with isHead | inInner
            · exact Or.inl isHead
            · exact Or.inr (mem_addSub sublevel rest other inInner)
          refine ⟨fun other member => ?_, insertSorted_pairwise cmpSub_strict head inner.sorted,
            fun first firstMember second secondMember below => ?_⟩
          · rcases origin other member with isHead | isNew | inRest
            · rw [isHead]
              exact headGood
            · rw [isNew]
              exact isGood
            · exact canonical.good other (List.mem_cons_of_mem _ inRest)
          · rcases mem_insertSorted cmpSub head _ first firstMember with firstHead | firstInner
            · rcases mem_insertSorted cmpSub head _ second secondMember with secondHead | secondInner
              · rw [firstHead, secondHead]
              · rcases mem_addSub sublevel rest second secondInner with isNew | inRest
                · rw [firstHead, isNew] at below
                  exact absurd below dominates
                · exact canonical.antichain first (by rw [firstHead]; exact List.mem_cons_self) second
                    (List.mem_cons_of_mem _ inRest) below
            · rcases mem_insertSorted cmpSub head _ second secondMember with secondHead | secondInner
              · rcases mem_addSub sublevel rest first firstInner with isNew | inRest
                · rw [isNew, secondHead] at below
                  exact absurd below dominated
                · exact canonical.antichain first (List.mem_cons_of_mem _ inRest) second
                    (by rw [secondHead]; exact List.mem_cons_self) below
              · exact inner.antichain first firstInner second secondInner below

/-- Inserting the sublevels of a list one by one keeps a canonical set
canonical. -/
theorem foldAdd :
    ∀ (list : List Sublevel) {accumulated : List Sublevel}, (∀ sublevel ∈ list, good sublevel) →
      Canonical good accumulated →
        Canonical good (list.foldl (fun accumulated' element => LeanMinus.addSub element accumulated')
          accumulated)
  | [], _, _, canonical => canonical
  | head :: rest, _, listGood, canonical =>
      foldAdd rest (fun sublevel member => listGood sublevel (List.mem_cons_of_mem _ member))
        (Canonical.addSub (listGood head List.mem_cons_self) canonical)

/-- Incrementing every sublevel keeps a canonical set canonical. -/
theorem map_incrSub {set : List Sublevel} (canonical : Canonical good set)
    (incr : ∀ {sublevel : Sublevel}, good sublevel → good (incrSub sublevel)) :
    Canonical good (set.map incrSub) where
  good := fun sublevel member => by
    obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
    rw [← same]
    exact incr (canonical.good original originalMember)
  sorted := by
    rw [List.pairwise_map]
    exact canonical.sorted.imp fun {first second} before => by
      rw [cmpSub_incrSub]
      exact before
  antichain := fun first firstMember second secondMember below => by
    obtain ⟨firstOriginal, firstOriginalMember, firstSame⟩ := List.mem_map.mp firstMember
    obtain ⟨secondOriginal, secondOriginalMember, secondSame⟩ := List.mem_map.mp secondMember
    rw [← firstSame, ← secondSame, leSub_incrSub] at below
    rw [← firstSame, ← secondSame,
      canonical.antichain firstOriginal firstOriginalMember secondOriginal secondOriginalMember below]

end Canonical

/-- **The set computed for every level is canonical**, for the corrected `Add`
and a kind of sublevels that holds the constant `1` and the codes of the
variables, and is kept by the increment and by the guarded copies. -/
theorem normalSetWith_canonical {good : Sublevel → Prop} {leaf : Nat → Sublevel}
    (one : good (.cst [] 1)) (leafGood : ∀ index, good (leaf index))
    (incr : ∀ {sublevel : Sublevel}, good sublevel → good (incrSub sublevel))
    (addguard : ∀ {first second : Sublevel}, good first → good second →
      good (addguardSub first second)) :
    ∀ level : LeanLevel, Canonical good (normalSetWith addSub leaf level)
  | .zero => Canonical.nil
  | .param index => Canonical.singleton (leafGood index)
  | .succ level =>
      Canonical.addSub one
        ((normalSetWith_canonical one leafGood incr addguard level).map_incrSub incr)
  | .max first second =>
      Canonical.foldAdd _ (normalSetWith_canonical one leafGood incr addguard first).good
        (normalSetWith_canonical one leafGood incr addguard second)
  | .imax first second => by
      have firstCanonical := normalSetWith_canonical one leafGood incr addguard first
      have secondCanonical := normalSetWith_canonical one leafGood incr addguard second
      change Canonical good (imaxSetWith addSub _ _)
      generalize normalSetWith addSub leaf second = secondSet at secondCanonical
      cases secondSet with
      | nil => exact Canonical.nil
      | cons head rest =>
          refine Canonical.foldAdd _ (fun sublevel member => ?_) secondCanonical
          obtain ⟨element, elementMember, inner⟩ := List.mem_flatMap.mp member
          obtain ⟨guarding, guardingMember, same⟩ := List.mem_map.mp inner
          rw [← same]
          exact addguard (firstCanonical.good element elementMember)
            (secondCanonical.good guarding guardingMember)

/-! ## Two valuations that decide dominance -/

/-- The valuation that is `1` on a set of variables and `0` elsewhere. -/
def indicator (support : Nat → Bool) (index : Nat) : Nat := if support index then 1 else 0

/-- The same valuation with the value `height` at the variable `peak`. -/
def spike (support : Nat → Bool) (peak height : Nat) (index : Nat) : Nat :=
  if index = peak then height else indicator support index

theorem indicator_ne_zero {support : Nat → Bool} {index : Nat} :
    indicator support index ≠ 0 ↔ support index = true := by
  unfold indicator
  cases support index <;> simp

theorem indicator_eq_one {support : Nat → Bool} {index : Nat} (inside : support index = true) :
    indicator support index = 1 := by
  simp [indicator, inside]

theorem spike_ne_zero {support : Nat → Bool} {peak height index : Nat} (positive : height ≠ 0)
    (inside : support peak = true) :
    spike support peak height index ≠ 0 ↔ support index = true := by
  unfold spike
  by_cases same : index = peak
  · subst same
    simp [positive, inside]
  · simp [same, indicator_ne_zero]

theorem guardHolds_indicator {support : Nat → Bool} {guard : List Nat} :
    guardHolds (indicator support) guard = true ↔ ∀ index ∈ guard, support index = true := by
  rw [guardHolds_iff]
  exact forall₂_congr fun _ _ => indicator_ne_zero

theorem guardHolds_spike {support : Nat → Bool} {peak height : Nat} {guard : List Nat}
    (positive : height ≠ 0) (inside : support peak = true) :
    guardHolds (spike support peak height) guard = true ↔ ∀ index ∈ guard, support index = true := by
  rw [guardHolds_iff]
  exact forall₂_congr fun _ _ => spike_ne_zero positive inside

theorem sublevelEval_le_setEval {valuation : Nat → Nat} {other : Sublevel} :
    ∀ {set : List Sublevel}, other ∈ set → sublevelEval valuation other ≤ setEval valuation set
  | head :: rest, member => by
      rw [setEval_cons]
      rcases List.mem_cons.mp member with same | inRest
      · rw [same]
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (sublevelEval_le_setEval inRest) (Nat.le_max_right _ _)

/-- A positive amount below the value of a set is below the value of one of
its sublevels. -/
theorem exists_le_sublevelEval {valuation : Nat → Nat} {amount : Nat} (positive : 1 ≤ amount) :
    ∀ {set : List Sublevel}, amount ≤ setEval valuation set →
      ∃ other ∈ set, amount ≤ sublevelEval valuation other
  | [], below => by
      rw [setEval_nil] at below
      omega
  | head :: rest, below => by
      rw [setEval_cons] at below
      by_cases atHead : amount ≤ sublevelEval valuation head
      · exact ⟨head, List.mem_cons_self, atHead⟩
      · have inRest : amount ≤ setEval valuation rest := by omega
        obtain ⟨other, member, reached⟩ := exists_le_sublevelEval positive inRest
        exact ⟨other, List.mem_cons_of_mem _ member, reached⟩

/-- A sublevel with a positive value has its guard holding. -/
theorem guardHolds_of_sublevelEval_pos {valuation : Nat → Nat} {sublevel : Sublevel}
    (positive : 1 ≤ sublevelEval valuation sublevel) :
    guardHolds valuation (guardOfSub sublevel) = true := by
  cases sublevel with
  | cst guard constant =>
      by_contra fails
      have failsGuard : ¬ guardHolds valuation guard = true := fails
      simp only [sublevelEval, if_neg failsGuard] at positive
      omega
  | var guard index offset =>
      by_contra fails
      have failsGuard : ¬ guardHolds valuation guard = true := fails
      simp only [sublevelEval, if_neg failsGuard] at positive
      omega

/-- A bound above the constant, or above the offset, of a sublevel. -/
def sublevelBound : Sublevel → Nat
  | .cst _ constant => constant
  | .var _ _ offset => offset + 1

/-- A bound above the constants and the offsets of a set. -/
def setBound : List Sublevel → Nat
  | [] => 0
  | head :: rest => sublevelBound head + setBound rest

theorem sublevelBound_le_setBound {other : Sublevel} :
    ∀ {set : List Sublevel}, other ∈ set → sublevelBound other ≤ setBound set
  | head :: rest, member => by
      rcases List.mem_cons.mp member with same | inRest
      · rw [same]
        exact Nat.le_add_right _ _
      · exact Nat.le_trans (sublevelBound_le_setBound inRest) (Nat.le_add_left _ _)

/-- **A sublevel whose value does not exceed the value of a set, at the two
valuations that test it, is below one sublevel of the set.**  The valuations
are `1` on a set of variables that holds the guard of the sublevel; the
sublevels of the set that are alive there have their guards inside the guard
of the sublevel, and their variables alive. -/
theorem exists_leSub_of_eval_le {support : Nat → Bool} {sublevel : Sublevel} {set : List Sublevel}
    (inside : ∀ index ∈ guardOfSub sublevel, support index = true)
    (positive : ∀ guard constant, sublevel = .cst guard constant → 1 ≤ constant)
    (peakInside : ∀ guard index offset, sublevel = .var guard index offset → support index = true)
    (covers : ∀ other ∈ set, (∀ index ∈ guardOfSub other, support index = true) →
      inclNat (guardOfSub other) (guardOfSub sublevel) = true ∧
        ∀ guard index offset, other = .var guard index offset → support index = true)
    (atIndicator : sublevelEval (indicator support) sublevel ≤ setEval (indicator support) set)
    (atSpike : ∀ peak, sublevelEval (spike support peak (setBound set + 1)) sublevel ≤
      setEval (spike support peak (setBound set + 1)) set) :
    ∃ other ∈ set, leSub sublevel other = true := by
  cases sublevel with
  | cst guard constant =>
      have atLeastOne := positive guard constant rfl
      have holds : guardHolds (indicator support) guard = true := guardHolds_indicator.mpr inside
      have value : sublevelEval (indicator support) (.cst guard constant) = constant := by
        simp [sublevelEval, holds]
      rw [value] at atIndicator
      obtain ⟨other, member, reached⟩ := exists_le_sublevelEval atLeastOne atIndicator
      have otherHolds := guardHolds_of_sublevelEval_pos (Nat.le_trans atLeastOne reached)
      obtain ⟨included, variableInside⟩ := covers other member (guardHolds_indicator.mp otherHolds)
      refine ⟨other, member, ?_⟩
      cases other with
      | cst guard' constant' =>
          have otherValue : sublevelEval (indicator support) (.cst guard' constant') = constant' := by
            simp [sublevelEval, show guardHolds (indicator support) guard' = true from otherHolds]
          rw [otherValue] at reached
          simp only [leSub, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨included, reached⟩
      | var guard' index' offset' =>
          have otherValue : sublevelEval (indicator support) (.var guard' index' offset') =
              1 + offset' := by
            simp [sublevelEval, show guardHolds (indicator support) guard' = true from otherHolds,
              indicator_eq_one (variableInside guard' index' offset' rfl)]
          rw [otherValue] at reached
          simp only [leSub, Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨included, by omega⟩
  | var guard index offset =>
      have peakIn := peakInside guard index offset rfl
      have heightPositive : setBound set + 1 ≠ 0 := Nat.succ_ne_zero _
      have holds : guardHolds (spike support index (setBound set + 1)) guard = true :=
        (guardHolds_spike heightPositive peakIn).mpr inside
      have value : sublevelEval (spike support index (setBound set + 1)) (.var guard index offset) =
          setBound set + 1 + offset := by
        simp [sublevelEval, holds, spike]
      have below := atSpike index
      rw [value] at below
      obtain ⟨other, member, reached⟩ :=
        exists_le_sublevelEval (amount := setBound set + 1 + offset) (by omega) below
      have otherHolds := guardHolds_of_sublevelEval_pos (valuation := spike support index (setBound set + 1))
        (sublevel := other) (by omega)
      obtain ⟨included, variableInside⟩ :=
        covers other member ((guardHolds_spike heightPositive peakIn).mp otherHolds)
      have bounded := sublevelBound_le_setBound member
      refine ⟨other, member, ?_⟩
      cases other with
      | cst guard' constant' =>
          have otherValue : sublevelEval (spike support index (setBound set + 1)) (.cst guard' constant') =
              constant' := by
            simp [sublevelEval,
              show guardHolds (spike support index (setBound set + 1)) guard' = true from otherHolds]
          rw [otherValue] at reached
          simp only [sublevelBound] at bounded
          omega
      | var guard' index' offset' =>
          have otherHolds' : guardHolds (spike support index (setBound set + 1)) guard' = true :=
            otherHolds
          simp only [sublevelBound] at bounded
          by_cases same : index' = index
          · subst same
            have otherValue : sublevelEval (spike support index' (setBound set + 1))
                (.var guard' index' offset') = setBound set + 1 + offset' := by
              simp [sublevelEval, otherHolds', spike]
            rw [otherValue] at reached
            simp only [leSub, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨included, trivial, by omega⟩
          · have otherValue : sublevelEval (spike support index (setBound set + 1))
                (.var guard' index' offset') = 1 + offset' := by
              simp [sublevelEval, otherHolds', spike, same,
                indicator_eq_one (variableInside guard' index' offset' rfl)]
            rw [otherValue] at reached
            omega

/-! ## A canonical set is determined by the sublevels it dominates -/

/-- **Two canonical sets each of whose sublevels is below a sublevel of the
other are one set.** -/
theorem Canonical.eq_of_dominations {good : Sublevel → Prop}
    (guardSorted : ∀ {sublevel : Sublevel}, good sublevel → GuardSorted sublevel)
    {first second : List Sublevel} (firstCanonical : Canonical good first)
    (secondCanonical : Canonical good second)
    (firstBelow : ∀ sublevel ∈ first, ∃ other ∈ second, leSub sublevel other = true)
    (secondBelow : ∀ sublevel ∈ second, ∃ other ∈ first, leSub sublevel other = true) :
    first = second := by
  have move : ∀ {left right : List Sublevel}, Canonical good left → Canonical good right →
      (∀ sublevel ∈ left, ∃ other ∈ right, leSub sublevel other = true) →
      (∀ sublevel ∈ right, ∃ other ∈ left, leSub sublevel other = true) →
        ∀ sublevel ∈ left, sublevel ∈ right := by
    intro left right leftCanonical rightCanonical leftBelow rightBelow sublevel member
    obtain ⟨above, aboveMember, below⟩ := leftBelow sublevel member
    obtain ⟨back, backMember, belowBack⟩ := rightBelow above aboveMember
    have sublevelSorted := guardSorted (leftCanonical.good sublevel member)
    have aboveSorted := guardSorted (rightCanonical.good above aboveMember)
    have backSorted := guardSorted (leftCanonical.good back backMember)
    have same : sublevel = back :=
      leftCanonical.antichain sublevel member back backMember
        (leSub_trans sublevelSorted backSorted below belowBack)
    rw [← same] at belowBack
    rw [leSub_antisymm sublevelSorted aboveSorted below belowBack]
    exact aboveMember
  exact eq_of_pairwise_of_mem_iff (before := fun first second => cmpSub first second = .lt)
    (fun element before => by
      rw [cmpSub_strict.irrefl element] at before
      cases before)
    cmpSub_strict.trans firstCanonical.sorted secondCanonical.sorted fun element =>
      ⟨move firstCanonical secondCanonical firstBelow secondBelow element,
        move secondCanonical firstCanonical secondBelow firstBelow element⟩

/-! ## The corrected code: guards that hold their variables -/

/-- The sublevels of the corrected code: a sorted guard, a constant at least
`1`, and a variable in its own guard. -/
def Guarded : Sublevel → Prop
  | .cst guard constant => SortedGuard guard ∧ 1 ≤ constant
  | .var guard index _ => SortedGuard guard ∧ index ∈ guard

theorem Guarded.guardSorted {sublevel : Sublevel} (guarded : Guarded sublevel) : GuardSorted sublevel := by
  cases sublevel with
  | cst guard constant => exact guarded.1
  | var guard index offset => exact guarded.1

theorem Guarded.incrSub {sublevel : Sublevel} (guarded : Guarded sublevel) :
    Guarded (incrSub sublevel) := by
  cases sublevel with
  | cst guard constant => exact ⟨guarded.1, Nat.le_add_left 1 constant⟩
  | var guard index offset => exact guarded

theorem Guarded.addguardSub {first second : Sublevel} (firstGuarded : Guarded first)
    (secondGuarded : Guarded second) : Guarded (addguardSub first second) := by
  cases first with
  | cst guard constant => exact ⟨sortedGuard_union guard secondGuarded.guardSorted, firstGuarded.2⟩
  | var guard index offset =>
      exact ⟨sortedGuard_union guard secondGuarded.guardSorted,
        (mem_unionSorted_cmpNat guard _ index).mpr (Or.inl firstGuarded.2)⟩

/-- **The computed set of every level is canonical.** -/
theorem normalSet_canonical (level : LeanLevel) : Canonical Guarded (normalSet level) := by
  rw [← normalSetWith_addSub_guardedLeaf]
  exact normalSetWith_canonical (good := Guarded) (leaf := guardedLeaf)
    (show Guarded (.cst [] 1) from ⟨List.Pairwise.nil, Nat.le_refl 1⟩)
    (fun index => show Guarded (.var [index] index 0) from
      ⟨List.pairwise_singleton _ _, List.mem_cons_self⟩)
    (fun guarded => guarded.incrSub) (fun firstGuarded secondGuarded =>
      firstGuarded.addguardSub secondGuarded) level

/-- In a canonical set of the corrected code, a sublevel whose value never
exceeds the value of another such set is below one of its sublevels. -/
theorem Guarded.exists_leSub {sublevel : Sublevel} {set : List Sublevel} (guarded : Guarded sublevel)
    (setGuarded : ∀ other ∈ set, Guarded other)
    (below : ∀ valuation, sublevelEval valuation sublevel ≤ setEval valuation set) :
    ∃ other ∈ set, leSub sublevel other = true := by
  refine exists_leSub_of_eval_le (support := fun index => decide (index ∈ guardOfSub sublevel))
    (fun index member => decide_eq_true member) ?_ ?_ ?_ (below _) fun _ => below _
  · intro guard constant same
    rw [same] at guarded
    exact guarded.2
  · intro guard index offset same
    rw [same] at guarded ⊢
    exact decide_eq_true guarded.2
  · intro other member alive
    have otherGuarded := setGuarded other member
    have included : ∀ index ∈ guardOfSub other, index ∈ guardOfSub sublevel := fun index inGuard =>
      of_decide_eq_true (alive index inGuard)
    refine ⟨inclNat_of_subset otherGuarded.guardSorted guarded.guardSorted included, ?_⟩
    intro guard index offset same
    rw [same] at otherGuarded included
    exact decide_eq_true (included index otherGuarded.2)

/-- **Canonical sets of the corrected code with one value at every valuation
are one set.** -/
theorem Canonical.eq_of_setEval {first second : List Sublevel} (firstCanonical : Canonical Guarded first)
    (secondCanonical : Canonical Guarded second)
    (same : ∀ valuation, setEval valuation first = setEval valuation second) : first = second :=
  Canonical.eq_of_dominations Guarded.guardSorted firstCanonical secondCanonical
    (fun sublevel member => (firstCanonical.good sublevel member).exists_leSub secondCanonical.good
      fun valuation => same valuation ▸ sublevelEval_le_setEval member)
    (fun sublevel member => (secondCanonical.good sublevel member).exists_leSub firstCanonical.good
      fun valuation => (same valuation).symm ▸ sublevelEval_le_setEval member)

/-- **Equivalent levels have one computed set**, with any number of level
variables. -/
theorem normalSet_eq_of_equiv {first second : LeanLevel} (equivalent : LeanLevel.Equiv first second) :
    normalSet first = normalSet second :=
  Canonical.eq_of_setEval (normalSet_canonical first) (normalSet_canonical second) fun valuation => by
    rw [setEval_normalSet, setEval_normalSet]
    exact equivalent valuation

/-- **Theorem 3, for all levels**: equivalent levels have convertible codes in
the theory with explicit level substitution, with any number of level
variables. -/
theorem theorem3_all_levels {first second : LeanLevel} (equivalent : LeanLevel.Equiv first second) :
    Conv leanTheoryExplicit (code first) (code second) :=
  conv_code_iff_normalSet.mpr (normalSet_eq_of_equiv equivalent)

/-- **Theorem 3, for all levels, in a frame.** -/
theorem theorem3_all_levels_in (frame : Term) {first second : LeanLevel}
    (equivalent : LeanLevel.Equiv first second) :
    Conv leanTheoryExplicit (levelIn frame first) (levelIn frame second) :=
  Conv.app (.refl _) (theorem3_all_levels equivalent)

/-- **Theorem 2, for all levels**: two levels have convertible codes in the
theory with explicit level substitution exactly when they are equivalent. -/
theorem theorem2_all_levels {first second : LeanLevel} :
    Conv leanTheoryExplicit (code first) (code second) ↔ LeanLevel.Equiv first second :=
  ⟨equiv_of_conv_code, theorem3_all_levels⟩

/-- **Theorem 2 inside a declaration, for all levels.** -/
theorem theorem2_all_levels_in {index : Nat} {first second : LeanLevel} :
    Conv leanTheoryExplicit (levelIn (.var index) first) (levelIn (.var index) second) ↔
      LeanLevel.Equiv first second :=
  conv_subVar_iff.trans theorem2_all_levels

/-! ## The paper's code of a variable: the empty guard -/

/-- The sublevels of the paper's code: the empty guard, and a constant at least
`1`. -/
def Unguarded : Sublevel → Prop
  | .cst guard constant => guard = [] ∧ 1 ≤ constant
  | .var guard _ _ => guard = []

theorem Unguarded.guard_eq_nil {sublevel : Sublevel} (unguarded : Unguarded sublevel) :
    guardOfSub sublevel = [] := by
  cases sublevel with
  | cst guard constant => exact unguarded.1
  | var guard index offset => exact unguarded

theorem Unguarded.guardSorted {sublevel : Sublevel} (unguarded : Unguarded sublevel) :
    GuardSorted sublevel := by
  unfold GuardSorted
  rw [unguarded.guard_eq_nil]
  exact List.Pairwise.nil

theorem Unguarded.incrSub {sublevel : Sublevel} (unguarded : Unguarded sublevel) :
    Unguarded (incrSub sublevel) := by
  cases sublevel with
  | cst guard constant => exact ⟨unguarded.1, Nat.le_add_left 1 constant⟩
  | var guard index offset => exact unguarded

theorem Unguarded.addguardSub {first second : Sublevel} (firstUnguarded : Unguarded first)
    (secondUnguarded : Unguarded second) : Unguarded (addguardSub first second) := by
  cases first with
  | cst guard constant =>
      refine ⟨?_, firstUnguarded.2⟩
      rw [firstUnguarded.1, secondUnguarded.guard_eq_nil]
      rfl
  | var guard index offset =>
      change unionSorted cmpNat guard (guardOfSub second) = []
      rw [show guard = [] from firstUnguarded, secondUnguarded.guard_eq_nil]
      rfl

/-- **The set computed with the empty guard is canonical.** -/
theorem unguardedSet_canonical (level : LeanLevel) :
    Canonical Unguarded (normalSetWith addSub unguardedLeaf level) :=
  normalSetWith_canonical (good := Unguarded) (leaf := unguardedLeaf)
    (show Unguarded (.cst [] 1) from ⟨rfl, Nat.le_refl 1⟩)
    (fun index => show Unguarded (.var [] index 0) from rfl)
    (fun unguarded => unguarded.incrSub) (fun firstUnguarded secondUnguarded =>
      firstUnguarded.addguardSub secondUnguarded) level

/-- In a canonical set of the paper's code, a sublevel whose value does not
exceed the value of another such set at the positive valuations is below one
of its sublevels. -/
theorem Unguarded.exists_leSub {sublevel : Sublevel} {set : List Sublevel}
    (unguarded : Unguarded sublevel) (setUnguarded : ∀ other ∈ set, Unguarded other)
    (below : ∀ valuation : Nat → Nat, (∀ index, valuation index ≠ 0) →
      sublevelEval valuation sublevel ≤ setEval valuation set) :
    ∃ other ∈ set, leSub sublevel other = true := by
  refine exists_leSub_of_eval_le (support := fun _ => true) (fun _ _ => rfl) ?_ (fun _ _ _ _ => rfl) ?_
    (below _ fun index => indicator_ne_zero.mpr rfl)
    fun peak => below _ fun index => (spike_ne_zero (Nat.succ_ne_zero _) rfl).mpr rfl
  · intro guard constant same
    rw [same] at unguarded
    exact unguarded.2
  · intro other member _
    refine ⟨?_, fun _ _ _ _ => rfl⟩
    rw [(setUnguarded other member).guard_eq_nil, unguarded.guard_eq_nil]
    rfl

/-- **Canonical sets of the paper's code with one value at every positive
valuation are one set.** -/
theorem Canonical.eq_of_setEval_positive {first second : List Sublevel}
    (firstCanonical : Canonical Unguarded first) (secondCanonical : Canonical Unguarded second)
    (same : ∀ valuation : Nat → Nat, (∀ index, valuation index ≠ 0) →
      setEval valuation first = setEval valuation second) : first = second :=
  Canonical.eq_of_dominations Unguarded.guardSorted firstCanonical secondCanonical
    (fun sublevel member => (firstCanonical.good sublevel member).exists_leSub secondCanonical.good
      fun valuation positive => same valuation positive ▸ sublevelEval_le_setEval member)
    (fun sublevel member => (secondCanonical.good sublevel member).exists_leSub firstCanonical.good
      fun valuation positive => (same valuation positive).symm ▸ sublevelEval_le_setEval member)

/-- **With the rule on `Add` corrected, the paper's codes of two levels are
convertible exactly when the levels have one value at every valuation that is
positive everywhere**, with any number of level variables. -/
theorem conv_paperCode_explicit_iff_positive {first second : LeanLevel} :
    Conv leanTheoryExplicit (paperCode first) (paperCode second) ↔
      ∀ valuation : Nat → Nat, (∀ index, valuation index ≠ 0) →
        first.eval valuation = second.eval valuation := by
  refine ⟨fun convertible _ positive => eval_eq_of_conv_paperCode_explicit convertible positive,
    fun same => conv_paperCode_explicit_iff.mpr ?_⟩
  exact Canonical.eq_of_setEval_positive (unguardedSet_canonical first) (unguardedSet_canonical second)
    fun valuation positive => by
      rw [setEval_unguarded (addSub_sound valuation) positive,
        setEval_unguarded (addSub_sound valuation) positive]
      exact same valuation positive

#print axioms cmpSub_strict
#print axioms insertSorted_pairwise
#print axioms eq_of_pairwise_of_mem_iff
#print axioms inclNat_of_subset
#print axioms leSub_trans
#print axioms leSub_antisymm
#print axioms Canonical.addSub
#print axioms normalSetWith_canonical
#print axioms exists_leSub_of_eval_le
#print axioms Canonical.eq_of_dominations
#print axioms normalSet_canonical
#print axioms Canonical.eq_of_setEval
#print axioms normalSet_eq_of_equiv
#print axioms theorem3_all_levels
#print axioms theorem3_all_levels_in
#print axioms theorem2_all_levels
#print axioms theorem2_all_levels_in
#print axioms unguardedSet_canonical
#print axioms Canonical.eq_of_setEval_positive
#print axioms conv_paperCode_explicit_iff_positive

end Mettapedia.GSLT.Dedukti.LeanMinus
