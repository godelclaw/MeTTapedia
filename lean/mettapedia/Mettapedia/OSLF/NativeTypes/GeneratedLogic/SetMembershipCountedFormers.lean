import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCountedTypes
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipDetermined

/-!
# Formers decided by the counts of the members' types

Each former is shown to be decided by the counts of the members' types up to a cap (`CountDetermined`,
`SetMembershipCountedTypes`), with the cap it needs:

- **What the members' types decide, their counts decide** at every positive cap (`Determined.counted`): steps forward,
  emptiness, named sets.
- **Counting members** with a formula of the closure sums the counts of the types that contain it
  (`card_filter_type`), and a sum is decided up to a cap by its terms up to that cap (`min_sum_min`): at least `k`
  members is decided at cap `k` (`countDetermined_atLeast`, `countDetermined_allButFewer`).
- **A singleton** is a set with one member: decided at cap two (`countDetermined_single`,
  `countDetermined_everySingle`).
- **A split** of formulas decided at caps `a` and `b` is decided at `a + b` (`countDetermined_split`): a split of `x`
  is matched part for part by a split of any set with the same counts up to `a + b`, since a type with at least
  `a + b` members has at least `a` of them in the first part or `b` in the second (`exists_split_match_counted`).
- **A step back reads the type of the set itself** (`countDetermined_sometimeBefore`): a container of `x` with `y`
  put in place of `x` has the same counts, or already contains `y`.
- Counts for a larger closure decide counts for a smaller one, at any cap up to theirs (`countOf_sublist`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Classical

noncomputable section

variable {closure : List (Formula 0)} {cap : ℕ}

/-! ## Sums up to a cap -/

/-- **A sum up to a cap is decided by its terms up to any larger cap.** -/
theorem min_sum_min {ι : Type} (T : Finset ι) (a : ι → ℕ) {small large : ℕ} (le : small ≤ large) :
    min small (∑ i ∈ T, a i) = min small (∑ i ∈ T, min large (a i)) := by
  by_cases big : ∃ i ∈ T, large ≤ a i
  · obtain ⟨i, found, bigger⟩ := big
    have first := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) found
    have second := Finset.single_le_sum (f := fun i => min large (a i)) (fun _ _ => Nat.zero_le _) found
    rw [min_eq_left (by omega), min_eq_left (by omega)]
  · push Not at big
    rw [Finset.sum_congr rfl fun i found => (min_eq_right (big i found).le).symm]

/-! ## Counting the members whose type has a property -/

variable (closure) in
/-- The types of a closure with a property. -/
def typesWith (property : Finset (Formula 0) → Prop) [DecidablePred property] : Finset (Finset (Formula 0)) :=
  closure.toFinset.powerset.filter property

/-- **The members whose type has a property are counted type by type.** -/
theorem card_filter_type (property : Finset (Formula 0) → Prop) [DecidablePred property] (x : HF) :
    ((memberSet x).filter fun m => property (typeOf closure m)).card =
      ∑ τ ∈ typesWith closure property, (membersOfType closure x τ).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := typeOf closure) (t := typesWith closure property)]
  · refine Finset.sum_congr rfl fun τ found => congrArg Finset.card ?_
    ext m
    simp only [Finset.mem_filter, membersOfType]
    constructor
    · rintro ⟨⟨member, -⟩, typed⟩
      exact ⟨member, typed⟩
    · rintro ⟨member, typed⟩
      exact ⟨⟨member, typed ▸ (Finset.mem_filter.mp found).2⟩, typed⟩
  · intro m found
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at found
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (typeOf_subset closure m), found.2⟩

/-- **How many members have a type with a property, up to a cap, is decided by the counts at any larger cap.** -/
theorem min_card_type_eq (property : Finset (Formula 0) → Prop) [DecidablePred property] {small : ℕ} (le : small ≤ cap) {x y : HF}
    (same : countOf closure cap x = countOf closure cap y) :
    min small ((memberSet x).filter fun m => property (typeOf closure m)).card =
      min small ((memberSet y).filter fun m => property (typeOf closure m)).card := by
  rw [card_filter_type, card_filter_type, min_sum_min _ _ le, min_sum_min _ (fun τ => (membersOfType closure y τ).card) le]
  exact congrArg (min small) (Finset.sum_congr rfl fun τ _ => congrFun same τ)

/-- Having a formula of the closure is having it in one's type. -/
theorem sat_iff_mem_typeOf {φ : Formula 0} (inside : φ ∈ closure) (m : HF) :
    HFSets.sat Env.closed φ m ↔ φ ∈ typeOf closure m := by
  rw [mem_typeOf]
  exact (and_iff_right inside).symm

/-! ## Counting -/

/-- **At least `k` sets with a property, among a finite set that holds all of them.** -/
theorem hfAtLeast_iff {P : HF → Prop} [DecidablePred P] (S : Finset HF) (within : ∀ y, P y → y ∈ S) (k : ℕ) :
    HFSets.AtLeast k P ↔ k ≤ (S.filter P).card := by
  constructor
  · rintro ⟨witnesses, length, apart, holds⟩
    have nodup : witnesses.Nodup := apart.imp fun differ equal => differ (congrArg Subtype.val equal)
    have sub : witnesses.toFinset ⊆ S.filter P := fun y found => by
      have member := List.mem_toFinset.mp found
      exact Finset.mem_filter.mpr ⟨within y (holds y member), holds y member⟩
    rw [← length, ← List.toFinset_card_of_nodup nodup]
    exact Finset.card_le_card sub
  · intro enough
    obtain ⟨chosen, sub, size⟩ := Finset.exists_subset_card_eq enough
    refine ⟨chosen.toList, by rw [Finset.length_toList, size], ?_, fun y found => ?_⟩
    · exact (Finset.nodup_toList chosen).imp fun differ equal => differ (Subtype.ext equal)
    · exact (Finset.mem_filter.mp (sub (Finset.mem_toList.mp found))).2

/-- The members a forward step reaches with a label. -/
theorem stepIn_forward_iff {x m : HF} {label : StepLabel} :
    HFSets.stepIn .forward x label m ↔ memberLabel label ∧ m ∈ memberSet x := by
  rw [mem_memberSet]
  exact Iff.rfl

theorem sat_atLeast_iff {inner : Formula 0} (k : ℕ) (label : StepLabel) (x : HF) :
    HFSets.sat Env.closed (.atLeast k .forward label inner) x ↔
      k ≤ ((memberSet x).filter fun m => memberLabel label ∧ HFSets.sat Env.closed inner m).card := by
  change HFSets.AtLeast k _ ↔ _
  rw [hfAtLeast_iff (memberSet x) (fun y holds => (stepIn_forward_iff.mp holds.1).2)]
  constructor <;> intro enough <;> refine enough.trans (Finset.card_le_card fun m found => ?_)
  · obtain ⟨member, step, holds⟩ := Finset.mem_filter.mp found
    exact Finset.mem_filter.mpr ⟨member, (stepIn_forward_iff.mp step).1, holds⟩
  · obtain ⟨member, labelled, holds⟩ := Finset.mem_filter.mp found
    exact Finset.mem_filter.mpr ⟨member, stepIn_forward_iff.mpr ⟨labelled, member⟩, holds⟩

/-- **At least `k` members with a formula of the closure** is decided by the counts at cap `k`. -/
theorem countDetermined_atLeast {inner : Formula 0} (inside : inner ∈ closure) (k : ℕ) (label : StepLabel)
    (le : k ≤ cap) : CountDetermined closure cap (HFSets.sat Env.closed (.atLeast k .forward label inner)) := by
  intro x y same
  rw [sat_atLeast_iff, sat_atLeast_iff]
  by_cases labelled : memberLabel label
  · have ex : ((memberSet x).filter fun m => memberLabel label ∧ HFSets.sat Env.closed inner m) =
        (memberSet x).filter fun m => inner ∈ typeOf closure m :=
      Finset.filter_congr fun m _ => by rw [sat_iff_mem_typeOf inside]; exact and_iff_right labelled
    have ey : ((memberSet y).filter fun m => memberLabel label ∧ HFSets.sat Env.closed inner m) =
        (memberSet y).filter fun m => inner ∈ typeOf closure m :=
      Finset.filter_congr fun m _ => by rw [sat_iff_mem_typeOf inside]; exact and_iff_right labelled
    have counts : min k ((memberSet x).filter fun m => inner ∈ typeOf closure m).card =
        min k ((memberSet y).filter fun m => inner ∈ typeOf closure m).card :=
      min_card_type_eq (fun τ => inner ∈ τ) le same
    rw [ex, ey]
    constructor <;> intro enough <;> omega
  · simp only [labelled, false_and, Finset.filter_false, Finset.card_empty]

theorem sat_allButFewer_iff {inner : Formula 0} (k : ℕ) (label : StepLabel) (x : HF) :
    HFSets.sat Env.closed (.allButFewer k .forward label inner) x ↔
      ¬ k ≤ ((memberSet x).filter fun m => memberLabel label ∧ ¬ HFSets.sat Env.closed inner m).card := by
  change ¬ HFSets.AtLeast k _ ↔ _
  rw [hfAtLeast_iff (memberSet x) (fun y holds => (stepIn_forward_iff.mp holds.1).2)]
  refine not_congr ?_
  constructor <;> intro enough <;> refine enough.trans (Finset.card_le_card fun m found => ?_)
  · obtain ⟨member, step, holds⟩ := Finset.mem_filter.mp found
    exact Finset.mem_filter.mpr ⟨member, (stepIn_forward_iff.mp step).1, holds⟩
  · obtain ⟨member, labelled, holds⟩ := Finset.mem_filter.mp found
    exact Finset.mem_filter.mpr ⟨member, stepIn_forward_iff.mpr ⟨labelled, member⟩, holds⟩

theorem countDetermined_allButFewer {inner : Formula 0} (inside : inner ∈ closure) (k : ℕ) (label : StepLabel)
    (le : k ≤ cap) : CountDetermined closure cap (HFSets.sat Env.closed (.allButFewer k .forward label inner)) := by
  intro x y same
  rw [sat_allButFewer_iff, sat_allButFewer_iff]
  refine not_congr ?_
  by_cases labelled : memberLabel label
  · have ex : ((memberSet x).filter fun m => memberLabel label ∧ ¬ HFSets.sat Env.closed inner m) =
        (memberSet x).filter fun m => inner ∉ typeOf closure m :=
      Finset.filter_congr fun m _ => by rw [sat_iff_mem_typeOf inside]; exact and_iff_right labelled
    have ey : ((memberSet y).filter fun m => memberLabel label ∧ ¬ HFSets.sat Env.closed inner m) =
        (memberSet y).filter fun m => inner ∉ typeOf closure m :=
      Finset.filter_congr fun m _ => by rw [sat_iff_mem_typeOf inside]; exact and_iff_right labelled
    have counts : min k ((memberSet x).filter fun m => inner ∉ typeOf closure m).card =
        min k ((memberSet y).filter fun m => inner ∉ typeOf closure m).card :=
      min_card_type_eq (fun τ => inner ∉ τ) le same
    rw [ex, ey]
    constructor <;> intro enough <;> omega
  · simp only [labelled, false_and, Finset.filter_false, Finset.card_empty]

/-! ## Singletons -/

/-- **A set is a singleton of a set with a property** exactly when it has one member, which has the property. -/
theorem single_iff_card {x : HF} {P : HF → Prop} :
    (∃ member : HF, x.1 = {member.1} ∧ P member) ↔ (memberSet x).card = 1 ∧ ∀ m ∈ memberSet x, P m := by
  constructor
  · rintro ⟨member, single, holds⟩
    have equal : memberSet x = {member} := by
      ext m
      rw [mem_memberSet, single, ZFSet.mem_singleton, Finset.mem_singleton]
      exact ⟨fun same => Subtype.ext same, fun same => same ▸ rfl⟩
    rw [equal]
    exact ⟨Finset.card_singleton _, fun m found => (Finset.mem_singleton.mp found) ▸ holds⟩
  · rintro ⟨one, every⟩
    obtain ⟨member, equal⟩ := Finset.card_eq_one.mp one
    have found : member ∈ memberSet x := equal ▸ Finset.mem_singleton_self member
    refine ⟨member, ZFSet.ext fun z => ?_, every member found⟩
    rw [ZFSet.mem_singleton]
    constructor
    · intro inside
      obtain ⟨term, holds, same⟩ := x.2
      have zHF : IsHFSet z := isHFSet_of_member holds (same ▸ inside)
      have : (⟨z, zHF⟩ : HF) ∈ memberSet x := mem_memberSet.mpr inside
      rw [equal, Finset.mem_singleton] at this
      exact congrArg Subtype.val this
    · rintro rfl
      exact mem_memberSet.mp found

theorem sat_single_iff {inner : Formula 0} (kind : CollType) (x : HF) :
    HFSets.sat Env.closed (.single kind inner) x ↔
      kind = .hashSet ∧ (memberSet x).card = 1 ∧ ∀ m ∈ memberSet x, HFSets.sat Env.closed inner m := by
  change (∃ member : HF, (kind = .hashSet ∧ x.1 = {member.1}) ∧ _) ↔ _
  constructor
  · rintro ⟨member, ⟨hashSet, single⟩, holds⟩
    exact ⟨hashSet, single_iff_card.mp ⟨member, single, holds⟩⟩
  · rintro ⟨hashSet, rest⟩
    obtain ⟨member, single, holds⟩ := single_iff_card.mpr rest
    exact ⟨member, ⟨hashSet, single⟩, holds⟩

theorem sat_everySingle_iff {inner : Formula 0} (kind : CollType) (x : HF) :
    HFSets.sat Env.closed (.everySingle kind inner) x ↔
      (kind = .hashSet ∧ (memberSet x).card = 1 → ∀ m ∈ memberSet x, HFSets.sat Env.closed inner m) := by
  change (∀ member : HF, (kind = .hashSet ∧ x.1 = {member.1}) → _) ↔ _
  constructor
  · rintro every ⟨hashSet, one⟩ m found
    obtain ⟨member, single, -⟩ := single_iff_card (P := fun _ => True).mpr ⟨one, fun _ _ => trivial⟩
    have equal : m = member := by
      have := mem_memberSet.mp found
      rw [single, ZFSet.mem_singleton] at this
      exact Subtype.ext this
    exact equal ▸ every member ⟨hashSet, single⟩
  · rintro every member ⟨hashSet, single⟩
    have rest := single_iff_card (P := fun _ => True).mp ⟨member, single, trivial⟩
    exact every ⟨hashSet, rest.1⟩ member (mem_memberSet.mpr (by rw [single, ZFSet.mem_singleton]))

/-- Having one member, and every member having a formula, are decided by the counts at cap two. -/
theorem one_and_every_iff {inner : Formula 0} (inside : inner ∈ closure) (le : 2 ≤ cap) {x y : HF}
    (same : countOf closure cap x = countOf closure cap y) :
    ((memberSet x).card = 1 ↔ (memberSet y).card = 1) ∧
      ((∀ m ∈ memberSet x, HFSets.sat Env.closed inner m) ↔ ∀ m ∈ memberSet y, HFSets.sat Env.closed inner m) := by
  have total : min 2 (memberSet x).card = min 2 (memberSet y).card := by
    have := min_card_type_eq (closure := closure) (fun _ => True) le same
    simpa using this
  have none : min 1 ((memberSet x).filter fun m => inner ∉ typeOf closure m).card =
      min 1 ((memberSet y).filter fun m => inner ∉ typeOf closure m).card :=
    min_card_type_eq (fun τ => inner ∉ τ) (show 1 ≤ cap by omega) same
  have every : ∀ z : HF, (∀ m ∈ memberSet z, HFSets.sat Env.closed inner m) ↔
      min 1 ((memberSet z).filter fun m => inner ∉ typeOf closure m).card = 0 := by
    intro z
    rw [Nat.min_eq_zero_iff]
    simp only [Nat.one_ne_zero, false_or, Finset.card_eq_zero, Finset.filter_eq_empty_iff, not_not,
      sat_iff_mem_typeOf inside]
  refine ⟨?_, by rw [every, every, none]⟩
  constructor <;> intro one <;> omega

theorem countDetermined_single {inner : Formula 0} (inside : inner ∈ closure) (kind : CollType) (le : 2 ≤ cap) :
    CountDetermined closure cap (HFSets.sat Env.closed (.single kind inner)) := by
  intro x y same
  obtain ⟨one, every⟩ := one_and_every_iff inside le same
  rw [sat_single_iff, sat_single_iff, one, every]

theorem countDetermined_everySingle {inner : Formula 0} (inside : inner ∈ closure) (kind : CollType) (le : 2 ≤ cap) :
    CountDetermined closure cap (HFSets.sat Env.closed (.everySingle kind inner)) := by
  intro x y same
  obtain ⟨one, every⟩ := one_and_every_iff inside le same
  rw [sat_everySingle_iff, sat_everySingle_iff, one, every]

/-! ## Splits -/

/-- **Covering a finite set by two parts of given sizes, up to caps**: a set of `n` elements covered by parts of sizes
`nA` and `nB` gives, for any set with the same size up to `a + b`, a covering by parts of the same sizes up to `a`
and `b`. Below the cap the sizes are kept exactly; from the cap on one part takes everything. -/
theorem exists_cover {Y : Finset HF} {a b n nA nB : ℕ} (cover : n ≤ nA + nB)
    (subA : nA ≤ n) (subB : nB ≤ n) (sameCount : min (a + b) n = min (a + b) Y.card) :
    ∃ A' ⊆ Y, ∃ B' ⊆ Y, A' ∪ B' = Y ∧ min a A'.card = min a nA ∧ min b B'.card = min b nB := by
  by_cases small : n < a + b
  · have equal : Y.card = n := by omega
    obtain ⟨B', subB', sizeB⟩ := Finset.exists_subset_card_eq (show nB ≤ Y.card by omega)
    obtain ⟨C, subC, sizeC⟩ := Finset.exists_subset_card_eq (show nA + nB - n ≤ B'.card by omega)
    refine ⟨(Y \ B') ∪ C, Finset.union_subset Finset.sdiff_subset (subC.trans subB'), B', subB', ?_, ?_, by rw [sizeB]⟩
    · rw [Finset.union_assoc, Finset.union_eq_right.mpr subC, Finset.sdiff_union_of_subset subB']
    · rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right subC Finset.sdiff_disjoint),
        Finset.card_sdiff_of_subset subB', sizeB, sizeC]
      congr 1
      omega
  · push Not at small
    by_cases firstBig : a ≤ nA
    · obtain ⟨B', subB', sizeB⟩ := Finset.exists_subset_card_eq (show min b nB ≤ Y.card by omega)
      exact ⟨Y, subset_refl _, B', subB', Finset.union_eq_left.mpr subB', by omega, by rw [sizeB]; omega⟩
    · obtain ⟨A', subA', sizeA⟩ := Finset.exists_subset_card_eq (show min a nA ≤ Y.card by omega)
      exact ⟨A', subA', Y, subset_refl _, Finset.union_eq_right.mpr subA', by rw [sizeA]; omega, by omega⟩

/-- A subset of a set's members, as a hereditarily finite set. -/
def subsetOf (y : HF) (parts : Finset HF) : HF :=
  ⟨ZFSet.sep (fun z => ∃ m ∈ parts, m.1 = z) y.1, isHFSet_of_subset_hf y.2 fun _ inside => (ZFSet.mem_sep.mp inside).1⟩

theorem subsetOf_subset (y : HF) (parts : Finset HF) : (subsetOf y parts).1 ⊆ y.1 :=
  fun _ inside => (ZFSet.mem_sep.mp (show _ ∈ ZFSet.sep (fun z => ∃ m ∈ parts, m.1 = z) y.1 from inside)).1

theorem memberSet_subsetOf {y : HF} {parts : Finset HF} (within : parts ⊆ memberSet y) :
    memberSet (subsetOf y parts) = parts := by
  ext m
  rw [mem_memberSet]
  show m.1 ∈ ZFSet.sep (fun z => ∃ m ∈ parts, m.1 = z) y.1 ↔ m ∈ parts
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨-, other, found, same⟩
    rwa [← Subtype.ext same]
  · exact fun found => ⟨mem_memberSet.mp (within found), m, found, rfl⟩

theorem membersOfType_union {x A B : HF} (union : x.1 = A.1 ∪ B.1) (ρ : Finset (Formula 0)) :
    membersOfType closure x ρ = membersOfType closure A ρ ∪ membersOfType closure B ρ := by
  ext m
  simp only [membersOfType, Finset.mem_union, Finset.mem_filter, mem_memberSet, union, ZFSet.mem_union]
  tauto

/-- **A split is matched part for part** by a split of any set with the same counts up to `a + b`. -/
theorem exists_split_match_counted {a b : ℕ} (positive : 1 ≤ a + b) {x y : HF}
    (same : countOf closure (a + b) x = countOf closure (a + b) y) {A B : HF} (union : x.1 = A.1 ∪ B.1) :
    ∃ A' B' : HF, y.1 = A'.1 ∪ B'.1 ∧ countOf closure a A' = countOf closure a A ∧
      countOf closure b B' = countOf closure b B := by
  have covers : ∀ ρ, ∃ A' ⊆ membersOfType closure y ρ, ∃ B' ⊆ membersOfType closure y ρ,
      A' ∪ B' = membersOfType closure y ρ ∧ min a A'.card = min a (membersOfType closure A ρ).card ∧
        min b B'.card = min b (membersOfType closure B ρ).card := by
    intro ρ
    have split := membersOfType_union (closure := closure) union ρ
    refine exists_cover ?_ ?_ ?_ (congrFun same ρ)
    · rw [split]
      exact Finset.card_union_le _ _
    · exact Finset.card_le_card (split ▸ Finset.subset_union_left)
    · exact Finset.card_le_card (split ▸ Finset.subset_union_right)
  choose first firstSub second secondSub cover firstCount secondCount using covers
  let firstSet := (memberTypeSet (closure := closure) y).biUnion first
  let secondSet := (memberTypeSet (closure := closure) y).biUnion second
  have typedFirst : ∀ ρ, ∀ m ∈ first ρ, m ∈ memberSet y ∧ typeOf closure m = ρ := fun ρ m found =>
    Finset.mem_filter.mp (firstSub ρ found)
  have typedSecond : ∀ ρ, ∀ m ∈ second ρ, m ∈ memberSet y ∧ typeOf closure m = ρ := fun ρ m found =>
    Finset.mem_filter.mp (secondSub ρ found)
  have firstWithin : firstSet ⊆ memberSet y := fun m found => by
    obtain ⟨ρ, -, picked⟩ := Finset.mem_biUnion.mp found
    exact (typedFirst ρ m picked).1
  have secondWithin : secondSet ⊆ memberSet y := fun m found => by
    obtain ⟨ρ, -, picked⟩ := Finset.mem_biUnion.mp found
    exact (typedSecond ρ m picked).1
  -- the members of each part of a type
  have partType : ∀ (choice : Finset (Formula 0) → Finset HF),
      (∀ ρ, ∀ m ∈ choice ρ, m ∈ memberSet y ∧ typeOf closure m = ρ) → ∀ ρ,
        ((memberTypeSet (closure := closure) y).biUnion choice).filter (fun m => typeOf closure m = ρ) =
          if ρ ∈ memberTypeSet (closure := closure) y then choice ρ else ∅ := by
    intro choice typed ρ
    ext m
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨σ, found, chosen⟩, rfl⟩
      have := (typed σ m chosen).2
      subst this
      rw [if_pos found]
      exact chosen
    · intro chosen
      split at chosen
      · rename_i found
        exact ⟨⟨ρ, found, chosen⟩, (typed ρ m chosen).2⟩
      · cases chosen
  -- a type no member of `y` has has no member of `x`, hence none of `A` or `B`
  have absent : ∀ ρ, ρ ∉ memberTypeSet (closure := closure) y →
      membersOfType closure A ρ = ∅ ∧ membersOfType closure B ρ = ∅ := by
    intro ρ missing
    have none := membersOfType_eq_empty (closure := closure) missing
    have counts := congrFun same ρ
    simp only [countOf, none, Finset.card_empty] at counts
    have empty : membersOfType closure x ρ = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [membersOfType_union union, Finset.union_eq_empty] at empty
    exact empty
  refine ⟨subsetOf y firstSet, subsetOf y secondSet, ZFSet.ext fun z => ?_, funext fun ρ => ?_, funext fun ρ => ?_⟩
  · rw [ZFSet.mem_union]
    constructor
    · intro inside
      obtain ⟨term, holds, sameSet⟩ := y.2
      let m : HF := ⟨z, isHFSet_of_member holds (sameSet ▸ inside)⟩
      have member : m ∈ memberSet y := mem_memberSet.mpr inside
      have typed : m ∈ membersOfType closure y (typeOf closure m) := Finset.mem_filter.mpr ⟨member, rfl⟩
      have found : typeOf closure m ∈ memberTypeSet (closure := closure) y := Finset.mem_image.mpr ⟨m, member, rfl⟩
      rw [← cover] at typed
      rcases Finset.mem_union.mp typed with picked | picked
      · exact .inl (mem_memberSet.mp (by
          rw [memberSet_subsetOf firstWithin]
          exact Finset.mem_biUnion.mpr ⟨_, found, picked⟩))
      · exact .inr (mem_memberSet.mp (by
          rw [memberSet_subsetOf secondWithin]
          exact Finset.mem_biUnion.mpr ⟨_, found, picked⟩))
    · rintro (inside | inside)
      · exact subsetOf_subset y firstSet inside
      · exact subsetOf_subset y secondSet inside
  · have members : membersOfType closure (subsetOf y firstSet) ρ =
        if ρ ∈ memberTypeSet (closure := closure) y then first ρ else ∅ := by
      simp only [membersOfType, memberSet_subsetOf firstWithin]
      exact partType first typedFirst ρ
    simp only [countOf]
    rw [members]
    split
    · exact firstCount ρ
    · rename_i missing
      rw [(absent ρ missing).1]
  · have members : membersOfType closure (subsetOf y secondSet) ρ =
        if ρ ∈ memberTypeSet (closure := closure) y then second ρ else ∅ := by
      simp only [membersOfType, memberSet_subsetOf secondWithin]
      exact partType second typedSecond ρ
    simp only [countOf]
    rw [members]
    split
    · exact secondCount ρ
    · rename_i missing
      rw [(absent ρ missing).2]

/-- **A split of formulas decided at caps `a` and `b` is decided at `a + b`.** -/
theorem countDetermined_split {left right : Formula 0} (kind : CollType) {a b : ℕ} (positive : 1 ≤ a + b)
    (leftDetermined : CountDetermined closure a (HFSets.sat Env.closed left))
    (rightDetermined : CountDetermined closure b (HFSets.sat Env.closed right)) :
    CountDetermined closure (a + b) (HFSets.sat Env.closed (.split kind left right)) := by
  have direction : ∀ x y : HF, countOf closure (a + b) x = countOf closure (a + b) y →
      HFSets.sat Env.closed (.split kind left right) x → HFSets.sat Env.closed (.split kind left right) y := by
    rintro x y same ⟨A, B, ⟨hashSet, union⟩, leftHolds, rightHolds⟩
    obtain ⟨A', B', union', sameA, sameB⟩ := exists_split_match_counted positive same union
    exact ⟨A', B', ⟨hashSet, union'⟩, (leftDetermined A' A sameA).mpr leftHolds, (rightDetermined B' B sameB).mpr rightHolds⟩
  exact fun x y same => ⟨direction x y same, direction y x same.symm⟩

theorem countDetermined_everySplit {left right : Formula 0} (kind : CollType) {a b : ℕ} (positive : 1 ≤ a + b)
    (leftDetermined : CountDetermined closure a (HFSets.sat Env.closed left))
    (rightDetermined : CountDetermined closure b (HFSets.sat Env.closed right)) :
    CountDetermined closure (a + b) (HFSets.sat Env.closed (.everySplit kind left right)) := by
  have direction : ∀ x y : HF, countOf closure (a + b) x = countOf closure (a + b) y →
      HFSets.sat Env.closed (.everySplit kind left right) x →
        HFSets.sat Env.closed (.everySplit kind left right) y := by
    rintro x y same every A' B' ⟨hashSet, union'⟩
    obtain ⟨A, B, union, sameA, sameB⟩ := exists_split_match_counted positive same.symm union'
    rcases every A B ⟨hashSet, union⟩ with leftHolds | rightHolds
    · exact .inl ((leftDetermined A A' sameA).mp leftHolds)
    · exact .inr ((rightDetermined B B' sameB).mp rightHolds)
  exact fun x y same => ⟨direction x y same, direction y x same.symm⟩

/-! ## Larger closures -/

/-- **Counts for a larger closure decide counts for a smaller one**, at any cap up to theirs. -/
theorem countOf_sublist {small large : List (Formula 0)} (within : small ⊆ large) {low : ℕ} (le : low ≤ cap) {x y : HF}
    (same : countOf large cap x = countOf large cap y) : countOf small low x = countOf small low y := by
  funext ρ
  have cut : ∀ z : HF, membersOfType small z ρ =
      (memberSet z).filter fun m => (fun τ => τ.filter (· ∈ small) = ρ) (typeOf large m) := by
    intro z
    ext m
    simp only [membersOfType, Finset.mem_filter, typeOf_sublist within m]
  simp only [countOf, cut]
  exact min_card_type_eq (closure := large) (fun τ => τ.filter (· ∈ small) = ρ) le same

theorem CountDetermined.mono_closure {small large : List (Formula 0)} (within : small ⊆ large) {low : ℕ}
    (le : low ≤ cap) {p : HF → Prop} (determined : CountDetermined small low p) : CountDetermined large cap p :=
  fun x y same => determined x y (countOf_sublist within le same)

/-! ## Steps back -/

/-- `z` with `x` taken out and `y` put in. -/
def swapIn (z x y : HF) : HF :=
  ⟨insert y.1 (ZFSet.sep (fun w => w ≠ x.1) z.1),
    isHFSet_insert y.2 (isHFSet_of_subset_hf z.2 fun _ inside => (ZFSet.mem_sep.mp inside).1)⟩

theorem memberSet_swapIn (z x y : HF) : memberSet (swapIn z x y) = insert y ((memberSet z).erase x) := by
  ext m
  rw [mem_memberSet, Finset.mem_insert, Finset.mem_erase, mem_memberSet]
  change m.1 ∈ insert y.1 (ZFSet.sep _ z.1) ↔ _
  rw [ZFSet.mem_insert_iff, ZFSet.mem_sep]
  constructor
  · rintro (same | ⟨inside, differ⟩)
    · exact .inl (Subtype.ext same)
    · exact .inr ⟨fun equal => differ (congrArg Subtype.val equal), inside⟩
  · rintro (rfl | ⟨differ, inside⟩)
    · exact .inl rfl
    · exact .inr ⟨inside, fun equal => differ (Subtype.ext equal)⟩

/-- **A member swapped for a set of its type, absent from the container, keeps the counts exactly.** -/
theorem countOf_swapIn {small : List (Formula 0)} (low : ℕ) {x y z : HF} (member : x.1 ∈ z.1) (absent : y.1 ∉ z.1)
    (same : typeOf small x = typeOf small y) : countOf small low (swapIn z x y) = countOf small low z := by
  funext ρ
  simp only [countOf, membersOfType, memberSet_swapIn]
  congr 1
  have xIn : x ∈ memberSet z := mem_memberSet.mpr member
  have yOut : y ∉ memberSet z := fun found => absent (mem_memberSet.mp found)
  rw [Finset.filter_insert, Finset.filter_erase]
  by_cases typed : typeOf small y = ρ
  · have xTyped : x ∈ (memberSet z).filter fun m => typeOf small m = ρ :=
      Finset.mem_filter.mpr ⟨xIn, same.trans typed⟩
    have yNot : y ∉ ((memberSet z).filter fun m => typeOf small m = ρ).erase x := fun found =>
      yOut (Finset.mem_filter.mp (Finset.mem_of_mem_erase found)).1
    rw [if_pos typed, Finset.card_insert_of_notMem yNot, Finset.card_erase_add_one xTyped]
  · have xNot : x ∉ (memberSet z).filter fun m => typeOf small m = ρ := fun found =>
      typed (same ▸ (Finset.mem_filter.mp found).2)
    rw [if_neg typed, Finset.erase_eq_of_notMem xNot]

/-- **A step back reads the type of the set itself**, which a count-local closure decides. -/
theorem countDetermined_sometimeBefore {small : List (Formula 0)} {low : ℕ} (within : small ⊆ closure) (le : low ≤ cap)
    (loc : IsCountLocal small low) {inner : Formula 0} (inside : inner ∈ small) (label : StepLabel) :
    CountDetermined closure cap (HFSets.sat Env.closed (.sometimeBefore label inner)) := by
  have direction : ∀ x y : HF, typeOf small x = typeOf small y →
      HFSets.sat Env.closed (.sometimeBefore label inner) x → HFSets.sat Env.closed (.sometimeBefore label inner) y := by
    rintro x y same ⟨z, ⟨labelled, member⟩, holds⟩
    by_cases present : y.1 ∈ z.1
    · exact ⟨z, ⟨labelled, present⟩, holds⟩
    · refine ⟨swapIn z x y, ⟨labelled, ZFSet.mem_insert_iff.mpr (.inl rfl)⟩, ?_⟩
      exact (loc inner inside _ _ (countOf_swapIn low member present same)).mpr holds
  intro x y counts
  have same := loc.typeOf_eq (countOf_sublist within le counts)
  exact ⟨direction x y same, direction y x same.symm⟩

theorem countDetermined_alwaysBefore {small : List (Formula 0)} {low : ℕ} (within : small ⊆ closure) (le : low ≤ cap)
    (loc : IsCountLocal small low) {inner : Formula 0} (inside : inner ∈ small) (label : StepLabel) :
    CountDetermined closure cap (HFSets.sat Env.closed (.alwaysBefore label inner)) := by
  have direction : ∀ x y : HF, typeOf small x = typeOf small y →
      HFSets.sat Env.closed (.alwaysBefore label inner) x → HFSets.sat Env.closed (.alwaysBefore label inner) y := by
    rintro x y same every z ⟨labelled, member⟩
    by_cases present : x.1 ∈ z.1
    · exact every z ⟨labelled, present⟩
    · have swapped := every (swapIn z y x) ⟨labelled, ZFSet.mem_insert_iff.mpr (.inl rfl)⟩
      exact (loc inner inside _ _ (countOf_swapIn low member present same.symm)).mp swapped
  intro x y counts
  have same := loc.typeOf_eq (countOf_sublist within le counts)
  exact ⟨direction x y same, direction y x same.symm⟩

end

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
