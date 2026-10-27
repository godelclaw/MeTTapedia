import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTypes
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Substitution

/-!
# Formers decided by the members' types

A closure is local when each of its formulas is decided by the types of a set's members (`IsLocal`,
`SetMembershipTypes`). Here each former is shown to preserve that, so that closures built from subformulas are local:

- the connectives and constants (`Determined.and`, `Determined.or`, `Determined.const`);
- **a step forward reads the members' types** (`determined_possibly`, `determined_necessarily`), and emptiness is having
  no member types (`determined_empty`);
- **a named set is pinned by the names of its members** (`determined_is`), whose closure is local
  (`nameClosure_isLocal`);
- **a split of `x` is matched part for part** by a split of any set with the same members' types
  (`exists_split_match`, `determined_split`);
- **a step back reads the type of the set itself**, which a local closure decides (`determined_sometimeBefore`), and a
  quantifier over a sort does not depend on the set (`determined_someOf`).

A larger closure decides what a smaller one does (`Determined.mono`). The closures of fixed points are built and shown
local in `SetMembershipFixedPoints`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Classical

noncomputable section

variable {closure : List (Formula 0)}

/-! ## Determined formers -/

theorem Determined.of_iff {p q : HF → Prop} (same : ∀ x, p x ↔ q x) (determined : Determined closure q) :
    Determined closure p := fun x y members => by rw [same, same]; exact determined x y members

theorem Determined.const (P : Prop) : Determined closure fun _ => P := fun _ _ _ => Iff.rfl

theorem Determined.and {p q : HF → Prop} (first : Determined closure p) (second : Determined closure q) :
    Determined closure fun x => p x ∧ q x := fun x y members => and_congr (first x y members) (second x y members)

theorem Determined.or {p q : HF → Prop} (first : Determined closure p) (second : Determined closure q) :
    Determined closure fun x => p x ∨ q x := fun x y members => or_congr (first x y members) (second x y members)

theorem Determined.not {p : HF → Prop} (determined : Determined closure p) : Determined closure fun x => ¬ p x :=
  fun x y members => not_congr (determined x y members)

/-- The type for a smaller closure is the type for the larger one, cut down. -/
theorem typeOf_sublist {small large : List (Formula 0)} (within : small ⊆ large) (x : HF) :
    typeOf small x = (typeOf large x).filter (· ∈ small) := by
  ext φ
  simp only [mem_typeOf, Finset.mem_filter]
  exact ⟨fun ⟨inside, holds⟩ => ⟨⟨within inside, holds⟩, inside⟩, fun ⟨⟨_, holds⟩, inside⟩ => ⟨inside, holds⟩⟩

theorem memberTypes_sublist {small large : List (Formula 0)} (within : small ⊆ large) {x y : HF}
    (same : memberTypes large x = memberTypes large y) : memberTypes small x = memberTypes small y := by
  have image : ∀ z : HF, memberTypes small z = (fun τ => τ.filter (· ∈ small)) '' memberTypes large z := by
    intro z
    ext τ
    simp only [memberTypes, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨m, inside, rfl⟩
      exact ⟨typeOf large m, ⟨m, inside, rfl⟩, (typeOf_sublist within m).symm⟩
    · rintro ⟨_, ⟨m, inside, rfl⟩, rfl⟩
      exact ⟨m, inside, typeOf_sublist within m⟩
  rw [image, image, same]

/-- **A larger closure decides what a smaller one does.** -/
theorem Determined.mono {small large : List (Formula 0)} (within : small ⊆ large) {p : HF → Prop}
    (determined : Determined small p) : Determined large p :=
  fun x y members => determined x y (memberTypes_sublist within members)

theorem IsLocal.mono_determined {small large : List (Formula 0)} (within : small ⊆ large) (loc : IsLocal small)
    {φ : Formula 0} (inside : φ ∈ small) : Determined large (HFSets.sat Env.closed φ) :=
  (loc φ inside).mono within

theorem mem_memberTypes {x : HF} {τ : Finset (Formula 0)} :
    τ ∈ memberTypes closure x ↔ ∃ m : HF, m.1 ∈ x.1 ∧ typeOf closure m = τ := Iff.rfl

/-- **A step forward reads the members' types.** -/
theorem determined_possibly {inner : Formula 0} (inside : inner ∈ closure) (label : StepLabel) :
    Determined closure (HFSets.sat Env.closed (.possibly label inner)) := by
  have reading : ∀ x : HF, HFSets.sat Env.closed (.possibly label inner) x ↔
      memberLabel label ∧ ∃ τ ∈ memberTypes closure x, inner ∈ τ := by
    intro x
    constructor
    · rintro ⟨m, step, holds⟩
      exact ⟨step.1, typeOf closure m, ⟨m, step.2, rfl⟩, mem_typeOf.mpr ⟨inside, holds⟩⟩
    · rintro ⟨labelled, _, ⟨m, member, rfl⟩, found⟩
      exact ⟨m, ⟨labelled, member⟩, (mem_typeOf.mp found).2⟩
  exact Determined.of_iff reading fun x y members => by rw [members]

theorem determined_necessarily {inner : Formula 0} (inside : inner ∈ closure) (label : StepLabel) :
    Determined closure (HFSets.sat Env.closed (.necessarily label inner)) := by
  have reading : ∀ x : HF, HFSets.sat Env.closed (.necessarily label inner) x ↔
      (memberLabel label → ∀ τ ∈ memberTypes closure x, inner ∈ τ) := by
    intro x
    constructor
    · rintro every labelled _ ⟨m, member, rfl⟩
      exact mem_typeOf.mpr ⟨inside, every m ⟨labelled, member⟩⟩
    · intro every m step
      exact (mem_typeOf.mp (every step.1 _ ⟨m, step.2, rfl⟩)).2
  exact Determined.of_iff reading fun x y members => by rw [members]

theorem memberTypes_eq_empty {x : HF} : memberTypes closure x = ∅ ↔ x.1 = ∅ := by
  constructor
  · intro none
    ext z
    simp only [ZFSet.notMem_empty, iff_false]
    intro member
    have : typeOf closure (memberOf x member) ∈ memberTypes closure x := ⟨memberOf x member, member, rfl⟩
    rw [none] at this
    exact this
  · intro empty
    ext τ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨m, member, -⟩
    rw [empty] at member
    exact ZFSet.notMem_empty _ member

theorem determined_empty (kind : CollType) : Determined closure (HFSets.sat Env.closed (.empty kind)) := by
  have reading : ∀ x : HF, HFSets.sat Env.closed (.empty kind) x ↔ kind = .hashSet ∧ memberTypes closure x = ∅ :=
    fun x => and_congr_right fun _ => memberTypes_eq_empty.symm
  exact Determined.of_iff reading fun x y members => by rw [members]

theorem determined_nonEmpty (kind : CollType) : Determined closure (HFSets.sat Env.closed (.nonEmpty kind)) :=
  (determined_empty kind).not

/-- **A named set is pinned by the names of its members.** -/
theorem determined_is {target : Pattern} (names : ∀ value ∈ membersOf target, Formula.is value ∈ closure) :
    Determined closure (HFSets.sat Env.closed (.is target)) := by
  by_cases targetHolds : IsHF target
  · have direction : ∀ x y : HF, memberTypes closure x = memberTypes closure y → x.1 = zfOf target →
        y.1 = zfOf target := by
      intro x y members named
      have pinned : ∀ (m m' : HF) (value : Pattern), value ∈ membersOf target → m'.1 = zfOf value →
          typeOf closure m = typeOf closure m' → m.1 = zfOf value := by
        intro m m' value listed same equal
        have holds : HFSets.sat Env.closed (.is value) m' := ⟨hf_members targetHolds value listed, same⟩
        have found : Formula.is value ∈ typeOf closure m := equal ▸ mem_typeOf.mpr ⟨names value listed, holds⟩
        exact (mem_typeOf.mp found).2.2
      apply ZFSet.ext
      intro z
      rw [mem_zfOf_hf targetHolds]
      constructor
      · intro member
        have : typeOf closure (memberOf y member) ∈ memberTypes closure x := by
          rw [members]; exact ⟨memberOf y member, member, rfl⟩
        obtain ⟨m', inside', same⟩ := this
        rw [named, mem_zfOf_hf targetHolds] at inside'
        obtain ⟨value, listed, equal⟩ := inside'
        exact ⟨value, listed, (pinned (memberOf y member) m' value listed equal.symm same.symm).symm⟩
      · rintro ⟨value, listed, rfl⟩
        have inside : zfOf value ∈ x.1 := by rw [named, mem_zfOf_hf targetHolds]; exact ⟨value, listed, rfl⟩
        have : typeOf closure (memberOf x inside) ∈ memberTypes closure y := by
          rw [← members]; exact ⟨memberOf x inside, inside, rfl⟩
        obtain ⟨m, member, same⟩ := this
        rw [pinned m (memberOf x inside) value listed rfl same] at member
        exact member
    have reading : ∀ x : HF, HFSets.sat Env.closed (.is target) x ↔ x.1 = zfOf target :=
      fun x => ⟨fun named => named.2, fun same => ⟨targetHolds, same⟩⟩
    exact Determined.of_iff reading fun x y members =>
      ⟨direction x y members, direction y x members.symm⟩
  · exact Determined.of_iff (fun x => ⟨fun named => absurd named.1 targetHolds, False.elim⟩) (Determined.const False)

theorem determined_isNot {target : Pattern} (names : ∀ value ∈ membersOf target, Formula.is value ∈ closure) :
    Determined closure (HFSets.sat Env.closed (.isNot target)) :=
  (determined_is names).not

/-- The members of `y` whose types are among the members' types of `part`. -/
def cutByTypes (closure : List (Formula 0)) (y part : HF) : HF :=
  ⟨ZFSet.sep (fun z => ∃ held : IsHFSet z, typeOf closure ⟨z, held⟩ ∈ memberTypes closure part) y.1, isHFSet_sep y.2 _⟩

theorem mem_cutByTypes {y part : HF} {z : ZFSet.{0}} : z ∈ (cutByTypes closure y part).1 ↔
    z ∈ y.1 ∧ ∃ held : IsHFSet z, typeOf closure ⟨z, held⟩ ∈ memberTypes closure part := by
  unfold cutByTypes
  simp only [ZFSet.mem_sep]

/-- **A split is matched part for part** by a split of a set with the same members' types. -/
theorem exists_split_match {x y : HF} (members : memberTypes closure x = memberTypes closure y) {a b : HF}
    (union : x.1 = a.1 ∪ b.1) : ∃ a' b' : HF, y.1 = a'.1 ∪ b'.1 ∧ memberTypes closure a' = memberTypes closure a ∧
      memberTypes closure b' = memberTypes closure b := by
  let cut : HF → HF := cutByTypes closure y
  have mem_cut : ∀ (part : HF) (z : ZFSet.{0}), z ∈ (cut part).1 ↔
      z ∈ y.1 ∧ ∃ held : IsHFSet z, typeOf closure ⟨z, held⟩ ∈ memberTypes closure part :=
    fun part z => mem_cutByTypes
  have within : ∀ part : HF, part.1 ⊆ x.1 → memberTypes closure (cut part) = memberTypes closure part := by
    intro part inside
    ext τ
    constructor
    · rintro ⟨m, member, rfl⟩
      obtain ⟨-, held, found⟩ := (mem_cut part m.1).mp member
      exact found
    · rintro ⟨m, member, rfl⟩
      have : typeOf closure m ∈ memberTypes closure y := by rw [← members]; exact ⟨m, inside member, rfl⟩
      obtain ⟨m', member', same⟩ := this
      exact ⟨m', (mem_cut part m'.1).mpr ⟨member', m'.2, by rw [same]; exact ⟨m, member, rfl⟩⟩, same⟩
  refine ⟨cut a, cut b, ?_, within a fun z h => union ▸ ZFSet.mem_union.mpr (Or.inl h), within b fun z h => union ▸ ZFSet.mem_union.mpr (Or.inr h)⟩
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_union, mem_cut, mem_cut]
  constructor
  · intro member
    have : typeOf closure (memberOf y member) ∈ memberTypes closure x := by
      rw [members]; exact ⟨memberOf y member, member, rfl⟩
    obtain ⟨m, inside, same⟩ := this
    rw [union, ZFSet.mem_union] at inside
    rcases inside with inside | inside
    · exact .inl ⟨member, (memberOf y member).2, same ▸ ⟨m, inside, rfl⟩⟩
    · exact .inr ⟨member, (memberOf y member).2, same ▸ ⟨m, inside, rfl⟩⟩
  · rintro (⟨member, -⟩ | ⟨member, -⟩) <;> exact member

theorem split_iff_union {x a b : HF} (kind : CollType) :
    HFSets.split x kind a b ↔ kind = .hashSet ∧ x.1 = a.1 ∪ b.1 := Iff.rfl

/-- **A split of formulas decided by the members' types is decided by them.** -/
theorem determined_split {left right : Formula 0} (kind : CollType)
    (leftDetermined : Determined closure (HFSets.sat Env.closed left))
    (rightDetermined : Determined closure (HFSets.sat Env.closed right)) :
    Determined closure (HFSets.sat Env.closed (.split kind left right)) := by
  have direction : ∀ x y : HF, memberTypes closure x = memberTypes closure y →
      HFSets.sat Env.closed (.split kind left right) x → HFSets.sat Env.closed (.split kind left right) y := by
    rintro x y members ⟨a, b, ⟨hashSet, union⟩, leftHolds, rightHolds⟩
    obtain ⟨a', b', union', sameA, sameB⟩ := exists_split_match members union
    exact ⟨a', b', ⟨hashSet, union'⟩, (leftDetermined a' a sameA).mpr leftHolds,
      (rightDetermined b' b sameB).mpr rightHolds⟩
  exact fun x y members => ⟨direction x y members, direction y x members.symm⟩

theorem determined_everySplit {left right : Formula 0} (kind : CollType)
    (leftDetermined : Determined closure (HFSets.sat Env.closed left))
    (rightDetermined : Determined closure (HFSets.sat Env.closed right)) :
    Determined closure (HFSets.sat Env.closed (.everySplit kind left right)) := by
  have direction : ∀ x y : HF, memberTypes closure x = memberTypes closure y →
      HFSets.sat Env.closed (.everySplit kind left right) x →
        HFSets.sat Env.closed (.everySplit kind left right) y := by
    intro x y members every a' b' split
    obtain ⟨hashSet, union'⟩ := split
    obtain ⟨a, b, union, sameA, sameB⟩ := exists_split_match members.symm union'
    rcases every a b ⟨hashSet, union⟩ with leftHolds | rightHolds
    · exact .inl ((leftDetermined a a' sameA).mp leftHolds)
    · exact .inr ((rightDetermined b b' sameB).mp rightHolds)
  exact fun x y members => ⟨direction x y members, direction y x members.symm⟩

/-- `x` and `y` of the same type, each added to the same part, give sets of the same members' types. -/
theorem memberTypes_insertStage {small : List (Formula 0)} {x y : HF} (same : typeOf small x = typeOf small y)
    {k : ℕ} {part : ZFSet.{0}} (within : part ⊆ stage k) :
    memberTypes small (insertStage x within) = memberTypes small (insertStage y within) := by
  apply memberTypes_eq_of_match
  · intro m inside
    rcases ZFSet.mem_insert_iff.mp inside with equal | found
    · exact ⟨y, ZFSet.mem_insert_iff.mpr (Or.inl rfl), by rw [← same, Subtype.ext equal]⟩
    · exact ⟨m, ZFSet.mem_insert_iff.mpr (Or.inr found), rfl⟩
  · intro m inside
    rcases ZFSet.mem_insert_iff.mp inside with equal | found
    · exact ⟨x, ZFSet.mem_insert_iff.mpr (Or.inl rfl), by rw [same, Subtype.ext equal]⟩
    · exact ⟨m, ZFSet.mem_insert_iff.mpr (Or.inr found), rfl⟩

/-- **A step back reads the type of the set itself**, which a local closure decides. -/
theorem determined_sometimeBefore {small : List (Formula 0)} (within : small ⊆ closure) (loc : IsLocal small)
    {inner : Formula 0} (inside : inner ∈ small) (label : StepLabel) :
    Determined closure (HFSets.sat Env.closed (.sometimeBefore label inner)) := by
  intro x y members
  have same : typeOf small x = typeOf small y := loc.typeOf_eq (memberTypes_sublist within members)
  rw [sometimeBefore_iff_stage loc le_rfl inside, sometimeBefore_iff_stage loc le_rfl inside]
  refine and_congr_right fun _ => exists_congr fun part => exists_congr fun stageWithin => ?_
  exact loc inner inside _ _ (memberTypes_insertStage same stageWithin)

theorem determined_alwaysBefore {small : List (Formula 0)} (within : small ⊆ closure) (loc : IsLocal small)
    {inner : Formula 0} (inside : inner ∈ small) (label : StepLabel) :
    Determined closure (HFSets.sat Env.closed (.alwaysBefore label inner)) := by
  intro x y members
  have same : typeOf small x = typeOf small y := loc.typeOf_eq (memberTypes_sublist within members)
  rw [alwaysBefore_iff_stage loc le_rfl inside, alwaysBefore_iff_stage loc le_rfl inside]
  refine imp_congr_right fun _ => forall_congr' fun part => forall_congr' fun stageWithin => ?_
  exact loc inner inside _ _ (memberTypes_insertStage same stageWithin)

theorem determined_someOf (type : TypeExpr) (inner : Formula 0) :
    Determined closure (HFSets.sat Env.closed (.someOf type inner)) := fun _ _ _ => Iff.rfl

theorem determined_everyOf (type : TypeExpr) (inner : Formula 0) :
    Determined closure (HFSets.sat Env.closed (.everyOf type inner)) := fun _ _ _ => Iff.rfl

/-! ## The names of a named set -/

/-- **The names of a named set's hereditary members**, with its own. -/
def nameClosure (target : Pattern) : List (Formula 0) :=
  .is target :: (membersOf target).attach.flatMap fun value => nameClosure value.1
termination_by height target
decreasing_by exact height_lt_of_mem value.2

theorem is_mem_nameClosure (target : Pattern) : Formula.is target ∈ nameClosure target := by
  rw [nameClosure]
  exact List.mem_cons_self

theorem nameClosure_subset {target value : Pattern} (listed : value ∈ membersOf target) :
    nameClosure value ⊆ nameClosure target := by
  intro φ found
  rw [nameClosure]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨⟨value, listed⟩, List.mem_attach _ _, found⟩)

/-- **The names of a named set's members decide it**, all the way down. -/
theorem nameClosure_isLocal (target : Pattern) : IsLocal (nameClosure target) := by
  induction hTarget : height target using Nat.strong_induction_on generalizing target with
  | _ k ih =>
    intro φ found
    rw [nameClosure] at found
    rcases List.mem_cons.mp found with rfl | found
    · exact determined_is fun value listed => nameClosure_subset listed (is_mem_nameClosure value)
    · obtain ⟨⟨value, listed⟩, -, inside⟩ := List.mem_flatMap.mp found
      exact ((ih (height value) (hTarget ▸ height_lt_of_mem listed) value rfl) φ inside).mono
        (nameClosure_subset listed)


theorem names_of_nameClosure {target : Pattern} {C : List (Formula 0)} (within : nameClosure target ⊆ C) :
    ∀ value ∈ membersOf target, Formula.is value ∈ C :=
  fun value listed => within (nameClosure_subset listed (is_mem_nameClosure value))


end

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
