import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTypes

/-!
# Representatives of types

The searches for containers and for sets of a sort range over `V_(2^n)` (`SetMembershipTypes`): every type of a local
closure of `n` formulas is realized there. Far fewer sets serve: one representative of each type, as long as the
representatives are closed under forming sets of them.

- **Closed representatives** (`RepsClosed`): hereditary terms such that every set of some of them has the type of one
  of them.
- **They represent every type** (`RepsClosed.covers`), by induction along membership: replace each member of a set by
  the representative of its type; the set formed has the same members' types, so the same type, and it is the type of a
  representative.
- **So the searches range over them** (`sometimeBefore_iff_reps`, `alwaysBefore_iff_reps`, `someOf_iff_reps`,
  `everyOf_iff_reps`): a container of `x` has a formula exactly when `x` added to some of the representatives does,
  and some set has it exactly when some representative does.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Classical

noncomputable section

variable {closure : List (Formula 0)}

variable (closure) in
/-- **The type of a term**: the formulas of the closure that hold at the set it denotes. -/
def termType (term : Pattern) : Finset (Formula 0) :=
  closure.toFinset.filter fun φ => ∃ holds : IsHF term, HFSets.sat Env.closed φ (hfOf holds)

theorem termType_eq {term : Pattern} (holds : IsHF term) : termType closure term = typeOf closure (hfOf holds) := by
  ext φ
  simp only [termType, typeOf, Finset.mem_filter]
  exact and_congr_right fun _ => ⟨fun ⟨_, sat⟩ => sat, fun sat => ⟨holds, sat⟩⟩

theorem set_hf {values : List Pattern} (all : ∀ value ∈ values, IsHF value) : IsHF (set values) :=
  .members all

/-- **Closed representatives**: hereditary terms such that every set formed of some of them, in their order, has the
type of one of them. -/
structure RepsClosed (closure : List (Formula 0)) (reps : List Pattern) : Prop where
  hf : ∀ r ∈ reps, IsHF r
  sets : ∀ sub ∈ reps.sublists, ∃ r ∈ reps, termType closure r = termType closure (set sub)

/-- Two lists with the same members denote the same set. -/
theorem zfOf_set_congr {first second : List Pattern} (same : ∀ value, value ∈ first ↔ value ∈ second) :
    zfOf (set first) = zfOf (set second) := by
  ext z
  rw [zfOf_set, zfOf_set, mem_zfOfList, mem_zfOfList]
  exact ⟨fun ⟨value, inside, eq⟩ => ⟨value, (same value).mp inside, eq⟩,
    fun ⟨value, inside, eq⟩ => ⟨value, (same value).mpr inside, eq⟩⟩

theorem termType_congr {first second : Pattern} (firstHolds : IsHF first) (secondHolds : IsHF second)
    (same : zfOf first = zfOf second) : termType closure first = termType closure second := by
  rw [termType_eq firstHolds, termType_eq secondHolds]
  exact congrArg (typeOf closure) (Subtype.ext same)

/-- **A set of representatives in any order and with repetitions has the type of one of them.** -/
theorem RepsClosed.sets_of_mem {reps : List Pattern} (closed : RepsClosed closure reps) {sub : List Pattern}
    (within : ∀ value ∈ sub, value ∈ reps) : ∃ r ∈ reps, termType closure r = termType closure (set sub) := by
  let ordered := reps.filter fun r => decide (r ∈ sub)
  have orderedSub : ordered ∈ reps.sublists := List.mem_sublists.mpr List.filter_sublist
  obtain ⟨r, inside, same⟩ := closed.sets ordered orderedSub
  have members : ∀ value, value ∈ ordered ↔ value ∈ sub := by
    intro value
    simp only [ordered, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun found => found.2, fun found => ⟨within value found, found⟩⟩
  have orderedHolds : IsHF (set ordered) :=
    set_hf fun value found => closed.hf value ((members value).mp found |> within value)
  have subHolds : IsHF (set sub) := set_hf fun value found => closed.hf value (within value found)
  exact ⟨r, inside, same.trans (termType_congr orderedHolds subHolds (zfOf_set_congr members))⟩

/-- A member of the set a hereditary term denotes is denoted by one of its members. -/
theorem mem_hfOf {term : Pattern} (holds : IsHF term) {m : HF} (inside : m.1 ∈ (hfOf holds).1) :
    ∃ value ∈ membersOf term, ∃ valueHolds : IsHF value, hfOf valueHolds = m := by
  obtain ⟨value, member, same⟩ := (mem_zfOf_hf holds).mp inside
  exact ⟨value, member, hf_members holds value member, Subtype.ext same⟩

/-- **Sets matched type for type have the same type.** -/
theorem termType_of_match (loc : IsLocal closure) {first second : List Pattern} (firstHolds : IsHF (set first))
    (secondHolds : IsHF (set second))
    (forth : ∀ value ∈ first, ∃ value' ∈ second, termType closure value' = termType closure value)
    (back : ∀ value' ∈ second, ∃ value ∈ first, termType closure value = termType closure value') :
    termType closure (set first) = termType closure (set second) := by
  rw [termType_eq firstHolds, termType_eq secondHolds]
  apply loc.typeOf_eq
  apply memberTypes_eq_of_match
  · intro m inside
    obtain ⟨value, member, valueHolds, rfl⟩ := mem_hfOf firstHolds inside
    obtain ⟨value', member', same⟩ := forth value member
    have valueHolds' := hf_members secondHolds value' member'
    refine ⟨hfOf valueHolds', ?_, ?_⟩
    · exact (mem_zfOf_hf secondHolds).mpr ⟨value', member', rfl⟩
    · rw [← termType_eq, ← termType_eq, same]
  · intro m inside
    obtain ⟨value', member', valueHolds', rfl⟩ := mem_hfOf secondHolds inside
    obtain ⟨value, member, same⟩ := back value' member'
    have valueHolds := hf_members firstHolds value member
    refine ⟨hfOf valueHolds, ?_, ?_⟩
    · exact (mem_zfOf_hf firstHolds).mpr ⟨value, member, rfl⟩
    · rw [← termType_eq, ← termType_eq, same]

/-- **Closed representatives represent every type**, by induction along membership. -/
theorem RepsClosed.covers (loc : IsLocal closure) {reps : List Pattern} (closed : RepsClosed closure reps) :
    ∀ {term : Pattern}, IsHF term → ∃ r ∈ reps, termType closure r = termType closure term := by
  intro term holds
  induction holds with
  | atom atom => exact absurd atom (membership_pure _)
  | @members values all ih =>
    have pick : ∀ value ∈ values, ∃ r ∈ reps, termType closure r = termType closure value := fun value inside =>
      ih value inside
    let chosen : List Pattern := values.attach.map fun value => (pick value.1 value.2).choose
    have chosenIn : ∀ r ∈ chosen, r ∈ reps := by
      intro r found
      obtain ⟨value, -, rfl⟩ := List.mem_map.mp found
      exact (pick value.1 value.2).choose_spec.1
    obtain ⟨r, inside, same⟩ := closed.sets_of_mem chosenIn
    refine ⟨r, inside, same.trans (termType_of_match loc (set_hf fun r found => closed.hf r (chosenIn r found))
      (set_hf all) ?_ ?_)⟩
    · intro r found
      obtain ⟨value, -, rfl⟩ := List.mem_map.mp found
      exact ⟨value.1, value.2, ((pick value.1 value.2).choose_spec.2).symm⟩
    · intro value member
      exact ⟨(pick value member).choose, List.mem_map.mpr ⟨⟨value, member⟩, List.mem_attach _ _, rfl⟩,
        (pick value member).choose_spec.2⟩

/-! ## Searching the representatives -/

variable {reps : List Pattern}

/-- A hereditarily finite set, as the set a hereditary term denotes. -/
theorem exists_term (z : HF) : ∃ term, ∃ holds : IsHF term, hfOf holds = z := by
  obtain ⟨term, holds, same⟩ := z.2
  exact ⟨term, holds, Subtype.ext same⟩

theorem sat_of_termType {φ : Formula 0} (inside : φ ∈ closure) {first second : Pattern} (firstHolds : IsHF first)
    (secondHolds : IsHF second) (same : termType closure first = termType closure second) :
    HFSets.sat Env.closed φ (hfOf firstHolds) ↔ HFSets.sat Env.closed φ (hfOf secondHolds) := by
  rw [termType_eq firstHolds, termType_eq secondHolds] at same
  exact sat_iff_of_typeOf_eq inside same

/-- **Some container has the type of `x` added to some representatives**: replace each of its members by the
representative of its type. -/
theorem exists_container_reps (loc : IsLocal closure) (closed : RepsClosed closure reps) {term : Pattern}
    (holds : IsHF term) {z : HF} (inside : (hfOf holds).1 ∈ z.1) :
    ∃ sub ∈ reps.sublists, ∃ containerHolds : IsHF (set (term :: sub)),
      typeOf closure (hfOf containerHolds) = typeOf closure z := by
  obtain ⟨container, containerHolds, rfl⟩ := exists_term z
  let matched : Pattern → Prop := fun r => ∃ value ∈ membersOf container, termType closure r = termType closure value
  let sub := reps.filter fun r => decide (matched r)
  have subSub : sub ∈ reps.sublists := List.mem_sublists.mpr List.filter_sublist
  have subIn : ∀ r ∈ sub, r ∈ reps := fun r found => (List.mem_filter.mp found).1
  have newHolds : IsHF (set (term :: sub)) := set_hf fun value found => by
    rcases List.mem_cons.mp found with rfl | found
    · exact holds
    · exact closed.hf value (subIn value found)
  obtain ⟨values, same, all⟩ := hf_set containerHolds
  have containerSet : IsHF (set values) := same ▸ containerHolds
  have members : membersOf container = values := by rw [same]; rfl
  refine ⟨sub, subSub, newHolds, ?_⟩
  rw [← termType_eq newHolds, ← termType_eq containerHolds]
  have containerEq : termType closure container = termType closure (set values) := by rw [same]
  rw [containerEq]
  apply termType_of_match loc newHolds containerSet
  · intro value found
    rcases List.mem_cons.mp found with rfl | found
    · obtain ⟨value', member', eq⟩ := (mem_zfOf_hf containerHolds).mp inside
      rw [members] at member'
      exact ⟨value', member', termType_congr (all value' member') holds eq⟩
    · obtain ⟨-, matchedValue⟩ := List.mem_filter.mp found
      obtain ⟨value', member', eq⟩ := of_decide_eq_true matchedValue
      rw [members] at member'
      exact ⟨value', member', eq.symm⟩
  · intro value member
    obtain ⟨r, rIn, eq⟩ := closed.covers loc (all value member)
    refine ⟨r, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨rIn, decide_eq_true ?_⟩), eq⟩
    exact ⟨value, by rw [members]; exact member, eq⟩

/-- **Some set containing `x` has a formula of a local closure exactly when `x` added to some of the representatives
has it.** -/
theorem sometimeBefore_iff_reps (loc : IsLocal closure) (closed : RepsClosed closure reps) {φ : Formula 0}
    (inside : φ ∈ closure) (label : StepLabel) {term : Pattern} (holds : IsHF term) :
    HFSets.sat Env.closed (.sometimeBefore label φ) (hfOf holds) ↔
      memberLabel label ∧ ∃ sub ∈ reps.sublists, ∃ containerHolds : IsHF (set (term :: sub)),
        HFSets.sat Env.closed φ (hfOf containerHolds) := by
  constructor
  · rintro ⟨z, step, sat⟩
    obtain ⟨sub, subSub, containerHolds, same⟩ := exists_container_reps loc closed holds step.2
    exact ⟨step.1, sub, subSub, containerHolds, (sat_iff_of_typeOf_eq inside same).mpr sat⟩
  · rintro ⟨labelled, sub, -, containerHolds, sat⟩
    refine ⟨hfOf containerHolds, ⟨labelled, ?_⟩, sat⟩
    exact (mem_zfOf_hf containerHolds).mpr ⟨term, List.mem_cons_self, rfl⟩

/-- **Every set containing `x` has a formula of a local closure exactly when `x` added to any of the representatives
has it.** -/
theorem alwaysBefore_iff_reps (loc : IsLocal closure) (closed : RepsClosed closure reps) {φ : Formula 0}
    (inside : φ ∈ closure) (label : StepLabel) {term : Pattern} (holds : IsHF term) :
    HFSets.sat Env.closed (.alwaysBefore label φ) (hfOf holds) ↔
      (memberLabel label → ∀ sub ∈ reps.sublists, ∀ containerHolds : IsHF (set (term :: sub)),
        HFSets.sat Env.closed φ (hfOf containerHolds)) := by
  constructor
  · intro every labelled sub _ containerHolds
    exact every _ ⟨labelled, (mem_zfOf_hf containerHolds).mpr ⟨term, List.mem_cons_self, rfl⟩⟩
  · intro every z step
    obtain ⟨sub, subSub, containerHolds, same⟩ := exists_container_reps loc closed holds step.2
    exact (sat_iff_of_typeOf_eq inside same).mp (every step.1 sub subSub containerHolds)

/-- **Some set has a formula of a local closure exactly when some representative has it.** -/
theorem someOf_iff_reps (loc : IsLocal closure) (closed : RepsClosed closure reps) {φ : Formula 0}
    (inside : φ ∈ closure) (x : HF) :
    HFSets.sat Env.closed (.someOf (.base "Set") φ) x ↔
      ∃ r, ∃ rIn : r ∈ reps, HFSets.sat Env.closed φ (hfOf (closed.hf r rIn)) := by
  constructor
  · rintro ⟨witness, -, sat⟩
    obtain ⟨term, holds, rfl⟩ := exists_term witness
    obtain ⟨r, rIn, same⟩ := closed.covers loc holds
    exact ⟨r, rIn, (sat_of_termType inside (closed.hf r rIn) holds same).mpr sat⟩
  · rintro ⟨r, rIn, sat⟩
    exact ⟨_, rfl, sat⟩

/-- **Every set has a formula of a local closure exactly when every representative has it.** -/
theorem everyOf_iff_reps (loc : IsLocal closure) (closed : RepsClosed closure reps) {φ : Formula 0}
    (inside : φ ∈ closure) (x : HF) :
    HFSets.sat Env.closed (.everyOf (.base "Set") φ) x ↔
      ∀ r, ∀ rIn : r ∈ reps, HFSets.sat Env.closed φ (hfOf (closed.hf r rIn)) := by
  constructor
  · intro every r rIn
    exact every _ rfl
  · intro every witness _
    obtain ⟨term, holds, rfl⟩ := exists_term witness
    obtain ⟨r, rIn, same⟩ := closed.covers loc holds
    exact (sat_of_termType inside (closed.hf r rIn) holds same).mp (every r rIn)

end

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
