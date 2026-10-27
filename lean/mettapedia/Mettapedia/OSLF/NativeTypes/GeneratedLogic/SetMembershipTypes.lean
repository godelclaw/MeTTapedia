import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipTwoWay

/-!
# Types of hereditarily finite sets

A finite list of closed formulas, a closure, gives each hereditarily finite set a type: the formulas of the closure
that hold there (`typeOf`). When every formula of the closure is decided by the types of a set's members (`IsLocal`),
the hereditarily finite sets behave like a finite algebra of types, whatever the formulas say:

- **The realized types stabilize** (`realizedAt`): the types realized in `V_k` grow with `k`, and once two
  consecutive stages agree all later ones do (`realizedAt_stable`), since a set with members in `V_(k+1)` has the type of
  a set whose members are representatives in `V_k`. The types are subsets of the closure, so this happens by stage
  `2 ^ n` for a closure of `n` formulas, and every type of a hereditarily finite set is realized in that stage
  (`typeOf_mem_realizedAt_bound`).
- **Steps back and sorts by representatives**: a set containing `x` with a formula of the closure may be taken to be
  `x` with a subset of that stage (`sometimeBefore_iff_stage`, `alwaysBefore_iff_stage`), and some set has the
  formula exactly when some set of that stage has it (`someOf_iff_stage`, `everyOf_iff_stage`).

Which closures are local is a question about the formulas; fixed points are taken up in `SetMembershipFixedPoints`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Classical

noncomputable section

/-- A member of a hereditarily finite set, as a hereditarily finite set. -/
def memberOf (x : HF) {z : ZFSet.{0}} (inside : z ∈ x.1) : HF :=
  ⟨z, by obtain ⟨term, holds, same⟩ := x.2; exact isHFSet_of_member holds (same ▸ inside)⟩

/-- `V_k`. -/
abbrev stage (k : ℕ) : ZFSet.{0} := ZFSet.vonNeumann (k : Ordinal)

theorem stage_mono {k l : ℕ} (le : k ≤ l) : stage k ⊆ stage l :=
  ZFSet.vonNeumann_subset_of_le (Nat.cast_le.mpr le)

theorem mem_stage_succ {k : ℕ} {z : ZFSet.{0}} : z ∈ stage (k + 1) ↔ z ⊆ stage k := by
  rw [stage, Nat.cast_succ, ZFSet.vonNeumann_add_one, ZFSet.mem_powerset]

/-- Every hereditarily finite set lies in some stage. -/
theorem exists_mem_stage (x : HF) : ∃ k, x.1 ∈ stage k := by
  obtain ⟨term, holds, same⟩ := x.2
  exact ⟨height term + 1, mem_stage_succ.mpr (same ▸ zfOf_subset_vonNeumann term holds)⟩

/-- A subset of a stage, as a hereditarily finite set. -/
def ofStage {k : ℕ} {z : ZFSet.{0}} (within : z ⊆ stage k) : HF := ⟨z, isHFSet_of_subset_vonNeumann within⟩

/-- `x` added to a subset of a stage. -/
def insertStage (x : HF) {k : ℕ} {part : ZFSet.{0}} (within : part ⊆ stage k) : HF :=
  ⟨insert x.1 part, isHFSet_insert x.2 (isHFSet_of_subset_vonNeumann within)⟩

/-! ## Types -/

section Types

variable (closure : List (Formula 0))

/-- **The type of a set**: the formulas of the closure that hold there. -/
def typeOf (x : HF) : Finset (Formula 0) := closure.toFinset.filter fun φ => HFSets.sat Env.closed φ x

variable {closure} in
theorem mem_typeOf {x : HF} {φ : Formula 0} : φ ∈ typeOf closure x ↔ φ ∈ closure ∧ HFSets.sat Env.closed φ x := by
  simp [typeOf]

theorem typeOf_subset (x : HF) : typeOf closure x ⊆ closure.toFinset := Finset.filter_subset _ _

/-- The types of the members. -/
def memberTypes (x : HF) : Set (Finset (Formula 0)) := {τ | ∃ m : HF, m.1 ∈ x.1 ∧ typeOf closure m = τ}

/-- **A property decided by the types of the members.** -/
def Determined (p : HF → Prop) : Prop :=
  ∀ x y : HF, memberTypes closure x = memberTypes closure y → (p x ↔ p y)

/-- **A local closure**: each of its formulas is decided by the types of the members. -/
def IsLocal : Prop := ∀ φ ∈ closure, Determined closure (HFSets.sat Env.closed φ)

variable {closure}

/-- In a local closure, the type is decided by the members' types. -/
theorem IsLocal.typeOf_eq (loc : IsLocal closure) {x y : HF} (same : memberTypes closure x = memberTypes closure y) :
    typeOf closure x = typeOf closure y := by
  ext φ
  simp only [mem_typeOf]
  exact and_congr_right fun inside => loc φ inside x y same

/-- Two sets whose members are matched type for type have the same members' types. -/
theorem memberTypes_eq_of_match {x y : HF}
    (forth : ∀ m : HF, m.1 ∈ x.1 → ∃ m' : HF, m'.1 ∈ y.1 ∧ typeOf closure m' = typeOf closure m)
    (back : ∀ m' : HF, m'.1 ∈ y.1 → ∃ m : HF, m.1 ∈ x.1 ∧ typeOf closure m = typeOf closure m') :
    memberTypes closure x = memberTypes closure y := by
  ext τ
  constructor
  · rintro ⟨m, inside, rfl⟩
    obtain ⟨m', inside', same⟩ := forth m inside
    exact ⟨m', inside', same⟩
  · rintro ⟨m', inside', rfl⟩
    obtain ⟨m, inside, same⟩ := back m' inside'
    exact ⟨m, inside, same⟩

/-! ## Realized types -/

variable (closure) in
/-- **The types realized in `V_k`.** -/
def realizedAt (k : ℕ) : Finset (Finset (Formula 0)) :=
  closure.toFinset.powerset.filter fun τ => ∃ y : HF, y.1 ∈ stage k ∧ typeOf closure y = τ

theorem mem_realizedAt {k : ℕ} {τ : Finset (Formula 0)} :
    τ ∈ realizedAt closure k ↔ ∃ y : HF, y.1 ∈ stage k ∧ typeOf closure y = τ := by
  simp only [realizedAt, Finset.mem_filter, Finset.mem_powerset, and_iff_right_iff_imp]
  rintro ⟨y, -, rfl⟩
  exact typeOf_subset closure y

theorem realizedAt_mono {k l : ℕ} (le : k ≤ l) : realizedAt closure k ⊆ realizedAt closure l := by
  intro τ found
  obtain ⟨y, inside, same⟩ := mem_realizedAt.mp found
  exact mem_realizedAt.mpr ⟨y, stage_mono le inside, same⟩

/-- **A set whose members' types are realized in `V_k` has the type of a set in `V_(k+1)`**: replace each member by a
representative of its type. -/
theorem exists_representative (loc : IsLocal closure) {k : ℕ} (y : HF)
    (realized : ∀ m : HF, m.1 ∈ y.1 → typeOf closure m ∈ realizedAt closure k) :
    ∃ y' : HF, y'.1 ⊆ stage k ∧ typeOf closure y' = typeOf closure y := by
  let pick : HF → HF := fun m =>
    if found : typeOf closure m ∈ realizedAt closure k then (mem_realizedAt.mp found).choose else m
  have pick_spec : ∀ m : HF, m.1 ∈ y.1 → (pick m).1 ∈ stage k ∧ typeOf closure (pick m) = typeOf closure m := by
    intro m inside
    have found := realized m inside
    simp only [pick, dif_pos found]
    exact (mem_realizedAt.mp found).choose_spec
  let part := ZFSet.sep (fun z => ∃ m : HF, m.1 ∈ y.1 ∧ (pick m).1 = z) (stage k)
  have within : part ⊆ stage k := fun z inside => (ZFSet.mem_sep.mp inside).1
  refine ⟨ofStage within, within, loc.typeOf_eq (memberTypes_eq_of_match ?_ ?_)⟩
  · intro m' inside'
    obtain ⟨-, m, inside, same⟩ := ZFSet.mem_sep.mp (show m'.1 ∈ part from inside')
    refine ⟨m, inside, ?_⟩
    rw [← (pick_spec m inside).2]
    exact congrArg (typeOf closure) (Subtype.ext same)
  · intro m inside
    exact ⟨pick m, show (pick m).1 ∈ part from ZFSet.mem_sep.mpr ⟨(pick_spec m inside).1, m, inside, rfl⟩,
      (pick_spec m inside).2⟩

/-- **Once two consecutive stages realize the same types, so does the next.** -/
theorem realizedAt_succ_eq (loc : IsLocal closure) {k : ℕ} (same : realizedAt closure k = realizedAt closure (k + 1)) :
    realizedAt closure (k + 1) = realizedAt closure (k + 2) := by
  refine le_antisymm (realizedAt_mono (Nat.le_succ _)) fun τ found => ?_
  obtain ⟨y, inside, rfl⟩ := mem_realizedAt.mp found
  have realized : ∀ m : HF, m.1 ∈ y.1 → typeOf closure m ∈ realizedAt closure k := by
    intro m member
    rw [same]
    exact mem_realizedAt.mpr ⟨m, mem_stage_succ.mp inside member, rfl⟩
  obtain ⟨y', within, sameType⟩ := exists_representative loc y realized
  exact mem_realizedAt.mpr ⟨y', mem_stage_succ.mpr within, sameType⟩

theorem realizedAt_stable (loc : IsLocal closure) {k : ℕ} (same : realizedAt closure k = realizedAt closure (k + 1))
    (j : ℕ) : realizedAt closure (k + j) = realizedAt closure k := by
  have both : ∀ j, realizedAt closure (k + j) = realizedAt closure k ∧
      realizedAt closure (k + j) = realizedAt closure (k + j + 1) := by
    intro j
    induction j with
    | zero => exact ⟨rfl, same⟩
    | succ j ih =>
      have next := realizedAt_succ_eq loc ih.2
      exact ⟨ih.2.symm.trans ih.1, next⟩
  exact (both j).1

variable (closure) in
/-- **The stage by which every type is realized**: `2 ^ n` for a closure of `n` distinct formulas. -/
def typeBound : ℕ := closure.toFinset.powerset.card

theorem card_realizedAt_le (k : ℕ) : (realizedAt closure k).card ≤ typeBound closure :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- **Some stage up to the bound realizes the same types as the next.** -/
theorem exists_stable_le : ∃ k ≤ typeBound closure, realizedAt closure k = realizedAt closure (k + 1) := by
  by_contra never
  simp only [not_exists, not_and] at never
  have growing : ∀ k ≤ typeBound closure + 1, k ≤ (realizedAt closure k).card := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro le
      have strict : realizedAt closure k ⊂ realizedAt closure (k + 1) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨realizedAt_mono (Nat.le_succ k), never k (by omega)⟩
      have := Finset.card_lt_card strict
      have := ih (by omega)
      omega
  have := growing (typeBound closure + 1) le_rfl
  have := card_realizedAt_le (closure := closure) (typeBound closure + 1)
  omega

/-- **Every type of a hereditarily finite set is realized in `V_(2^n)`.** -/
theorem typeOf_mem_realizedAt_bound (loc : IsLocal closure) (x : HF) :
    typeOf closure x ∈ realizedAt closure (typeBound closure) := by
  obtain ⟨k, bounded, same⟩ := exists_stable_le (closure := closure)
  obtain ⟨j, inside⟩ := exists_mem_stage x
  have found : typeOf closure x ∈ realizedAt closure j := mem_realizedAt.mpr ⟨x, inside, rfl⟩
  rcases le_total j (typeBound closure) with low | high
  · exact realizedAt_mono low found
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (le_trans bounded high)
    rw [realizedAt_stable loc same i] at found
    exact realizedAt_mono bounded found

/-- **A representative in `V_(2^n)` of every type.** -/
theorem exists_typeRepresentative (loc : IsLocal closure) (x : HF) :
    ∃ y : HF, y.1 ∈ stage (typeBound closure) ∧ typeOf closure y = typeOf closure x :=
  mem_realizedAt.mp (typeOf_mem_realizedAt_bound loc x)

theorem typeBound_le_pow : typeBound closure ≤ 2 ^ closure.length := by
  rw [typeBound, Finset.card_powerset]
  exact Nat.pow_le_pow_right (by decide) (List.toFinset_card_le closure)

/-- A representative of every type in any stage from `V_(2^n)` on. -/
theorem exists_typeRepresentative_le (loc : IsLocal closure) {bound : ℕ} (enough : typeBound closure ≤ bound)
    (x : HF) : ∃ y : HF, y.1 ∈ stage bound ∧ typeOf closure y = typeOf closure x := by
  obtain ⟨y, inside, same⟩ := exists_typeRepresentative loc x
  exact ⟨y, stage_mono enough inside, same⟩

/-! ## Steps back and sorts by representatives -/

/-- **A container whose members are representatives**: every set containing `x` has the type of `x` added to a subset
of `V_(2^n)`. -/
theorem exists_container_in_stage (loc : IsLocal closure) {bound : ℕ} (enough : typeBound closure ≤ bound) {x z : HF}
    (inside : x.1 ∈ z.1) :
    ∃ part, ∃ within : part ⊆ stage bound, typeOf closure (insertStage x within) = typeOf closure z := by
  let pick : HF → HF := fun m => (exists_typeRepresentative_le loc enough m).choose
  have pick_spec : ∀ m : HF, (pick m).1 ∈ stage bound ∧ typeOf closure (pick m) = typeOf closure m :=
    fun m => (exists_typeRepresentative_le loc enough m).choose_spec
  let part := ZFSet.sep (fun w => ∃ m : HF, m.1 ∈ z.1 ∧ (pick m).1 = w) (stage bound)
  have within : part ⊆ stage bound := fun w found => (ZFSet.mem_sep.mp found).1
  refine ⟨part, within, loc.typeOf_eq (memberTypes_eq_of_match ?_ ?_)⟩
  · intro m' inside'
    rcases ZFSet.mem_insert_iff.mp inside' with same | found
    · exact ⟨x, inside, congrArg (typeOf closure) (Subtype.ext same.symm)⟩
    · obtain ⟨-, m, member, same⟩ := ZFSet.mem_sep.mp found
      refine ⟨m, member, ?_⟩
      rw [← (pick_spec m).2]
      exact congrArg (typeOf closure) (Subtype.ext same)
  · intro m member
    exact ⟨pick m, ZFSet.mem_insert_iff.mpr (Or.inr (ZFSet.mem_sep.mpr ⟨(pick_spec m).1, m, member, rfl⟩)),
      (pick_spec m).2⟩

theorem sat_iff_of_typeOf_eq {φ : Formula 0} (inside : φ ∈ closure) {x y : HF}
    (same : typeOf closure x = typeOf closure y) : HFSets.sat Env.closed φ x ↔ HFSets.sat Env.closed φ y := by
  have := congrArg (φ ∈ ·) same
  simp only [mem_typeOf, eq_iff_iff] at this
  exact ⟨fun holds => (this.mp ⟨inside, holds⟩).2, fun holds => (this.mpr ⟨inside, holds⟩).2⟩

/-- **Some set containing `x` has a formula of a local closure exactly when `x` added to some subset of `V_(2^n)` has
it.** -/
theorem sometimeBefore_iff_stage (loc : IsLocal closure) {bound : ℕ} (enough : typeBound closure ≤ bound)
    {φ : Formula 0} (inside : φ ∈ closure) (label : StepLabel) (x : HF) : HFSets.sat Env.closed (.sometimeBefore label φ) x ↔
      memberLabel label ∧ ∃ part, ∃ within : part ⊆ stage bound,
        HFSets.sat Env.closed φ (insertStage x within) := by
  constructor
  · rintro ⟨z, step, holds⟩
    obtain ⟨part, within, same⟩ := exists_container_in_stage loc enough step.2
    exact ⟨step.1, part, within, (sat_iff_of_typeOf_eq inside same).mpr holds⟩
  · rintro ⟨labelled, part, within, holds⟩
    exact ⟨insertStage x within, ⟨labelled, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩, holds⟩

/-- **Every set containing `x` has a formula of a local closure exactly when `x` added to every subset of `V_(2^n)`
has it.** -/
theorem alwaysBefore_iff_stage (loc : IsLocal closure) {bound : ℕ} (enough : typeBound closure ≤ bound)
    {φ : Formula 0} (inside : φ ∈ closure) (label : StepLabel) (x : HF) : HFSets.sat Env.closed (.alwaysBefore label φ) x ↔
      (memberLabel label → ∀ part, ∀ within : part ⊆ stage bound,
        HFSets.sat Env.closed φ (insertStage x within)) := by
  constructor
  · intro every labelled part within
    exact every (insertStage x within) ⟨labelled, ZFSet.mem_insert_iff.mpr (Or.inl rfl)⟩
  · intro every z step
    obtain ⟨part, within, same⟩ := exists_container_in_stage loc enough step.2
    exact (sat_iff_of_typeOf_eq inside same).mp (every step.1 part within)

/-- **Some set has a formula of a local closure exactly when some set of `V_(2^n)` has it.** -/
theorem someOf_iff_stage (loc : IsLocal closure) {bound : ℕ} (enough : typeBound closure ≤ bound)
    {φ : Formula 0} (inside : φ ∈ closure) (x : HF) :
    HFSets.sat Env.closed (.someOf (.base "Set") φ) x ↔
      ∃ y : HF, y.1 ∈ stage bound ∧ HFSets.sat Env.closed φ y := by
  constructor
  · rintro ⟨witness, -, holds⟩
    obtain ⟨y, found, same⟩ := exists_typeRepresentative_le loc enough witness
    exact ⟨y, found, (sat_iff_of_typeOf_eq inside same).mpr holds⟩
  · rintro ⟨y, -, holds⟩
    exact ⟨y, rfl, holds⟩

/-- **Every set has a formula of a local closure exactly when every set of `V_(2^n)` has it.** -/
theorem everyOf_iff_stage (loc : IsLocal closure) {bound : ℕ} (enough : typeBound closure ≤ bound)
    {φ : Formula 0} (inside : φ ∈ closure) (x : HF) :
    HFSets.sat Env.closed (.everyOf (.base "Set") φ) x ↔
      ∀ y : HF, y.1 ∈ stage bound → HFSets.sat Env.closed φ y := by
  constructor
  · intro every y _
    exact every y rfl
  · intro every witness _
    obtain ⟨y, found, same⟩ := exists_typeRepresentative_le loc enough witness
    exact (sat_iff_of_typeOf_eq inside same).mp (every y found)

end Types

end

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
