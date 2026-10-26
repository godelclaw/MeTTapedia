import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Filter

/-!
# The quantifiers of a transform: `each`, `every` and `unique`

A transform finds the match rows of its sources in a store and commits some of them. Each row has
what its commit takes from the store and what it writes back. The quantifier says which rows one firing
commits:

* `each` commits one row; the different rows give different outcomes (`EachStep`);
* `every` commits all rows at once, as one amalgamated firing (`EveryStep`);
* `unique` commits the row when there is exactly one (`UniqueEnabled`).

## Modalities live over `each`; `every` is an aggregation

The modal operators of a step relation are `Dia` (some successor satisfies the formula) and `Box` (every
successor does). Over `each`, `Box` and `Dia` quantify over rows: a formula holds after every outcome, or
after some outcome. `every` is a different relation, not the box of `each`:

* it is functional (`everyStep_functional`), so its diamond and its box coincide where it is enabled
  (`dia_every_iff_box_every`);
* a formula can hold after every `each` outcome and fail after `every` (`every_not_box_each`), and
  hold after `every` while no `each` outcome satisfies it (`every_not_dia_each`).

What `every` does is fold the rows into one update. Its take and its write are sums over the rows, so
they are monoid homomorphisms out of the bag of rows (`totalTake_add`, `totalWrite_add`): rows divided
among workers combine by addition. Committed in sequence, in any order, the rows reach the amalgamated
state (`foldl_fire_eq_every`): the firing is the product of the per-row state transformers.

The universal reading of `every` is its postcondition. After `every`, every row's writes are present
(`every_post`); after `each`, some row's writes are (`each_post`). So `each` supplies one row as its
witness and `every` supplies all of them.

## When `each` and `every` agree

With a shared activation taken once (the kernel of the firing) and rows that only emit answers, the
answers of the `each` outcomes add up to the answers of `every` (`each_answers_sum_eq_every`), and all
outcomes leave the same store (`each_store_eq_every_of_no_writes`). That is the case of evaluation. Once
rows write the store, the outcomes differ (`Controls.each_store_ne_every`). `every` over rows whose takes
overlap is not enabled while each row alone is (`Controls.every_disabled_by_conflict`).

## `unique` is not monotone

Over a read source, `each` stays enabled when the store grows (`eachEnabled_mono`). `unique` does not: a
second match disables it (`Controls.unique_not_monotone`). It is `each` together with the absence of a
second row (`uniqueEnabled_iff`), so it reads the whole match set, as an absence condition does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TransformQuantifiers

universe u v w

/-! ## Rows and their commits -/

/-- What committing a row takes from the store and what it writes. -/
structure Footprints (ρ : Type v) (α : Type u) where
  take : ρ → Multiset α
  write : ρ → Multiset α

variable {α : Type u} [DecidableEq α] {ρ : Type v} (F : Footprints ρ α)

namespace Footprints

/-- Commit one row: remove what it takes, add what it writes. -/
def fire (M : Multiset α) (r : ρ) : Multiset α := M - F.take r + F.write r

/-- **`each`**: one firing commits one enabled row. -/
def EachStep (rows : Multiset ρ) (M N : Multiset α) : Prop :=
  ∃ r ∈ rows, F.take r ≤ M ∧ N = F.fire M r

/-- What all the rows take together. -/
def totalTake (rows : Multiset ρ) : Multiset α := (rows.map F.take).sum

/-- What all the rows write together. -/
def totalWrite (rows : Multiset ρ) : Multiset α := (rows.map F.write).sum

/-- **`every`**: one firing commits all rows, amalgamated. -/
def EveryStep (rows : Multiset ρ) (M N : Multiset α) : Prop :=
  F.totalTake rows ≤ M ∧ N = M - F.totalTake rows + F.totalWrite rows

end Footprints

/-! ## Modalities -/

section Modalities

variable {β : Type w}

/-- Some successor satisfies the formula. -/
def Dia (step : β → β → Prop) (φ : β → Prop) (s : β) : Prop := ∃ t, step s t ∧ φ t

/-- Every successor satisfies the formula. -/
def Box (step : β → β → Prop) (φ : β → Prop) (s : β) : Prop := ∀ t, step s t → φ t

theorem box_iff_not_dia_not (step : β → β → Prop) (φ : β → Prop) (s : β) :
    Box step φ s ↔ ¬ Dia step (fun t => ¬ φ t) s := by
  simp [Box, Dia]

end Modalities

namespace Footprints

/-- **Over `each`, the diamond quantifies existentially over the enabled rows.** -/
theorem dia_each_iff (rows : Multiset ρ) (φ : Multiset α → Prop) (M : Multiset α) :
    Dia (F.EachStep rows) φ M ↔ ∃ r ∈ rows, F.take r ≤ M ∧ φ (F.fire M r) := by
  constructor
  · rintro ⟨N, ⟨r, member, enabled, rfl⟩, holds⟩
    exact ⟨r, member, enabled, holds⟩
  · rintro ⟨r, member, enabled, holds⟩
    exact ⟨_, ⟨r, member, enabled, rfl⟩, holds⟩

/-- **Over `each`, the box quantifies universally over the enabled rows.** -/
theorem box_each_iff (rows : Multiset ρ) (φ : Multiset α → Prop) (M : Multiset α) :
    Box (F.EachStep rows) φ M ↔ ∀ r ∈ rows, F.take r ≤ M → φ (F.fire M r) := by
  constructor
  · intro holds r member enabled
    exact holds _ ⟨r, member, enabled, rfl⟩
  · rintro holds N ⟨r, member, enabled, rfl⟩
    exact holds r member enabled

/-- **`every` is functional**: one firing has at most one outcome. -/
theorem everyStep_functional {rows : Multiset ρ} {M N₁ N₂ : Multiset α}
    (first : F.EveryStep rows M N₁) (second : F.EveryStep rows M N₂) : N₁ = N₂ :=
  first.2.trans second.2.symm

/-- **Where `every` is enabled, its diamond and its box coincide.** -/
theorem dia_every_iff_box_every {rows : Multiset ρ} {M : Multiset α}
    (enabled : F.totalTake rows ≤ M) (φ : Multiset α → Prop) :
    Dia (F.EveryStep rows) φ M ↔ Box (F.EveryStep rows) φ M := by
  constructor
  · rintro ⟨N, step, holds⟩ N' step'
    rw [← F.everyStep_functional step step']
    exact holds
  · intro holds
    exact ⟨_, ⟨enabled, rfl⟩, holds _ ⟨enabled, rfl⟩⟩

/-! ## `every` is a fold of the rows -/

omit [DecidableEq α] in
/-- **The take of `every` is a monoid homomorphism out of the bag of rows.** -/
theorem totalTake_add (rows₁ rows₂ : Multiset ρ) :
    F.totalTake (rows₁ + rows₂) = F.totalTake rows₁ + F.totalTake rows₂ := by
  simp [totalTake, Multiset.map_add, Multiset.sum_add]

omit [DecidableEq α] in
/-- **The write of `every` is a monoid homomorphism out of the bag of rows.** -/
theorem totalWrite_add (rows₁ rows₂ : Multiset ρ) :
    F.totalWrite (rows₁ + rows₂) = F.totalWrite rows₁ + F.totalWrite rows₂ := by
  simp [totalWrite, Multiset.map_add, Multiset.sum_add]

omit [DecidableEq α] in
@[simp] theorem totalTake_cons (r : ρ) (rows : Multiset ρ) :
    F.totalTake (r ::ₘ rows) = F.take r + F.totalTake rows := by
  simp [totalTake]

omit [DecidableEq α] in
@[simp] theorem totalWrite_cons (r : ρ) (rows : Multiset ρ) :
    F.totalWrite (r ::ₘ rows) = F.write r + F.totalWrite rows := by
  simp [totalWrite]

/-- **Committed one after another, in any order, the rows reach the amalgamated state.** The firing
of `every` is the product of the per-row state transformers. -/
theorem foldl_fire_eq_every : ∀ (rows : List ρ) (M : Multiset α),
    F.totalTake (rows : Multiset ρ) ≤ M →
      rows.foldl F.fire M = M - F.totalTake (rows : Multiset ρ) + F.totalWrite (rows : Multiset ρ)
  | [], M, _ => by simp [totalTake, totalWrite]
  | r :: rows, M, enabled => by
      have split : F.take r + F.totalTake (rows : Multiset ρ) ≤ M := by
        simpa [← Multiset.cons_coe] using enabled
      have restFits : F.totalTake (rows : Multiset ρ) ≤ M - F.take r :=
        le_tsub_of_add_le_left split
      have restFits' : F.totalTake (rows : Multiset ρ) ≤ F.fire M r :=
        le_trans restFits (Multiset.le_add_right _ _)
      rw [List.foldl_cons, foldl_fire_eq_every rows (F.fire M r) restFits']
      simp only [fire, ← Multiset.cons_coe, totalTake_cons, totalWrite_cons]
      rw [← tsub_add_eq_add_tsub restFits, tsub_tsub, add_assoc]

/-! ## The postconditions: one witness or all of them -/

/-- **After `every`, every row's writes are present.** -/
theorem every_post {rows : Multiset ρ} {M N : Multiset α} (step : F.EveryStep rows M N) :
    ∀ r ∈ rows, F.write r ≤ N := by
  intro r member
  obtain ⟨-, rfl⟩ := step
  have inTotal : F.write r ≤ F.totalWrite rows := by
    obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem member
    rw [totalWrite_cons]
    exact Multiset.le_add_right _ _
  exact le_trans inTotal (Multiset.le_add_left _ _)

/-- **After `each`, some row's writes are present.** -/
theorem each_post {rows : Multiset ρ} {M N : Multiset α} (step : F.EachStep rows M N) :
    ∃ r ∈ rows, F.write r ≤ N := by
  obtain ⟨r, member, -, rfl⟩ := step
  exact ⟨r, member, Multiset.le_add_left _ _⟩

end Footprints

/-! ## A shared activation with answer-emitting rows -/

section Answers

variable {β : Type w}

/-- The outcomes of `each` when one activation `kernel` is taken per firing and every row writes
`write r` and answers `answer r`: one outcome per row, with its store and its answers. -/
def eachOutcomes (kernel : Multiset α) (write : ρ → Multiset α) (answer : ρ → Multiset β)
    (rows : Multiset ρ) (M : Multiset α) : Multiset (Multiset α × Multiset β) :=
  rows.map fun r => (M - kernel + write r, answer r)

/-- The outcome of `every` with the same activation, taken once: one store and all answers. -/
def everyOutcome (kernel : Multiset α) (write : ρ → Multiset α) (answer : ρ → Multiset β)
    (rows : Multiset ρ) (M : Multiset α) : Multiset α × Multiset β :=
  (M - kernel + (rows.map write).sum, (rows.map answer).sum)

/-- **The answers of the `each` outcomes add up to the answers of `every`.** -/
theorem each_answers_sum_eq_every (kernel : Multiset α) (write : ρ → Multiset α)
    (answer : ρ → Multiset β) (rows : Multiset ρ) (M : Multiset α) :
    ((eachOutcomes kernel write answer rows M).map Prod.snd).sum =
      (everyOutcome kernel write answer rows M).2 := by
  simp [eachOutcomes, everyOutcome, Multiset.map_map]

/-- **Rows that write nothing leave every `each` outcome in the store `every` reaches.** This is the
case of evaluation, whose rows only emit answers. -/
theorem each_store_eq_every_of_no_writes (kernel : Multiset α) (write : ρ → Multiset α)
    (answer : ρ → Multiset β) (rows : Multiset ρ) (M : Multiset α) (silent : ∀ r ∈ rows, write r = 0) :
    ∀ outcome ∈ eachOutcomes kernel write answer rows M,
      outcome.1 = (everyOutcome kernel write answer rows M).1 := by
  intro outcome member
  obtain ⟨r, inRows, rfl⟩ := Multiset.mem_map.mp member
  have total : (rows.map write).sum = 0 := by
    rw [Multiset.map_congr rfl silent]
    simp
  simp [everyOutcome, silent r inRows, total]

end Answers

/-! ## Read sources: `each` is monotone, `unique` is not -/

section ReadSource

variable (p : α → Prop) [DecidablePred p]

/-- The rows of a read source: the stored occurrences satisfying the pattern. -/
def readRows (M : Multiset α) : Multiset α := M.filter p

/-- `each` over a read source is enabled when some occurrence matches. -/
def EachEnabled (M : Multiset α) : Prop := readRows p M ≠ 0

/-- `unique` over a read source is enabled when exactly one occurrence matches. -/
def UniqueEnabled (M : Multiset α) : Prop := (readRows p M).card = 1

omit [DecidableEq α] in
/-- **`each` over a read source stays enabled when the store grows.** -/
theorem eachEnabled_mono {M M' : Multiset α} (grows : M ≤ M') (enabled : EachEnabled p M) :
    EachEnabled p M' := by
  intro empty
  apply enabled
  exact Multiset.le_zero.mp (empty ▸ Multiset.filter_le_filter p grows)

omit [DecidableEq α] in
/-- **`unique` is `each` together with the absence of a second row.** -/
theorem uniqueEnabled_iff (M : Multiset α) :
    UniqueEnabled p M ↔ EachEnabled p M ∧ (readRows p M).card ≤ 1 := by
  unfold UniqueEnabled EachEnabled
  rw [Ne, ← Multiset.card_eq_zero]
  omega

end ReadSource

/-! ## Controls -/

namespace Controls

/-- Atoms of the controls. -/
inductive Atom where
  | a | b | k | tok
  deriving DecidableEq, Repr

open Atom

/-- Two keep-only rows: one writes `a`, the other writes `b`. -/
def writers : Footprints Bool Atom where
  take := fun _ => 0
  write := fun r => if r then {a} else {b}

def bothRows : Multiset Bool := {true, false}

/-- Every `each` outcome holds exactly one write. -/
theorem each_box_one_write : Box (writers.EachStep bothRows) (fun N => N.card = 1) 0 := by
  rw [Footprints.box_each_iff]
  intro r member _
  cases r <;> simp [Footprints.fire, writers]

/-- `every` writes both. -/
theorem every_writes_both : writers.EveryStep bothRows 0 {a, b} := by
  refine ⟨by simp [Footprints.totalTake, writers, bothRows], ?_⟩
  simp [Footprints.totalTake, Footprints.totalWrite, writers, bothRows]

/-- **`every` is not the box of `each`**: every `each` outcome holds one write, the `every` outcome
holds two. -/
theorem every_not_box_each :
    ∃ φ : Multiset Atom → Prop, Box (writers.EachStep bothRows) φ 0 ∧
      ∃ N, writers.EveryStep bothRows 0 N ∧ ¬ φ N :=
  ⟨fun N => N.card = 1, each_box_one_write, {a, b}, every_writes_both, by decide⟩

/-- **`every` is not the diamond of `each`**: no `each` outcome holds both writes, the `every`
outcome does. -/
theorem every_not_dia_each :
    ∃ φ : Multiset Atom → Prop, ¬ Dia (writers.EachStep bothRows) φ 0 ∧
      Dia (writers.EveryStep bothRows) φ 0 := by
  refine ⟨fun N => a ∈ N ∧ b ∈ N, ?_, ⟨{a, b}, every_writes_both, by decide⟩⟩
  rw [Footprints.dia_each_iff]
  rintro ⟨r, -, -, holds⟩
  cases r <;> simp [Footprints.fire, writers] at holds

/-- **Once rows write the store, the `each` outcomes and the `every` outcome differ.** -/
theorem each_store_ne_every :
    ∃ outcome ∈ eachOutcomes ({k} : Multiset Atom) writers.write (fun r : Bool => ({r} : Multiset Bool))
        bothRows {k},
      outcome.1 ≠ (everyOutcome ({k} : Multiset Atom) writers.write
        (fun r : Bool => ({r} : Multiset Bool)) bothRows {k}).1 := by
  refine ⟨(({k} : Multiset Atom) - {k} + {a}, {true}), ?_, ?_⟩
  · simp [eachOutcomes, bothRows, writers]
  · simp [everyOutcome, bothRows, writers]

/-- Two rows that each take the one token. -/
def takers : Footprints Bool Atom where
  take := fun _ => {tok}
  write := fun r => if r then {a} else {b}

/-- **`every` over rows whose takes overlap is not enabled, while each row alone is.** -/
theorem every_disabled_by_conflict :
    (∀ r ∈ bothRows, takers.take r ≤ ({tok} : Multiset Atom)) ∧
      ¬ takers.totalTake bothRows ≤ ({tok} : Multiset Atom) := by
  refine ⟨fun r _ => by cases r <;> simp [takers], ?_⟩
  simp [Footprints.totalTake, takers, bothRows]
  decide

/-- A pattern matching `a`. -/
def isA (x : Atom) : Prop := x = a

instance : DecidablePred isA := fun x => inferInstanceAs (Decidable (x = a))

/-- **`unique` is not monotone**: one `a` enables it, a second `a` disables it, while `each` stays
enabled. -/
theorem unique_not_monotone :
    ({a} : Multiset Atom) ≤ {a, a} ∧ UniqueEnabled isA ({a} : Multiset Atom) ∧
      ¬ UniqueEnabled isA ({a, a} : Multiset Atom) ∧ EachEnabled isA ({a, a} : Multiset Atom) := by
  refine ⟨by decide, ?_, ?_, ?_⟩ <;> simp only [UniqueEnabled, EachEnabled, readRows, isA] <;> decide

end Controls

end Mettapedia.Languages.MeTTa.TransformQuantifiers
