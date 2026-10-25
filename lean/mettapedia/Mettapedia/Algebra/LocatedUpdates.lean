import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Finset.Basic

/-!
# Located updates: overwriting, accumulating, and when two updates commute

A change to a store is a family of local updates, one per location.  The local
updates at one location form a monoid acting on that location's value, and a
located update acts location by location (`act`).  Two families of local monoids
cover the stores of a space:

* **overwriting** (`Overwrite β`): keep the value, or replace it.  Membership in a
  set, the value under a dict key and a cell are overwritten.  Every overwrite is
  idempotent (`Overwrite.mul_self`), and two overwrites commute exactly when one of
  them keeps the value or both write the same value (`Overwrite.commute_iff`);
* **accumulating**: a commutative monoid acting on the value, such as counts of a
  bag (the Z-sets of `Mettapedia.Languages.MeTTa.SpaceDeltas`) or a commutative
  merge of values.  Any two accumulations commute.

## Commutation is local

* **Commutation is decided location by location** (`commute_iff_pointwise`).
* **Parallelism by disjointness** (`commute_of_disjoint`): updates changing
  disjoint sets of locations commute.
* **Parallelism by commutativity** (`commute_of_commutative`): updates of
  accumulating stores commute whatever they change.  Disjointness is sufficient and
  not necessary (`Controls.increments_overlap_and_commute`).

## Sets

An edit of a set removes the members of one finite set and adds the members of
another (`edit`), adds winning.  Edits compose by a closed formula
(`edit_mul_edit`), and two edits commute exactly when neither adds what the other
removes (`edit_commute_iff`).

An executable step of MM2 in the MORK kernel writes its additions while its
matches are enumerated and subtracts its removals afterwards, so removals win
(`removeAfterAdd`).  Applying the same additions and removals in the authored
order "remove, then add" lets additions win (`addAfterRemove`).  The two agree
exactly when nothing is both added and removed (`removeAfterAdd_eq_addAfterRemove_iff`).
That is the general form of the difference between the kernel and the authored
support profile recorded in
`Mettapedia.Languages.ProcessCalculi.MORK.MM2MainlineProviders`.

## Dicts

Storing a value under a key and deleting a key are overwrites at that key
(`put`, `delete`).  Two stores commute exactly when they name different keys or
store the same value (`put_commute_iff`): a last-writer-wins dict is not order
independent.

## Snapshot transactions

A transaction reads part of a snapshot and computes an update from it
(`Transaction`); committing applies that update to the state it was computed
from.  **If neither of two transactions writes what the other reads and their
updates commute, both serial orders equal the one wave that applies both updates,
computed from the same snapshot** (`serial_eq_wave`).  This is the
read/write condition of Bernstein with commutation in place of disjoint writes.
The disjoint-write diamond of
`Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions`
is its special case of disjoint supports; two counters incrementing one location
are admitted here and refused there.  Two consumers of one token read what the
other writes, and the two serial orders end differently
(`Controls.consumers_disagree`).

For guarded proposals with answers over located bags, the wave theorem with both
tests, read and write sets and additions as deltas, is
`Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.Compatibility`
(with `PatternFootprints.Deltas`).  What this module adds is the overwriting
stores, sets with removal, dicts and cells, whose commutation is not a matter of
additions, and the statement that every located store commutes by the same local
test.

A whole wave of pairwise commuting updates may be applied in any order:
that is `Mettapedia.Algebra.ActionFold.foldl_op_smul_perm` for the action
here, and two adjacent updates swap exactly when they commute
(`Mettapedia.Algebra.OrderedProductCommutation.prod_pair_eq_iff_commute`).

What this module does not say: it fixes no representation, scheduler or
validation protocol, and a commuting pair of updates says nothing about the
chronology an observer of intermediate states sees.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.LocatedUpdates

universe u v w

/-! ## Overwriting one value -/

/-- A local update of one value: keep it, or replace it. -/
inductive Overwrite (β : Type u) where
  | keep
  | set (value : β)
  deriving DecidableEq, Repr

namespace Overwrite

variable {β : Type u}

/-- `u * v` performs `v`, then `u`: the later write wins.  This is the order of a
left action, `(u * v) • b = u • (v • b)`. -/
instance : Monoid (Overwrite β) where
  mul u v := match u with
    | keep => v
    | set b => set b
  one := keep
  mul_assoc u _ _ := by cases u <;> rfl
  one_mul _ := rfl
  mul_one u := by cases u <;> rfl

@[simp] theorem one_eq_keep : (1 : Overwrite β) = keep := rfl

@[simp] theorem keep_mul (v : Overwrite β) : keep * v = v := rfl

@[simp] theorem set_mul (b : β) (v : Overwrite β) : set b * v = set b := rfl

/-- The value after an update. -/
instance : MulAction (Overwrite β) β where
  smul u b := match u with
    | keep => b
    | set a => a
  one_smul _ := rfl
  mul_smul u _ _ := by cases u <;> rfl

@[simp] theorem keep_smul (b : β) : (keep : Overwrite β) • b = b := rfl

@[simp] theorem set_smul (a b : β) : (set a : Overwrite β) • b = a := rfl

/-- **Every overwrite is idempotent**: writing a value twice is writing it once. -/
theorem mul_self (u : Overwrite β) : u * u = u := by cases u <;> rfl

/-- **Two overwrites commute exactly when one keeps the value or both write the
same value.** -/
theorem commute_iff (u v : Overwrite β) : Commute u v ↔ u = keep ∨ v = keep ∨ u = v := by
  cases u with
  | keep => exact iff_of_true (Commute.one_left v) (Or.inl rfl)
  | set a =>
      cases v with
      | keep => exact iff_of_true (Commute.one_right _) (Or.inr (Or.inl rfl))
      | set b =>
          change set a = set b ↔ _
          constructor
          · intro same
            exact Or.inr (Or.inr same)
          · rintro (impossible | impossible | same)
            · cases impossible
            · cases impossible
            · exact same

/-- Two different writes of one value do not commute. -/
theorem not_commute_set {a b : β} (different : a ≠ b) : ¬ Commute (set a) (set b) := by
  rw [commute_iff]
  rintro (impossible | impossible | same)
  · cases impossible
  · cases impossible
  · exact different (by cases same; rfl)

end Overwrite

/-! ## Located updates -/

section Located

variable {L : Type u} {M : L → Type v} [∀ x, Monoid (M x)]

/-- The locations a located update changes: where it is not the identity. -/
def support (update : ∀ x, M x) : Set L := {x | update x ≠ 1}

theorem mem_support {update : ∀ x, M x} {x : L} : x ∈ support update ↔ update x ≠ 1 :=
  Iff.rfl

theorem eq_one_of_not_mem_support {update : ∀ x, M x} {x : L} (outside : x ∉ support update) :
    update x = 1 := by
  by_contra changed
  exact outside changed

/-- **Commutation is decided location by location.** -/
theorem commute_iff_pointwise {first second : ∀ x, M x} :
    Commute first second ↔ ∀ x, Commute (first x) (second x) :=
  Pi.commute_iff

/-- **Parallelism by disjointness**: updates changing disjoint locations commute. -/
theorem commute_of_disjoint {first second : ∀ x, M x}
    (disjoint : Disjoint (support first) (support second)) : Commute first second := by
  rw [commute_iff_pointwise]
  intro x
  by_cases firstKeeps : first x = 1
  · rw [firstKeeps]
    exact Commute.one_left _
  · have secondKeeps : second x = 1 := by
      by_contra secondChanges
      exact Set.disjoint_left.mp disjoint firstKeeps secondChanges
    rw [secondKeeps]
    exact Commute.one_right _

/-- **Parallelism by commutativity**: when every local monoid is commutative,
every two located updates commute, whatever they change. -/
theorem commute_of_commutative (commutative : ∀ x (a b : M x), Commute a b)
    (first second : ∀ x, M x) : Commute first second :=
  commute_iff_pointwise.mpr fun x => commutative x (first x) (second x)

variable {β : L → Type w} [∀ x, MulAction (M x) (β x)]

/-- Apply a located update to a located state, location by location. -/
def act (update : ∀ x, M x) (state : ∀ x, β x) : ∀ x, β x :=
  fun x => update x • state x

theorem act_apply (update : ∀ x, M x) (state : ∀ x, β x) (x : L) :
    act update state x = update x • state x :=
  rfl

theorem act_one (state : ∀ x, β x) : act (1 : ∀ x, M x) state = state :=
  funext fun x => one_smul (M x) (state x)

/-- Composite updates act in sequence: `act (u * v)` performs `v`, then `u`. -/
theorem act_mul (first second : ∀ x, M x) (state : ∀ x, β x) :
    act (first * second) state = act first (act second state) :=
  funext fun x => mul_smul (first x) (second x) (state x)

/-- **Frame**: an update leaves every location outside its support unchanged. -/
theorem act_of_not_mem_support {update : ∀ x, M x} {x : L} (outside : x ∉ support update)
    (state : ∀ x, β x) : act update state x = state x := by
  rw [act_apply, eq_one_of_not_mem_support outside, one_smul]

/-- Commuting updates reach one state in either order. -/
theorem act_comm_of_commute {first second : ∀ x, M x} (commute : Commute first second)
    (state : ∀ x, β x) : act first (act second state) = act second (act first state) := by
  rw [← act_mul, ← act_mul, commute.eq]

end Located

/-! ## Sets: adding and removing -/

section Sets

variable {α : Type u} [DecidableEq α]

open Overwrite

/-- The update of a membership function that removes `removes` and adds `adds`;
an atom in both is added. -/
def edit (removes adds : Finset α) : α → Overwrite Bool := fun x =>
  if x ∈ adds then set true else if x ∈ removes then set false else keep

/-- Membership after an edit. -/
theorem act_edit (removes adds : Finset α) (members : α → Bool) (x : α) :
    act (edit removes adds) members x =
      if x ∈ adds then true else if x ∈ removes then false else members x := by
  unfold act edit
  split_ifs <;> rfl

/-- Adding a finite set. -/
def addAll (adds : Finset α) : α → Overwrite Bool := edit ∅ adds

/-- Removing a finite set. -/
def removeAll (removes : Finset α) : α → Overwrite Bool := edit removes ∅

/-- **Edits compose by a closed formula.**  Editing by `(removes₁, adds₁)` and then
by `(removes₂, adds₂)` is one edit: everything removed by either, and what the
second adds together with what the first adds and the second does not remove. -/
theorem edit_mul_edit (removes₁ adds₁ removes₂ adds₂ : Finset α) :
    edit removes₂ adds₂ * edit removes₁ adds₁ =
      edit (removes₁ ∪ removes₂) (adds₁ \ removes₂ ∪ adds₂) := by
  funext x
  change edit removes₂ adds₂ x * edit removes₁ adds₁ x = _
  unfold edit
  by_cases a₂ : x ∈ adds₂ <;> by_cases r₂ : x ∈ removes₂ <;>
    by_cases a₁ : x ∈ adds₁ <;> by_cases r₁ : x ∈ removes₁ <;>
    simp [a₂, r₂, a₁, r₁]

/-- **Two edits commute exactly when neither adds what the other removes**, among
the atoms the other does not also add. -/
theorem edit_commute_iff (removes₁ adds₁ removes₂ adds₂ : Finset α) :
    Commute (edit removes₁ adds₁) (edit removes₂ adds₂) ↔
      (∀ x, x ∈ adds₁ → x ∈ removes₂ → x ∈ adds₂) ∧
        (∀ x, x ∈ adds₂ → x ∈ removes₁ → x ∈ adds₁) := by
  rw [commute_iff_pointwise]
  constructor
  · intro commute
    refine ⟨fun x a₁ r₂ => ?_, fun x a₂ r₁ => ?_⟩
    · by_contra a₂
      have local_ := (Overwrite.commute_iff _ _).mp (commute x)
      simp [edit, a₁, r₂, a₂] at local_
    · by_contra a₁
      have local_ := (Overwrite.commute_iff _ _).mp (commute x)
      simp [edit, a₁, r₁, a₂] at local_
  · rintro ⟨first, second⟩ x
    rw [Overwrite.commute_iff]
    unfold edit
    by_cases a₁ : x ∈ adds₁ <;> by_cases a₂ : x ∈ adds₂ <;>
      by_cases r₁ : x ∈ removes₁ <;> by_cases r₂ : x ∈ removes₂ <;>
      simp_all

/-- Additions commute with additions. -/
theorem addAll_commute (adds₁ adds₂ : Finset α) : Commute (addAll adds₁) (addAll adds₂) :=
  (edit_commute_iff _ _ _ _).mpr ⟨fun _ _ r => absurd r (Finset.notMem_empty _),
    fun _ _ r => absurd r (Finset.notMem_empty _)⟩

/-- Removals commute with removals. -/
theorem removeAll_commute (removes₁ removes₂ : Finset α) :
    Commute (removeAll removes₁) (removeAll removes₂) :=
  (edit_commute_iff _ _ _ _).mpr ⟨fun _ a => absurd a (Finset.notMem_empty _),
    fun _ a => absurd a (Finset.notMem_empty _)⟩

/-- **The kernel's order**: additions while matching, removals afterwards.
Removals win. -/
def removeAfterAdd (adds removes : Finset α) : α → Overwrite Bool :=
  removeAll removes * addAll adds

/-- **The authored order "remove, then add"**.  Additions win. -/
def addAfterRemove (adds removes : Finset α) : α → Overwrite Bool :=
  addAll adds * removeAll removes

theorem removeAfterAdd_eq (adds removes : Finset α) :
    removeAfterAdd adds removes = edit removes (adds \ removes) := by
  rw [removeAfterAdd, removeAll, addAll, edit_mul_edit]
  congr 1
  · simp
  · ext x; simp

theorem addAfterRemove_eq (adds removes : Finset α) :
    addAfterRemove adds removes = edit removes adds := by
  rw [addAfterRemove, removeAll, addAll, edit_mul_edit]
  congr 1
  · simp
  · ext x; simp

/-- Membership after the kernel's order: `(s ∪ adds) \ removes`. -/
theorem act_removeAfterAdd (adds removes : Finset α) (members : α → Bool) (x : α) :
    act (removeAfterAdd adds removes) members x = ((members x || decide (x ∈ adds)) &&
      !decide (x ∈ removes)) := by
  rw [removeAfterAdd_eq, act_edit]
  by_cases a : x ∈ adds <;> by_cases r : x ∈ removes <;> simp [a, r]

/-- **The two orders agree exactly when nothing is both added and removed.** -/
theorem removeAfterAdd_eq_addAfterRemove_iff (adds removes : Finset α) :
    removeAfterAdd adds removes = addAfterRemove adds removes ↔ Disjoint adds removes := by
  rw [removeAfterAdd_eq, addAfterRemove_eq, Finset.disjoint_left]
  constructor
  · intro same x a r
    have atX := congrFun same x
    simp [edit, a, r] at atX
  · intro apart
    funext x
    unfold edit
    by_cases a : x ∈ adds
    · simp [a, apart a]
    · simp [a]

end Sets

/-! ## Dicts -/

section Dicts

variable {K : Type u} [DecidableEq K] {V : Type v}

open Overwrite

/-- Store `value` under `key`, whatever was there. -/
def put (key : K) (value : V) : K → Overwrite (Option V) :=
  Pi.mulSingle key (set (some value))

/-- Delete `key`. -/
def delete (key : K) : K → Overwrite (Option V) :=
  Pi.mulSingle key (set none)

theorem act_put (key : K) (value : V) (dict : K → Option V) :
    act (put key value) dict = Function.update dict key (some value) := by
  funext other
  by_cases same : other = key
  · subst same
    simp [act, put]
  · simp [act, put, same]

/-- **Two stores commute exactly when they name different keys or store the same
value.** -/
theorem put_commute_iff (key₁ key₂ : K) (value₁ value₂ : V) :
    Commute (put key₁ value₁) (put key₂ value₂) ↔ key₁ ≠ key₂ ∨ value₁ = value₂ := by
  constructor
  · intro commute
    by_cases same : key₁ = key₂
    · subst same
      right
      have atKey := (commute_iff_pointwise.mp commute) key₁
      simp only [put, Pi.mulSingle_eq_same] at atKey
      rcases (Overwrite.commute_iff _ _).mp atKey with impossible | impossible | equal
      · cases impossible
      · cases impossible
      · cases equal; rfl
    · exact Or.inl same
  · rintro (different | rfl)
    · exact Pi.mulSingle_commute different _ _
    · by_cases same : key₁ = key₂
      · subst same; exact Commute.refl _
      · exact Pi.mulSingle_commute same _ _

end Dicts

/-! ## Snapshot transactions -/

section Transactions

variable {L : Type u} {M : L → Type v} [∀ x, Monoid (M x)]
variable {β : L → Type w} [∀ x, MulAction (M x) (β x)]

variable (M β) in
/-- A transaction computes its update from a snapshot and reads only `reads`. -/
structure Transaction where
  reads : Set L
  update : (∀ x, β x) → ∀ x, M x
  reads_only : ∀ first second : ∀ x, β x, (∀ x ∈ reads, first x = second x) →
    update first = update second

namespace Transaction

/-- Commit: apply the update computed from the state it is applied to. -/
def commit (transaction : Transaction M β) (state : ∀ x, β x) : ∀ x, β x :=
  act (transaction.update state) state

/-- The locations a transaction writes from a state. -/
def writes (transaction : Transaction M β) (state : ∀ x, β x) : Set L :=
  support (transaction.update state)

/-- A transaction computes the same update after another transaction that writes
nothing it reads. -/
theorem update_commit_of_disjoint (first second : Transaction M β) (state : ∀ x, β x)
    (apart : Disjoint (first.writes state) second.reads) :
    second.update (first.commit state) = second.update state := by
  apply second.reads_only
  intro x read
  exact act_of_not_mem_support (fun written => Set.disjoint_left.mp apart written read) state

/-- **Serial equals one wave.**  If neither transaction writes what the other
reads and their updates, computed from one snapshot, commute, then both serial
orders equal applying both updates to that snapshot. -/
theorem serial_eq_wave (first second : Transaction M β) (state : ∀ x, β x)
    (firstApart : Disjoint (first.writes state) second.reads)
    (secondApart : Disjoint (second.writes state) first.reads)
    (commute : Commute (first.update state) (second.update state)) :
    second.commit (first.commit state) = act (second.update state * first.update state) state ∧
      first.commit (second.commit state) = act (second.update state * first.update state) state := by
  constructor
  · rw [commit, update_commit_of_disjoint first second state firstApart, commit, act_mul]
  · rw [commit, update_commit_of_disjoint second first state secondApart, commit, ← act_mul,
      commute.eq]

/-- The two serial orders meet. -/
theorem serial_comm (first second : Transaction M β) (state : ∀ x, β x)
    (firstApart : Disjoint (first.writes state) second.reads)
    (secondApart : Disjoint (second.writes state) first.reads)
    (commute : Commute (first.update state) (second.update state)) :
    second.commit (first.commit state) = first.commit (second.commit state) := by
  obtain ⟨forward, backward⟩ := serial_eq_wave first second state firstApart secondApart commute
  rw [forward, backward]

end Transaction

end Transactions

/-! ## Controls -/

namespace Controls

open Overwrite

/-- Add `amount` to the count at `x`: an accumulating located update. -/
def increment (x : Bool) (amount : ℕ) : Bool → Multiplicative ℕ :=
  Pi.mulSingle x (Multiplicative.ofAdd amount)

/-- **Disjointness is sufficient, not necessary**: two different increments of
one location both change it and still commute, because counts accumulate. -/
theorem increments_overlap_and_commute :
    ¬ Disjoint (support (increment true 1)) (support (increment true 2)) ∧
      Commute (increment true 1) (increment true 2) ∧ increment true 1 ≠ increment true 2 := by
  refine ⟨fun disjoint => ?_, commute_of_commutative (fun _ a b => Commute.all a b) _ _,
    fun same => ?_⟩
  · have first : true ∈ support (increment true 1) := by simp [support, increment]
    have second : true ∈ support (increment true 2) := by simp [support, increment]
    exact Set.disjoint_left.mp disjoint first second
  · have atTrue := congrFun same true
    simp [increment] at atTrue

/-- Adding an atom and removing it do not commute. -/
theorem add_remove_not_commute :
    ¬ Commute (addAll ({0} : Finset ℕ)) (removeAll ({0} : Finset ℕ)) := by
  rw [addAll, removeAll, edit_commute_iff]
  rintro ⟨first, -⟩
  simpa using first 0 (by simp) (by simp)

/-- The kernel's order and the authored order differ on an atom both added and
removed. -/
theorem kernel_and_authored_orders_differ :
    removeAfterAdd ({0} : Finset ℕ) {0} ≠ addAfterRemove {0} {0} := by
  rw [Ne, removeAfterAdd_eq_addAfterRemove_iff]
  simp

/-- A last-writer-wins dict is order dependent. -/
theorem lastWriterWins_order_dependent :
    ¬ Commute (put (K := Unit) () 1) (put () 2) := by
  rw [put_commute_iff]
  simp

/-- Two consumers of one token: each reads the token and, if present, removes it
and records itself as the winner. -/
def consumer (winner : ℕ) : Transaction (fun _ : ℕ => Overwrite Bool) (fun _ : ℕ => Bool) where
  reads := {0}
  update state := if state 0 then edit {0} {winner} else 1
  reads_only first second agree := by
    have same : first 0 = second 0 := agree 0 rfl
    simp only [same]

/-- The store holding only the token, at location `0`. -/
def tokenOnly : ℕ → Bool := fun x => decide (x = 0)

/-- **Consumption is arbitrated by order**: the two serial orders of two consumers
of one token end differently. -/
theorem consumers_disagree :
    (consumer 2).commit ((consumer 1).commit tokenOnly) ≠
      (consumer 1).commit ((consumer 2).commit tokenOnly) := by
  intro same
  have atOne := congrFun same 1
  simp [Transaction.commit, consumer, tokenOnly, act_edit, act_one] at atOne

/-- The two consumers violate the read/write condition: each writes the token the
other reads. -/
theorem consumers_conflict :
    ¬ Disjoint ((consumer 1).writes tokenOnly) (consumer 2).reads := by
  intro apart
  have written : (0 : ℕ) ∈ (consumer 1).writes tokenOnly := by
    simp [Transaction.writes, consumer, tokenOnly, support, edit]
  exact Set.disjoint_left.mp apart written rfl

end Controls

end Mettapedia.Algebra.LocatedUpdates
