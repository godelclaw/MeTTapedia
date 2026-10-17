import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Machines.OwnedPullDriver

/-!
# Validated commitment of writes computed from reads

Several owners compute writes from reads of one shared store. An owner runs
its transaction, a pure adaptive query whose answer is a list of writes,
against the snapshot it saw, and proposes the writes together with the
complete read certificate. The ledger commits a proposal only when every
recorded read still agrees with the current store; otherwise it refuses the
proposal and changes nothing.

An accepted proposal writes exactly what its transaction would write if it ran
on the current store (`commit_fresh`). A sequence of commitments is therefore
serializable: the final store is the result of running the accepted
transactions one after another, each on the store its predecessors left
(`commitAll_serial`). A proposal is refused exactly when one of its reads
changed (`commit_refused_iff`), so a write to a key the transaction did not read
keeps the proposal valid.

The ledger is a retained state whose committed write lists grow by prefix. The
owned host therefore delivers each accepted write list to an external world
exactly once, and the ledger's store is always its start under exactly its
accepted writes (`ledger_published_once`, `ledger_store`).

This is optimistic concurrency control with backward validation (Kung and
Robinson, ACM TODS 6(2), 1981). A refused owner may run its transaction again
on a fresh snapshot; replaying the refused writes would lose an update.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ValidatedCommit

open ReadOnlyQuery
open OwnedPullDriver (interpret)

universe u v

abbrev Writes (Key : Type u) (Value : Type v) := List (Key × Value)

/-- A pure adaptive query whose answer is the writes it wants to make. -/
abbrev Transaction (Key : Type u) (Value : Type v) := Program Key Value (Writes Key Value)

structure Proposal (Key : Type u) (Value : Type v) where
  reads : Reads Key Value
  writes : Writes Key Value

variable {Key : Type u} {Value : Type v}

/-- Run a transaction on the snapshot an owner sees. -/
def propose (snapshot : Key → Value) (transaction : Transaction Key Value) : Proposal Key Value :=
  ⟨(run snapshot transaction).reads, (run snapshot transaction).answer⟩

variable [DecidableEq Key]

def write (store : Key → Value) (writes : Writes Key Value) : Key → Value :=
  writes.foldl (fun current entry => Function.update current entry.1 entry.2) store

variable [DecidableEq Value]

/-- Commit a proposal when every recorded read agrees with the current store. -/
def commit (store : Key → Value) (proposal : Proposal Key Value) : Option (Key → Value) :=
  if checkReads store proposal.reads then some (write store proposal.writes) else none

/-- A proposal is always accepted on the snapshot it was computed from. -/
theorem commit_own_snapshot (store : Key → Value) (transaction : Transaction Key Value) :
    commit store (propose store transaction) = some (write store (run store transaction).answer) := by
  simp [commit, propose, (checkReads_iff _ _).mpr (run_agrees store transaction)]

/-- **An accepted proposal writes what the transaction writes now.** -/
theorem commit_fresh (snapshot current : Key → Value) (transaction : Transaction Key Value)
    (next : Key → Value) (accepted : commit current (propose snapshot transaction) = some next) :
    next = write current (run current transaction).answer := by
  unfold commit propose at accepted
  split at accepted
  · rename_i valid
    cases accepted
    rw [validated_answer snapshot current transaction valid]
  · contradiction

/-- **A proposal is refused exactly when one of its reads changed.** -/
theorem commit_refused_iff (snapshot current : Key → Value) (transaction : Transaction Key Value) :
    commit current (propose snapshot transaction) = none ↔ ¬ Agrees current (run snapshot transaction).reads := by
  rw [← checkReads_iff]
  unfold commit propose
  split <;> simp_all

/-- A submission: the snapshot an owner saw and its transaction. -/
abbrev Submission (Key : Type u) (Value : Type v) := (Key → Value) × Transaction Key Value

/-- Commit submissions in order. The result is the final store and the
accepted transactions in commit order. -/
def commitAll (store : Key → Value) : List (Submission Key Value) → (Key → Value) × List (Transaction Key Value)
  | [] => (store, [])
  | submission :: rest =>
      match commit store (propose submission.1 submission.2) with
      | some next => ((commitAll next rest).1, submission.2 :: (commitAll next rest).2)
      | none => commitAll store rest

/-- Run transactions one after another, each on the store its predecessors left. -/
def serial (store : Key → Value) : List (Transaction Key Value) → Key → Value
  | [] => store
  | transaction :: rest => serial (write store (run store transaction).answer) rest

/-- **Validated commitment is serializable.** -/
theorem commitAll_serial (store : Key → Value) (submissions : List (Submission Key Value)) :
    (commitAll store submissions).1 = serial store (commitAll store submissions).2 := by
  induction submissions generalizing store with
  | nil => rfl
  | cons submission rest ih =>
      cases committed : commit store (propose submission.1 submission.2) with
      | some next =>
          have fresh := commit_fresh submission.1 store submission.2 next committed
          simp only [commitAll, committed, serial, ← fresh]
          exact ih next
      | none =>
          simp only [commitAll, committed]
          exact ih store

omit [DecidableEq Value] in
/-- A batch cannot change a coordinate it never writes. -/
theorem write_untouched (store : Key → Value) (writes : Writes Key Value) (key : Key)
    (untouched : ∀ entry ∈ writes, entry.1 ≠ key) : write store writes key = store key := by
  induction writes generalizing store with
  | nil => rfl
  | cons entry rest ih =>
    change write (Function.update store entry.1 entry.2) rest key = store key
    rw [ih _ (fun other member => untouched other (by simp [member]))]
    exact Function.update_of_ne (untouched entry (by simp)).symm _ _

omit [DecidableEq Value] in
/-- Dependency validation survives any batch that leaves its read keys alone. -/
theorem write_preserves_reads (store : Key → Value) (writes : Writes Key Value)
    (reads : Reads Key Value) (valid : Agrees store reads)
    (disjoint : ∀ entry ∈ writes, ∀ read ∈ reads, entry.1 ≠ read.1) :
    Agrees (write store writes) reads := by
  intro read member
  rw [write_untouched store writes read.1 (fun entry present => disjoint entry present read member)]
  exact valid read member

omit [DecidableEq Value] in
/-- One update commutes with a batch touching only other coordinates. -/
theorem write_update_comm (store : Key → Value) (writes : Writes Key Value)
    (key : Key) (value : Value) (disjoint : ∀ entry ∈ writes, entry.1 ≠ key) :
    write (Function.update store key value) writes = Function.update (write store writes) key value := by
  induction writes generalizing store with
  | nil => rfl
  | cons entry rest ih =>
    change write (Function.update (Function.update store key value) entry.1 entry.2) rest = _
    rw [Function.update_comm (disjoint entry (by simp)).symm]
    exact ih _ (fun other member => disjoint other (by simp [member]))

omit [DecidableEq Value] in
/-- Disjoint concrete writes commute; no commuting-action premise is assumed. -/
theorem write_disjoint_comm (store : Key → Value) (first second : Writes Key Value)
    (disjoint : ∀ left ∈ first, ∀ right ∈ second, left.1 ≠ right.1) :
    write (write store first) second = write (write store second) first := by
  induction first generalizing store with
  | nil => rfl
  | cons entry rest ih =>
    change write (write (Function.update store entry.1 entry.2) rest) second = _
    rw [ih _ (fun left present => disjoint left (by simp [present]))]
    rw [write_update_comm store second entry.1 entry.2
      (fun right present => (disjoint entry (by simp) right present).symm)]
    rfl

/-- Independence checks actual read/write coordinates, including allocation
and negative reads. Read-only overlap is permitted. -/
structure Proposal.Independent (first second : Proposal Key Value) : Prop where
  writes : ∀ left ∈ first.writes, ∀ right ∈ second.writes, left.1 ≠ right.1
  firstReads : ∀ right ∈ second.writes, ∀ read ∈ first.reads, right.1 ≠ read.1
  secondReads : ∀ left ∈ first.writes, ∀ read ∈ second.reads, left.1 ≠ read.1

omit [DecidableEq Key] [DecidableEq Value] in
theorem Proposal.Independent.symm {first second : Proposal Key Value}
    (independent : first.Independent second) : second.Independent first :=
  ⟨fun right hr left hl => (independent.writes left hl right hr).symm,
    independent.secondReads, independent.firstReads⟩

/-- An unchanged read certificate licenses exactly the original proposal. -/
theorem commit_of_agrees (store : Key → Value) (proposal : Proposal Key Value)
    (valid : Agrees store proposal.reads) :
    commit store proposal = some (write store proposal.writes) := by
  simp [commit, (checkReads_iff _ _).mpr valid]

/-- Both serializations of independent, currently valid proposals succeed
and have the same final store. Their chronological histories need not agree. -/
theorem commit_independent_diamond (store : Key → Value)
    (first second : Proposal Key Value) (independent : first.Independent second)
    (firstValid : Agrees store first.reads) (secondValid : Agrees store second.reads) :
    commit store first = some (write store first.writes) ∧
    commit (write store first.writes) second = some (write (write store first.writes) second.writes) ∧
    commit store second = some (write store second.writes) ∧
    commit (write store second.writes) first = some (write (write store second.writes) first.writes) ∧
    write (write store first.writes) second.writes = write (write store second.writes) first.writes := by
  exact ⟨commit_of_agrees _ _ firstValid,
    commit_of_agrees _ _ (write_preserves_reads _ _ _ secondValid independent.secondReads),
    commit_of_agrees _ _ secondValid,
    commit_of_agrees _ _ (write_preserves_reads _ _ _ firstValid independent.firstReads),
    write_disjoint_comm _ _ _ independent.writes⟩

omit [DecidableEq Value] in
/-- Noninterfering writes preserve both valid and invalid read certificates. -/
theorem agrees_write_iff (store : Key → Value) (writes : Writes Key Value)
    (reads : Reads Key Value)
    (disjoint : ∀ entry ∈ writes, ∀ read ∈ reads, entry.1 ≠ read.1) :
    Agrees (write store writes) reads ↔ Agrees store reads := by
  constructor
  · intro agrees read member
    have same := write_untouched store writes read.1 (fun entry present => disjoint entry present read member)
    rw [← same]
    exact agrees read member
  · exact fun agrees => write_preserves_reads _ _ _ agrees disjoint

/-- Reorder actual accepted steps, preserving the exact final store. In
particular, the second action was not merely presumed enabled at the start. -/
theorem commit_swap_actual {first second : Proposal Key Value}
    (independent : first.Independent second) {source middle target : Key → Value}
    (firstStep : commit source first = some middle)
    (secondStep : commit middle second = some target) :
    ∃ afterSecond, commit source second = some afterSecond ∧
      commit afterSecond first = some target := by
  have firstValid : Agrees source first.reads := by
    unfold commit at firstStep
    split at firstStep
    · rename_i valid; exact (checkReads_iff _ _).mp valid
    · cases firstStep
  have middleEq : middle = write source first.writes := by
    rw [commit_of_agrees _ _ firstValid] at firstStep
    exact (Option.some.inj firstStep).symm
  have secondValid : Agrees middle second.reads := by
    unfold commit at secondStep
    split at secondStep
    · rename_i valid; exact (checkReads_iff _ _).mp valid
    · cases secondStep
  have initially : Agrees source second.reads :=
    (agrees_write_iff source first.writes second.reads independent.secondReads).mp
      (middleEq ▸ secondValid)
  obtain ⟨_, secondAfter, secondBefore, firstAfter, same⟩ :=
    commit_independent_diamond source first second independent firstValid initially
  refine ⟨write source second.writes, secondBefore, ?_⟩
  rw [firstAfter]
  apply congrArg some
  have targetEq : write (write source first.writes) second.writes = target := by
    rw [middleEq, secondAfter] at secondStep
    exact Option.some.inj secondStep
  exact same.symm.trans targetEq
/-- A changed dependency is rejected, including one that only controlled a
negative branch and did not itself receive a write. -/
theorem commit_rejects_changed_read (store : Key → Value) (proposal : Proposal Key Value)
    {read : Key × Value} (member : read ∈ proposal.reads) (changed : store read.1 ≠ read.2) :
    commit store proposal = none := by
  have invalid : checkReads store proposal.reads ≠ true := by
    intro checked
    exact changed ((checkReads_iff _ _).mp checked read member)
  simp [commit, invalid]


/-! ## The ledger under the owned host -/

structure Ledger (Key : Type u) (Value : Type v) where
  store : Key → Value
  history : List (Writes Key Value)

/-- Committing to the ledger: an accepted proposal writes and records its
writes; a refused one changes nothing. -/
def Ledger.submit (proposal : Proposal Key Value) (ledger : Ledger Key Value) : Ledger Key Value :=
  match commit ledger.store proposal with
  | some next => ⟨next, ledger.history ++ [proposal.writes]⟩
  | none => ledger

def ledger : OwnedPullDriver.Owned.Retained (Ledger Key Value) (Proposal Key Value) (Writes Key Value) where
  apply := Ledger.submit
  committed := Ledger.history
  grows := by
    intro proposal state
    unfold Ledger.submit
    split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

/-- The ledger's store is its start under exactly its accepted writes, in order. -/
theorem ledger_store {start state : Ledger Key Value} (empty : start.history = [])
    (derived : OwnedPullDriver.Owned.Host.Derived ledger start state) :
    state.store = state.history.foldl write start.store := by
  induction derived with
  | refl => simp [empty]
  | tail _ step ih =>
      obtain ⟨proposal, rfl⟩ := step
      change (Ledger.submit proposal _).store = (Ledger.submit proposal _).history.foldl write start.store
      unfold Ledger.submit
      split
      · rename_i next committed
        unfold commit at committed
        split at committed
        · cases committed
          simp [List.foldl_append, ih]
        · contradiction
      · exact ih

/-- **Accepted writes reach the external world exactly once.** In every host
state reached from a ledger with no history, the delivered history is the
ledger's accepted write lists and the world is the origin under exactly those
writes. -/
theorem ledger_published_once {World : Type*} (act : Writes Key Value → World → World) (origin : World)
    {start : Ledger Key Value}
    {host : OwnedPullDriver.Owned.Host (Ledger Key Value) (Writes Key Value) World}
    (reached : OwnedPullDriver.Owned.Host.Reached ledger act origin start host)
    {state : Ledger Key Value} (retained : host.retained = some state) :
    host.delivered = state.history ∧ host.world = interpret act state.history origin := by
  have accounts := reached.accounts
  have delivered := accounts.delivered state retained
  exact ⟨delivered, by rw [accounts.world, delivered]; rfl⟩

/-- The ledger keeps both effects as occurrences. Only the final-store and
bag-of-commits observer identifies the two independent schedules. -/
theorem Ledger.independent_diamond (state : Ledger Key Value)
    (first second : Proposal Key Value) (independent : first.Independent second)
    (firstValid : Agrees state.store first.reads) (secondValid : Agrees state.store second.reads) :
    (Ledger.submit second (Ledger.submit first state)).store =
      (Ledger.submit first (Ledger.submit second state)).store ∧
    (Ledger.submit second (Ledger.submit first state)).history =
      state.history ++ [first.writes, second.writes] ∧
    (Ledger.submit first (Ledger.submit second state)).history =
      state.history ++ [second.writes, first.writes] := by
  obtain ⟨h₁, h₂, h₃, h₄, same⟩ := commit_independent_diamond state.store first second
    independent firstValid secondValid
  simp only [Ledger.submit, h₁, h₃, h₂, h₄]
  exact ⟨same, by simp, by simp⟩

/-! ## Controls -/

namespace Controls

/-- Read a counter and write its successor. -/
def increment (key : Nat) : Transaction Nat Nat := .read key fun value => .pure [(key, value + 1)]

def zeros : Nat → Nat := fun _ => 0

/-- Two owners increment one counter from the same snapshot: the second
proposal read a value the first one changed, so it is refused. -/
theorem stale_increment_refused :
    let result := commitAll zeros [(zeros, increment 0), (zeros, increment 0)]
    result.1 0 = 1 ∧ result.2.length = 1 := by
  decide

/-- Rerunning the refused transaction on a fresh snapshot commits both increments. -/
theorem fresh_retry_commits :
    let first := commitAll zeros [(zeros, increment 0)]
    let second := commitAll first.1 [(first.1, increment 0)]
    second.1 0 = 2 := by
  decide

/-- Writing both proposals without validation loses an update. -/
theorem blind_writes_lose_an_update :
    write (write zeros (propose zeros (increment 0)).writes) (propose zeros (increment 0)).writes 0 = 1 := by
  decide

/-- Increments of different counters read nothing the other writes: both commit. -/
theorem unrelated_writes_both_commit :
    let result := commitAll zeros [(zeros, increment 0), (zeros, increment 1)]
    result.1 0 = 1 ∧ result.1 1 = 1 ∧ result.2.length = 2 := by
  decide

/-- A read of the counter is recorded even when the write goes elsewhere: a
transaction copying counter 0 into counter 1 is refused after counter 0 changes. -/
def copy : Transaction Nat Nat := .read 0 fun value => .pure [(1, value)]

theorem changed_read_refuses_other_write :
    let result := commitAll zeros [(zeros, increment 0), (zeros, copy)]
    result.1 1 = 0 ∧ result.2.length = 1 := by
  decide

end Controls

end Mettapedia.Machines.ValidatedCommit
