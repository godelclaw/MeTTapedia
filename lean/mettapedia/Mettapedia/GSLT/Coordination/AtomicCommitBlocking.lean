import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic

/-!
# Atomic commit across owners: blocking, and what sagas give up

A commit that takes at two owners cannot run at either alone. Two answers exist: an atomic commit
protocol (two-phase commit) or a saga (each owner commits its part, and failures are undone by
compensation).

## Two-phase commit blocks

**Fault model.** The coordinator and participants may crash; messages may be lost. A participant
decides from what it has seen (`View`). Required: **uniform agreement** (no two processes decide
differently, crashed ones included), commit only if all voted yes, and commit when all vote yes
and nothing fails.

* **A participant that voted yes and has heard nothing cannot decide** (`uncertain_cannot_decide`):
  it sees the same in a run where the coordinator decided commit and told only another participant,
  and in a run where that other participant voted no and was told abort. Whatever it decides,
  some run breaks agreement; so it waits, and if the coordinator and the other participant stay
  down, it waits forever. This is the blocking of two-phase commit. The principle is general
  (`indistinguishable_forces_wait`): a view that two runs with different outcomes share cannot be
  decided from.

## Sagas give atomicity of effect, not isolation

* **Compensation restores the state** (`Controls.saga_restores`): a transfer that debits, fails to
  credit and compensates leaves the accounts as they were.
* **A concurrent reader sees a state no serial run shows** (`Controls.saga_dirty_read`): between
  the debit and the compensation the total is short by one, while every serial execution of whole
  transfers keeps the total.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.AtomicCommitBlocking

universe u v w

/-- **A view shared by two runs with different outcomes cannot be decided from**: any decision at
that view disagrees with the outcome of one of the runs. -/
theorem indistinguishable_forces_wait {Run : Type u} {View : Type v} {Outcome : Type w}
    (view : Run → View) (outcome : Run → Outcome) (decide : View → Outcome) {first second : Run}
    (sameView : view first = view second) (different : outcome first ≠ outcome second) :
    decide (view first) ≠ outcome first ∨ decide (view second) ≠ outcome second := by
  by_contra both
  push Not at both
  exact different (both.1.symm.trans (sameView ▸ both.2))

/-! ## Two-phase commit -/

/-- The decision of an atomic commit. -/
inductive Decision where
  | commit
  | abort
  deriving DecidableEq, Repr

/-- A two-phase commit run with two participants, `p` and `q`: their votes, the coordinator's
decision, and which participants received it before the coordinator crashed. -/
structure TwoPhaseRun where
  voteP : Bool
  voteQ : Bool
  decision : Decision
  toldP : Bool
  toldQ : Bool
  deriving DecidableEq

/-- The coordinator's rule: commit exactly when both voted yes. -/
def TwoPhaseRun.Valid (run : TwoPhaseRun) : Prop :=
  run.decision = if run.voteP && run.voteQ then .commit else .abort

instance (run : TwoPhaseRun) : Decidable run.Valid := inferInstanceAs (Decidable (_ = _))

/-- What `p` has seen: its own vote, and the decision if it was told. -/
def View (run : TwoPhaseRun) : Bool × Option Decision :=
  (run.voteP, if run.toldP then some run.decision else none)

/-- What `q` decides: the decision when told; nothing otherwise. -/
def decidedByQ (run : TwoPhaseRun) : Option Decision :=
  if run.toldQ then some run.decision else if run.voteQ then none else some .abort

/-- Both voted yes; the coordinator decided commit, told `q` only, and crashed. -/
def toldQCommit : TwoPhaseRun := ⟨true, true, .commit, false, true⟩

/-- `q` voted no; the coordinator decided abort, told `q` only, and crashed. -/
def toldQAbort : TwoPhaseRun := ⟨true, false, .abort, false, true⟩

theorem runs_valid : toldQCommit.Valid ∧ toldQAbort.Valid := by decide

/-- **An uncertain participant cannot decide**: `p` voted yes and heard nothing in both runs, `q`
decided commit in one and abort in the other, so any decision of `p` from its view disagrees with
`q` in one of them. -/
theorem uncertain_cannot_decide (decideP : Bool × Option Decision → Decision) :
    some (decideP (View toldQCommit)) ≠ decidedByQ toldQCommit ∨
      some (decideP (View toldQAbort)) ≠ decidedByQ toldQAbort := by
  have sameView : View toldQCommit = View toldQAbort := by decide
  have := indistinguishable_forces_wait View decidedByQ (fun seen => some (decideP seen)) sameView
    (by decide)
  exact this

/-- Once told, `p` decides as the coordinator did: the view determines the outcome. -/
theorem told_decides (run : TwoPhaseRun) (told : run.toldP = true) :
    (View run).2 = some run.decision := by
  simp [View, told]

/-! ## Controls: sagas -/

namespace Controls

/-- Two accounts holding five each. -/
def accounts : ℕ × ℕ := (5, 5)

/-- A transfer as a saga: debit the first account, then credit the second; if the credit fails,
compensate by crediting the first back. -/
def debit (s : ℕ × ℕ) : ℕ × ℕ := (s.1 - 1, s.2)
def credit (s : ℕ × ℕ) : ℕ × ℕ := (s.1, s.2 + 1)
def compensate (s : ℕ × ℕ) : ℕ × ℕ := (s.1 + 1, s.2)

def total (s : ℕ × ℕ) : ℕ := s.1 + s.2

/-- **Compensation restores the state**: debit, a failed credit, compensation. -/
theorem saga_restores : compensate (debit accounts) = accounts := by decide

/-- The states serial executions of whole transfers reach from the start: transfers that commit
fully, or not at all. -/
def serialStates : List (ℕ × ℕ) := [accounts, credit (debit accounts)]

/-- **A concurrent reader sees a state no serial run shows**: between debit and compensation the
total is nine, while every serial state totals ten. -/
theorem saga_dirty_read :
    total (debit accounts) = 9 ∧ ∀ s ∈ serialStates, total s = 10 := by
  decide

end Controls

end Mettapedia.GSLT.Coordination.AtomicCommitBlocking
