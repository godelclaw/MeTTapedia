import Std

/-!+# Native root publication and confirmation

An immutable candidate root names one whole batch. Appending, checksums and
scope validation have separate contracts. This model addresses the boundary
between an atomic root rename and durable acknowledgement. A rename error is
not a rollback certificate. A fresh reader must synchronize an unseen visible
root before trusting its application receipts.

`stable` is the last root protected by the modeled file/directory barriers.
The crash transition permits either that root or the newly renamed one. Its
choices model the filesystem assumptions, not a proof of fsync or the C code.
The native fault tests emit the same finite stage traces as this executable
model. Pure planning, remote effects and application receipt identity remain
outside this generic publication owner.
-/

namespace Mettapedia.Machines.NativeStorePublication

structure State where
  visible : Nat := 0
  stable : Nat := 0
  blocked : Bool := false
deriving DecidableEq, Repr

inductive Stage where
  | dataSync | manifestSync | renameBefore | renameAfter | directorySync | success
deriving DecidableEq, Repr

inductive Answer where
  | io | unknown | committed | recoveryRequired
deriving DecidableEq, Repr

def publish (state : State) (candidate : Nat) (stage : Stage) : Answer × State :=
  if state.blocked then (.recoveryRequired, state)
  else match stage with
    | .dataSync | .manifestSync => (.io, state)
    | .renameBefore => (.unknown, { state with blocked := true })
    | .renameAfter | .directorySync =>
        (.unknown, { state with visible := candidate, blocked := true })
    | .success => (.committed, ⟨candidate, candidate, false⟩)

/-- On failure no root is returned. Merely reading bytes is not confirmation. -/
def confirm (state : State) (synchronized : Bool) : Option Nat × State :=
  if synchronized then (some state.visible, { state with stable := state.visible })
  else (none, state)

def recover (state : State) (synchronized : Bool) : Option Nat × State :=
  let result := confirm state synchronized
  if result.1.isSome then (result.1, { result.2 with blocked := false }) else result

/-- Recovery after a process/host crash loses the old handle's volatile gate.
The newly opened handle still has to confirm before returning a snapshot. -/
def crash (state : State) (renameSurvives : Bool) : State :=
  let root := if renameSurvives then state.visible else state.stable
  ⟨root, root, false⟩

theorem blocked_handle_cannot_publish (state : State) (candidate : Nat) (stage : Stage)
    (blocked : state.blocked = true) :
    publish state candidate stage = (.recoveryRequired, state) := by
  simp [publish, blocked]

theorem failed_preparation_preserves_visible_root (state : State) (candidate : Nat)
    (stage : Stage) (early : stage = .dataSync ∨ stage = .manifestSync) :
    (publish state candidate stage).2 = state := by
  rcases early with rfl | rfl <;> cases gate : state.blocked <;> simp [publish, gate]

theorem acknowledged_publication_is_durable (state : State) (candidate : Nat)
    (stage : Stage) (ack : (publish state candidate stage).1 = .committed) :
    (publish state candidate stage).2.visible = candidate ∧
      (publish state candidate stage).2.stable = candidate := by
  cases gate : state.blocked <;> cases stage <;> simp_all [publish]

theorem acknowledgement_survives_modeled_crash (state : State) (candidate : Nat)
    (stage : Stage) (renameSurvives : Bool)
    (ack : (publish state candidate stage).1 = .committed) :
    (crash (publish state candidate stage).2 renameSurvives).visible = candidate := by
  have roots := acknowledged_publication_is_durable state candidate stage ack
  cases renameSurvives <;> simp [crash, roots.1, roots.2]

theorem successful_snapshot_is_durable (state : State) (synchronized : Bool) (root : Nat)
    (ack : (confirm state synchronized).1 = some root) :
    (confirm state synchronized).2.visible = root ∧
      (confirm state synchronized).2.stable = root := by
  cases synchronized <;> simp_all [confirm]

theorem confirmed_snapshot_survives_modeled_crash (state : State)
    (synchronized renameSurvives : Bool) (root : Nat)
    (ack : (confirm state synchronized).1 = some root) :
    (crash (confirm state synchronized).2 renameSurvives).visible = root := by
  have roots := successful_snapshot_is_durable state synchronized root ack
  cases renameSurvives <;> simp [crash, roots.1, roots.2]

theorem failed_confirmation_grants_no_answer (state : State) :
    confirm state false = (none, state) := rfl

theorem failed_recovery_keeps_the_gate (state : State) :
    recover state false = (none, state) := rfl

theorem successful_recovery_clears_the_gate (state : State) :
    (recover state true).2.blocked = false ∧
      (recover state true).2.stable = state.visible := by
  simp [recover, confirm]

/-- The same unknown reply permits two different visible outcomes. -/
theorem unknown_is_not_a_rollback_certificate :
    (publish {} 1 .renameBefore).1 = .unknown ∧
      (publish {} 1 .renameAfter).1 = .unknown ∧
      (publish {} 1 .renameBefore).2.visible = 0 ∧
      (publish {} 1 .renameAfter).2.visible = 1 := by decide

/-- This is the concrete counterexample to trusting a fresh row read without
first confirming the root: its receipt can disappear in a permitted crash. -/
theorem unsynchronized_read_is_insufficient :
    let renamed := (publish {} 1 .renameAfter).2
    renamed.visible = 1 ∧ (crash renamed false).visible = 0 := by decide

def stageName : Stage → String
  | .dataSync => "sync-data" | .manifestSync => "sync-manifest"
  | .renameBefore => "rename-before" | .renameAfter => "rename-after"
  | .directorySync => "sync-directory" | .success => "success"

def answerName : Answer → String
  | .io => "io" | .unknown => "unknown" | .committed => "committed"
  | .recoveryRequired => "recovery-required"

/-- Consumed by the fault-trace bridge, not a substitute for the proofs. -/
def traceLines : List String :=
  [Stage.dataSync, .manifestSync, .renameBefore, .renameAfter, .directorySync, .success].map
    fun stage =>
      let attempted := publish {} 1 stage
      let recovered := recover attempted.2 true
      s!"STORE_PUBLICATION {stageName stage} {answerName attempted.1} {recovered.2.visible}"

end Mettapedia.Machines.NativeStorePublication

#eval (Mettapedia.Machines.NativeStorePublication.traceLines.forM IO.println : IO Unit)
