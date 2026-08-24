import Mettapedia.Logic.LP.RuntimeUnificationSoundness

/-!
# Exact structured-branch restoration on the shared query runtime

`RuntimeQuery.branchStep` and `backtrackStep` are the one engine's concrete
choice-point operations.  The pure fixed-program least-model invariant in
`RuntimeUnificationSoundness` deliberately contains only clause cursors: it
cannot be used to dismiss a live Prolog branch as impossible.  This module
instead gives the actual `.branch` alternative its local executable
certificate.

The certificate is intentionally narrow.  It covers ordinary backtrackable
heap histories at persistent heap floor zero.  Persistent services,
collections, transactions, and the semantic interpretation of control each
need their own extensions; none are smuggled into this lemma.
-/

namespace Mettapedia.Logic.LP
namespace RuntimeBranchInvariant

open RuntimeTerm RuntimeQuery
open RuntimeUnificationSoundness

variable {σ : LPSignature}
variable {Instruction SourceClause : Type*}

/-- A saved structured alternative owns a checkpoint of `anchor`.  The live
memory may have advanced from that anchor only through the executable
write/allocation history that `Extends` records. -/
structure BranchCheckpoint
    (anchor : Memory σ.scoped)
    (state : StateCore σ Instruction SourceClause)
    (alternative : BranchChoiceCore σ Instruction) : Prop where
  checkpoint : alternative.checkpoint = anchor.checkpoint
  history : Extends anchor state.memory
  wellFormed : anchor.heap.WellFormed
  wellShaped : anchor.heap.WellShaped
  floorZero : state.persistentHeapFloor = 0

/-- A checkpoint certificate follows any further certified heap evolution.
This is the only way the local branch fact is carried between entry and
backtracking; no second transition system is introduced. -/
theorem BranchCheckpoint.advance
    {state : StateCore σ Instruction SourceClause}
    {alternative : BranchChoiceCore σ Instruction}
    (certificate : BranchCheckpoint anchor state alternative)
    {memory : Memory σ.scoped}
    (history : Extends state.memory memory) :
    BranchCheckpoint anchor { state with memory } alternative := by
  refine ⟨certificate.checkpoint, certificate.history.trans history,
    certificate.wellFormed, certificate.wellShaped, certificate.floorZero⟩

/-- Exact restoration for a certified branch alternative.  At the pure
runtime's zero persistent floor, protected restoration is ordinary checkpoint
restoration, and the existing `Extends.restore_exact` theorem identifies the
result with the saved anchor verbatim. -/
theorem BranchCheckpoint.restore_exact
    {state : StateCore σ Instruction SourceClause}
    {alternative : BranchChoiceCore σ Instruction}
    (certificate : BranchCheckpoint anchor state alternative) :
    state.memory.restorePreserving state.persistentHeapFloor
        alternative.checkpoint = .ok anchor := by
  rw [certificate.floorZero, Memory.restorePreserving_zero,
    certificate.checkpoint]
  exact certificate.history.restore_exact
    (Heap.check_of_wellFormed certificate.wellFormed)
    (Heap.check_of_wellShaped certificate.wellShaped)

/-- A successful canonical graph-unifier run advances, but cannot invalidate,
a live branch checkpoint.  This is the first nontrivial child computation a
structured branch can perform: the exact `Extends` history comes from the
unifier's real run induction, not an assumed monotonicity property. -/
theorem BranchCheckpoint.advance_unifier_success
    [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
    {anchor : Memory σ.scoped}
    {state : StateCore σ Instruction SourceClause}
    {alternative : BranchChoiceCore σ Instruction}
    (certificate : BranchCheckpoint anchor state alternative)
    (fuel : Nat) (agenda : List (Addr × Addr)) (memory : Memory σ.scoped)
    (run : RuntimeUnification.runSteps fuel
      (RuntimeUnification.startMany state.memory agenda) =
        .terminal (.success memory)) :
    BranchCheckpoint anchor { state with memory } alternative := by
  obtain ⟨_, history, _⟩ :=
    RuntimeUnificationSoundness.startMany_success_extension fuel
      state.memory agenda memory run
  exact certificate.advance history

/-- Entering a branch on the shared engine creates a real newest choice point
whose saved continuation is the right branch followed by the caller tail,
and whose checkpoint certificate is immediately inhabited. -/
theorem branchStep_creates_checkpoint
    (state : StateCore σ Instruction SourceClause)
    (left right rest : List Instruction)
    (wellFormed : state.memory.heap.WellFormed)
    (wellShaped : state.memory.heap.WellShaped)
    (floorZero : state.persistentHeapFloor = 0) :
    ∃ anchor alternative after,
      branchStep state left right rest = .next after none ∧
      after.choices = .branch alternative :: state.choices ∧
      after.control.current = left ++ rest ∧
      alternative.control.current = right ++ rest ∧
      BranchCheckpoint anchor after alternative := by
  let alternative : BranchChoiceCore σ Instruction := {
    checkpoint := state.memory.checkpoint
    control := {
      current := right ++ rest
      cutDepth := state.control.cutDepth
      frames := state.control.frames
    }
  }
  let after : StateCore σ Instruction SourceClause := {
    state with
    control := {
      current := left ++ rest
      cutDepth := state.control.cutDepth
      frames := state.control.frames
    }
    choices := .branch alternative :: state.choices
  }
  refine ⟨state.memory, alternative, after, rfl, rfl, rfl, rfl, ?_⟩
  exact ⟨rfl, .refl state.memory, wellFormed, wellShaped,
    floorZero⟩

/-- Backtracking through a certified newest branch restores its exact saved
memory and installs its saved right continuation.  Thus branch restoration is
not merely an operational test: it is tied to the same heap-history theorem
used for ordinary clause retries. -/
theorem backtrackStep_branch_of_checkpoint
    [DecidableEq σ.scoped.vars]
    {state : StateCore σ Instruction SourceClause}
    {alternative : BranchChoiceCore σ Instruction}
    {older : List (ChoicePointCore σ Instruction SourceClause)}
    (certificate : BranchCheckpoint anchor state alternative)
    (choices : state.choices = .branch alternative :: older) :
    backtrackStep state =
      .next {
        state with
        memory := anchor
        control := alternative.control
        choices := older
        phase := .dispatch
      } none :=
  RuntimeQuery.backtrackStep_branch_of_restore state alternative older
    anchor choices certificate.restore_exact

end RuntimeBranchInvariant
end Mettapedia.Logic.LP
