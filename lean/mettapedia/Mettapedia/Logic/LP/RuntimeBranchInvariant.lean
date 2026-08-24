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

/-- A branch checkpoint together with its exact occurrence in the live shared
choice stack.  The positional decomposition prevents a saved alternative from
being reused as detached evidence after it has been pruned or popped. -/
structure LiveBranchCheckpoint
    (anchor : Memory σ.scoped)
    (state : StateCore σ Instruction SourceClause)
    (alternative : BranchChoiceCore σ Instruction)
    (newer older : List (ChoicePointCore σ Instruction SourceClause)) : Prop where
  saved : BranchCheckpoint anchor state alternative
  occurrence : state.choices = newer ++ .branch alternative :: older

/-- Two nested ordinary branches with the heap history at their nesting
boundary retained explicitly.  The `ancestry` field is load-bearing: once the
inner branch performs writes, the later heap alone cannot reconstruct the
parent's original prefix.  Keeping it here lets the actual inner backtrack
restore a live outer branch without inventing a history. -/
structure NestedLiveBranchCheckpoint
    (outerAnchor parentMemory : Memory σ.scoped)
    (state : StateCore σ Instruction SourceClause)
    (outer inner : BranchChoiceCore σ Instruction)
    (newer older : List (ChoicePointCore σ Instruction SourceClause)) : Prop where
  outerLive : LiveBranchCheckpoint outerAnchor state outer
    (.branch inner :: newer) older
  innerLive : LiveBranchCheckpoint parentMemory state inner []
    (newer ++ .branch outer :: older)
  ancestry : Extends outerAnchor parentMemory

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

/-- Heap evolution preserves the positional ownership of a live branch: only
the memory field changes, so the same occurrence remains in the same stack. -/
theorem LiveBranchCheckpoint.advance
    {anchor : Memory σ.scoped}
    {state : StateCore σ Instruction SourceClause}
    {alternative : BranchChoiceCore σ Instruction}
    {newer older : List (ChoicePointCore σ Instruction SourceClause)}
    (certificate : LiveBranchCheckpoint anchor state alternative newer older)
    {memory : Memory σ.scoped}
    (history : Extends state.memory memory) :
    LiveBranchCheckpoint anchor { state with memory } alternative newer older := by
  exact ⟨certificate.saved.advance history, certificate.occurrence⟩

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
    ∃ alternative after,
      branchStep state left right rest = .next after none ∧
      after = {
        state with
        control := {
          current := left ++ rest
          cutDepth := state.control.cutDepth
          frames := state.control.frames
        }
        choices := .branch alternative :: state.choices
      } ∧
      after.choices = .branch alternative :: state.choices ∧
      after.memory = state.memory ∧
      after.control.current = left ++ rest ∧
      alternative.control.current = right ++ rest ∧
      BranchCheckpoint state.memory after alternative := by
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
  refine ⟨alternative, after, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact ⟨rfl, .refl state.memory, wellFormed, wellShaped,
    floorZero⟩

/-- Pushing an inner structured branch preserves an outer branch's live stack
occurrence and creates a newly live top occurrence.  This is the non-vacuous
nested-choice law: an outer checkpoint remains owned while its child is
explored, rather than being reintroduced only when the child fails. -/
theorem LiveBranchCheckpoint.branchStep
    {anchor : Memory σ.scoped}
    {state : StateCore σ Instruction SourceClause}
    {alternative : BranchChoiceCore σ Instruction}
    {newer older : List (ChoicePointCore σ Instruction SourceClause)}
    (certificate : LiveBranchCheckpoint anchor state alternative newer older)
    (left right rest : List Instruction)
    (wellFormed : state.memory.heap.WellFormed)
    (wellShaped : state.memory.heap.WellShaped)
    (floorZero : state.persistentHeapFloor = 0) :
    ∃ inner after,
      branchStep state left right rest = .next after none ∧
      LiveBranchCheckpoint anchor after alternative (.branch inner :: newer) older ∧
      LiveBranchCheckpoint state.memory after inner [] state.choices := by
  obtain ⟨inner, after, stepped, afterExact, choices, memory, _, _, innerSaved⟩ :=
    branchStep_creates_checkpoint state left right rest wellFormed wellShaped
      floorZero
  refine ⟨inner, after, stepped, ?_, ?_⟩
  · rcases certificate with ⟨saved, occurrence⟩
    have savedAfter : BranchCheckpoint anchor after alternative := by
      refine ⟨saved.checkpoint, ?_, saved.wellFormed, saved.wellShaped, ?_⟩
      · rw [memory]
        exact saved.history
      · rw [afterExact]
        exact saved.floorZero
    refine ⟨savedAfter, ?_⟩
    rw [afterExact, occurrence]
    rfl
  · exact ⟨innerSaved, by simp [choices]⟩

/-- Entering an inner branch records the exact parent heap as the child's
checkpoint anchor and retains the outer-to-parent history.  This is the
certificate needed to prove nested backtracking without treating a later heap
as though it could reveal a discarded historical prefix. -/
theorem NestedLiveBranchCheckpoint.branchStep
    {outerAnchor : Memory σ.scoped}
    {state : StateCore σ Instruction SourceClause}
    {outer : BranchChoiceCore σ Instruction}
    {newer older : List (ChoicePointCore σ Instruction SourceClause)}
    (certificate : LiveBranchCheckpoint outerAnchor state outer newer older)
    (left right rest : List Instruction)
    (wellFormed : state.memory.heap.WellFormed)
    (wellShaped : state.memory.heap.WellShaped)
    (floorZero : state.persistentHeapFloor = 0) :
    ∃ inner after,
      branchStep state left right rest = .next after none ∧
      NestedLiveBranchCheckpoint outerAnchor state.memory after outer inner
        newer older := by
  obtain ⟨inner, after, stepped, outerLive, innerLive⟩ :=
    certificate.branchStep left right rest wellFormed wellShaped floorZero
  rcases innerLive with ⟨innerSaved, innerOccurrence⟩
  refine ⟨inner, after, stepped, outerLive, ?_, certificate.saved.history⟩
  refine ⟨innerSaved, ?_⟩
  simpa [certificate.occurrence] using innerOccurrence

/-- Certified child heap evolution preserves the remembered nesting boundary:
both live occurrences advance to the new heap, while the parent-to-child
prefix remains the same historical fact. -/
theorem NestedLiveBranchCheckpoint.advance
    {outerAnchor parentMemory : Memory σ.scoped}
    {state : StateCore σ Instruction SourceClause}
    {outer inner : BranchChoiceCore σ Instruction}
    {newer older : List (ChoicePointCore σ Instruction SourceClause)}
    (certificate : NestedLiveBranchCheckpoint outerAnchor parentMemory state
      outer inner newer older)
    {memory : Memory σ.scoped}
    (history : Extends state.memory memory) :
    NestedLiveBranchCheckpoint outerAnchor parentMemory { state with memory }
      outer inner newer older := by
  exact ⟨certificate.outerLive.advance history,
    certificate.innerLive.advance history, certificate.ancestry⟩

/-- Popping the top inner branch restores its saved parent heap and leaves the
outer branch live at its original stack occurrence.  This is the nested
backtracking half of the choice-resource law: inner ownership is consumed
once, while the caller's retained branch remains usable. -/
theorem NestedLiveBranchCheckpoint.backtrackStep
    [DecidableEq σ.scoped.vars]
    {outerAnchor parentMemory : Memory σ.scoped}
    {state : StateCore σ Instruction SourceClause}
    {outer inner : BranchChoiceCore σ Instruction}
    {newer older : List (ChoicePointCore σ Instruction SourceClause)}
    (certificate : NestedLiveBranchCheckpoint outerAnchor parentMemory state
      outer inner newer older) :
    ∃ after,
      backtrackStep state = .next after none ∧
      LiveBranchCheckpoint outerAnchor after outer newer older := by
  let after : StateCore σ Instruction SourceClause := {
    state with
    memory := parentMemory
    control := inner.control
    choices := newer ++ .branch outer :: older
    phase := .dispatch
  }
  refine ⟨after, ?_, ?_⟩
  · simpa [after] using RuntimeQuery.backtrackStep_branch_of_restore state inner
      (newer ++ .branch outer :: older) parentMemory
      (by simpa using certificate.innerLive.occurrence)
      certificate.innerLive.saved.restore_exact
  · refine ⟨?_, rfl⟩
    exact ⟨certificate.outerLive.saved.checkpoint, certificate.ancestry,
      certificate.outerLive.saved.wellFormed,
      certificate.outerLive.saved.wellShaped, by
        simp [after, certificate.outerLive.saved.floorZero]⟩

/-- Keeping the oldest suffix of a newest-first stack removes a newer prefix
exactly.  This is the list fact behind caller-survival for cut. -/
private theorem retainBottom_suffix
    (newer suffix : List α) :
    retainBottom suffix.length (newer ++ suffix) = suffix := by
  simp [retainBottom, List.length_append]

/-- The one-extra-element form used when a cut consumes the branch at its
boundary. -/
private theorem retainBottom_after_branch
    (newer older : List α) (branch : α) :
    retainBottom older.length (newer ++ branch :: older) = older := by
  induction newer with
  | nil => simp [retainBottom]
  | cons head newer ih =>
      simp [retainBottom, List.length_append] at ih ⊢
      have hIndex :
          newer.length + (older.length + 1) + 1 - older.length =
            (newer.length + (older.length + 1) - older.length) + 1 := by
        omega
      rw [hIndex]
      simp
      exact ih

/-- A cut at the boundary immediately below a live branch discards every
newer choice but retains that branch and its older caller suffix.  The exact
stack equation makes caller survival an ownership fact, rather than a count
claim. -/
theorem LiveBranchCheckpoint.cutStep_preserves
    {anchor : Memory σ.scoped}
    {state : StateCore σ Instruction SourceClause}
    {alternative : BranchChoiceCore σ Instruction}
    {newer older : List (ChoicePointCore σ Instruction SourceClause)}
    (certificate : LiveBranchCheckpoint anchor state alternative newer older)
    (rest : List Instruction)
    (cutDepth : state.control.cutDepth = (.branch alternative :: older).length) :
    ∃ after,
      cutStep state rest = .next after none ∧
      after.choices = .branch alternative :: older ∧
      LiveBranchCheckpoint anchor after alternative [] older := by
  let after : StateCore σ Instruction SourceClause := {
    state with
    control := { state.control with current := rest }
    choices := .branch alternative :: older
  }
  refine ⟨after, ?_, rfl, ?_⟩
  · rw [cutStep]
    have valid : state.control.cutDepth ≤ state.choices.length := by
      rw [cutDepth, certificate.occurrence]
      simp [List.length_append]
    simp only [dif_pos valid]
    congr 2
    rw [certificate.occurrence, cutDepth]
    exact retainBottom_suffix newer (.branch alternative :: older)
  · rcases certificate with ⟨saved, occurrence⟩
    refine ⟨?_, rfl⟩
    exact ⟨saved.checkpoint, saved.history, saved.wellFormed,
      saved.wellShaped, by simp [after, saved.floorZero]⟩

/-- At the boundary below a live branch, cut consumes that branch and every
newer choice while retaining exactly the older caller suffix.  This is the
intentional counterpart to `cutStep_preserves`: a discarded occurrence is
removed by the shared engine rather than being left as reusable evidence. -/
theorem LiveBranchCheckpoint.cutStep_prunes
    {anchor : Memory σ.scoped}
    {state : StateCore σ Instruction SourceClause}
    {alternative : BranchChoiceCore σ Instruction}
    {newer older : List (ChoicePointCore σ Instruction SourceClause)}
    (certificate : LiveBranchCheckpoint anchor state alternative newer older)
    (rest : List Instruction)
    (cutDepth : state.control.cutDepth = older.length) :
    ∃ after,
      cutStep state rest = .next after none ∧
      after.choices = older := by
  let after : StateCore σ Instruction SourceClause := {
    state with
    control := { state.control with current := rest }
    choices := older
  }
  refine ⟨after, ?_, rfl⟩
  rw [cutStep]
  have valid : state.control.cutDepth ≤ state.choices.length := by
    rw [cutDepth, certificate.occurrence]
    simp [List.length_append]
    omega
  simp only [dif_pos valid]
  congr 2
  rw [certificate.occurrence, cutDepth]
  exact retainBottom_after_branch newer older (.branch alternative)

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
