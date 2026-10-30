import Mettapedia.Machines.PreparedSharedFrontier

/-!
# Branching saved callers

An older pending equation and a newer call may have different saved callers
with a shared ancestor. Each layer therefore selects an already allocated
caller root before optionally adding a frame. The source stores full caller
lists; the target stores parent links. Both refuse a root beyond the retained
arena. The results retain each pending task's own context.

The roots and frame values are an abstract representation of native
continuations. Source-plan ownership, root validity under C allocation and
rollback, and native source-fuel correspondence are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedBranchedFrontier

open SharedContinuation PreparedSharedFrontier

variable {Context Control Frame : Type}

structure BranchLayer (Context Control Frame : Type) where
  parent : Nat
  layer : Layer Context Control Frame

structure Bank (Context Control Frame : Type) where
  lookup : Nat → List Frame
  count : Nat
  root : Nat
  pending : List (Task Context Control Frame)

def Bank.decode (state : Bank Context Control Frame) : Source Context Control Frame :=
  ⟨state.lookup state.root, state.pending⟩

def pushBank (lookup : Nat → List Frame) (count parent : Nat) (frame : Frame) :
    Nat → List Frame :=
  fun index => if index = count + 1 then frame :: lookup parent else lookup index

def sourceStep? (state : Bank Context Control Frame) (branch : BranchLayer Context Control Frame) :
    Option (Bank Context Control Frame) :=
  if branch.parent ≤ state.count then
    let advanced := PreparedSharedFrontier.sourceStep
      ⟨state.lookup branch.parent, state.pending⟩ branch.layer
    match branch.layer.caller with
    | none => some ⟨state.lookup, state.count, branch.parent, advanced.pending⟩
    | some frame => some ⟨pushBank state.lookup state.count branch.parent frame,
        state.count + 1, state.count + 1, advanced.pending⟩
  else none

def sharedStep? (state : Shared Context Control Frame)
    (branch : BranchLayer Context Control Frame) : Option (Shared Context Control Frame) :=
  if branch.parent ≤ state.arena.length then
    some (PreparedSharedFrontier.sharedStep {state with root := branch.parent} branch.layer)
  else none

/-- `lookup` is the independent, fully expanded source representation. -/
structure Related (source : Bank Context Control Frame) (shared : Shared Context Control Frame) : Prop where
  valid : shared.Valid
  count : source.count = shared.arena.length
  root : source.root = shared.root
  lookup : ∀ root, root ≤ source.count → source.lookup root = shared.arena.expand root
  pending : source.pending = shared.pending.map (RootTask.decode shared.arena)

theorem pushBank_exact (lookup : Nat → List Frame) (arena : Arena Frame)
    (parent : Nat) (frame : Frame)
    (represented : ∀ root, root ≤ arena.length → lookup root = arena.expand root)
    (parentBound : parent ≤ arena.length) (root : Nat) (bound : root ≤ arena.length + 1) :
    pushBank lookup arena.length parent frame root =
      Arena.expand ((frame, parent) :: arena) root := by
  by_cases fresh : root = arena.length + 1
  · subst root
    simp [pushBank, Arena.expand, represented parent parentBound]
  · have old : root ≤ arena.length := by omega
    simp [pushBank, fresh, Arena.expand_old arena frame parent root old, represented root old]

/-- A pair of steps either both refuse the parent address or both retain
equivalent states. Refusal does not manufacture an empty answer. -/
inductive StepRelated : Option (Bank Context Control Frame) →
    Option (Shared Context Control Frame) → Prop where
  | refused : StepRelated none none
  | moved {source shared} : Related source shared → StepRelated (some source) (some shared)

/-- An admitted branch can select any retained ancestor, not just the
preceding task's root. Its new node leaves every older root intact. -/
theorem step_exact (source : Bank Context Control Frame)
    (shared : Shared Context Control Frame) (related : Related source shared)
    (branch : BranchLayer Context Control Frame) :
    StepRelated (sourceStep? source branch) (sharedStep? shared branch) := by
  by_cases admitted : branch.parent ≤ source.count
  · have sharedBound : branch.parent ≤ shared.arena.length := by
      simpa [related.count] using admitted
    let base : Shared Context Control Frame := {shared with root := branch.parent}
    have baseValid : base.Valid := by
      exact ⟨related.valid.1, sharedBound, related.valid.2.2⟩
    have baseDecode : base.decode = ⟨source.lookup branch.parent, source.pending⟩ := by
      simp [base, Shared.decode, related.lookup branch.parent admitted, related.pending]
    obtain ⟨nextValid, nextExact⟩ := sharedStep_exact base baseValid branch.layer
    rw [baseDecode] at nextExact
    have pendingExact :
        (PreparedSharedFrontier.sourceStep
            ⟨source.lookup branch.parent, source.pending⟩ branch.layer).pending =
          (PreparedSharedFrontier.sharedStep base branch.layer).pending.map
            (RootTask.decode (PreparedSharedFrontier.sharedStep base branch.layer).arena) := by
      have projected := congrArg Source.pending nextExact
      simpa only [Shared.decode] using projected.symm
    have represented : ∀ root, root ≤ shared.arena.length →
        source.lookup root = shared.arena.expand root := by
      intro root bound
      exact related.lookup root (by simpa [related.count] using bound)
    simp only [sourceStep?, admitted, ↓reduceIte, sharedStep?, sharedBound]
    cases caller : branch.layer.caller with
    | none =>
        apply StepRelated.moved
        refine ⟨nextValid, ?_, ?_, ?_, pendingExact⟩
        · simp [PreparedSharedFrontier.sharedStep, caller, related.count]
        · simp [PreparedSharedFrontier.sharedStep, caller]
        · intro root bound
          simpa [PreparedSharedFrontier.sharedStep, caller, base] using
            related.lookup root bound
    | some frame =>
        apply StepRelated.moved
        refine ⟨nextValid, ?_, ?_, ?_, pendingExact⟩
        · simp [PreparedSharedFrontier.sharedStep, caller, related.count]
        · simp [PreparedSharedFrontier.sharedStep, caller, related.count]
        · intro root bound
          have rootBound : root ≤ shared.arena.length + 1 := by
            simpa [related.count] using bound
          simpa [PreparedSharedFrontier.sharedStep, caller, base, related.count] using
            pushBank_exact source.lookup shared.arena branch.parent frame represented sharedBound root rootBound
  · have refused : ¬branch.parent ≤ shared.arena.length := by
      simpa [related.count] using admitted
    simp [sourceStep?, admitted, sharedStep?, refused, StepRelated.refused]

def sourceRun : Bank Context Control Frame → List (BranchLayer Context Control Frame) →
    Option (Bank Context Control Frame)
  | state, [] => some state
  | state, branch :: rest => (sourceStep? state branch).bind fun next => sourceRun next rest

def sharedRun : Shared Context Control Frame → List (BranchLayer Context Control Frame) →
    Option (Shared Context Control Frame)
  | state, [] => some state
  | state, branch :: rest => (sharedStep? state branch).bind fun next => sharedRun next rest

/-- Repeated branch installation has the same success or refusal and
preserves every captured task in the successful case. -/
theorem run_exact (source : Bank Context Control Frame)
    (shared : Shared Context Control Frame) (related : Related source shared)
    (branches : List (BranchLayer Context Control Frame)) :
    StepRelated (sourceRun source branches) (sharedRun shared branches) := by
  induction branches generalizing source shared with
  | nil => exact StepRelated.moved related
  | cons branch rest ih =>
      have first := step_exact source shared related branch
      cases sourceResult : sourceStep? source branch with
      | none =>
          cases sharedResult : sharedStep? shared branch with
          | none =>
              simp [sourceRun, sharedRun, sourceResult, sharedResult, StepRelated.refused]
          | some next =>
              rw [sourceResult, sharedResult] at first
              cases first
      | some nextSource =>
          cases sharedResult : sharedStep? shared branch with
          | none =>
              rw [sourceResult, sharedResult] at first
              cases first
          | some nextShared =>
              rw [sourceResult, sharedResult] at first
              cases first with
              | moved nextRelated =>
                  simpa [sourceRun, sharedRun, sourceResult, sharedResult] using
                    ih nextSource nextShared nextRelated

def callerCount : List (BranchLayer Context Control Frame) → Nat
  | [] => 0
  | branch :: rest =>
      (if branch.layer.caller.isSome then 1 else 0) + callerCount rest

theorem step_nodes (state next : Shared Context Control Frame)
    (branch : BranchLayer Context Control Frame)
    (advanced : sharedStep? state branch = some next) :
    next.arena.length = state.arena.length +
      (if branch.layer.caller.isSome then 1 else 0) := by
  unfold sharedStep? at advanced
  split at advanced
  next admitted =>
    simp only [Option.some.injEq] at advanced
    subst next
    simpa using sharedStep_nodes {state with root := branch.parent} branch.layer
  next refused => simp at advanced

/-- Successful branching creates one node per caller, irrespective of how
many alternatives refer to those nodes. This counts nodes, not bytes. -/
theorem run_nodes (state next : Shared Context Control Frame)
    (branches : List (BranchLayer Context Control Frame))
    (finished : sharedRun state branches = some next) :
    next.arena.length = state.arena.length + callerCount branches := by
  induction branches generalizing state with
  | nil =>
      simp [sharedRun] at finished
      subst next
      simp [callerCount]
  | cons branch rest ih =>
      cases advanced : sharedStep? state branch with
      | none => simp [sharedRun, advanced] at finished
      | some middle =>
          have later : sharedRun middle rest = some next := by
            simpa [sharedRun, advanced] using finished
          have count := step_nodes state middle branch advanced
          have tail := ih middle later
          simp only [callerCount]
          omega

theorem related_decode (source : Bank Context Control Frame)
    (shared : Shared Context Control Frame) (related : Related source shared) :
    source.decode = shared.decode := by
  have rootBound : source.root ≤ source.count := by
    simpa [related.root, related.count] using related.valid.2.1
  have same := related.lookup source.root rootBound
  rw [related.root] at same
  simp [Bank.decode, Shared.decode, related.root,
    same, related.pending]

variable {Call Answer : Type}

/-- A retained branching frontier can be run in either machine for any
physical allowance without changing its published prefix or residual. -/
theorem related_slice_exact (program : Program Context Control Call Frame Answer)
    (source : Bank Context Control Frame) (shared : Shared Context Control Frame)
    (related : Related source shared) (entered : Context × Control)
    (emitted : List (Context × Answer)) (allowance : Nat) :
    ((MachineCore.runSlice (sharedCore program) allowance
        (shared.finish related.valid entered emitted)).1.1.decode,
      (MachineCore.runSlice (sharedCore program) allowance
        (shared.finish related.valid entered emitted)).2) =
      MachineCore.runSlice (referenceCore program) allowance
        (source.decode.finish entered emitted) := by
  have sliced := slice_exact program allowance (shared.finish related.valid entered emitted)
  simpa only [finish_decode, related_decode source shared related] using sliced

theorem run_results_related (source result : Bank Context Control Frame)
    (shared target : Shared Context Control Frame) (related : Related source shared)
    (branches : List (BranchLayer Context Control Frame))
    (sourceFinished : sourceRun source branches = some result)
    (sharedFinished : sharedRun shared branches = some target) : Related result target := by
  have exactRun := run_exact source shared related branches
  rw [sourceFinished, sharedFinished] at exactRun
  cases exactRun with
  | moved final => exact final

/-- The installation theorem joins directly to bounded execution; no
re-elaboration of the entered control is part of this transition. -/
theorem run_then_slice_exact (program : Program Context Control Call Frame Answer)
    (source result : Bank Context Control Frame) (shared target : Shared Context Control Frame)
    (related : Related source shared) (branches : List (BranchLayer Context Control Frame))
    (sourceFinished : sourceRun source branches = some result)
    (sharedFinished : sharedRun shared branches = some target)
    (entered : Context × Control) (emitted : List (Context × Answer)) (allowance : Nat) :
    ∃ valid : target.Valid,
      ((MachineCore.runSlice (sharedCore program) allowance
          (target.finish valid entered emitted)).1.1.decode,
        (MachineCore.runSlice (sharedCore program) allowance
          (target.finish valid entered emitted)).2) =
        MachineCore.runSlice (referenceCore program) allowance
          (result.decode.finish entered emitted) := by
  have final := run_results_related source result shared target related branches
    sourceFinished sharedFinished
  exact ⟨final.valid, related_slice_exact program result target final entered emitted allowance⟩

/-- Switching representations between two slices preserves the paid prefix
and resumes the actual remaining tasks. -/
theorem related_split_exact (program : Program Context Control Call Frame Answer)
    (source : Bank Context Control Frame) (shared : Shared Context Control Frame)
    (related : Related source shared) (entered : Context × Control)
    (emitted : List (Context × Answer)) (before after : Nat) :
    (let first := MachineCore.runSlice (sharedCore program) before
        (shared.finish related.valid entered emitted)
     let later := MachineCore.runSlice (referenceCore program) after first.1.1.decode
     (later.1, first.2 + later.2)) =
      MachineCore.runSlice (referenceCore program) (before + after)
        (source.decode.finish entered emitted) := by
  have exactSlice := related_slice_exact program source shared related entered emitted before
  have states := congrArg Prod.fst exactSlice
  have counts := congrArg Prod.snd exactSlice
  dsimp only at states counts ⊢
  rw [states, counts]
  exact (MachineCore.runSlice_add (referenceCore program) before after _).symm

namespace Controls

abbrev TestControl := Instruction Unit (List Nat) Nat

def bank : Bank (List Nat) TestControl (List Nat) := ⟨fun _ => [], 0, 0, []⟩
def initial : Shared (List Nat) TestControl (List Nat) := ⟨[], 0, []⟩

theorem initial_related : Related bank initial := by
  refine ⟨?_, rfl, rfl, ?_, rfl⟩
  · simp [initial, Shared.Valid, Arena.Valid]
  · intro root bound
    have zero : root = 0 := by simpa [bank] using bound
    subst root
    simp [bank, initial]

def branches : List (BranchLayer (List Nat) TestControl (List Nat)) :=
  [⟨0, ⟨some [5, 5], [([30], .ret 11), ([30], .ret 11)], 0⟩⟩,
   ⟨1, ⟨some [7, 8], [([20], .ret 21)], 0⟩⟩,
   ⟨1, ⟨some [9, 10], [([25], .ret 9)], 0⟩⟩,
   ⟨1, ⟨some [11, 12], [], 0⟩⟩]

def built : Shared (List Nat) TestControl (List Nat) :=
  ⟨[([11, 12], 1), ([9, 10], 1), ([7, 8], 1), ([5, 5], 0)], 4,
    [⟨[25], .ret 9, 3⟩, ⟨[20], .ret 21, 2⟩,
     ⟨[30], .ret 11, 1⟩, ⟨[30], .ret 11, 1⟩]⟩

theorem branching_installation : sharedRun initial branches = some built := by
  rfl

theorem built_valid : built.Valid := by
  simp [built, Shared.Valid, Arena.Valid]

/-- The siblings have different heads but retain the same older caller. -/
theorem sibling_callers_share_the_old_root :
    built.arena.read 2 = some ([7, 8], 1) ∧
      built.arena.read 3 = some ([9, 10], 1) ∧
      built.arena.expand 2 = [[7, 8], [5, 5]] ∧
      built.arena.expand 3 = [[9, 10], [5, 5]] := by
  decide +kernel

/-- The branch installation has an actual corresponding source state. -/
theorem branching_has_source : ∃ source,
    sourceRun bank branches = some source ∧ Related source built := by
  have exactRun := run_exact bank initial initial_related branches
  rw [branching_installation] at exactRun
  cases result : sourceRun bank branches with
  | none => rw [result] at exactRun; cases exactRun
  | some source =>
      rw [result] at exactRun
      cases exactRun with
      | moved related => exact ⟨source, rfl, related⟩

def entered : List Nat × TestControl := ([1], .ret 1)

/-- Separate captured callers and duplicate alternatives survive execution. -/
theorem branching_answers_and_aliases :
    (MachineCore.runSlice (sharedCore PreparedSharedFrontier.Controls.program) 40
      (built.finish built_valid entered [])).1.1.emitted =
      [([1, 11, 12, 5, 5], 1), ([25, 9, 10, 5, 5], 9),
       ([20, 7, 8, 5, 5], 21), ([30, 5, 5], 11), ([30, 5, 5], 11)] := by
  decide +kernel

theorem out_of_range_parent_refused :
    sourceStep? bank ⟨2, ⟨some [7], [], 0⟩⟩ = none ∧
      sharedStep? initial ⟨2, ⟨some [7], [], 0⟩⟩ = none := by
  decide +kernel

/-- Pointing the second sibling through the first changes its caller stack. -/
theorem wrong_parent_is_observable :
    Arena.expand [([9, 10], 2), ([7, 8], 1), ([5, 5], 0)] 3 ≠
      built.arena.expand 3 := by
  decide +kernel

end Controls

end Mettapedia.Machines.PreparedBranchedFrontier
