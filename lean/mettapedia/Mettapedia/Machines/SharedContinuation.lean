import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Mettapedia.Machines.ResumableRegion
import Mettapedia.Machines.SnapshotBatch
import Mettapedia.Machines.Cursor.ProducerOccurrenceLog

/-!
# Shared return continuations with branch-local contexts

A return continuation and a search alternative have different roles. A return
resumes a caller on each callee answer; an alternative retains a branch's own
context. This machine keeps both, including after an answer has been published.

The reference carries lists of return frames. The second representation stores
immutable frames once in a topologically ordered arena and puts roots on the
frontier. Its step function follows a root without expanding the saved stack.
Decoding is reserved for observation and representation transfer.

The list presentation of the arena specifies stable natural-number addresses;
it does not claim constant-time lookup. A native array is a further realization.
Contexts may contain store images, snapshots and ownership handles. Their native
validity and the semantics of `branches` and `resume` remain separate obligations.

The two representations also inhabit `MachineCore`: bounded slices retain the
complete frontier and emitted prefix, stop at exhaustion, and count only steps
actually performed. The shared arena allocates at most one frame node per step,
regardless of branch width. These are model transition and node counts, not
native instruction, byte, synchronization or elapsed-time costs.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SharedContinuation

variable {Frame : Type}

/-- Newest node first. Root zero is the empty continuation; a newly allocated
node has address `older.length + 1`. Nodes only refer to older nodes. -/
abbrev Arena (Frame : Type) := List (Frame × Nat)

def Arena.Valid : Arena Frame → Prop
  | [] => True
  | (_, parent) :: older => Arena.Valid older ∧ parent ≤ older.length

def Arena.read : Arena Frame → Nat → Option (Frame × Nat)
  | [], _ => none
  | node :: older, root =>
      if root = older.length + 1 then some node else Arena.read older root

def Arena.expand : Arena Frame → Nat → List Frame
  | [], _ => []
  | (frame, parent) :: older, root =>
      if root = older.length + 1 then frame :: Arena.expand older parent
      else Arena.expand older root

@[simp] theorem Arena.read_zero (arena : Arena Frame) : arena.read 0 = none := by
  induction arena with
  | nil => rfl
  | cons node older ih => simp [read, ih]

@[simp] theorem Arena.expand_zero (arena : Arena Frame) : arena.expand 0 = [] := by
  induction arena with
  | nil => rfl
  | cons node older ih => simp [expand, ih]

theorem Arena.read_old (arena : Arena Frame) (frame : Frame) (parent root : Nat)
    (old : root ≤ arena.length) :
    Arena.read ((frame, parent) :: arena) root = arena.read root := by
  simp [read, show root ≠ arena.length + 1 by omega]

theorem Arena.expand_old (arena : Arena Frame) (frame : Frame) (parent root : Nat)
    (old : root ≤ arena.length) :
    Arena.expand ((frame, parent) :: arena) root = arena.expand root := by
  simp [expand, show root ≠ arena.length + 1 by omega]

theorem Arena.read_bounds (arena : Arena Frame) (valid : arena.Valid)
    {root parent : Nat} {frame : Frame} (found : arena.read root = some (frame, parent)) :
    0 < root ∧ root ≤ arena.length ∧ parent < root := by
  induction arena with
  | nil => simp [read] at found
  | cons node older ih =>
      rcases node with ⟨head, previous⟩
      rcases valid with ⟨valid, bound⟩
      by_cases atHead : root = older.length + 1
      · simp [read, atHead] at found
        rcases found with ⟨rfl, rfl⟩
        simp only [List.length_cons]
        omega
      · have foundOld : Arena.read older root = some (frame, parent) := by
          simpa [read, atHead] using found
        have := ih valid foundOld
        simp only [List.length_cons]
        omega

theorem Arena.read_exists (arena : Arena Frame) {root : Nat}
    (positive : 0 < root) (bound : root ≤ arena.length) :
    ∃ frame parent, arena.read root = some (frame, parent) := by
  induction arena with
  | nil => simp at bound; omega
  | cons node older ih =>
      by_cases atHead : root = older.length + 1
      · exact ⟨node.1, node.2, by simp [read, atHead]⟩
      · have := ih (by simp only [List.length_cons] at bound; omega)
        simpa [read, atHead] using this

theorem Arena.expand_read (arena : Arena Frame) (valid : arena.Valid)
    {root parent : Nat} {frame : Frame} (found : arena.read root = some (frame, parent)) :
    arena.expand root = frame :: arena.expand parent := by
  induction arena with
  | nil => simp [read] at found
  | cons node older ih =>
      rcases node with ⟨head, previous⟩
      rcases valid with ⟨valid, bound⟩
      by_cases atHead : root = older.length + 1
      · have same : head = frame ∧ previous = parent := by
          simpa [read, atHead] using found
        rcases same with ⟨rfl, rfl⟩
        rw [expand_old older head previous previous bound]
        simp [expand, atHead]
      · have foundOld : Arena.read older root = some (frame, parent) := by
          simpa [read, atHead] using found
        have bounds := read_bounds older valid foundOld
        rw [expand_old older head previous parent (by omega)]
        simpa [expand, atHead] using ih valid foundOld

theorem Arena.expand_eq_nil_iff (arena : Arena Frame) (valid : arena.Valid)
    (root : Nat) (bound : root ≤ arena.length) :
    arena.expand root = [] ↔ root = 0 := by
  constructor
  · intro empty
    by_contra nonzero
    obtain ⟨frame, parent, found⟩ := arena.read_exists (by omega) bound
    rw [arena.expand_read valid found] at empty
    cases empty
  · rintro rfl
    exact arena.expand_zero

/-- Reify a return stack into fresh nodes. This is a boundary conversion,
not an operation performed at each native step. -/
def Arena.save (arena : Arena Frame) : List Frame → Arena Frame × Nat
  | [] => (arena, 0)
  | frame :: rest =>
      let saved := arena.save rest
      ((frame, saved.2) :: saved.1, saved.1.length + 1)

theorem Arena.save_spec (arena : Arena Frame) (valid : arena.Valid) (frames : List Frame) :
    (arena.save frames).1.Valid ∧
    (arena.save frames).2 ≤ (arena.save frames).1.length ∧
    (arena.save frames).1.expand (arena.save frames).2 = frames ∧
    (arena.save frames).1.length = arena.length + frames.length ∧
    (∀ root, root ≤ arena.length →
      (arena.save frames).1.expand root = arena.expand root) := by
  induction frames with
  | nil => simp [save, valid]
  | cons frame rest ih =>
      rcases ih with ⟨hv, hb, he, hl, ho⟩
      simp only [save, List.length_cons]
      refine ⟨⟨hv, hb⟩, le_rfl, ?_, by omega, ?_⟩
      · simp [expand, he]
      · intro root bound
        rw [expand_old _ frame _ root (by omega)]
        exact ho root bound

theorem Arena.valid_drop (arena : Arena Frame) (valid : arena.Valid) (count : Nat) :
    Arena.Valid (arena.drop count) := by
  induction count generalizing arena with
  | zero => exact valid
  | succ count ih =>
      cases arena with
      | nil => trivial
      | cons node older => exact ih older valid.1

/-- A root below a region mark can only reach nodes below that mark. -/
theorem Arena.expand_drop (arena : Arena Frame) (count root : Nat)
    (bound : root ≤ (arena.drop count).length) :
    Arena.expand (arena.drop count) root = arena.expand root := by
  induction count generalizing arena with
  | zero => rfl
  | succ count ih =>
      cases arena with
      | nil => rfl
      | cons node older =>
          rcases node with ⟨frame, parent⟩
          have smaller : root ≤ older.length := by
            have reduced : root ≤ older.length - count := by
              simpa only [List.drop_succ_cons, List.length_drop] using bound
            exact reduced.trans (Nat.sub_le older.length count)
          rw [expand_old older frame parent root smaller]
          exact ih older bound

variable {Context Control Call Answer : Type}

/-- One semantic control boundary. A return is not a published answer until
the return stack is empty. Failure is only exhaustion of this alternative. -/
inductive Instruction (Call Frame Answer : Type) where
  | ret (value : Answer)
  | fail
  | call (callee : Call) (returnFrame : Frame)
  | tail (callee : Call)

/-- The same operational fragment is executed in both representations.
Context updates occur through these operations, never through an arena node. -/
structure Program (Context Control Call Frame Answer : Type) where
  inspect : Control → Instruction Call Frame Answer
  branches : Context → Call → List (Context × Control)
  resume : Context → Frame → Answer → Context × Control

structure Task (Context Control Frame : Type) where
  context : Context
  control : Control
  returns : List Frame

structure State (Context Control Frame Answer : Type) where
  frontier : List (Task Context Control Frame)
  emitted : List (Context × Answer)

def step (program : Program Context Control Call Frame Answer)
    (state : State Context Control Frame Answer) : State Context Control Frame Answer :=
  match state.frontier with
  | [] => state
  | task :: rest =>
      match program.inspect task.control with
      | .ret value =>
          match task.returns with
          | [] => ⟨rest, state.emitted ++ [(task.context, value)]⟩
          | frame :: pending =>
              let next := program.resume task.context frame value
              ⟨⟨next.1, next.2, pending⟩ :: rest, state.emitted⟩
      | .fail => ⟨rest, state.emitted⟩
      | .call callee frame =>
          ⟨(program.branches task.context callee).map (fun next =>
            ⟨next.1, next.2, frame :: task.returns⟩) ++ rest, state.emitted⟩
      | .tail callee =>
          ⟨(program.branches task.context callee).map (fun next =>
            ⟨next.1, next.2, task.returns⟩) ++ rest, state.emitted⟩

structure RootTask (Context Control : Type) where
  context : Context
  control : Control
  root : Nat

structure ArenaState (Context Control Frame Answer : Type) where
  arena : Arena Frame
  frontier : List (RootTask Context Control)
  emitted : List (Context × Answer)

def ArenaState.Valid (state : ArenaState Context Control Frame Answer) : Prop :=
  state.arena.Valid ∧ ∀ task ∈ state.frontier, task.root ≤ state.arena.length

def RootTask.decode (arena : Arena Frame) (task : RootTask Context Control) :
    Task Context Control Frame := ⟨task.context, task.control, arena.expand task.root⟩

def ArenaState.decode (state : ArenaState Context Control Frame Answer) :
    State Context Control Frame Answer :=
  ⟨state.frontier.map (RootTask.decode state.arena), state.emitted⟩

/-- Invalid addresses refuse execution (`none`); they are not interpreted as
logical failure or an empty answer collection. Well-formed states never refuse. -/
def arenaStep (program : Program Context Control Call Frame Answer)
    (state : ArenaState Context Control Frame Answer) :
    Option (ArenaState Context Control Frame Answer) :=
  match state.frontier with
  | [] => some state
  | task :: rest =>
      match program.inspect task.control with
      | .ret value =>
          if task.root = 0 then
            some ⟨state.arena, rest, state.emitted ++ [(task.context, value)]⟩
          else (state.arena.read task.root).map fun (frame, parent) =>
            let next := program.resume task.context frame value
            ⟨state.arena, ⟨next.1, next.2, parent⟩ :: rest, state.emitted⟩
      | .fail => some ⟨state.arena, rest, state.emitted⟩
      | .call callee frame =>
          some ⟨(frame, task.root) :: state.arena,
            (program.branches task.context callee).map (fun next =>
              ⟨next.1, next.2, state.arena.length + 1⟩) ++ rest, state.emitted⟩
      | .tail callee =>
          some ⟨state.arena, (program.branches task.context callee).map (fun next =>
            ⟨next.1, next.2, task.root⟩) ++ rest, state.emitted⟩

theorem decode_old_frontier (arena : Arena Frame) (frame : Frame) (parent : Nat)
    (frontier : List (RootTask Context Control))
    (bounded : ∀ task ∈ frontier, task.root ≤ arena.length) :
    frontier.map (RootTask.decode ((frame, parent) :: arena)) =
      frontier.map (RootTask.decode arena) := by
  apply List.map_congr_left
  intro task member
  simp only [RootTask.decode, Arena.expand_old arena frame parent task.root (bounded task member)]

/-- An arena step exists, retains well-formed roots and decodes to exactly one
reference step. This proves both preservation and no invention of behavior. -/
theorem arenaStep_exact (program : Program Context Control Call Frame Answer)
    (state : ArenaState Context Control Frame Answer) (valid : state.Valid) :
    ∃ next, arenaStep program state = some next ∧ next.Valid ∧
      next.decode = step program state.decode := by
  rcases state with ⟨arena, frontier, emitted⟩
  rcases valid with ⟨validArena, bounded⟩
  cases frontier with
  | nil => exact ⟨_, rfl, ⟨validArena, bounded⟩, rfl⟩
  | cons task rest =>
      have rootBound := bounded task (by simp)
      have restBound : ∀ task ∈ rest, task.root ≤ arena.length :=
        fun other member => bounded other (by simp [member])
      cases instruction : program.inspect task.control with
      | ret value =>
          by_cases empty : task.root = 0
          · refine ⟨⟨arena, rest, emitted ++ [(task.context, value)]⟩,
              by simp [arenaStep, instruction, empty],
              ⟨validArena, restBound⟩, ?_⟩
            simp [step, ArenaState.decode, RootTask.decode, instruction, empty]
          · obtain ⟨frame, parent, found⟩ := arena.read_exists (by omega) rootBound
            have bounds := arena.read_bounds validArena found
            refine ⟨⟨arena, ⟨(program.resume task.context frame value).1,
              (program.resume task.context frame value).2, parent⟩ :: rest, emitted⟩,
              by simp [arenaStep, instruction, empty, found], ?_, ?_⟩
            · refine ⟨validArena, ?_⟩
              intro other member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · dsimp; omega
              · exact restBound other member
            · simp [step, ArenaState.decode, RootTask.decode, instruction,
                arena.expand_read validArena found]
      | fail =>
          exact ⟨⟨arena, rest, emitted⟩, by simp [arenaStep, instruction], ⟨validArena, restBound⟩,
            by simp [step, ArenaState.decode, RootTask.decode, instruction]⟩
      | call callee frame =>
          refine ⟨⟨(frame, task.root) :: arena,
            (program.branches task.context callee).map (fun next =>
              ⟨next.1, next.2, arena.length + 1⟩) ++ rest, emitted⟩,
            by simp [arenaStep, instruction], ?_, ?_⟩
          · refine ⟨⟨validArena, rootBound⟩, ?_⟩
            intro other member
            simp only [List.mem_append, List.mem_map] at member
            rcases member with ⟨next, _, rfl⟩ | member
            · simp
            · have := restBound other member
              simp only [List.length_cons]; omega
          · simp only [ArenaState.decode, List.map_append]
            rw [decode_old_frontier arena frame task.root rest restBound]
            simp [step, RootTask.decode, instruction, Arena.expand, List.map_map]
      | tail callee =>
          refine ⟨⟨arena, (program.branches task.context callee).map (fun next =>
            ⟨next.1, next.2, task.root⟩) ++ rest, emitted⟩,
            by simp [arenaStep, instruction], ?_, ?_⟩
          · refine ⟨validArena, ?_⟩
            intro other member
            simp only [List.mem_append, List.mem_map] at member
            rcases member with ⟨next, _, rfl⟩ | member
            · exact rootBound
            · exact restBound other member
          · simp [step, ArenaState.decode, RootTask.decode, instruction, List.map_map]

/-- The checked carrier is for already admitted native states. An untrusted
root still goes through the explicit refusal result of `arenaStep`. -/
abbrev CheckedState (Context Control Frame Answer : Type) :=
  { state : ArenaState Context Control Frame Answer // state.Valid }

def checkedStep (program : Program Context Control Call Frame Answer)
    (state : CheckedState Context Control Frame Answer) :
    CheckedState Context Control Frame Answer :=
  let proof := arenaStep_exact program state.1 state.2
  let next := (arenaStep program state.1).get (by
    obtain ⟨next, found, _, _⟩ := proof
    simp [found])
  ⟨next, by
    dsimp only [next]
    obtain ⟨next, found, valid, _⟩ := proof
    simpa only [found, Option.get_some] using valid⟩

theorem decode_checkedStep (program : Program Context Control Call Frame Answer)
    (state : CheckedState Context Control Frame Answer) :
    (checkedStep program state).1.decode = step program state.1.decode := by
  obtain ⟨next, found, _, exactStep⟩ := arenaStep_exact program state.1 state.2
  simpa [checkedStep, found] using exactStep

/-- Import an arbitrary suspended reference frontier, including pending
returns. Already imported roots remain valid when subsequent nodes are added. -/
def saveFrontier (arena : Arena Frame) : List (Task Context Control Frame) →
    Arena Frame × List (RootTask Context Control)
  | [] => (arena, [])
  | task :: rest =>
      let saved := arena.save task.returns
      let later := saveFrontier saved.1 rest
      (later.1, ⟨task.context, task.control, saved.2⟩ :: later.2)

theorem saveFrontier_spec (arena : Arena Frame) (valid : arena.Valid)
    (frontier : List (Task Context Control Frame)) :
    (saveFrontier arena frontier).1.Valid ∧
    (∀ task ∈ (saveFrontier arena frontier).2,
      task.root ≤ (saveFrontier arena frontier).1.length) ∧
    (saveFrontier arena frontier).2.map
      (RootTask.decode (saveFrontier arena frontier).1) = frontier ∧
    arena.length ≤ (saveFrontier arena frontier).1.length ∧
    (∀ root, root ≤ arena.length →
      (saveFrontier arena frontier).1.expand root = arena.expand root) := by
  induction frontier generalizing arena with
  | nil => simp [saveFrontier, valid]
  | cons task rest ih =>
      obtain ⟨savedValid, savedBound, savedExact, savedLength, savedOld⟩ :=
        arena.save_spec valid task.returns
      obtain ⟨laterValid, laterBound, laterExact, laterLength, laterOld⟩ :=
        ih (arena.save task.returns).1 savedValid
      simp only [saveFrontier, List.map_cons]
      refine ⟨laterValid, ?_, ?_, by omega, ?_⟩
      · intro other member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · dsimp; omega
        · exact laterBound other member
      · rw [laterExact]
        simp only [RootTask.decode, laterOld _ savedBound, savedExact]
      · intro root bound
        rw [laterOld root (by omega), savedOld root bound]

def encode (state : State Context Control Frame Answer) :
    CheckedState Context Control Frame Answer :=
  let saved := saveFrontier [] state.frontier
  ⟨⟨saved.1, saved.2, state.emitted⟩,
    (saveFrontier_spec [] (by trivial) state.frontier).1,
    (saveFrontier_spec [] (by trivial) state.frontier).2.1⟩

@[simp] theorem decode_encode (state : State Context Control Frame Answer) :
    (encode state).1.decode = state := by
  have exactFrontier := (saveFrontier_spec [] (by trivial) state.frontier).2.2.1
  dsimp only [encode, ArenaState.decode]
  rw [exactFrontier]

/-- Execute an already suspended configuration, including its emitted prefix.
An empty frontier is final rather than a repeatedly charged no-op. -/
def referenceCore (program : Program Context Control Call Frame Answer) :
    MachineCore (State Context Control Frame Answer) where
  State := State Context Control Frame Answer
  load := id
  step state := if state.frontier = [] then none else some (step program state)

/-- The same bounded interface with checked shared roots. Loading converts a
captured configuration once; each subsequent slice resumes its retained arena. -/
def sharedCore (program : Program Context Control Call Frame Answer) :
    MachineCore (State Context Control Frame Answer) where
  State := CheckedState Context Control Frame Answer
  load := encode
  step state := if state.1.frontier = [] then none else some (checkedStep program state)

/-- Ignoring idle allowance changes neither the retained frontier nor the
published prefix. This equality concerns the endpoint; `runSlice` separately
counts only transitions actually performed. -/
theorem reference_slice_iterate (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : State Context Control Frame Answer) :
    (MachineCore.runSlice (referenceCore program) fuel state).1 =
      (step program)^[fuel] state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      by_cases final : state.frontier = []
      · have idle : step program state = state := by simp [step, final]
        simpa only [MachineCore.runSlice, referenceCore, final, ↓reduceIte] using
          (Function.iterate_fixed idle (fuel + 1)).symm
      · simp only [MachineCore.runSlice, referenceCore, final, ↓reduceIte]
        change (MachineCore.runSlice (referenceCore program) fuel (step program state)).1 =
          (step program)^[fuel + 1] state
        rw [ih, Function.iterate_succ_apply]

theorem core_step_exact (program : Program Context Control Call Frame Answer)
    (state : CheckedState Context Control Frame Answer) :
    ((sharedCore program).step state).map (fun next => next.1.decode) =
      (referenceCore program).step state.1.decode := by
  rcases state with ⟨⟨arena, frontier, emitted⟩, valid⟩
  cases frontier with
  | nil => rfl
  | cons task rest =>
      simpa [sharedCore, referenceCore, ArenaState.decode] using
        congrArg some (decode_checkedStep program ⟨⟨arena, task :: rest, emitted⟩, valid⟩)

/-- Equality of complete bounded readouts: residual contexts, controls, return
stacks, ordered answer occurrences and actual transition counts all survive. -/
theorem slice_exact (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : CheckedState Context Control Frame Answer) :
    ((MachineCore.runSlice (sharedCore program) fuel state).1.1.decode,
      (MachineCore.runSlice (sharedCore program) fuel state).2) =
        MachineCore.runSlice (referenceCore program) fuel state.1.decode :=
  MachineCore.runSlice_decode (referenceCore program) (sharedCore program)
    (fun next => next.1.decode) (core_step_exact program) fuel state

theorem slice_encode_exact (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : State Context Control Frame Answer) :
    ((MachineCore.runSlice (sharedCore program) fuel (encode state)).1.1.decode,
      (MachineCore.runSlice (sharedCore program) fuel (encode state)).2) =
        MachineCore.runSlice (referenceCore program) fuel state := by
  simpa only [decode_encode] using slice_exact program fuel (encode state)

/-- Leaving the shared representation between slices neither restarts the
query nor repeats a debit. It preserves partial answers and pending returns. -/
theorem slice_transfer_exact (program : Program Context Control Call Frame Answer)
    (before after : Nat) (state : State Context Control Frame Answer) :
    (let earlier := MachineCore.runSlice (sharedCore program) before (encode state)
     let later := MachineCore.runSlice (referenceCore program) after earlier.1.1.decode
     (later.1, earlier.2 + later.2)) =
      MachineCore.runSlice (referenceCore program) (before + after) state := by
  have exactSlice := slice_encode_exact program before state
  have states := congrArg Prod.fst exactSlice
  have counts := congrArg Prod.snd exactSlice
  dsimp only at states counts ⊢
  rw [states, counts]
  exact (MachineCore.runSlice_add (referenceCore program) before after state).symm


section ReturnElision

variable {Context Control Call Frame Answer : Type}

/-- Only a return frame that retains its context and answer can be elided at
this observation. Native receiver identities, effects and authority need
their own realization laws; this predicate does not erase those obligations. -/
structure TransparentReturns (program : Program Context Control Call Frame Answer) where
  erase : Frame → Bool
  resume_context : ∀ context frame answer, erase frame = true →
    (program.resume context frame answer).1 = context
  resume_return : ∀ context frame answer, erase frame = true →
    program.inspect (program.resume context frame answer).2 = .ret answer

def TransparentReturns.instruction
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) : Instruction Call Frame Answer →
      Instruction Call Frame Answer
  | .call callee frame => if law.erase frame then .tail callee else .call callee frame
  | other => other

/-- The fused machine is specified by the existing instruction semantics;
calls with a transparent receiving frame become tail calls. -/
def TransparentReturns.program
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) :
    Program Context (Instruction Call Frame Answer) Call Frame Answer where
  inspect := id
  branches context callee := (program.branches context callee).map fun next =>
    (next.1, law.instruction (program.inspect next.2))
  resume context frame answer :=
    let next := program.resume context frame answer
    (next.1, law.instruction (program.inspect next.2))

def TransparentReturns.task
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (task : Task Context Control Frame) :
    Task Context (Instruction Call Frame Answer) Frame :=
  ⟨task.context, law.instruction (program.inspect task.control),
    task.returns.filter fun frame => !law.erase frame⟩

def TransparentReturns.state
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (state : State Context Control Frame Answer) :
    State Context (Instruction Call Frame Answer) Frame Answer :=
  ⟨state.frontier.map law.task, state.emitted⟩

def State.headReturnDepth (state : State Context Control Frame Answer) : Nat :=
  match state.frontier with
  | [] => 0
  | current :: _ => current.returns.length

def TransparentReturns.administrative
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (state : State Context Control Frame Answer) : Bool :=
  match state.frontier with
  | [] => false
  | current :: _ =>
      match program.inspect current.control, current.returns with
      | .ret _, frame :: _ => law.erase frame
      | _, _ => false

/-- An elided return consumes a real saved frame. It cannot loop invisibly or
lose the still-running task. -/
theorem TransparentReturns.administrative_step
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (state : State Context Control Frame Answer)
    (administrative : law.administrative state = true) :
    law.state (step program state) = law.state state ∧
      (step program state).frontier ≠ [] ∧
      (step program state).headReturnDepth + 1 = state.headReturnDepth := by
  rcases state with ⟨frontier, emitted⟩
  cases frontier with
  | nil => simp [TransparentReturns.administrative] at administrative
  | cons current rest =>
      cases inspected : program.inspect current.control with
      | fail => simp [TransparentReturns.administrative, inspected] at administrative
      | call callee frame =>
          simp [TransparentReturns.administrative, inspected] at administrative
      | tail callee => simp [TransparentReturns.administrative, inspected] at administrative
      | ret value =>
        cases returns : current.returns with
        | nil => simp [TransparentReturns.administrative, inspected, returns] at administrative
        | cons frame pending =>
            have erased : law.erase frame = true := by
              simpa [TransparentReturns.administrative, inspected, returns] using administrative
            refine ⟨?_, ?_, ?_⟩
            · simp [step, TransparentReturns.state, TransparentReturns.task,
                TransparentReturns.instruction, inspected, returns, erased,
                law.resume_context current.context frame value erased,
                law.resume_return current.context frame value erased]
            · simp [step, inspected, returns]
            · simp [step, State.headReturnDepth, inspected, returns]

/-- A nonadministrative source dispatch performs the independently defined
fused dispatch. Classification is by the actual instruction and return stack. -/
theorem TransparentReturns.visible_step
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (state : State Context Control Frame Answer)
    (visible : law.administrative state = false) :
    law.state (step program state) = step law.program (law.state state) := by
  rcases state with ⟨frontier, emitted⟩
  cases frontier with
  | nil => rfl
  | cons current rest =>
      cases inspected : program.inspect current.control with
      | fail =>
          simp [step, TransparentReturns.state, TransparentReturns.task,
            TransparentReturns.instruction, TransparentReturns.program, inspected]
      | tail callee =>
          simp [step, TransparentReturns.state, TransparentReturns.task,
            TransparentReturns.instruction, TransparentReturns.program, inspected,
            List.map_map, Function.comp_def]
      | call callee frame =>
          cases erased : law.erase frame <;>
            simp [step, TransparentReturns.state, TransparentReturns.task,
              TransparentReturns.instruction, TransparentReturns.program, inspected,
              erased, List.map_map, Function.comp_def]
      | ret value =>
          cases returns : current.returns with
          | nil =>
              simp [step, TransparentReturns.state, TransparentReturns.task,
                TransparentReturns.instruction, TransparentReturns.program, inspected, returns]
          | cons frame pending =>
              have erased : law.erase frame = false := by
                simpa [TransparentReturns.administrative, inspected, returns] using visible
              simp [step, TransparentReturns.state, TransparentReturns.task,
                TransparentReturns.instruction, TransparentReturns.program, inspected,
                returns, erased]

/-- Classify readback through the same administrative and visible proofs. -/
theorem TransparentReturns.step_readback
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (state : State Context Control Frame Answer) :
    law.state (step program state) = law.state state ∨
      law.state (step program state) = step law.program (law.state state) := by
  cases classified : law.administrative state with
  | false => exact .inr (law.visible_step state classified)
  | true => exact .inl (law.administrative_step state classified).1

theorem TransparentReturns.core_readback
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (state next : State Context Control Frame Answer)
    (transition : (referenceCore program).step state = some next) :
    law.state next = law.state state ∨
      (referenceCore law.program).step (law.state state) = some (law.state next) := by
  rcases state with ⟨frontier, emitted⟩
  cases frontier with
  | nil => simp [referenceCore] at transition
  | cons current rest =>
      have nextEq : next = step program ⟨current :: rest, emitted⟩ := by
        simpa [referenceCore] using transition.symm
      subst next
      rcases law.step_readback ⟨current :: rest, emitted⟩ with unchanged | advanced
      · exact .inl unchanged
      · right
        simpa [referenceCore, TransparentReturns.state] using congrArg some advanced.symm

/-- Every implementation slice has an exact projected endpoint in the fused
machine, including its ordered answer occurrences and remaining opaque frames.
Different dispatch counts remain explicit. No converse productivity is inferred
from this finite-prefix theorem. -/
theorem TransparentReturns.slice_readback
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (fuel : Nat)
    (state : State Context Control Frame Answer) :
    ∃ used, used ≤ (MachineCore.runSlice (referenceCore program) fuel state).2 ∧
      MachineCore.runSlice (referenceCore law.program) used (law.state state) =
        (law.state (MachineCore.runSlice (referenceCore program) fuel state).1, used) :=
  MachineCore.runSlice_decode_stuttering (referenceCore law.program) (referenceCore program)
    law.state law.core_readback fuel state

/-- Every fused step can be implemented from the supplied uncompressed state.
Only the transparent return prefix is drained, bounded by its actual depth;
no earlier caller, answer prefix or unrelated alternative is reconstructed. -/
theorem TransparentReturns.realizes_step
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (state : State Context Control Frame Answer)
    (active : state.frontier ≠ []) :
    ∃ ticks, 0 < ticks ∧ ticks ≤ state.headReturnDepth + 1 ∧
      (MachineCore.runSlice (referenceCore program) ticks state).2 = ticks ∧
      law.state (MachineCore.runSlice (referenceCore program) ticks state).1 =
        step law.program (law.state state) := by
  generalize depthEq : state.headReturnDepth = depth
  induction depth using Nat.strong_induction_on generalizing state with
  | h depth ih =>
      have transition : (referenceCore program).step state = some (step program state) := by
        cases frontierEq : state.frontier with
        | nil => exact False.elim (active frontierEq)
        | cons current rest => simp [referenceCore, frontierEq]
      cases classified : law.administrative state with
      | false =>
          refine ⟨1, by omega, by omega, ?_, ?_⟩
          · simp [MachineCore.runSlice, transition]
          · simpa only [MachineCore.runSlice, transition] using law.visible_step state classified
      | true =>
          obtain ⟨unchanged, stillActive, reduced⟩ := law.administrative_step state classified
          have smaller : (step program state).headReturnDepth < depth := by omega
          obtain ⟨ticks, positive, bounded, paid, realized⟩ :=
            ih (step program state).headReturnDepth smaller (step program state) stillActive rfl
          refine ⟨ticks + 1, by omega, by omega, ?_, ?_⟩
          · simpa only [MachineCore.runSlice, transition] using congrArg (· + 1) paid
          · simpa only [MachineCore.runSlice, transition, unchanged] using realized

/-- Return elision preserves finality as well as intermediate frontiers. -/
theorem TransparentReturns.final_readback
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (state : State Context Control Frame Answer) :
    (referenceCore law.program).step (law.state state) = none ↔
      (referenceCore program).step state = none := by
  rcases state with ⟨frontier, emitted⟩
  cases frontier <;> simp [referenceCore, TransparentReturns.state]

theorem TransparentReturns.core_realizes
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (state : State Context Control Frame Answer)
    (next : State Context (Instruction Call Frame Answer) Frame Answer)
    (transition : (referenceCore law.program).step (law.state state) = some next) :
    ∃ ticks, 0 < ticks ∧
      (MachineCore.runSlice (referenceCore program) ticks state).2 = ticks ∧
      law.state (MachineCore.runSlice (referenceCore program) ticks state).1 = next := by
  rcases state with ⟨frontier, emitted⟩
  cases frontier with
  | nil => simp [referenceCore, TransparentReturns.state] at transition
  | cons current rest =>
      obtain ⟨ticks, positive, _, paid, endpoint⟩ :=
        law.realizes_step ⟨current :: rest, emitted⟩ (by simp)
      have nextEq : next = step law.program (law.state ⟨current :: rest, emitted⟩) := by
        simpa [referenceCore, TransparentReturns.state] using transition.symm
      exact ⟨ticks, positive, paid, endpoint.trans nextEq.symm⟩

/-- Forward correspondence composes across an arbitrary finite fused slice.
The original state is resumed in place; no query is restarted. -/
theorem TransparentReturns.realizes_slice
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (fuel : Nat)
    (state : State Context Control Frame Answer) :
    ∃ ticks,
      (MachineCore.runSlice (referenceCore law.program) fuel (law.state state)).2 ≤ ticks ∧
      (MachineCore.runSlice (referenceCore program) ticks state).2 = ticks ∧
      law.state (MachineCore.runSlice (referenceCore program) ticks state).1 =
        (MachineCore.runSlice (referenceCore law.program) fuel (law.state state)).1 :=
  MachineCore.runSlice_realizes (referenceCore law.program) (referenceCore program)
    law.state law.core_realizes fuel state

/-- The existing shared arena realizes the same return-elision readback;
no second arena semantics or copying rule is introduced. -/
theorem TransparentReturns.shared_slice_readback
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (fuel : Nat)
    (state : CheckedState Context Control Frame Answer) :
    ∃ used, used ≤ (MachineCore.runSlice (sharedCore program) fuel state).2 ∧
      MachineCore.runSlice (referenceCore law.program) used (law.state state.1.decode) =
        (law.state (MachineCore.runSlice (sharedCore program) fuel state).1.1.decode, used) := by
  have exactSlice := slice_exact program fuel state
  have states := congrArg Prod.fst exactSlice
  have counts := congrArg Prod.snd exactSlice
  dsimp only at states counts
  rw [states, counts]
  exact law.slice_readback fuel state.1.decode

/-- A fused endpoint is also reachable through actual checked shared-arena
execution, with its separately counted implementation dispatches. -/
theorem TransparentReturns.realizes_shared_slice
    {program : Program Context Control Call Frame Answer}
    (law : TransparentReturns program) (fuel : Nat)
    (state : CheckedState Context Control Frame Answer) :
    ∃ ticks,
      (MachineCore.runSlice (referenceCore law.program) fuel
        (law.state state.1.decode)).2 ≤ ticks ∧
      (MachineCore.runSlice (sharedCore program) ticks state).2 = ticks ∧
      law.state (MachineCore.runSlice (sharedCore program) ticks state).1.1.decode =
        (MachineCore.runSlice (referenceCore law.program) fuel
          (law.state state.1.decode)).1 := by
  obtain ⟨ticks, bound, paid, endpoint⟩ := law.realizes_slice fuel state.1.decode
  have exactSlice := slice_exact program ticks state
  have states := congrArg Prod.fst exactSlice
  have counts := congrArg Prod.snd exactSlice
  dsimp only at states counts
  exact ⟨ticks, bound, counts.trans paid, (congrArg law.state states).trans endpoint⟩

end ReturnElision

/-! ## Independently owned ready occurrences -/

section ReadyOccurrences

universe uId
variable {Id : Type uId}

/-- The receipt stays with the full private reference continuation. -/
abbrev ReferenceSliceCell := Nat × State Context Control Frame Answer

/-- The private arena and every frontier root stay with the paid continuation. -/
abbrev SharedSliceCell := Nat × CheckedState Context Control Frame Answer

def decodeSliceCell (cell : SharedSliceCell (Context := Context) (Control := Control)
    (Frame := Frame) (Answer := Answer)) :
    ReferenceSliceCell (Context := Context) (Control := Control) (Frame := Frame) (Answer := Answer) :=
  (cell.1, cell.2.1.decode)

def resumeReferenceSlice (program : Program Context Control Call Frame Answer)
    (quantum : Nat) (cell : ReferenceSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer)) :
    ReferenceSliceCell (Context := Context) (Control := Control) (Frame := Frame) (Answer := Answer) :=
  let next := MachineCore.runSlice (referenceCore program) quantum cell.2
  (cell.1 + next.2, next.1)

def resumeSharedSlice (program : Program Context Control Call Frame Answer)
    (quantum : Nat) (cell : SharedSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer)) :
    SharedSliceCell (Context := Context) (Control := Control) (Frame := Frame) (Answer := Answer) :=
  let next := MachineCore.runSlice (sharedCore program) quantum cell.2
  (cell.1 + next.2, next.1)

/-- The arena realization preserves earlier charges and the complete private
world. The reference slice executes its list machine independently. -/
theorem resumeSharedSlice_decode (program : Program Context Control Call Frame Answer)
    (quantum : Nat) (cell : SharedSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer)) :
    decodeSliceCell (resumeSharedSlice program quantum cell) =
      resumeReferenceSlice program quantum (decodeSliceCell cell) := by
  have exactSlice := slice_exact program quantum cell.2
  have states := congrArg Prod.fst exactSlice
  have charges := congrArg Prod.snd exactSlice
  dsimp only at states charges
  dsimp only [decodeSliceCell, resumeSharedSlice, resumeReferenceSlice]
  rw [states, charges]

/-- Repeated grants continue the paid arena rather than loading the query again. -/
theorem resumeSharedSlice_add (program : Program Context Control Call Frame Answer)
    (first second : Nat) (cell : SharedSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer)) :
    resumeSharedSlice program (first + second) cell =
      resumeSharedSlice program second (resumeSharedSlice program first cell) := by
  dsimp only [resumeSharedSlice, sharedCore]
  rw [MachineCore.runSlice_add]
  simp only [Nat.add_assoc]

/-- The shared snapshot is the program; each command grants one private owner
a quantum. Neither kernel can read a different owner's mutable continuation. -/
def referenceSliceKernel (Id : Type uId) : SnapshotBatch.Kernel
    (Program Context Control Call Frame Answer) (Id × Nat) Nat Id
    (ReferenceSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer)) where
  destination := Prod.fst
  compute program _ quantum cell := resumeReferenceSlice program quantum cell

def sharedSliceKernel (Id : Type uId) : SnapshotBatch.Kernel
    (Program Context Control Call Frame Answer) (Id × Nat) Nat Id
    (SharedSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer)) where
  destination := Prod.fst
  compute program _ quantum cell := resumeSharedSlice program quantum cell

variable [DecidableEq Id]

/-- Worker placement and completion order preserve every private residual,
prefix, context and charge. This grants no access to a common mutable Need cell. -/
theorem shared_ready_partitioned_exact (program : Program Context Control Call Frame Answer)
    (parts : List (List (Id × Nat))) (commands : List (Id × Nat))
    (pool : Id → SharedSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer))
    (coverage : parts.flatten.Perm commands) (distinct : (commands.map Prod.fst).Nodup) :
    (fun owner => decodeSliceCell
      ((sharedSliceKernel Id).partitioned program Prod.snd pool parts owner)) =
    (referenceSliceKernel Id).run program Prod.snd
      (fun owner => decodeSliceCell (pool owner)) commands := by
  rw [SnapshotBatch.Kernel.partitioned_eq_batch]
  have transported := (sharedSliceKernel Id).batch_map program Prod.snd
    (referenceSliceKernel Id) decodeSliceCell (fun _ => rfl)
    (fun _ quantum cell => resumeSharedSlice_decode program quantum cell) pool parts.flatten
  have unique : (referenceSliceKernel (Context := Context) (Control := Control)
      (Call := Call) (Frame := Frame) (Answer := Answer) Id).Disjoint parts.flatten :=
    (coverage.map Prod.fst).nodup_iff.mpr distinct
  exact transported.trans
    (((referenceSliceKernel Id).batch_eq_run program Prod.snd _ _ unique).trans
      ((referenceSliceKernel Id).run_perm program Prod.snd _ coverage unique))

/-- The coordinator exposes only the canonical prefix. Later completed owners
stay buffered while an earlier owner still has a live frontier. -/
def orderedReadyPrefix (pool : Id → ReferenceSliceCell (Context := Context) (Control := Control)
    (Frame := Frame) (Answer := Answer)) : List Id → List (Context × Answer)
  | [] => []
  | owner :: rest =>
      (pool owner).2.emitted ++
        if (pool owner).2.frontier = [] then orderedReadyPrefix pool rest else []

/-- Canonical publication is independent of physical completion order under
the complete private-state comparison, even before every owner finishes. -/
theorem shared_ready_prefix_exact (program : Program Context Control Call Frame Answer)
    (parts : List (List (Id × Nat))) (commands : List (Id × Nat))
    (pool : Id → SharedSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer))
    (coverage : parts.flatten.Perm commands) (distinct : (commands.map Prod.fst).Nodup)
    (order : List Id) :
    orderedReadyPrefix (fun owner => decodeSliceCell
      ((sharedSliceKernel Id).partitioned program Prod.snd pool parts owner)) order =
    orderedReadyPrefix ((referenceSliceKernel Id).run program Prod.snd
      (fun owner => decodeSliceCell (pool owner)) commands) order := by
  rw [shared_ready_partitioned_exact program parts commands pool coverage distinct]

/-- Combine exclusive grants on the same already loaded owner. -/
theorem resumeSharedSlice_fold (program : Program Context Control Call Frame Answer)
    (grants : List Nat) (cell : SharedSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer)) :
    grants.foldl (fun current grant => resumeSharedSlice program grant current) cell =
      resumeSharedSlice program grants.sum cell := by
  induction grants generalizing cell with
  | nil => rfl
  | cons grant rest ih =>
      simp only [List.foldl_cons, List.sum_cons]
      rw [ih]
      exact (resumeSharedSlice_add program grant rest.sum cell).symm

/-- Every owner retains its paid private state across arbitrarily interleaved
exclusive slices. The comparison independently runs the reference list
machine with that owner's total grant; no disjoint-snapshot overwrite occurs. -/
theorem shared_refill_exact (program : Program Context Control Call Frame Answer)
    (commands : List (Id × Nat))
    (pool : Id → SharedSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer)) :
    (fun owner => decodeSliceCell
      ((sharedSliceKernel Id).run program Prod.snd pool commands owner)) =
      fun owner => resumeReferenceSlice program
        ((commands.filter (fun command => decide (command.1 = owner))).map Prod.snd).sum
        (decodeSliceCell (pool owner)) := by
  funext owner
  rw [SnapshotBatch.Kernel.run_at_location]
  change decodeSliceCell
    ((commands.filter (fun command => decide (command.1 = owner))).foldl
      (fun current command => resumeSharedSlice program command.2 current) (pool owner)) = _
  have mapped :
      (commands.filter (fun command => decide (command.1 = owner))).foldl
        (fun current command => resumeSharedSlice program command.2 current) (pool owner) =
      ((commands.filter (fun command => decide (command.1 = owner))).map Prod.snd).foldl
        (fun current grant => resumeSharedSlice program grant current) (pool owner) := by
    rw [List.foldl_map]
  rw [mapped]
  rw [resumeSharedSlice_fold, resumeSharedSlice_decode]


end ReadyOccurrences

/-- Publication only appends occurrences. Matching answers are not coalesced. -/
theorem step_emitted_extension (program : Program Context Control Call Frame Answer)
    (state : State Context Control Frame Answer) :
    ∃ suffix, (step program state).emitted = state.emitted ++ suffix := by
  rcases state with ⟨frontier, emitted⟩
  cases frontier with
  | nil => exact ⟨[], by simp [step]⟩
  | cons task rest =>
      cases instruction : program.inspect task.control with
      | ret value =>
          cases pending : task.returns with
          | nil => exact ⟨[(task.context, value)], by simp [step, instruction, pending]⟩
          | cons frame frames => exact ⟨[], by simp [step, instruction, pending]⟩
      | fail => exact ⟨[], by simp [step, instruction]⟩
      | call callee frame => exact ⟨[], by simp [step, instruction]⟩
      | tail callee => exact ⟨[], by simp [step, instruction]⟩

theorem reference_slice_emitted_extension (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : State Context Control Frame Answer) :
    ∃ suffix, (MachineCore.runSlice (referenceCore program) fuel state).1.emitted =
      state.emitted ++ suffix := by
  induction fuel generalizing state with
  | zero => exact ⟨[], by simp [MachineCore.runSlice]⟩
  | succ fuel ih =>
      cases advanced : (referenceCore program).step state with
      | none => exact ⟨[], by simp [MachineCore.runSlice, advanced]⟩
      | some next =>
          have nextStep : next = step program state := by
            simp only [referenceCore] at advanced
            split at advanced
            next final => simp at advanced
            next live => exact (Option.some.inj advanced).symm
          obtain ⟨first, firstExact⟩ := step_emitted_extension program state
          obtain ⟨later, laterExact⟩ := ih next
          refine ⟨first ++ later, ?_⟩
          simp only [MachineCore.runSlice, advanced]
          rw [laterExact, nextStep, firstExact, List.append_assoc]

theorem shared_slice_emitted_extension (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : CheckedState Context Control Frame Answer) :
    ∃ suffix, (MachineCore.runSlice (sharedCore program) fuel state).1.1.emitted =
      state.1.emitted ++ suffix := by
  have states := congrArg Prod.fst (slice_exact program fuel state)
  obtain ⟨suffix, exactPrefix⟩ := reference_slice_emitted_extension program fuel state.1.decode
  refine ⟨suffix, ?_⟩
  rw [← states] at exactPrefix
  exact exactPrefix

section OrderedRefills

universe uId
variable {Id : Type uId}

/-- A completed owner cannot be reopened by another grant. Neither its
published occurrences nor its accumulated charge change. -/
theorem resumeReferenceSlice_completed (program : Program Context Control Call Frame Answer)
    (quantum : Nat) (cell : ReferenceSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer)) (completed : cell.2.frontier = []) :
    resumeReferenceSlice program quantum cell = cell := by
  have final : (referenceCore program).step cell.2 = none := by
    simp [referenceCore, completed]
  simp [resumeReferenceSlice, MachineCore.runSlice_of_final _ _ final]

/-- Owner-local append-only publication is sufficient for an ordered global
prefix only when completed owners remain completed. Later ready owners stay
behind the first unfinished owner. -/
theorem orderedReadyPrefix_extension
    (before after : Id → ReferenceSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer))
    (grows : ∀ owner, ∃ suffix,
      (after owner).2.emitted = (before owner).2.emitted ++ suffix)
    (finished : ∀ owner, (before owner).2.frontier = [] → after owner = before owner)
    (order : List Id) :
    ∃ suffix, orderedReadyPrefix after order = orderedReadyPrefix before order ++ suffix := by
  induction order with
  | nil => exact ⟨[], rfl⟩
  | cons owner rest ih =>
      by_cases completed : (before owner).2.frontier = []
      · obtain ⟨suffix, exactTail⟩ := ih
        refine ⟨suffix, ?_⟩
        simp only [orderedReadyPrefix, finished owner completed, completed, if_pos]
        rw [exactTail, List.append_assoc]
      · obtain ⟨suffix, exactOwner⟩ := grows owner
        refine ⟨suffix ++ (if (after owner).2.frontier = [] then
          orderedReadyPrefix after rest else []), ?_⟩
        simp only [orderedReadyPrefix, completed, if_false, List.append_nil]
        rw [exactOwner, List.append_assoc]

variable [DecidableEq Id]

/-- Arbitrary exclusive refill grants, including zero grants and repeated
owners, extend the exact ordered answer prefix. Quantum choice does not grant
permission to publish later owners ahead of unfinished earlier ones. -/
theorem shared_refill_published_extension (program : Program Context Control Call Frame Answer)
    (commands : List (Id × Nat))
    (pool : Id → SharedSliceCell (Context := Context) (Control := Control)
      (Frame := Frame) (Answer := Answer)) (order : List Id) :
    ∃ suffix,
      orderedReadyPrefix (fun owner => decodeSliceCell
        ((sharedSliceKernel Id).run program Prod.snd pool commands owner)) order =
      orderedReadyPrefix (fun owner => decodeSliceCell (pool owner)) order ++ suffix := by
  rw [shared_refill_exact]
  apply orderedReadyPrefix_extension
  · intro owner
    exact reference_slice_emitted_extension program _ (decodeSliceCell (pool owner)).2
  · intro owner completed
    exact resumeReferenceSlice_completed program _ _ completed

end OrderedRefills

/-- An ordered branching call allocates one return node, independently of
the number of callee alternatives and the caller's existing return depth. -/
theorem call_allocates_one (program : Program Context Control Call Frame Answer)
    (arena : Arena Frame) (task : RootTask Context Control)
    (rest : List (RootTask Context Control)) (emitted : List (Context × Answer))
    (callee : Call) (frame : Frame) (instruction : program.inspect task.control = .call callee frame) :
    (arenaStep program ⟨arena, task :: rest, emitted⟩).map (fun next => next.arena.length) =
      some (arena.length + 1) := by
  simp [arenaStep, instruction]

/-- Only a call allocates a frame node; its alternatives share that node.
This counts retained arena nodes, without estimating native storage overhead. -/
theorem arenaStep_node_count (program : Program Context Control Call Frame Answer)
    (state next : ArenaState Context Control Frame Answer)
    (advanced : arenaStep program state = some next) :
    next.arena.length = state.arena.length ∨
      next.arena.length = state.arena.length + 1 := by
  rcases state with ⟨arena, frontier, emitted⟩
  cases frontier with
  | nil => simp only [arenaStep, Option.some.injEq] at advanced; subst next; exact Or.inl rfl
  | cons task rest =>
      cases instruction : program.inspect task.control with
      | ret value =>
          by_cases empty : task.root = 0
          · simp [arenaStep, instruction, empty] at advanced
            subst next
            exact Or.inl rfl
          · cases found : arena.read task.root with
            | none => simp [arenaStep, instruction, empty, found] at advanced
            | some node =>
                simp [arenaStep, instruction, empty, found] at advanced
                subst next
                exact Or.inl rfl
      | fail =>
          simp [arenaStep, instruction] at advanced
          subst next
          exact Or.inl rfl
      | call callee frame =>
          simp [arenaStep, instruction] at advanced
          subst next
          exact Or.inr rfl
      | tail callee =>
          simp [arenaStep, instruction] at advanced
          subst next
          exact Or.inl rfl

theorem sharedCore_step_node_count (program : Program Context Control Call Frame Answer)
    (state next : CheckedState Context Control Frame Answer)
    (advanced : (sharedCore program).step state = some next) :
    next.1.arena.length = state.1.arena.length ∨
      next.1.arena.length = state.1.arena.length + 1 := by
  simp only [sharedCore] at advanced
  split at advanced
  next final => simp at advanced
  next live =>
    simp only [Option.some.injEq] at advanced
    subst next
    obtain ⟨next, found, _, _⟩ := arenaStep_exact program state.1 state.2
    simpa [checkedStep, found] using arenaStep_node_count program state.1 next found

/-- Retained return-node growth is bounded by performed transitions, not by
the number of alternatives or the requested budget. Final no-ops are free. -/
theorem slice_node_bounds (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : CheckedState Context Control Frame Answer) :
    state.1.arena.length ≤
        (MachineCore.runSlice (sharedCore program) fuel state).1.1.arena.length ∧
      (MachineCore.runSlice (sharedCore program) fuel state).1.1.arena.length ≤
        state.1.arena.length + (MachineCore.runSlice (sharedCore program) fuel state).2 := by
  induction fuel generalizing state with
  | zero => simp [MachineCore.runSlice]
  | succ fuel ih =>
      cases advanced : (sharedCore program).step state with
      | none => simp [MachineCore.runSlice, advanced]
      | some next =>
          have nodeCount := sharedCore_step_node_count program state next advanced
          have later := ih next
          simp only [MachineCore.runSlice, advanced]
          rcases nodeCount with equal | added <;> constructor <;> omega

/-- Retire the newest region only when every frontier root and every externally
held root lies below its mark. The native capture inventory must include roots
held by exported closures or other owners; omitting such roots is not licensed.
Frame addresses below the mark do not change. -/
def retire? (count : Nat) (held : List Nat)
    (state : ArenaState Context Control Frame Answer) :
    Option (ArenaState Context Control Frame Answer) :=
  let kept := state.arena.drop count
  if state.frontier.all (fun task => decide (task.root ≤ kept.length)) &&
      held.all (fun root => decide (root ≤ kept.length)) then
    some { state with arena := kept }
  else none

/-- Checked retirement preserves the complete residual and every declared
external continuation, and keeps the arena well formed. -/
theorem retire?_exact (count : Nat) (held : List Nat)
    (state next : ArenaState Context Control Frame Answer) (valid : state.Valid)
    (retired : retire? count held state = some next) :
    next.Valid ∧ next.decode = state.decode ∧
      (∀ root ∈ held, next.arena.expand root = state.arena.expand root) ∧
      next.arena.length = state.arena.length - count := by
  unfold retire? at retired
  dsimp only at retired
  split at retired
  next admitted =>
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at admitted
    obtain ⟨frontierBound, heldBound⟩ := admitted
    cases Option.some.inj retired
    refine ⟨⟨state.arena.valid_drop valid.1 count, frontierBound⟩, ?_, ?_, ?_⟩
    · apply congrArg (fun frontier => State.mk frontier state.emitted)
      apply List.map_congr_left
      intro task member
      simp only [RootTask.decode, Arena.expand_drop _ count _ (frontierBound task member)]
    · intro root member
      exact state.arena.expand_drop count root (heldBound root member)
    · exact List.length_drop
  next refused => simp at retired

/-- A checked retirement preserves every subsequent bounded continuation,
including its ordered emissions, residual and actual transition count. -/
theorem retire?_slice_exact (program : Program Context Control Call Frame Answer)
    (count : Nat) (held : List Nat) (state : CheckedState Context Control Frame Answer)
    (next : ArenaState Context Control Frame Answer)
    (retired : retire? count held state.1 = some next) (fuel : Nat) :
    (let admitted : CheckedState Context Control Frame Answer :=
        ⟨next, (retire?_exact count held state.1 next state.2 retired).1⟩
     ((MachineCore.runSlice (sharedCore program) fuel admitted).1.1.decode,
       (MachineCore.runSlice (sharedCore program) fuel admitted).2)) =
      ((MachineCore.runSlice (sharedCore program) fuel state).1.1.decode,
        (MachineCore.runSlice (sharedCore program) fuel state).2) := by
  dsimp only
  rw [slice_exact, slice_exact]
  rw [(retire?_exact count held state.1 next state.2 retired).2.1]

section ExclusiveFrontier

/-- Retain later alternatives behind one exclusively advanced frontier. -/
def State.appendFrontier (state : State Context Control Frame Answer)
    (later : List (Task Context Control Frame)) : State Context Control Frame Answer :=
  { state with frontier := state.frontier ++ later }

theorem step_appendFrontier (program : Program Context Control Call Frame Answer)
    (state : State Context Control Frame Answer) (later : List (Task Context Control Frame))
    (live : state.frontier ≠ []) :
    step program (state.appendFrontier later) = (step program state).appendFrontier later := by
  rcases state with ⟨frontier, emitted⟩
  cases frontier with
  | nil => exact False.elim (live rfl)
  | cons task rest =>
      cases inspected : program.inspect task.control with
      | ret value =>
          cases pending : task.returns <;> simp [State.appendFrontier, step, inspected, pending]
      | fail => simp [State.appendFrontier, step, inspected]
      | call callee frame => simp [State.appendFrontier, step, inspected, List.append_assoc]
      | tail callee => simp [State.appendFrontier, step, inspected, List.append_assoc]

/-- The exact paid endpoint of a detached slice embeds in the original
frontier. Unused allowance must not execute a later alternative. -/
theorem reference_slice_append_paid (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : State Context Control Frame Answer)
    (later : List (Task Context Control Frame)) :
    MachineCore.runSlice (referenceCore program)
        (MachineCore.runSlice (referenceCore program) fuel state).2
        (state.appendFrontier later) =
      ((MachineCore.runSlice (referenceCore program) fuel state).1.appendFrontier later,
        (MachineCore.runSlice (referenceCore program) fuel state).2) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      by_cases final : state.frontier = []
      · simp [MachineCore.runSlice, referenceCore, final]
      · have joinedLive : (state.appendFrontier later).frontier ≠ [] := by
          intro empty
          simp only [State.appendFrontier, List.append_eq_nil_iff] at empty
          exact final empty.1
        have localStep : (referenceCore program).step state = some (step program state) := by
          simp [referenceCore, final]
        have joinedStep : (referenceCore program).step (state.appendFrontier later) =
            some ((step program state).appendFrontier later) := by
          simp [referenceCore, joinedLive, step_appendFrontier program state later final]
        simp only [MachineCore.runSlice, localStep]
        rw [joinedStep]
        simp only
        rw [ih]
        rfl

def ArenaState.appendFrontier (state : ArenaState Context Control Frame Answer)
    (later : List (RootTask Context Control)) : ArenaState Context Control Frame Answer :=
  { state with frontier := state.frontier ++ later }

/-- A step changes only the selected frontier prefix; the arena and emitted
prefix are the same as in the independently executed selected state. -/
theorem arenaStep_appendFrontier (program : Program Context Control Call Frame Answer)
    (state : ArenaState Context Control Frame Answer) (later : List (RootTask Context Control))
    (live : state.frontier ≠ []) :
    arenaStep program (state.appendFrontier later) =
      (arenaStep program state).map (fun next => next.appendFrontier later) := by
  rcases state with ⟨arena, frontier, emitted⟩
  cases frontier with
  | nil => exact False.elim (live rfl)
  | cons task rest =>
      cases inspected : program.inspect task.control with
      | ret value =>
          by_cases empty : task.root = 0
          · simp [arenaStep, ArenaState.appendFrontier, inspected, empty]
          · cases found : arena.read task.root <;>
              simp [arenaStep, ArenaState.appendFrontier, inspected, empty, found]
      | fail => simp [arenaStep, ArenaState.appendFrontier, inspected]
      | call callee frame => simp [arenaStep, ArenaState.appendFrontier, inspected, List.append_assoc]
      | tail callee => simp [arenaStep, ArenaState.appendFrontier, inspected, List.append_assoc]

/-- Each successful step only prepends nodes to the existing return arena. -/
theorem arenaStep_arena_extension (program : Program Context Control Call Frame Answer)
    (state next : ArenaState Context Control Frame Answer)
    (advanced : arenaStep program state = some next) :
    ∃ added, next.arena = added ++ state.arena := by
  rcases state with ⟨arena, frontier, emitted⟩
  cases frontier with
  | nil =>
      simp only [arenaStep, Option.some.injEq] at advanced
      subst next
      exact ⟨[], rfl⟩
  | cons task rest =>
      cases inspected : program.inspect task.control with
      | ret value =>
          by_cases empty : task.root = 0
          · simp [arenaStep, inspected, empty] at advanced
            subst next
            exact ⟨[], rfl⟩
          · cases found : arena.read task.root with
            | none => simp [arenaStep, inspected, empty, found] at advanced
            | some node =>
                simp [arenaStep, inspected, empty, found] at advanced
                subst next
                exact ⟨[], rfl⟩
      | fail =>
          simp [arenaStep, inspected] at advanced
          subst next
          exact ⟨[], rfl⟩
      | call callee frame =>
          simp [arenaStep, inspected] at advanced
          subst next
          exact ⟨[(frame, task.root)], rfl⟩
      | tail callee =>
          simp [arenaStep, inspected] at advanced
          subst next
          exact ⟨[], rfl⟩

theorem sharedCore_step_arena_extension (program : Program Context Control Call Frame Answer)
    (state next : CheckedState Context Control Frame Answer)
    (advanced : (sharedCore program).step state = some next) :
    ∃ added, next.1.arena = added ++ state.1.arena := by
  simp only [sharedCore] at advanced
  split at advanced
  next final => simp at advanced
  next live =>
    simp only [Option.some.injEq] at advanced
    subst next
    obtain ⟨next, found, _, _⟩ := arenaStep_exact program state.1 state.2
    simpa [checkedStep, found] using arenaStep_arena_extension program state.1 next found

/-- Any finite slice preserves the existing return-node suffix verbatim. -/
theorem slice_arena_extension (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : CheckedState Context Control Frame Answer) :
    ∃ added, (MachineCore.runSlice (sharedCore program) fuel state).1.1.arena =
      added ++ state.1.arena := by
  induction fuel generalizing state with
  | zero => exact ⟨[], rfl⟩
  | succ fuel ih =>
      cases advanced : (sharedCore program).step state with
      | none => simp [MachineCore.runSlice, advanced]
      | some next =>
          obtain ⟨first, firstExact⟩ := sharedCore_step_arena_extension program state next advanced
          obtain ⟨second, secondExact⟩ := ih next
          refine ⟨second ++ first, ?_⟩
          simp only [MachineCore.runSlice, advanced]
          rw [secondExact, firstExact, List.append_assoc]

theorem Arena.expand_prefix (arena added : Arena Frame) (root : Nat)
    (bounded : root ≤ arena.length) :
    (added ++ arena).expand root = arena.expand root := by
  induction added with
  | nil => rfl
  | cons node rest ih =>
      rcases node with ⟨frame, parent⟩
      rw [List.cons_append, Arena.expand_old (rest ++ arena) frame parent root (by
        simp only [List.length_append]; omega)]
      exact ih

/-- Externally retained return roots keep their original frame payloads and
addresses across a slice. This includes roots outside its selected frontier. -/
theorem slice_held_root_exact (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : CheckedState Context Control Frame Answer) (root : Nat)
    (bounded : root ≤ state.1.arena.length) :
    (MachineCore.runSlice (sharedCore program) fuel state).1.1.arena.expand root =
      state.1.arena.expand root := by
  obtain ⟨added, extension⟩ := slice_arena_extension program fuel state
  rw [extension]
  exact Arena.expand_prefix state.1.arena added root bounded

theorem slice_held_task_exact (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : CheckedState Context Control Frame Answer)
    (task : RootTask Context Control) (bounded : task.root ≤ state.1.arena.length) :
    task.decode (MachineCore.runSlice (sharedCore program) fuel state).1.1.arena =
      task.decode state.1.arena := by
  simp only [RootTask.decode, slice_held_root_exact program fuel state task.root bounded]

def appendCheckedFrontier (state : CheckedState Context Control Frame Answer)
    (later : List (RootTask Context Control))
    (bounded : ∀ task ∈ later, task.root ≤ state.1.arena.length) :
    CheckedState Context Control Frame Answer :=
  ⟨state.1.appendFrontier later, state.2.1, by
    intro task member
    rcases List.mem_append.mp member with selected | retained
    · exact state.2.2 task selected
    · exact bounded task retained⟩

theorem appendCheckedFrontier_decode (state : CheckedState Context Control Frame Answer)
    (later : List (RootTask Context Control))
    (bounded : ∀ task ∈ later, task.root ≤ state.1.arena.length) :
    (appendCheckedFrontier state later bounded).1.decode =
      state.1.decode.appendFrontier (later.map (RootTask.decode state.1.arena)) := by
  simp [appendCheckedFrontier, ArenaState.appendFrontier, ArenaState.decode, State.appendFrontier]

theorem checkedStep_appendFrontier (program : Program Context Control Call Frame Answer)
    (state : CheckedState Context Control Frame Answer) (later : List (RootTask Context Control))
    (bounded : ∀ task ∈ later, task.root ≤ state.1.arena.length)
    (live : state.1.frontier ≠ []) :
    (checkedStep program (appendCheckedFrontier state later bounded)).1 =
      (checkedStep program state).1.appendFrontier later := by
  obtain ⟨next, advanced, _, _⟩ := arenaStep_exact program state.1 state.2
  have joined : arenaStep program (state.1.appendFrontier later) =
      some (next.appendFrontier later) := by
    rw [arenaStep_appendFrontier program state.1 later live, advanced]
    rfl
  simp [checkedStep, appendCheckedFrontier, advanced, joined]

/-- This stronger comparison retains the actual arena, unchanged later root
addresses and the whole emitted prefix, as well as the exact paid debit. -/
theorem shared_slice_append_paid_arena (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : CheckedState Context Control Frame Answer)
    (later : List (RootTask Context Control))
    (bounded : ∀ task ∈ later, task.root ≤ state.1.arena.length) :
    let detached := MachineCore.runSlice (sharedCore program) fuel state
    let joined := MachineCore.runSlice (sharedCore program) detached.2
      (appendCheckedFrontier state later bounded)
    joined.1.1 = detached.1.1.appendFrontier later ∧ joined.2 = detached.2 := by
  induction fuel generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      by_cases final : state.1.frontier = []
      · simp [MachineCore.runSlice, sharedCore, final, appendCheckedFrontier]
      · have localStep : (sharedCore program).step state = some (checkedStep program state) := by
          simp [sharedCore, final]
        have growth : state.1.arena.length ≤ (checkedStep program state).1.arena.length := by
          have count := sharedCore_step_node_count program state (checkedStep program state) localStep
          omega
        have nextBound : ∀ task ∈ later,
            task.root ≤ (checkedStep program state).1.arena.length :=
          fun task member => (bounded task member).trans growth
        have joinedLive : (appendCheckedFrontier state later bounded).1.frontier ≠ [] := by
          intro empty
          simp only [appendCheckedFrontier, ArenaState.appendFrontier, List.append_eq_nil_iff] at empty
          exact final empty.1
        have joinedStep : (sharedCore program).step (appendCheckedFrontier state later bounded) =
            some (appendCheckedFrontier (checkedStep program state) later nextBound) := by
          simp only [sharedCore, if_neg joinedLive]
          apply congrArg some
          apply Subtype.ext
          exact checkedStep_appendFrontier program state later bounded final
        dsimp only
        simp only [MachineCore.runSlice, localStep]
        rw [joinedStep]
        simp only
        obtain ⟨states, charges⟩ := ih (checkedStep program state) nextBound
        exact ⟨states, congrArg (fun used : Nat => used + 1) charges⟩

/-- The shared arena also embeds the detached paid endpoint in the original
ordered frontier, preserving contexts, return stacks, emitted occurrences and
the transition debit. Later roots keep their interpretation in the old arena. -/
theorem shared_slice_append_paid (program : Program Context Control Call Frame Answer)
    (fuel : Nat) (state : CheckedState Context Control Frame Answer)
    (later : List (RootTask Context Control))
    (bounded : ∀ task ∈ later, task.root ≤ state.1.arena.length) :
    let detached := MachineCore.runSlice (sharedCore program) fuel state
    let joined := MachineCore.runSlice (sharedCore program) detached.2
      (appendCheckedFrontier state later bounded)
    (joined.1.1.decode, joined.2) =
      (detached.1.1.decode.appendFrontier (later.map (RootTask.decode state.1.arena)), detached.2) := by
  dsimp only
  rw [slice_exact, appendCheckedFrontier_decode]
  have exactSlice := slice_exact program fuel state
  have states := congrArg Prod.fst exactSlice
  have counts := congrArg Prod.snd exactSlice
  dsimp only at states counts
  rw [counts, states]
  exact reference_slice_append_paid program fuel state.1.decode _

end ExclusiveFrontier

section ProducerComposition

open Cursor

/-- An emitted return is a distinct producer occurrence only after the caller
stack has emptied. This classifier does not inspect earlier emissions. -/
def referenceReturn? (program : Program Context Control Call Frame Answer)
    (state : State Context Control Frame Answer) : Option (Context × Answer) :=
  match state.frontier with
  | [] => none
  | task :: _ =>
      match program.inspect task.control, task.returns with
      | .ret value, [] => some (task.context, value)
      | _, _ => none

/-- The shared classifier uses the current root directly. It expands neither
the saved stack nor the emitted prefix. -/
def sharedReturn? (program : Program Context Control Call Frame Answer)
    (state : ArenaState Context Control Frame Answer) : Option (Context × Answer) :=
  match state.frontier with
  | [] => none
  | task :: _ =>
      match program.inspect task.control with
      | .ret value => if task.root = 0 then some (task.context, value) else none
      | _ => none

theorem return?_decode (program : Program Context Control Call Frame Answer)
    (state : ArenaState Context Control Frame Answer) (valid : state.Valid) :
    referenceReturn? program state.decode = sharedReturn? program state := by
  rcases state with ⟨arena, frontier, emitted⟩
  cases frontier with
  | nil => rfl
  | cons task rest =>
      have bound := valid.2 task (by simp)
      cases inspected : program.inspect task.control with
      | ret value =>
          cases expanded : arena.expand task.root with
          | nil =>
              have zero := (arena.expand_eq_nil_iff valid.1 task.root bound).mp expanded
              simp [referenceReturn?, sharedReturn?, ArenaState.decode, RootTask.decode,
                inspected, zero]
          | cons frame pending =>
              have nonzero : task.root ≠ 0 := by
                intro zero
                simp [zero] at expanded
              simp [referenceReturn?, sharedReturn?, ArenaState.decode, RootTask.decode,
                inspected, expanded, nonzero]
      | fail => simp [referenceReturn?, sharedReturn?, ArenaState.decode, RootTask.decode, inspected]
      | call callee frame =>
          simp [referenceReturn?, sharedReturn?, ArenaState.decode, RootTask.decode, inspected]
      | tail callee =>
          simp [referenceReturn?, sharedReturn?, ArenaState.decode, RootTask.decode, inspected]

def referenceProducerStep (program : Program Context Control Call Frame Answer)
    (state : State Context Control Frame Answer) :
    ProducerOccurrenceLog.ProducerOutcome (State Context Control Frame Answer)
      (Context × Answer) Empty Empty :=
  match state.frontier with
  | [] => .completed state
  | _ :: _ =>
      let next := step program state
      match referenceReturn? program state with
      | none => .progress next
      | some row => .returned row next

/-- Production executes `checkedStep` on the retained arena. Reference decoding
is only used in its correctness theorem. -/
def sharedProducerStep (program : Program Context Control Call Frame Answer)
    (state : CheckedState Context Control Frame Answer) :
    ProducerOccurrenceLog.ProducerOutcome (CheckedState Context Control Frame Answer)
      (Context × Answer) Empty Empty :=
  match state.1.frontier with
  | [] => .completed state
  | _ :: _ =>
      let next := checkedStep program state
      match sharedReturn? program state.1 with
      | none => .progress next
      | some row => .returned row next

/-- Classifying a return loses no emissions: exactly zero or one new occurrence
is appended by the actual transition, including at the completion boundary. -/
theorem referenceProducerStep_emitted (program : Program Context Control Call Frame Answer)
    (state : State Context Control Frame Answer) :
    (referenceProducerStep program state).next.emitted = state.emitted ++
      (referenceProducerStep program state).returns := by
  rcases state with ⟨frontier, emitted⟩
  cases frontier with
  | nil => simp [referenceProducerStep, ProducerOccurrenceLog.ProducerOutcome.next,
      ProducerOccurrenceLog.ProducerOutcome.returns]
  | cons task rest =>
      cases inspected : program.inspect task.control with
      | ret value =>
          cases pending : task.returns <;>
            simp [referenceProducerStep, referenceReturn?, step, inspected, pending,
              ProducerOccurrenceLog.ProducerOutcome.next, ProducerOccurrenceLog.ProducerOutcome.returns]
      | fail =>
          simp [referenceProducerStep, referenceReturn?, step, inspected,
            ProducerOccurrenceLog.ProducerOutcome.next, ProducerOccurrenceLog.ProducerOutcome.returns]
      | call callee frame =>
          simp [referenceProducerStep, referenceReturn?, step, inspected,
            ProducerOccurrenceLog.ProducerOutcome.next, ProducerOccurrenceLog.ProducerOutcome.returns]
      | tail callee =>
          simp [referenceProducerStep, referenceReturn?, step, inspected,
            ProducerOccurrenceLog.ProducerOutcome.next, ProducerOccurrenceLog.ProducerOutcome.returns]

theorem sharedProducerStep_square (program : Program Context Control Call Frame Answer)
    (state : CheckedState Context Control Frame Answer) :
    referenceProducerStep program state.1.decode =
      (sharedProducerStep program state).mapProducer (fun retained => retained.1.decode) := by
  cases frontier : state.1.frontier with
  | nil =>
      simp [referenceProducerStep, sharedProducerStep, ArenaState.decode, frontier,
        ProducerOccurrenceLog.ProducerOutcome.mapProducer]
  | cons task rest =>
      have decoded : state.1.decode.frontier = task.decode state.1.arena ::
          rest.map (RootTask.decode state.1.arena) := by simp [ArenaState.decode, frontier]
      unfold referenceProducerStep sharedProducerStep
      rw [frontier, decoded, return?_decode program state.1 state.2]
      cases sharedReturn? program state.1 <;>
        simp [ProducerOccurrenceLog.ProducerOutcome.mapProducer, decode_checkedStep]

/-- The producer representation square lifts through capture refusal, bounded
buffering, context checks and ordered publication, with the complete residual. -/
theorem producer_run_exact {Stored SourceContext Output : Type} {clients : Nat}
    (program : Program Context Control Call Frame Answer)
    (capture : (Context × Answer) → Option Stored) (capacity : Stored → Bool)
    (compatible : SourceContext → Bool) (ticks : Nat)
    (state : ProducerOccurrenceLog.Configuration (CheckedState Context Control Frame Answer)
      (Context × Answer) Stored SourceContext Output Empty Empty clients) :
    ProducerOccurrenceLog.run (referenceProducerStep program) capture capacity compatible ticks
        (ProducerOccurrenceLog.mapProducer (fun retained => retained.1.decode) state) =
      ((ProducerOccurrenceLog.run (sharedProducerStep program) capture capacity compatible ticks state).1,
        ProducerOccurrenceLog.mapProducer (fun retained => retained.1.decode)
          (ProducerOccurrenceLog.run (sharedProducerStep program) capture capacity compatible ticks state).2) :=
  ProducerOccurrenceLog.run_mapProducer (fun retained => retained.1.decode)
    (sharedProducerStep program) (referenceProducerStep program)
    (sharedProducerStep_square program) capture capacity compatible ticks state

theorem producer_delivery_exact {Stored SourceContext Output : Type} {clients : Nat}
    [DecidableEq Stored] [DecidableEq Output] (compatible : SourceContext → Bool)
    (state : ProducerOccurrenceLog.Configuration (CheckedState Context Control Frame Answer)
      (Context × Answer) Stored SourceContext Output Empty Empty clients)
    (client : Fin clients) (output : Output) :
    ProducerOccurrenceLog.deliver compatible
        (ProducerOccurrenceLog.mapProducer (fun retained => retained.1.decode) state) client output =
      ((ProducerOccurrenceLog.deliver compatible state client output).1,
        ProducerOccurrenceLog.mapProducer (fun retained => retained.1.decode)
          (ProducerOccurrenceLog.deliver compatible state client output).2) :=
  ProducerOccurrenceLog.deliver_mapProducer (fun retained => retained.1.decode)
    compatible state client output

end ProducerComposition

namespace SliceControls

/-- Two equal answers remain two occurrences. The call adds one return frame
in front of the caller's already pending frame. -/
def program : Program Nat (Instruction Nat Nat Nat) Nat Nat Nat where
  inspect := id
  branches context callee := [(context, .ret callee), (context, .ret callee)]
  resume context frame value := (context, .ret (frame + value))

def captured : State Nat (Instruction Nat Nat Nat) Nat Nat :=
  ⟨[⟨7, .call 3 10, [100]⟩], [(9, 5), (9, 5)]⟩

/-- The captured prefix survives a partial run; both return obligations and
the second alternative remain explicit in the residual. -/
example : MachineCore.runSlice (referenceCore program) 2 captured =
    (⟨[⟨7, .ret 13, [100]⟩, ⟨7, .ret 3, [10, 100]⟩], [(9, 5), (9, 5)]⟩, 2) := rfl

/-- Completing both alternatives keeps equal emissions and the old prefix.
Unused final-state fuel contributes no additional transitions or arena nodes. -/
example :
    ((MachineCore.runSlice (sharedCore program) 20 (encode captured)).1.1.emitted,
      (MachineCore.runSlice (sharedCore program) 20 (encode captured)).1.1.frontier.length,
      (MachineCore.runSlice (sharedCore program) 20 (encode captured)).1.1.arena.length,
      (MachineCore.runSlice (sharedCore program) 20 (encode captured)).2) =
        ([(9, 5), (9, 5), (7, 113), (7, 113)], 0, 2, 7) := by
  decide +kernel

/-- Exhausting a two-step budget does not certify exhaustion of the frontier. -/
example : (MachineCore.runSlice (sharedCore program) 2 (encode captured)).2 = 2 ∧
    (MachineCore.runSlice (sharedCore program) 2 (encode captured)).1.1.frontier ≠ [] := by
  decide +kernel

/-- A newer node is unreachable by the captured task; externally held roots
must nevertheless be declared before that node can be retired. -/
def withUnusedNode : CheckedState Nat (Instruction Nat Nat Nat) Nat Nat :=
  ⟨{ (encode captured).1 with arena := (42, 1) :: (encode captured).1.arena }, by
    simp [ArenaState.Valid, encode, captured, saveFrontier, Arena.save, Arena.Valid]⟩

example : retire? 1 [1] withUnusedNode.1 = some (encode captured).1 := rfl

/-- Keeping an exported root prevents its retirement even when no task uses it. -/
example : retire? 1 [2] withUnusedNode.1 = none := rfl

/-- A live frontier root also prevents retirement, with no external holder. -/
example : retire? 1 [] (encode captured).1 = none := rfl

open Cursor

abbrev ProducerPacket := ProducerOccurrenceLog.Configuration
  (CheckedState Nat (Instruction Nat Nat Nat) Nat Nat)
  (Nat × Nat) (Nat × Nat) Nat Nat Empty Empty 2

def producerStart : ProducerPacket := ProducerOccurrenceLog.initial (encode captured) 0 4

def producerRun (ticks : Nat) :
    List (ProducerOccurrenceLog.Notice (Nat × Nat) (Nat × Nat) Empty Empty) × ProducerPacket :=
  ProducerOccurrenceLog.run (sharedProducerStep program) some (fun _ => true)
    (fun _ => true) ticks producerStart

def stagedProducer : ProducerPacket := (producerRun 4).2

/-- The first public row is staged only after both return frames were paid.
Its sibling alternative and old emitted prefix remain in the retained producer. -/
theorem staged_return_retains_paid_world :
    ProducerOccurrenceLog.pending stagedProducer = some (7, 113) ∧
      stagedProducer.delivery.log.rows = [] ∧
      (stagedProducer.execution.map fun execution => execution.producer.1.decode.frontier) =
        some [⟨7, .ret 3, [10, 100]⟩] ∧
      (stagedProducer.execution.map fun execution => execution.producer.1.emitted) =
        some [(9, 5), (9, 5), (7, 113)] := ⟨rfl, rfl, rfl, rfl⟩

theorem capture_refusal_keeps_complete_producer :
    ProducerOccurrenceLog.pump (sharedProducerStep program) (fun _ => none)
      (fun _ => true) (fun _ => true) stagedProducer = (.captureRefused, stagedProducer) := rfl

theorem retry_admits_without_producer_step :
    let retried := (ProducerOccurrenceLog.pump (sharedProducerStep program) some
      (fun _ => true) (fun _ => true) stagedProducer).2
    retried.execution.map (fun execution => execution.producer) =
        stagedProducer.execution.map (fun execution => execution.producer) ∧
      ProducerOccurrenceLog.pending retried = none ∧
      ProducerOccurrenceLog.acceptedCount retried = 1 ∧
      retried.delivery.log.rows = [(7, 113)] := ⟨rfl, rfl, rfl, rfl⟩

theorem duplicate_returns_remain_distinct_occurrences :
    (producerRun 10).2.delivery.log.rows = [(7, 113), (7, 113)] ∧
      (producerRun 10).2.delivery.log.completed = true ∧
      (producerRun 10).1.flatMap ProducerOccurrenceLog.returned = [(7, 113), (7, 113)] :=
  by decide +kernel

def droppedPendingProducer : ProducerPacket :=
  { stagedProducer with execution := stagedProducer.execution.map fun execution =>
      { execution with pending := none } }

/-- Advancing from the paid residual after dropping its pending row loses an
occurrence, even though the sibling eventually returns the same value. -/
theorem dropping_pending_loses_an_occurrence :
    (ProducerOccurrenceLog.run (sharedProducerStep program) some (fun _ => true)
      (fun _ => true) 10 droppedPendingProducer).2.delivery.log.rows ≠
        [(7, 113), (7, 113)] := by decide +kernel

/-- Three independently owned residuals contain one longer return stack and
two immediate answers. Earlier charges belong to the long residual. -/
def readyPool : Fin 3 → SharedSliceCell (Context := Nat)
    (Control := Instruction Nat Nat Nat) (Frame := Nat) (Answer := Nat)
  | ⟨0, _⟩ => (4, encode captured)
  | ⟨1, _⟩ => (0, encode ⟨[⟨2, .ret 5, []⟩], []⟩)
  | ⟨2, _⟩ => (0, encode ⟨[⟨3, .ret 5, []⟩], []⟩)

def readyParts : List (List (Fin 3 × Nat)) := [[(2, 1), (1, 1)], [(0, 2)]]

def readyPartial : Fin 3 → SharedSliceCell (Context := Nat)
    (Control := Instruction Nat Nat Nat) (Frame := Nat) (Answer := Nat) :=
  (sharedSliceKernel (Fin 3)).partitioned program Prod.snd readyPool readyParts

def readyReference : Fin 3 → ReferenceSliceCell (Context := Nat)
    (Control := Instruction Nat Nat Nat) (Frame := Nat) (Answer := Nat) :=
  (referenceSliceKernel (Fin 3)).run program Prod.snd
    (fun owner => decodeSliceCell (readyPool owner)) [(0, 2), (1, 1), (2, 1)]

theorem ready_completion_order_preserves_all_residuals :
    (fun owner => decodeSliceCell (readyPartial owner)) = readyReference := by
  apply shared_ready_partitioned_exact
  · decide +kernel
  · decide +kernel

theorem ready_partial_retains_long_owner :
    decodeSliceCell (readyPartial 0) =
      (6, ⟨[⟨7, .ret 13, [100]⟩, ⟨7, .ret 3, [10, 100]⟩], [(9, 5), (9, 5)]⟩) ∧
    decodeSliceCell (readyPartial 1) = (1, ⟨[], [(2, 5)]⟩) ∧
    decodeSliceCell (readyPartial 2) = (1, ⟨[], [(3, 5)]⟩) := ⟨rfl, rfl, rfl⟩

/-- The short owners have completed, but the long owner still precedes them.
Its already emitted duplicate prefix remains available to the coordinator. -/
theorem ready_later_answers_stay_buffered :
    orderedReadyPrefix (fun owner => decodeSliceCell (readyPartial owner)) [0, 1, 2] =
      [(9, 5), (9, 5)] := by decide +kernel

/-- Equal payloads do not justify exchanging their source occurrences.
Publishing by arrival order chooses a different first origin. -/
theorem ready_arrival_order_changes_first_origin :
    (orderedReadyPrefix (fun owner => decodeSliceCell (readyPartial owner)) [2, 1, 0]).take 1 ≠
      (orderedReadyPrefix (fun owner => decodeSliceCell (readyPartial owner)) [0, 1, 2]).take 1 := by
  decide +kernel

def readyFinished : Fin 3 → SharedSliceCell (Context := Nat)
    (Control := Instruction Nat Nat Nat) (Frame := Nat) (Answer := Nat) :=
  (sharedSliceKernel (Fin 3)).batch program Prod.snd readyPartial [(0, 10)]

/-- A later grant resumes the actual paid long owner. The two short owners,
all duplicate occurrences and the old prefix survive the completed join. -/
theorem ready_resume_keeps_paid_prefix_and_duplicates :
    (readyFinished 0).1 = 11 ∧ readyFinished 1 = readyPartial 1 ∧
    readyFinished 2 = readyPartial 2 ∧
    orderedReadyPrefix (fun owner => decodeSliceCell (readyFinished owner)) [0, 1, 2] =
      [(9, 5), (9, 5), (7, 113), (7, 113), (2, 5), (3, 5)] := ⟨rfl, rfl, rfl, rfl⟩

/-- Preparing the same owner twice from one snapshot overwrites a paid suffix.
The independent-private-write condition excludes exactly this loss. -/
theorem ready_aliased_preparation_loses_work :
    ¬ (sharedSliceKernel (Context := Nat) (Control := Instruction Nat Nat Nat)
      (Call := Nat) (Frame := Nat) (Answer := Nat) (Fin 3)).Disjoint [(0, 2), (0, 2)] ∧
    decodeSliceCell ((sharedSliceKernel (Fin 3)).batch program Prod.snd readyPool
      [(0, 2), (0, 2)] 0) ≠
    decodeSliceCell ((sharedSliceKernel (Fin 3)).run program Prod.snd readyPool
      [(0, 2), (0, 2)] 0) := by
  constructor
  · decide +kernel
  · intro equal
    have charges := congrArg Prod.fst equal
    change (6 : Nat) = 8 at charges
    omega


/-- Owners may resume repeatedly on different physical workers. Paid prefixes,
private return stacks and equal answers retain their original occurrences. -/
def refillCommands : List (Fin 3 × Nat) :=
  [(0, 2), (1, 1), (0, 2), (2, 1), (0, 10)]

def refillFinished : Fin 3 → SharedSliceCell (Context := Nat)
    (Control := Instruction Nat Nat Nat) (Frame := Nat) (Answer := Nat) :=
  (sharedSliceKernel (Fin 3)).run program Prod.snd readyPool refillCommands

theorem refill_preserves_paid_prefix_and_all_owners :
    (refillFinished 0).1 = 11 ∧ refillFinished 1 = readyFinished 1 ∧
      refillFinished 2 = readyFinished 2 ∧
      orderedReadyPrefix (fun owner => decodeSliceCell (refillFinished owner)) [0, 1, 2] =
        [(9, 5), (9, 5), (7, 113), (7, 113), (2, 5), (3, 5)] := ⟨rfl, rfl, rfl, rfl⟩

theorem arbitrary_refills_extend_the_published_prefix (grants : List (Fin 3 × Nat)) :
    ∃ suffix,
      orderedReadyPrefix (fun owner => decodeSliceCell
        ((sharedSliceKernel (Fin 3)).run program Prod.snd readyPartial grants owner)) [0, 1, 2] =
        [(9, 5), (9, 5)] ++ suffix := by
  simpa only [ready_later_answers_stay_buffered] using
    shared_refill_published_extension program grants readyPartial [0, 1, 2]

/-- Reopening a completed first owner keeps every local output list unchanged,
but hides later owners which have already been published. -/
def reopenedOwner : Fin 3 → ReferenceSliceCell (Context := Nat)
    (Control := Instruction Nat Nat Nat) (Frame := Nat) (Answer := Nat) :=
  Function.update (fun owner => decodeSliceCell (readyFinished owner)) 0
    ((readyFinished 0).1,
      ⟨[⟨7, .ret 999, []⟩], (readyFinished 0).2.1.emitted⟩)

theorem reopening_keeps_all_local_occurrences (owner : Fin 3) :
    (reopenedOwner owner).2.emitted = (decodeSliceCell (readyFinished owner)).2.emitted := by
  fin_cases owner <;> rfl

theorem reopening_completed_owner_retracts_global_occurrences :
    ¬ ∃ suffix, orderedReadyPrefix reopenedOwner [0, 1, 2] =
      orderedReadyPrefix (fun owner => decodeSliceCell (readyFinished owner)) [0, 1, 2] ++ suffix := by
  rintro ⟨suffix, equal⟩
  have lengths := congrArg List.length equal
  rw [List.length_append] at lengths
  change 4 = 6 + suffix.length at lengths
  omega

end SliceControls

namespace FrontierControls

def later : List (RootTask Nat (Instruction Nat Nat Nat)) := [⟨42, .ret 9, 0⟩]

def joined : CheckedState Nat (Instruction Nat Nat Nat) Nat Nat :=
  appendCheckedFrontier (encode SliceControls.captured) later (by
    intro task member
    simp only [later, List.mem_cons, List.not_mem_nil, or_false] at member
    subst task
    exact Nat.zero_le _)

/-- The paid handoff keeps duplicate old and new answers, the later target,
and the original return arena. -/
theorem completed_paid_frontier_retains_later_target :
    let detached := MachineCore.runSlice (sharedCore SliceControls.program) 20
      (encode SliceControls.captured)
    let retained := MachineCore.runSlice (sharedCore SliceControls.program) detached.2 joined
    detached.2 = 7 ∧ retained.2 = 7 ∧
      retained.1.1.emitted = [(9,5),(9,5),(7,113),(7,113)] ∧
      retained.1.1.frontier = later ∧
      retained.1.1.arena = [(10,1),(100,0)] ∧ retained.1.1.arena.expand 1 = [100] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem partial_paid_frontier_retains_all_return_frames :
    let retained := MachineCore.runSlice (sharedCore SliceControls.program) 2 joined
    retained.2 = 2 ∧ retained.1.1.decode =
      ⟨[⟨7,.ret 13,[100]⟩,⟨7,.ret 3,[10,100]⟩,⟨42,.ret 9,[]⟩],[(9,5),(9,5)]⟩ := by
  exact ⟨rfl, rfl⟩

/-- Reusing the requested allowance after an early completion crosses the
intended handoff boundary and consumes the later alternative. -/
theorem unused_allowance_advances_later_alternative :
    let overrun := MachineCore.runSlice (sharedCore SliceControls.program) 20 joined
    overrun.2 = 8 ∧ overrun.1.1.frontier = [] ∧
      overrun.1.1.emitted = [(9,5),(9,5),(7,113),(7,113),(42,9)] := by
  decide +kernel

end FrontierControls



namespace ReturnElisionControls

def program : Program Nat (Instruction Nat Bool Nat) Nat Bool Nat where
  inspect := id
  branches context value := [(context, .ret value), (context, .ret value)]
  resume context frame value :=
    if frame then (context, .ret value) else (context + 10, .ret (value + 1))

def transparent : TransparentReturns program where
  erase := id
  resume_context := by
    intro context frame value erased
    change frame = true at erased
    subst frame
    rfl
  resume_return := by
    intro context frame value erased
    change frame = true at erased
    subst frame
    rfl

def captured : State Nat (Instruction Nat Bool Nat) Bool Nat :=
  ⟨[⟨1, .call 7 true, [false]⟩], [(99, 7)]⟩

theorem elision_retains_duplicate_answers_and_opaque_caller :
    (MachineCore.runSlice (referenceCore program) 20 captured).1.emitted =
        [(99, 7), (11, 8), (11, 8)] ∧
      (MachineCore.runSlice (referenceCore transparent.program) 20
        (transparent.state captured)).1.emitted = [(99, 7), (11, 8), (11, 8)] ∧
      (MachineCore.runSlice (referenceCore program) 20 captured).2 = 7 ∧
      (MachineCore.runSlice (referenceCore transparent.program) 20
        (transparent.state captured)).2 = 5 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem administration_counts_do_not_agree :
    (MachineCore.runSlice (referenceCore program) 20 captured).2 ≠
      (MachineCore.runSlice (referenceCore transparent.program) 20
        (transparent.state captured)).2 := by
  decide +kernel

theorem partial_slice_retains_opaque_return :
    (transparent.state (MachineCore.runSlice (referenceCore program) 2 captured).1).frontier =
      [⟨1, .ret 7, [false]⟩, ⟨1, .ret 7, [false]⟩] := rfl

theorem opaque_frame_is_not_transparent :
    (program.resume 1 false 7).1 ≠ 1 ∧
      program.inspect (program.resume 1 false 7).2 ≠ .ret 7 := by
  constructor
  · decide +kernel
  · intro same
    have impossible : (8 : Nat) = 7 := Instruction.ret.inj same
    omega

def pendingTransparentReturns : State Nat (Instruction Nat Bool Nat) Bool Nat :=
  ⟨[⟨1, .ret 7, [true, true, false]⟩], [(99, 7)]⟩

theorem one_fused_step_retains_the_actual_three_dispatch_endpoint :
    (MachineCore.runSlice (referenceCore program) 3 pendingTransparentReturns).2 = 3 ∧
      (MachineCore.runSlice (referenceCore transparent.program) 1
        (transparent.state pendingTransparentReturns)).2 = 1 ∧
      transparent.state (MachineCore.runSlice (referenceCore program) 3
          pendingTransparentReturns).1 =
        (MachineCore.runSlice (referenceCore transparent.program) 1
          (transparent.state pendingTransparentReturns)).1 := by
  exact ⟨rfl, rfl, rfl⟩

theorem opaque_return_cannot_be_registered_for_elision :
    ¬ ∃ law : TransparentReturns program, law.erase false = true := by
  rintro ⟨law, erased⟩
  exact opaque_frame_is_not_transparent.1 (law.resume_context 1 false 7 erased)

end ReturnElisionControls

end Mettapedia.Machines.SharedContinuation
