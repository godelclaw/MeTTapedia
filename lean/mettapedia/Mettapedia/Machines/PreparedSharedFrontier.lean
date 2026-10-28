import Mettapedia.Machines.PreparedFrontierTransfer
import Mettapedia.Machines.SharedContinuation

/-!
# Sharing the saved callers of a prepared frontier

The source installs untried equation occurrences with their captured caller
stacks. The target retains those callers in an immutable arena and puts a root
on each pending task. Layers are presented outermost first; a layer may add
one caller or inherit its predecessor's caller (a tail call).

This model assumes that successive caller stacks have precisely this suffix
relationship. Establishing that relationship for every native cursor frame,
along with the lifetime of its plans and captured values, remains a C-level
obligation. Counts here are arena nodes, not allocation bytes or native time.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PreparedSharedFrontier

open SharedContinuation

variable {Context Control Frame : Type}

/-- One source call level. Equation occurrences retain their own contexts. -/
structure Layer (Context Control Frame : Type) where
  caller : Option Frame
  equations : List (Context × Control)
  next : Nat

def extend (caller : Option Frame) (returns : List Frame) : List Frame :=
  match caller with
  | none => returns
  | some frame => frame :: returns

/-- The source uses the existing frontier installer's equation walk. -/
def sourceFrame (returns : List Frame) (layer : Layer Context Control Frame) :
    PreparedFrontierTransfer.Frame (Task Context Control Frame) where
  equations := layer.equations.map fun item => ⟨item.1, item.2, []⟩
  next := layer.next
  resume := fun task => {task with returns := extend layer.caller returns}

structure Source (Context Control Frame : Type) where
  returns : List Frame
  pending : List (Task Context Control Frame)

def sourceStep (state : Source Context Control Frame) (layer : Layer Context Control Frame) :
    Source Context Control Frame :=
  let frame := sourceFrame state.returns layer
  ⟨extend layer.caller state.returns,
    PreparedFrontierTransfer.lowerFrame frame.resume frame.equations frame.next state.pending⟩

def sourceBuild : Source Context Control Frame → List (Layer Context Control Frame) →
    Source Context Control Frame
  | state, [] => state
  | state, layer :: rest => sourceBuild (sourceStep state layer) rest

structure Shared (Context Control Frame : Type) where
  arena : Arena Frame
  root : Nat
  pending : List (RootTask Context Control)

def Shared.Valid (state : Shared Context Control Frame) : Prop :=
  state.arena.Valid ∧ state.root ≤ state.arena.length ∧
    ∀ task ∈ state.pending, task.root ≤ state.arena.length

def Shared.decode (state : Shared Context Control Frame) : Source Context Control Frame :=
  ⟨state.arena.expand state.root, state.pending.map (RootTask.decode state.arena)⟩

def sharedStep (state : Shared Context Control Frame) (layer : Layer Context Control Frame) :
    Shared Context Control Frame :=
  let (arena, root) := match layer.caller with
    | none => (state.arena, state.root)
    | some caller => ((caller, state.root) :: state.arena, state.arena.length + 1)
  let added := (layer.equations.drop layer.next).map fun item =>
    RootTask.mk item.1 item.2 root
  ⟨arena, root, added ++ state.pending⟩

def sharedBuild : Shared Context Control Frame → List (Layer Context Control Frame) →
    Shared Context Control Frame
  | state, [] => state
  | state, layer :: rest => sharedBuild (sharedStep state layer) rest

def callerCount : List (Layer Context Control Frame) → Nat
  | [] => 0
  | layer :: rest => (if layer.caller.isSome then 1 else 0) + callerCount rest

/-- A single installation step preserves all earlier roots and equation
occurrences, including duplicates and their individual contexts. -/
theorem sharedStep_exact (state : Shared Context Control Frame)
    (valid : state.Valid) (layer : Layer Context Control Frame) :
    (sharedStep state layer).Valid ∧
      (sharedStep state layer).decode = sourceStep state.decode layer := by
  rcases valid with ⟨arenaValid, rootBound, pendingBound⟩
  cases caller : layer.caller with
  | none =>
      constructor
      · simp only [sharedStep, caller, Shared.Valid, List.mem_append, List.mem_map]
        refine ⟨arenaValid, rootBound, ?_⟩
        intro task member
        rcases member with ⟨item, _, rfl⟩ | old
        · exact rootBound
        · exact pendingBound task old
      · simp [sharedStep, caller, Shared.decode, sourceStep, sourceFrame,
          extend, PreparedFrontierTransfer.lowerFrame_refines, Function.comp_def,
          RootTask.decode]
  | some frame =>
      constructor
      · simp only [sharedStep, caller, Shared.Valid, Arena.Valid, List.length_cons,
          List.mem_append, List.mem_map]
        refine ⟨⟨arenaValid, rootBound⟩, by omega, ?_⟩
        intro task member
        rcases member with ⟨item, _, rfl⟩ | old
        · simp
        · have := pendingBound task old
          omega
      · have old := decode_old_frontier state.arena frame state.root state.pending pendingBound
        simp [sharedStep, caller, Shared.decode, sourceStep, sourceFrame,
          extend, PreparedFrontierTransfer.lowerFrame_refines, Function.comp_def, RootTask.decode,
          Arena.expand, old]

theorem sharedStep_nodes (state : Shared Context Control Frame)
    (layer : Layer Context Control Frame) :
    (sharedStep state layer).arena.length = state.arena.length +
      (if layer.caller.isSome then 1 else 0) := by
  cases caller : layer.caller <;> simp [sharedStep, caller]

/-- Installing arbitrarily many layers preserves the source frontier and adds
one node per saved caller, independent of the number of equations. -/
theorem sharedBuild_exact (state : Shared Context Control Frame)
    (valid : state.Valid) (layers : List (Layer Context Control Frame)) :
    (sharedBuild state layers).Valid ∧
      (sharedBuild state layers).decode = sourceBuild state.decode layers ∧
      (sharedBuild state layers).arena.length = state.arena.length + callerCount layers := by
  induction layers generalizing state with
  | nil => simp [sharedBuild, sourceBuild, callerCount, valid]
  | cons layer rest ih =>
      obtain ⟨nextValid, nextExact⟩ := sharedStep_exact state valid layer
      obtain ⟨finalValid, finalExact, finalNodes⟩ := ih (sharedStep state layer) nextValid
      simp only [sharedBuild, sourceBuild, callerCount]
      refine ⟨finalValid, ?_, ?_⟩
      · simpa only [nextExact] using finalExact
      · rw [finalNodes, sharedStep_nodes]
        omega

/-- The original frontier installer receives one source frame per layer,
with its caller assembled from the preceding layers. -/
def sourceFrames (returns : List Frame) : List (Layer Context Control Frame) →
    List (PreparedFrontierTransfer.Frame (Task Context Control Frame))
  | [] => []
  | layer :: rest => sourceFrame returns layer ::
      sourceFrames (extend layer.caller returns) rest

theorem sourceBuild_installs (returns : List Frame)
    (pending : List (Task Context Control Frame)) (layers : List (Layer Context Control Frame)) :
    (sourceBuild ⟨returns, pending⟩ layers).pending =
      PreparedFrontierTransfer.installFrames (sourceFrames returns layers) pending := by
  induction layers generalizing returns pending with
  | nil => rfl
  | cons layer rest ih =>
      simp only [sourceBuild, sourceStep, sourceFrames, PreparedFrontierTransfer.installFrames]
      exact ih _ _

variable {Answer Call : Type}

/-- The entered control is the actual residual; it is placed ahead of the
untried equations without reconstructing its entrance. -/
def Source.finish (state : Source Context Control Frame) (entered : Context × Control)
    (emitted : List (Context × Answer)) : State Context Control Frame Answer :=
  ⟨⟨entered.1, entered.2, state.returns⟩ :: state.pending, emitted⟩

theorem source_finished_frontier (returns : List Frame)
    (layers : List (Layer Context Control Frame)) (entered : Context × Control)
    (emitted : List (Context × Answer)) :
    ((sourceBuild ⟨returns, []⟩ layers).finish entered emitted).frontier =
      PreparedFrontierTransfer.install
        ⟨entered.1, entered.2, (sourceBuild ⟨returns, []⟩ layers).returns⟩
        (sourceFrames returns layers) := by
  simp only [Source.finish, PreparedFrontierTransfer.install]
  rw [sourceBuild_installs]

def Shared.finish (state : Shared Context Control Frame) (valid : state.Valid)
    (entered : Context × Control) (emitted : List (Context × Answer)) :
    CheckedState Context Control Frame Answer :=
  ⟨⟨state.arena, ⟨entered.1, entered.2, state.root⟩ :: state.pending, emitted⟩, by
    rcases valid with ⟨arenaValid, rootBound, pendingBound⟩
    refine ⟨arenaValid, ?_⟩
    intro task member
    simp only [List.mem_cons] at member
    rcases member with rfl | later
    · exact rootBound
    · exact pendingBound task later⟩

theorem finish_decode (state : Shared Context Control Frame) (valid : state.Valid)
    (entered : Context × Control) (emitted : List (Context × Answer)) :
    (state.finish valid entered emitted).1.decode = state.decode.finish entered emitted := by
  rfl

/-- Once the frontier is installed, every bounded slice has the same actual
transition count, published prefix and complete residual as the source. This
is physical machine fuel, not the separate source-occurrence debit. -/
theorem installed_slice_exact (program : Program Context Control Call Frame Answer)
    (state : Shared Context Control Frame) (valid : state.Valid)
    (layers : List (Layer Context Control Frame)) (entered : Context × Control)
    (emitted : List (Context × Answer)) (allowance : Nat) :
    (let built := sharedBuild state layers
     let checked := built.finish (sharedBuild_exact state valid layers).1 entered emitted
     ((MachineCore.runSlice (sharedCore program) allowance checked).1.1.decode,
       (MachineCore.runSlice (sharedCore program) allowance checked).2)) =
      MachineCore.runSlice (referenceCore program) allowance
        ((sourceBuild state.decode layers).finish entered emitted) := by
  have built := sharedBuild_exact state valid layers
  have sliced := slice_exact program allowance
    ((sharedBuild state layers).finish built.1 entered emitted)
  simpa only [finish_decode, built.2.1] using sliced

/-- A split run retains the first slice's actual endpoint and its charged
transitions when execution continues in the source representation. -/
theorem installed_split_exact (program : Program Context Control Call Frame Answer)
    (state : Shared Context Control Frame) (valid : state.Valid)
    (layers : List (Layer Context Control Frame)) (entered : Context × Control)
    (emitted : List (Context × Answer)) (before after : Nat) :
    (let built := sharedBuild state layers
     let checked := built.finish (sharedBuild_exact state valid layers).1 entered emitted
     let first := MachineCore.runSlice (sharedCore program) before checked
     let later := MachineCore.runSlice (referenceCore program) after first.1.1.decode
     (later.1, first.2 + later.2)) =
      MachineCore.runSlice (referenceCore program) (before + after)
        ((sourceBuild state.decode layers).finish entered emitted) := by
  have built := sharedBuild_exact state valid layers
  have exactSlice := slice_exact program before
    ((sharedBuild state layers).finish built.1 entered emitted)
  have states := congrArg Prod.fst exactSlice
  have counts := congrArg Prod.snd exactSlice
  dsimp only at states counts ⊢
  rw [states, counts, finish_decode, built.2.1]
  exact (MachineCore.runSlice_add (referenceCore program) before after _).symm

namespace Controls

abbrev TestControl := Instruction Unit (List Nat) Nat

def program : Program (List Nat) TestControl Unit (List Nat) Nat where
  inspect := id
  branches context _ := [(context ++ [999], .ret 1)]
  resume context frame value := (context ++ frame, .ret value)

def layers : List (Layer (List Nat) TestControl (List Nat)) :=
  [⟨some [5, 5], [([30], .ret 10), ([30], .ret 11), ([30], .ret 11)], 1⟩,
   ⟨some [7, 8], [([20], .ret 20), ([21], .ret 21)], 1⟩]

def start : Shared (List Nat) TestControl (List Nat) := ⟨[], 0, []⟩

theorem start_valid : start.Valid := by simp [start, Shared.Valid, Arena.Valid]

def entered : List Nat × TestControl := ([1], .ret 1)

def built := sharedBuild start layers

theorem built_valid : built.Valid := (sharedBuild_exact start start_valid layers).1

/-- Both copies survive, the inner saved variables remain distinct, and the
outer pair remains shared. The actual entered return produces no new call. -/
theorem completed_preserves_captures_and_occurrences :
    (MachineCore.runSlice (sharedCore program) 30 (built.finish built_valid entered [])).1.1.emitted =
      [([1, 7, 8, 5, 5], 1), ([21, 7, 8, 5, 5], 21),
       ([30, 5, 5], 11), ([30, 5, 5], 11)] := by
  decide +kernel

theorem bounded_prefix_keeps_pending_work :
    let run := MachineCore.runSlice (sharedCore program) 3 (built.finish built_valid entered [])
    run.1.1.emitted = [([1, 7, 8, 5, 5], 1)] ∧ run.1.1.frontier.length = 3 ∧ run.2 = 3 := by
  decide +kernel

/-- Reconstructing the entered call performs an additional observable effect. -/
theorem replay_changes_the_first_result :
    (MachineCore.runSlice (sharedCore program) 30
        (built.finish built_valid ([1], .call () []) [])).1.1.emitted ≠
      (MachineCore.runSlice (sharedCore program) 30 (built.finish built_valid entered [])).1.1.emitted := by
  decide +kernel

/-- A wrong alias in a captured caller changes observable results. -/
theorem collapsed_distinct_capture_changes_results :
    (MachineCore.runSlice (sharedCore program) 30
      ((sharedBuild start
        [⟨some [5, 5], [([30], .ret 10), ([30], .ret 11), ([30], .ret 11)], 1⟩,
         ⟨some [7, 7], [([20], .ret 20), ([21], .ret 21)], 1⟩]).finish
        (sharedBuild_exact start start_valid _).1 entered [])).1.1.emitted ≠
      (MachineCore.runSlice (sharedCore program) 30 (built.finish built_valid entered [])).1.1.emitted := by
  decide +kernel

/-- Removing one equal equation occurrence loses one answer. -/
theorem dropping_duplicate_changes_results :
    (MachineCore.runSlice (sharedCore program) 30
      ((sharedBuild start
        [⟨some [5, 5], [([30], .ret 10), ([30], .ret 11)], 1⟩,
         ⟨some [7, 8], [([20], .ret 20), ([21], .ret 21)], 1⟩]).finish
        (sharedBuild_exact start start_valid _).1 entered [])).1.1.emitted ≠
      (MachineCore.runSlice (sharedCore program) 30 (built.finish built_valid entered [])).1.1.emitted := by
  decide +kernel

/-- A tail layer and any number of duplicate alternatives share the
existing caller rather than allocating one caller per alternative. -/
theorem tail_and_many_equations_share_one_node (count : Nat) :
    (sharedBuild start
      [⟨some [4], [([0], .ret 1)], 0⟩,
       ⟨none, List.replicate count ([2], .ret 3), 0⟩]).arena.length = 1 := by
  have nodes := (sharedBuild_exact start start_valid
    [⟨some [4], [([0], .ret 1)], 0⟩,
     ⟨none, List.replicate count ([2], .ret 3), 0⟩]).2.2
  simpa [start, callerCount] using nodes

end Controls

end Mettapedia.Machines.PreparedSharedFrontier
