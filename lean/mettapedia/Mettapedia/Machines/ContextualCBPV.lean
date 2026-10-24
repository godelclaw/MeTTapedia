import Mettapedia.Machines.NativeCallReturn
import Mettapedia.Machines.ResumableRegion

/-!
# Contextual computations and retained continuations

Values, immutable suspension references, computations and continuations have
different roles. A dialect supplies lexical lookup, suspension construction,
force interpretation and native effects. The kernel sequences their results;
it does not infer execution permission from the spelling of a value.

Choice saves the lexical context and continuation, while effects remain in the
world. Logical stores, their rollback and Need memoization are not identified
with this lexical context. Those require their own concrete adapters.

Native entry changes control to a retained worker. Each pull retains the
returned branch's context and may perform further producer work. A worker can
fail or stop without invoking its entrance again. Native-return cursors are
one concrete instance of this interface, not its universal representation.
Source debits are explicit nodes: administrative transitions do not invent
source fuel. Worker-internal accounting requires the worker's own refinement.
This module does not assert that every C transition has yet been related to
this kernel or that its abstract transitions have unit native cost.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ContextualCBPV

open NativeCallReturn

variable (Value Call Effect Fault Delay Suspension Context World Worker : Type)

/-- The continuation receives provenance and conditional obligations as well
as the value. Raised control never enters an ordinary value continuation. -/
inductive Computation where
  | returned (value : Value)
  | sequence (producer : Computation) (body : Packet Value Fault Delay → Computation)
  | invoke (call : Call)
  | thunk (reference : Suspension)
  | force (value : Value)
  | choice (first second : Computation)
  | failure
  | raised (fault : Fault)
  | handle (producer : Computation) (handler : Fault → Computation)
  | native (effect : Effect)
  | source (occurrence debit : Nat) (body : Computation)

abbrev Code := Computation Value Call Effect Fault Delay Suspension

structure Semantics where
  /-- Current callee lookup does not execute the returned computation. -/
  enter : World → Context → Call → Context × Code Value Call Effect Fault Delay Suspension
  suspend : Context → Suspension → Value
  /-- Ordinary force reads the saved computation; it creates no Need cache. -/
  force : Context → Value → Context × Code Value Call Effect Fault Delay Suspension
  native : Context → World → Effect → World × Worker
  pull : World → Worker → World × Pull (Context × Packet Value Fault Delay) Worker
  /-- Restore lexical scope while retaining the returned logical branch. -/
  resume : Context → Context → Context

inductive Frame where
  | sequence (context : Context)
      (body : Packet Value Fault Delay → Code Value Call Effect Fault Delay Suspension)
  | handler (context : Context) (choiceFloor : Nat)
      (body : Fault → Code Value Call Effect Fault Delay Suspension)
  | restore (context : Context)

inductive Control where
  | compute (context : Context) (code : Code Value Call Effect Fault Delay Suspension)
  | delivery (worker : Worker)
  | returned (context : Context) (packet : Packet Value Fault Delay)
  | failed
  | stopped (reason : Stop)
  | unhandled (fault : Fault)

structure Work where
  control : Control Value Call Effect Fault Delay Suspension Context Worker
  frames : List (Frame Value Call Effect Fault Delay Suspension Context) := []

structure State where
  world : World
  focus : Work Value Call Effect Fault Delay Suspension Context Worker
  alternatives : List (Work Value Call Effect Fault Delay Suspension Context Worker) := []
  published : List (Context × Packet Value Fault Delay) := []
  nativeEntries : Nat := 0
  spent : Nat := 0
  sourceTrace : List Nat := []

variable {Value Call Effect Fault Delay Suspension Context World Worker}

abbrev KernelSemantics := Semantics Value Call Effect Fault Delay Suspension Context World Worker
abbrev KernelState := State Value Call Effect Fault Delay Suspension Context World Worker

def initial (world : World) (context : Context)
    (code : Code Value Call Effect Fault Delay Suspension) :
    KernelState (Value := Value) (Call := Call) (Effect := Effect) (Fault := Fault)
      (Delay := Delay) (Suspension := Suspension) (Context := Context) (World := World) (Worker := Worker) :=
  ⟨world, ⟨.compute context code, []⟩, [], [], 0, 0, []⟩

private def continueAlternatives
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :=
  match state.alternatives with
  | [] => {state with focus := ⟨.stopped .complete, []⟩}
  | next :: rest => {state with focus := next, alternatives := rest}

/-- Native work and lexical interpretation occur here. Publication is a
separate transition; the retained cursor has already crossed native entry. -/
def advance (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) : Option (KernelState
      (Value := Value) (Call := Call) (Effect := Effect) (Fault := Fault)
      (Delay := Delay) (Suspension := Suspension) (Context := Context) (World := World) (Worker := Worker)) :=
  let frames := state.focus.frames
  match state.focus.control with
  | .compute context code =>
      match code with
      | .returned value =>
          some {state with focus := ⟨.returned context (.value .completed value), frames⟩}
      | .sequence producer body =>
          some {state with focus := ⟨.compute context producer,
            .sequence context body :: frames⟩}
      | .invoke call =>
          let entered := sem.enter state.world context call
          some {state with focus := ⟨.compute entered.1 entered.2,
            .restore context :: frames⟩}
      | .thunk reference =>
          some {state with focus := ⟨.returned context
            (.value .completed (sem.suspend context reference)), frames⟩}
      | .force value =>
          let forced := sem.force context value
          some {state with focus := ⟨.compute forced.1 forced.2,
            .restore context :: frames⟩}
      | .choice first second =>
          some {state with
            focus := ⟨.compute context first, frames⟩
            alternatives := ⟨.compute context second, frames⟩ :: state.alternatives}
      | .failure => some {state with focus := ⟨.failed, frames⟩}
      | .raised fault => some {state with focus := ⟨.returned context (.raised fault), frames⟩}
      | .handle producer handler =>
          some {state with focus := ⟨.compute context producer,
            .handler context state.alternatives.length handler :: frames⟩}
      | .native effect =>
          let produced := sem.native context state.world effect
          some {state with
            world := produced.1
            focus := ⟨.delivery produced.2, frames⟩
            nativeEntries := state.nativeEntries + 1}
      | .source _ _ body => some {state with focus := ⟨.compute context body, frames⟩}
  | .delivery worker =>
      let produced := sem.pull state.world worker
      match produced.2 with
      | .returned item next =>
          some {state with
            world := produced.1
            focus := ⟨.returned item.1 item.2, frames⟩
            alternatives := ⟨.delivery next, frames⟩ :: state.alternatives}
      | .stopped .complete => some {state with world := produced.1, focus := ⟨.failed, frames⟩}
      | .stopped reason => some {state with world := produced.1, focus := ⟨.stopped reason, []⟩}
  | .returned context packet =>
      match frames with
      | .sequence saved body :: rest =>
          match packet with
          | .raised _ => some {state with focus := ⟨.returned (sem.resume saved context) packet, rest⟩}
          | _ => some {state with focus := ⟨.compute (sem.resume saved context) (body packet), rest⟩}
      | .handler saved floor handler :: rest =>
          match packet with
          | .raised fault => some {state with
              focus := ⟨.compute saved (handler fault), rest⟩
              alternatives := state.alternatives.drop (state.alternatives.length - floor)}
          | _ => some {state with focus := ⟨.returned (sem.resume saved context) packet, rest⟩}
      | .restore saved :: rest =>
          some {state with focus := ⟨.returned (sem.resume saved context) packet, rest⟩}
      | [] =>
          match packet with
          | .raised fault => some {state with focus := ⟨.unhandled fault, []⟩}
          | _ => some (continueAlternatives
              {state with published := state.published ++ [(context, packet)]})
  | .failed => some (continueAlternatives state)
  | .stopped _ | .unhandled _ => none

def debit (control : Control Value Call Effect Fault Delay Suspension Context Worker) : Nat :=
  match control with
  | .compute _ (.source _ cost _) => cost
  | _ => 0

def origin (control : Control Value Call Effect Fault Delay Suspension Context Worker) : Option Nat :=
  match control with
  | .compute _ (.source occurrence _ _) => some occurrence
  | _ => none

/-- Source charges belong to source nodes, independently of frame operations. -/
def step (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :=
  (advance sem state).map fun next => {next with
    spent := state.spent + debit state.focus.control
    sourceTrace := match origin state.focus.control with
      | some occurrence => state.sourceTrace ++ [occurrence]
      | none => state.sourceTrace}

def core (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker)) (world : World) (context : Context) :
    MachineCore (Code Value Call Effect Fault Delay Suspension) where
  State := KernelState
  load := initial world context
  step := step sem

/-- A publication acknowledgement does not step a worker. A refused loan
remains the same returned packet and context, with its continuation retained. -/
def publication (work : Work Value Call Effect Fault Delay Suspension Context Worker) :
    Option (Context × Packet Value Fault Delay) :=
  match work.control, work.frames with
  | .returned context (.value role value), [] => some (context, .value role value)
  | .returned context (.conditional value delayed), [] =>
      some (context, .conditional value delayed)
  | _, _ => none

def consumerStep (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (accept : Context × Packet Value Fault Delay → Bool)
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :=
  match publication state.focus with
  | some returned => if accept returned then step sem state else none
  | none => step sem state

theorem refused_publication_retains_packet
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (accept : Context × Packet Value Fault Delay → Bool)
    (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (returned : Context × Packet Value Fault Delay)
    (pending : publication state.focus = some returned)
    (refused : accept returned = false) : consumerStep sem accept state = none := by
  simp [consumerStep, pending, refused]

theorem step_charge (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (before after : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (advanced : step sem before = some after) :
    after.spent = before.spent + debit before.focus.control := by
  unfold step at advanced
  cases next : advance sem before with
  | none => simp [next] at advanced
  | some value => simp [next] at advanced; subst after; rfl

theorem step_source_trace
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (before after : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (advanced : step sem before = some after) :
    after.sourceTrace = match origin before.focus.control with
      | some occurrence => before.sourceTrace ++ [occurrence]
      | none => before.sourceTrace := by
  unfold step at advanced
  cases next : advance sem before with
  | none => simp [next] at advanced
  | some value => simp [next] at advanced; subst after; rfl

theorem native_entry_once (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (world : World) (context : Context) (effect : Effect) :
    advance sem (initial world context (.native effect)) = some
      ⟨(sem.native context world effect).1,
        ⟨.delivery (sem.native context world effect).2, []⟩,
        [], [], 1, 0, []⟩ := by
  simp [advance, initial]

theorem thunk_is_not_force (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (world : World) (context : Context) (reference : Suspension) :
    advance sem (initial world context (.thunk reference)) = some
      ⟨world, ⟨.returned context (.value .completed (sem.suspend context reference)), []⟩,
        [], [], 0, 0, []⟩ := by
  simp [advance, initial]

/-- Lower an already admitted worker to an invocation followed by one native
entrance. This adapter changes call lowering, not the suspension interpreter
or the effect service. Admission evidence belongs before this fragment. -/
def nativeWorker (sem : Semantics Value Call Call Fault Delay Suspension Context World Worker) :
    Semantics Value Call Call Fault Delay Suspension Context World Worker :=
  {sem with enter := fun _ context call => (context, .native call)}

/-- The independent invocation reference and the continuation kernel agree on
the complete world and return source of an admitted native worker. No value,
failure, raised control or interrupted source is collapsed at this boundary. -/
theorem admitted_worker_refines
    (sem : Semantics Value Call Call Fault Delay Suspension Context World (Cursor Value Fault Delay Context))
    (world : World) (context : Context) (call : Call)
    (source : NativeCallReturn.Invocation.Program Call Call World Value Fault Delay)
    (admitted : source.admission world call = some call)
    (backend : source.invoke world call =
      ((sem.native context world call).1, (sem.native context world call).2.source)) :
    let entered := (step (nativeWorker sem)
      (initial world context (.invoke call))).bind (step (nativeWorker sem))
    entered.map (fun state =>
      (state.world, match state.focus.control with
        | .delivery cursor => some cursor.source
        | _ => none)) =
      some ((NativeCallReturn.Invocation.reference source world call).1,
        (match (NativeCallReturn.Invocation.reference source world call).2 with
         | .inr result => some result
         | .inl _ => none)) := by
  simp [step, advance, initial, nativeWorker, debit, origin,
    NativeCallReturn.Invocation.reference, admitted, backend]

theorem split_resume (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker)) (world : World) (context : Context)
    (first second : Nat) (state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :
    (core sem world context).runSlice (first + second) state =
      let earlier := (core sem world context).runSlice first state
      let later := (core sem world context).runSlice second earlier.1
      (later.1, earlier.2 + later.2) :=
  MachineCore.runSlice_add (core sem world context) first second state

/-- A semantic purse is separate from the physical slice allowance. The
charge is checked before taking a transition, including a native entrance. -/
structure Metered where
  state : KernelState (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker)
  remaining : Nat

def meteredStep (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker))
    (meter : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) : Option (Metered
        (Value := Value) (Call := Call) (Effect := Effect) (Fault := Fault)
        (Delay := Delay) (Suspension := Suspension) (Context := Context) (World := World) (Worker := Worker)) :=
  if debit meter.state.focus.control ≤ meter.remaining then
    (step sem meter.state).map fun next =>
      ⟨next, meter.remaining - debit meter.state.focus.control⟩
  else none

theorem semantic_purse_conserved
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (before after : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (advanced : meteredStep sem before = some after) :
    after.state.spent + after.remaining = before.state.spent + before.remaining := by
  unfold meteredStep at advanced
  split at advanced
  next enough =>
    cases moved : step sem before.state with
    | none => simp [moved] at advanced
    | some state =>
        simp only [moved, Option.map_some, Option.some.injEq] at advanced
        subst after
        have charged := step_charge sem before.state state moved
        dsimp
        omega
  next => simp at advanced

theorem insufficient_source_fuel
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (meter : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (insufficient : meter.remaining < debit meter.state.focus.control) :
    meteredStep sem meter = none := by
  simp [meteredStep, Nat.not_le.mpr insufficient]

def meteredCore (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
    (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
    (Context := Context) (World := World) (Worker := Worker)) (world : World) (context : Context)
    (fuel : Nat) : MachineCore (Code Value Call Effect Fault Delay Suspension) where
  State := Metered
  load := fun code => ⟨initial world context code, fuel⟩
  step := meteredStep sem

theorem sliced_source_purse_conserved
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (world : World) (context : Context) (sourceFuel physicalSteps : Nat)
    (before : Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker)) :
    let after := ((meteredCore sem world context sourceFuel).runSlice physicalSteps before).1
    after.state.spent + after.remaining = before.state.spent + before.remaining := by
  exact MachineCore.runSlice_preserves (meteredCore sem world context sourceFuel)
    (fun meter => meter.state.spent + meter.remaining)
    (fun before after advanced => semantic_purse_conserved sem before after advanced)
    physicalSteps before

/-- Moving an administrative sequence across a source charge preserves the
exact world, continuation, alternatives and debit after the two transitions.
The charge remains present on both sides. -/
theorem sequence_charge_commutes
    (sem : KernelSemantics (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (world : World) (context : Context) (occurrence cost : Nat)
    (producer : Code Value Call Effect Fault Delay Suspension)
    (body : Packet Value Fault Delay → Code Value Call Effect Fault Delay Suspension) :
    (step sem (initial world context (.source occurrence cost (.sequence producer body)))).bind (step sem) =
    (step sem (initial world context (.sequence (.source occurrence cost producer) body))).bind (step sem) := by
  simp [step, advance, initial, debit, origin]

namespace Controls

inductive Datum where
  | number (value : Nat)
  | suspended (context reference : Nat)
  deriving DecidableEq, Repr

abbrev TestCode := Code Datum Unit Nat Nat Unit Nat

/-- An independent, state-changing native fixture: zero, one, duplicate,
raised and interrupted results have different return constructors. -/
def semantics : Semantics Datum Unit Nat Nat Unit Nat Nat Nat
    (Cursor Datum Nat Unit Nat) where
  enter := fun _ context _ => (context + 1, .native 1)
  suspend := Datum.suspended
  force := fun context value => match value with
    | .number n => (context, .returned (.number n))
    | .suspended saved reference => (saved, .native reference)
  native := fun context world effect =>
    (world + 1, ⟨(match effect with
      | 0 => .failure
      | 1 => .one (.value .completed (.number context))
      | 2 => .frontier #[.number context, .number context]
      | 3 => .one (.raised 7)
      | 5 => .one (.conditional (.number context) ())
      | _ => .interrupted), context, 0⟩)
  pull := fun world cursor => (world, NativeCallReturn.read cursor)
  resume := fun saved _ => saved

def run (context : Nat) (code : TestCode) :=
  ((core semantics 0 context).runSlice 40 (initial 0 context code)).1

theorem failed_native_keeps_effect :
    (run 4 (.native 0)).world = 1 ∧
    (run 4 (.native 0)).nativeEntries = 1 ∧
    (run 4 (.native 0)).published = [] := by decide

theorem thunk_return_does_not_run_body :
    (run 4 (.thunk 1)).world = 0 ∧
    (run 4 (.thunk 1)).published = [(4, .value .completed (.suspended 4 1))] := by decide

theorem force_reads_capture_and_restores_caller :
    (run 99 (.force (.suspended 4 1))).world = 1 ∧
    (run 99 (.force (.suspended 4 1))).published = [(99, .value .completed (.number 4))] := by decide

theorem ordinary_force_is_not_need :
    (run 99 (.sequence (.force (.suspended 4 1))
      (fun _ => .force (.suspended 4 1)))).nativeEntries = 2 := by decide

theorem duplicate_occurrences_survive :
    (run 4 (.native 2)).nativeEntries = 1 ∧
    (run 4 (.native 2)).published =
      [(4, .value .completed (.number 4)), (4, .value .completed (.number 4))] := by decide

theorem caught_raise_discards_protected_choices :
    (run 4 (.handle (.choice (.raised 7) (.native 1))
      (fun _ => .returned (.number 5)))).world = 0 ∧
    (run 4 (.handle (.choice (.raised 7) (.native 1))
      (fun _ => .returned (.number 5)))).published =
        [(4, .value .completed (.number 5))] := by decide

theorem caught_raise_preserves_outer_choice :
    (run 4 (.choice (.handle (.raised 7) (fun _ => .returned (.number 5)))
      (.native 1))).published =
        [(4, .value .completed (.number 5)), (4, .value .completed (.number 4))] := by decide

theorem caught_raise_keeps_committed_effect :
    (run 4 (.handle (.sequence (.native 1) (fun _ => .raised 7))
      (fun _ => .returned (.number 5)))).world = 1 ∧
    (run 4 (.handle (.sequence (.native 1) (fun _ => .raised 7))
      (fun _ => .returned (.number 5)))).nativeEntries = 1 := by decide

theorem uncaught_raise_is_not_a_value :
    (run 4 (.choice (.native 3) (.native 1))).world = 1 ∧
    (run 4 (.choice (.native 3) (.native 1))).published = [] ∧
    (run 4 (.choice (.native 3) (.native 1))).focus.control = .unhandled 7 :=
  ⟨rfl, rfl, rfl⟩

theorem conditional_return_keeps_obligation :
    (run 4 (.native 5)).published = [(4, .conditional (.number 4) ())] := by decide

theorem blocked_source_never_enters_native :
    let meter := ((meteredCore semantics 0 4 0).runSlice 40
      ⟨initial 0 4 (.source 9 1 (.native 1)), 0⟩).1
    meter.state.world = 0 ∧ meter.state.nativeEntries = 0 ∧ meter.state.spent = 0 := by decide

theorem interruption_is_not_failure :
    (run 4 (.choice (.native 4) (.native 1))).world = 1 ∧
    (run 4 (.choice (.native 4) (.native 1))).nativeEntries = 1 ∧
    (run 4 (.choice (.native 4) (.native 1))).focus.control = .stopped .cancelled :=
  ⟨rfl, rfl, rfl⟩

theorem source_charge_is_not_admin_steps :
    (run 4 (.source 7 2 (.sequence (.source 8 3 (.native 1))
      (fun _ => .source 9 4 (.returned (.number 8)))))).spent = 9 := by decide

theorem source_occurrences_survive_normalization :
    (run 4 (.source 7 2 (.sequence (.source 8 3 (.native 1))
      (fun _ => .source 9 4 (.returned (.number 8)))))).sourceTrace = [7, 8, 9] := by decide

theorem repeated_source_visits_are_not_a_set :
    (run 4 (.choice (.source 7 1 (.returned (.number 8)))
      (.source 7 1 (.returned (.number 8))))).sourceTrace = [7, 7] := by decide

end Controls

namespace WorkerControls

abbrev BranchContext := Nat × Nat
abbrev Returned := BranchContext × Packet Nat Nat Unit
abbrev BranchWorker := List Returned × Stop

/-- The first coordinate is lexical scope; the second is a persistent logical
branch. A resumed caller keeps its scope and the callee's branch updates. -/
def semantics : Semantics Nat Unit Nat Nat Unit Nat BranchContext Nat BranchWorker where
  enter := fun _ context _ => ((context.1 + 1, context.2), .native 0)
  suspend := fun context reference => context.1 * 100 + context.2 + reference
  force := fun context value => (context, .returned value)
  native := fun context world effect =>
    (world + 1,
      (if effect == 0 then
        [((context.1, context.2 + 1), .value .completed 4),
         ((context.1, context.2 + 2), .value .completed 5)]
       else [((context.1, context.2 + 1), .raised 7)], .complete))
  pull := fun world worker => (world + 1, referenceRead worker)
  resume := fun caller returned => (caller.1, returned.2)

def run (sem : Semantics Nat Unit Nat Nat Unit Nat BranchContext Nat BranchWorker)
    (code : Code Nat Unit Nat Nat Unit Nat) :=
  ((core sem 0 (1, 10)).runSlice 80 (initial 0 (1, 10) code)).1

theorem worker_keeps_each_returned_branch :
    (run semantics (.sequence (.native 0) (fun _ => .thunk 0))).published =
      [((1, 11), .value .completed 111), ((1, 12), .value .completed 112)] := by decide

theorem callee_restores_scope_and_keeps_bindings :
    (run semantics (.sequence (.invoke ()) (fun _ => .thunk 0))).published =
      [((1, 11), .value .completed 111), ((1, 12), .value .completed 112)] := by decide

theorem replacing_branch_with_entrance_changes_answers :
    (run {semantics with resume := fun saved _ => saved}
      (.sequence (.invoke ()) (fun _ => .thunk 0))).published ≠
      (run semantics (.sequence (.invoke ()) (fun _ => .thunk 0))).published := by decide

theorem pull_effects_do_not_reenter_native :
    (run semantics (.native 0)).world = 4 ∧
    (run semantics (.native 0)).nativeEntries = 1 := by decide

theorem handler_restores_branch_but_keeps_effects :
    (run semantics (.handle (.native 1) (fun _ => .thunk 0))).published =
      [((1, 10), .value .completed 110)] ∧
    (run semantics (.handle (.native 1) (fun _ => .thunk 0))).world = 2 := by decide

end WorkerControls

end Mettapedia.Machines.ContextualCBPV

#print axioms Mettapedia.Machines.ContextualCBPV.step_charge
#print axioms Mettapedia.Machines.ContextualCBPV.step_source_trace
#print axioms Mettapedia.Machines.ContextualCBPV.refused_publication_retains_packet
#print axioms Mettapedia.Machines.ContextualCBPV.native_entry_once
#print axioms Mettapedia.Machines.ContextualCBPV.thunk_is_not_force
#print axioms Mettapedia.Machines.ContextualCBPV.admitted_worker_refines
#print axioms Mettapedia.Machines.ContextualCBPV.split_resume
#print axioms Mettapedia.Machines.ContextualCBPV.semantic_purse_conserved
#print axioms Mettapedia.Machines.ContextualCBPV.insufficient_source_fuel
#print axioms Mettapedia.Machines.ContextualCBPV.sliced_source_purse_conserved
#print axioms Mettapedia.Machines.ContextualCBPV.sequence_charge_commutes
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.failed_native_keeps_effect
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.thunk_return_does_not_run_body
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.force_reads_capture_and_restores_caller
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.ordinary_force_is_not_need
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.duplicate_occurrences_survive
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.caught_raise_discards_protected_choices
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.caught_raise_preserves_outer_choice
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.caught_raise_keeps_committed_effect
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.uncaught_raise_is_not_a_value
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.conditional_return_keeps_obligation
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.blocked_source_never_enters_native
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.interruption_is_not_failure
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.source_charge_is_not_admin_steps
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.source_occurrences_survive_normalization
#print axioms Mettapedia.Machines.ContextualCBPV.Controls.repeated_source_visits_are_not_a_set
#print axioms Mettapedia.Machines.ContextualCBPV.WorkerControls.worker_keeps_each_returned_branch
#print axioms Mettapedia.Machines.ContextualCBPV.WorkerControls.callee_restores_scope_and_keeps_bindings
#print axioms Mettapedia.Machines.ContextualCBPV.WorkerControls.replacing_branch_with_entrance_changes_answers
#print axioms Mettapedia.Machines.ContextualCBPV.WorkerControls.pull_effects_do_not_reenter_native
#print axioms Mettapedia.Machines.ContextualCBPV.WorkerControls.handler_restores_branch_but_keeps_effects
