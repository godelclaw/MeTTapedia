import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic
import Mettapedia.Machines.ResumableRegion

/-!
# Native invocation operands and contextual occurrence returns

A completed native invocation lends an expression, a completed value, an ordered
frontier, a raised fault, or a conditional answer. Payload syntax never selects
its control role. The reference below constructs the observable occurrence list;
the cursor instead indexes the original array and preserves its context.

`read_refines` relates each concrete cursor step to an independent list consumer.
The contexts are identities, not frozen substitutions: any interpretation under
a later binding world still reads the same context. Invalid producer data and
interruption have explicit terminal reasons, distinct from logical exhaustion.

The native connection is `CettaCallReturnCursor` in `owned_execution.h`. Native
pointer validity, array bounds, borrowed lifetimes and C correspondence remain
separate obligations. This model assumes well-formed array elements; the C reader
also refuses malformed elements when reached. The cursor does not execute the producer,
interpret returned syntax, choose a dialect policy, or add memoization.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NativeCallReturn

universe u v w x

inductive ValueRole where
  | expression
  | completed
  deriving DecidableEq, Repr

inductive Packet (Value : Type u) (Fault : Type v) (Delay : Type w) where
  | value (role : ValueRole) (payload : Value)
  | raised (fault : Fault)
  | conditional (payload : Value) (delayed : Delay)
  deriving DecidableEq, Repr

inductive Source (Value : Type u) (Fault : Type v) (Delay : Type w) where
  | one (packet : Packet Value Fault Delay)
  | frontier (values : Array Value)
  | failure
  | interrupted
  | invalid
  deriving DecidableEq, Repr

inductive Stop where
  | complete
  | cancelled
  | hostFailure
  deriving DecidableEq, Repr

abbrev Returned (Value : Type u) (Fault : Type v) (Delay : Type w)
    (Context : Type x) := Context × Packet Value Fault Delay

structure Cursor (Value : Type u) (Fault : Type v) (Delay : Type w)
    (Context : Type x) where
  source : Source Value Fault Delay
  context : Context
  position : Nat
  deriving DecidableEq, Repr

inductive Pull (Item : Type u) (State : Type v) where
  | returned (item : Item) (next : State)
  | stopped (reason : Stop)
  deriving DecidableEq, Repr

variable {Value : Type u} {Fault : Type v} {Delay : Type w} {Context : Type x}

/-- Absence of a failure is the identity. A recorded cause is preserved in
chronological order through every later native return. -/
def recordCompletion {Reason : Type u} (current observed : Option Reason) : Option Reason :=
  match current with
  | none => observed
  | some reason => some reason

theorem record_completion_assoc {Reason : Type u} (first second third : Option Reason) :
    recordCompletion (recordCompletion first second) third =
      recordCompletion first (recordCompletion second third) := by
  cases first <;> rfl

theorem recorded_cause_survives {Reason : Type u} (reason : Reason)
    (later : List (Option Reason)) :
    later.foldl recordCompletion (some reason) = some reason := by
  induction later with
  | nil => rfl
  | cons next rest ih => simpa [recordCompletion] using ih

/-- Independent reference publication: the producer's tag alone selects whether
its payload is one value or several ordered occurrences. -/
def meaning (source : Source Value Fault Delay) (context : Context) :
    List (Returned Value Fault Delay Context) × Stop :=
  match source with
  | .one packet => ([⟨context, packet⟩], .complete)
  | .frontier values =>
      (values.toList.map fun value => ⟨context, .value .completed value⟩, .complete)
  | .failure => ([], .complete)
  | .interrupted => ([], .cancelled)
  | .invalid => ([], .hostFailure)

/-- The native algorithm indexes backing storage rather than constructing the
reference list. It advances only after lending one complete return. -/
def read (cursor : Cursor Value Fault Delay Context) :
    Pull (Returned Value Fault Delay Context) (Cursor Value Fault Delay Context) :=
  match cursor.source with
  | .one packet =>
      if cursor.position = 0 then
        .returned ⟨cursor.context, packet⟩ { cursor with position := 1 }
      else .stopped .complete
  | .frontier values =>
      match values[cursor.position]? with
      | none => .stopped .complete
      | some value =>
          .returned ⟨cursor.context, .value .completed value⟩
            { cursor with position := cursor.position + 1 }
  | .failure => .stopped .complete
  | .interrupted => .stopped .cancelled
  | .invalid => .stopped .hostFailure

def residual (cursor : Cursor Value Fault Delay Context) :
    List (Returned Value Fault Delay Context) × Stop :=
  let reference := meaning cursor.source cursor.context
  (reference.1.drop cursor.position, reference.2)

def referenceRead {Item : Type u} (state : List Item × Stop) : Pull Item (List Item × Stop) :=
  match state.1 with
  | [] => .stopped state.2
  | first :: rest => .returned first (rest, state.2)

def Pull.mapState {Item : Type u} {State : Type v} {Other : Type w}
    (map : State → Other) : Pull Item State → Pull Item Other
  | .returned item next => .returned item (map next)
  | .stopped reason => .stopped reason

/-- Every array/offset step preserves the independent ordered reference,
including context, control role and exact terminal reason. -/
theorem read_refines (cursor : Cursor Value Fault Delay Context) :
    (read cursor).mapState residual = referenceRead (residual cursor) := by
  rcases cursor with ⟨source, context, position⟩
  cases source with
  | one packet =>
      cases position <;> simp [read, residual, meaning, referenceRead, Pull.mapState]
  | frontier values =>
      cases found : values[position]? with
      | none =>
          have empty : values.toList.drop position = [] := by
            apply List.drop_eq_nil_iff.mpr
            simpa using (Array.getElem?_eq_none_iff.mp found)
          simp [read, found, residual, meaning, referenceRead, Pull.mapState,
            ← List.map_drop, empty]
      | some value =>
          have listFound : values.toList[position]? = some value := by simpa using found
          obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp listFound
          have head := List.drop_eq_getElem_cons bound
          rw [equal] at head
          simp [read, found, residual, meaning, referenceRead, Pull.mapState,
            ← List.map_drop, head]
  | failure => simp [read, residual, meaning, referenceRead, Pull.mapState]
  | interrupted => simp [read, residual, meaning, referenceRead, Pull.mapState]
  | invalid => simp [read, residual, meaning, referenceRead, Pull.mapState]

/-- Bounded delivery retains the actual cursor; no accepted return is replayed. -/
def advance : Nat → Cursor Value Fault Delay Context →
    List (Returned Value Fault Delay Context) × Cursor Value Fault Delay Context
  | 0, cursor => ([], cursor)
  | allowance + 1, cursor =>
      match read cursor with
      | .stopped _ => ([], cursor)
      | .returned item next =>
          let later := advance allowance next
          (item :: later.1, later.2)

private theorem read_returned_residual
    {cursor next : Cursor Value Fault Delay Context}
    {item : Returned Value Fault Delay Context}
    (returned : read cursor = .returned item next) :
    residual cursor = (item :: (residual next).1, (residual next).2) := by
  have step := read_refines cursor
  rw [returned] at step
  cases reference : residual cursor with
  | mk items reason =>
      cases items with
      | nil => simp [Pull.mapState, reference, referenceRead] at step
      | cons first rest =>
          simp only [Pull.mapState, reference, referenceRead,
            Pull.returned.injEq] at step
          rcases step with ⟨rfl, equal⟩
          rw [equal]

private theorem read_stopped_residual
    {cursor : Cursor Value Fault Delay Context} {reason : Stop}
    (stopped : read cursor = .stopped reason) : (residual cursor).1 = [] := by
  have step := read_refines cursor
  rw [stopped] at step
  cases reference : residual cursor with
  | mk items terminal =>
      cases items with
      | nil => rfl
      | cons first rest => simp [Pull.mapState, reference, referenceRead] at step

/-- The concrete cursor publishes exactly the demanded ordered prefix and
retains the entire remaining reference. -/
theorem advance_exact (allowance : Nat) (cursor : Cursor Value Fault Delay Context) :
    (advance allowance cursor).1 = (residual cursor).1.take allowance ∧
    residual (advance allowance cursor).2 =
      ((residual cursor).1.drop allowance, (residual cursor).2) := by
  induction allowance generalizing cursor with
  | zero => simp [advance]
  | succ allowance ih =>
      cases step : read cursor with
      | stopped reason =>
          have empty := read_stopped_residual step
          simp only [advance, step]
          constructor
          · simp [empty]
          · apply Prod.ext
            · simp [empty]
            · rfl
      | returned item next =>
          have reference := read_returned_residual step
          obtain ⟨initial, rest⟩ := ih next
          simp [advance, step, reference, initial, rest]

/-- Splitting the allowance preserves every return and the exact retained
machine, even when the first slice reaches exhaustion. -/
theorem advance_add (first second : Nat) (cursor : Cursor Value Fault Delay Context) :
    advance (first + second) cursor =
      let earlier := advance first cursor
      let later := advance second earlier.2
      (earlier.1 ++ later.1, later.2) := by
  induction first generalizing cursor with
  | zero => simp [advance]
  | succ first ih =>
      cases step : read cursor with
      | stopped reason =>
          have halted : ∀ n, advance n cursor = ([], cursor) := by
            intro n
            cases n <;> simp [advance, step]
          simp [halted]
      | returned item next =>
          simp [Nat.succ_add, advance, step, ih, List.cons_append]

/-- No publication budget can produce more returns than its allowance. -/
theorem advance_length_le (allowance : Nat) (cursor : Cursor Value Fault Delay Context) :
    (advance allowance cursor).1.length ≤ allowance := by
  rw [(advance_exact allowance cursor).1]
  exact List.length_take_le _ _

/-- The C final-return certificate concerns only this producer's remaining
occurrences. It grants no evaluation or constraint-solving permission. -/
def finalReturn (cursor : Cursor Value Fault Delay Context) : Bool :=
  match cursor.source with
  | .one _ => true
  | .frontier values => cursor.position + 1 == values.size
  | _ => false

theorem final_return_exact {cursor next : Cursor Value Fault Delay Context}
    {item : Returned Value Fault Delay Context}
    (returned : read cursor = .returned item next) :
    finalReturn cursor = true ↔ (residual next).1 = [] := by
  rcases cursor with ⟨source, context, position⟩
  cases source <;> simp only [read] at returned
  case one packet =>
    split at returned
    · rcases Pull.returned.inj returned with ⟨rfl, rfl⟩
      simp [finalReturn, residual, meaning]
    · contradiction
  case frontier values =>
    split at returned
    · contradiction
    · rename_i value found
      rcases Pull.returned.inj returned with ⟨rfl, rfl⟩
      have listFound : values.toList[position]? = some value := by simpa using found
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp listFound
      have within : position < values.size := by simpa using bound
      simp only [finalReturn, beq_iff_eq, residual, meaning, ← List.map_drop,
        List.map_eq_nil_iff, List.drop_eq_nil_iff, Array.length_toList]
      omega
  all_goals contradiction

/-- The implementation completes publication with exactly one accepted-return
unit per remaining occurrence. It does not traverse future occurrences. -/
theorem publication_allowance_attained (cursor : Cursor Value Fault Delay Context) :
    (advance (residual cursor).1.length cursor).1 = (residual cursor).1 := by
  simpa using (advance_exact (residual cursor).1.length cursor).1

/-- A smaller publication allowance cannot deliver the same complete ordered
stream: each actual cursor transition lends at most one occurrence. -/
theorem publication_allowance_minimal (cursor : Cursor Value Fault Delay Context)
    (allowance : Nat)
    (complete : (advance allowance cursor).1 = (residual cursor).1) :
    (residual cursor).1.length ≤ allowance := by
  rw [← complete]
  exact advance_length_le allowance cursor

/-- The context is carried unchanged, so arbitrary later-world observations
see the same identities rather than a captured substitution image. -/
theorem returned_context {cursor next : Cursor Value Fault Delay Context}
    {item : Returned Value Fault Delay Context}
    (returned : read cursor = .returned item next) : item.1 = cursor.context := by
  rcases cursor with ⟨source, context, position⟩
  cases source <;> simp [read] at returned
  case one packet =>
    split at returned
    · exact (congrArg Prod.fst (Pull.returned.inj returned).1).symm
    · contradiction
  case frontier values =>
    split at returned
    · contradiction
    · exact (congrArg Prod.fst (Pull.returned.inj returned).1).symm

theorem later_world_observation {World : Type*} {Observed : Type*}
    (observe : World → Context → Observed) (world : World)
    {cursor next : Cursor Value Fault Delay Context}
    {item : Returned Value Fault Delay Context}
    (returned : read cursor = .returned item next) :
    observe world item.1 = observe world cursor.context := by
  rw [returned_context returned]

namespace Arguments

/-- Ordered preparation with a borrowed prefix. On the first changed identity,
the call needs independent vector storage; the remaining values are prepared
in order. This models immutable argument identities, not evaluation effects. -/
def prepare {Argument : Type*} [DecidableEq Argument]
    (resolve : Argument → Argument) : List Argument → Bool × List Argument
  | [] => (false, [])
  | argument :: rest =>
      let ready := resolve argument
      if ready = argument then
        let tail := prepare resolve rest
        (tail.1, argument :: tail.2)
      else
        (true, ready :: rest.map resolve)

/-- Independent eager preparation and copy-on-replacement deliver exactly the
same ordered identities, including repeated arguments. -/
theorem prepare_exact {Argument : Type*} [DecidableEq Argument]
    (resolve : Argument → Argument) (arguments : List Argument) :
    (prepare resolve arguments).2 = arguments.map resolve := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
      by_cases same : resolve argument = argument
      · simpa [prepare, same] using congrArg (argument :: ·) ih
      · simp [prepare, same]

/-- Borrowing is allowed precisely when the entire vector is unchanged. A
changed suffix cannot silently overwrite the source or omit its prefix. -/
theorem borrow_iff_unchanged {Argument : Type*} [DecidableEq Argument]
    (resolve : Argument → Argument) (arguments : List Argument) :
    (prepare resolve arguments).1 = false ↔ arguments.map resolve = arguments := by
  induction arguments with
  | nil => simp [prepare]
  | cons argument rest ih =>
      by_cases same : resolve argument = argument
      · simpa [prepare, same] using ih
      · simp [prepare, same]

example : prepare id [1, 1, 2] = (false, [1, 1, 2]) := by decide
example : prepare (fun n : Nat => if n = 2 then 3 else n) [1, 1, 2] =
    (true, [1, 1, 3]) := by decide
example : (prepare (fun n : Nat => n + 1) [1, 1, 2]).1 ≠ false := by decide

/-- Invocation storage retains captured and newly supplied identities in two
borrowed arrays. The logical world and evaluation demand are not captured by
this representation. Native pointer lifetimes remain a separate obligation. -/
structure Input (Argument : Type*) where
  head : Argument
  captured : Array Argument
  supplied : Array Argument

namespace Input

variable {Argument Observed World : Type*}

def arity (input : Input Argument) : Nat := input.captured.size + input.supplied.size

/-- Independent flat argument meaning, including repeated occurrences. -/
def arguments (input : Input Argument) : List Argument :=
  input.captured.toList ++ input.supplied.toList

/-- A constant number of discriminations selects the original array cell;
no concatenated vector or substituted application is constructed. -/
def read (input : Input Argument) (index : Nat) : Option Argument :=
  if index < input.captured.size then input.captured[index]?
  else input.supplied[index - input.captured.size]?

theorem arguments_length (input : Input Argument) :
    input.arguments.length = input.arity := by simp [arguments, arity]

theorem read_refines (input : Input Argument) (index : Nat) :
    input.read index = input.arguments[index]? := by
  by_cases captured : index < input.captured.size
  · unfold arguments
    rw [List.getElem?_append_left (by simpa using captured)]
    simp [read, captured]
  · unfold arguments
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt captured)]
    simp [read, captured]

theorem read_outside (input : Input Argument) (index : Nat)
    (outside : input.arity ≤ index) : input.read index = none := by
  rw [read_refines]
  exact List.getElem?_eq_none (by simpa [arguments_length] using outside)

/-- Syntax consumers observe the head before its ordered argument fields. -/
def field (input : Input Argument) : Nat → Option Argument
  | 0 => some input.head
  | index + 1 => input.read index

theorem field_refines (input : Input Argument) (index : Nat) :
    input.field index = (input.head :: input.arguments)[index]? := by
  cases index with
  | zero => rfl
  | succ index => exact read_refines input index

/-- Qualification or substitution belongs to the consuming world. In
particular the invocation stores lexical identities, not their old values. -/
theorem observe_current_world (input : Input Argument)
    (observe : World → Argument → Observed) (world : World) (index : Nat) :
    (input.field index).map (observe world) =
      ((input.head :: input.arguments).map (observe world))[index]? := by
  rw [field_refines]
  rw [List.getElem?_map]

/-- The copying/native-ABI path observes each admitted operand in order.
The contiguous loan path has the same meaning without constructing this list. -/
def gather (input : Input Argument) (observe : Argument → Observed)
    (index : Nat) : Nat → Option (List Observed)
  | 0 => some []
  | count + 1 =>
      match input.read index with
      | none => none
      | some argument =>
          match gather input observe (index + 1) count with
          | none => none
          | some rest => some (observe argument :: rest)

theorem gather_refines (input : Input Argument) (observe : Argument → Observed)
    (index count : Nat) (fits : index + count ≤ input.arity) :
    input.gather observe index count =
      some (((input.arguments.drop index).take count).map observe) := by
  induction count generalizing index with
  | zero => simp [gather]
  | succ count ih =>
      have within : index < input.arguments.length := by
        rw [arguments_length]
        omega
      have found : input.arguments[index]? = some input.arguments[index] :=
        List.getElem?_eq_some_iff.mpr ⟨within, rfl⟩
      have split := List.drop_eq_getElem_cons within
      rw [gather, read_refines, found, ih (index + 1) (by omega), split]
      rfl

theorem gather_full (input : Input Argument) (observe : Argument → Observed) :
    input.gather observe 0 input.arity = some (input.arguments.map observe) := by
  have exact := gather_refines input observe 0 input.arity (by omega)
  simpa only [List.drop_zero, ← arguments_length input, List.take_length] using exact

example :
    let input : Input Nat := ⟨9, #[1, 1], #[2, 1]⟩
    [input.read 0, input.read 1, input.read 2, input.read 3, input.read 4] =
      [some 1, some 1, some 2, some 1, none] := by decide

/-- A cached observation would be wrong even though the invocation and its
lexical identity have not changed. -/
example :
    let input : Input Nat := ⟨9, #[1], #[]⟩
    (input.read 0).map (fun identity => identity + 10) ≠
      (input.read 0).map (fun identity => identity + 20) := by decide

end Input

end Arguments

namespace Invocation

variable {Input Call World : Type*}

inductive Control (Input Call Value Fault Delay : Type*) where
  | inspect (input : Input)
  | invoke (call : Call)
  | deliver (source : Source Value Fault Delay)
  | authored (input : Input)

structure Frame (Input Call World Value Fault Delay : Type*) where
  world : World
  control : Control Input Call Value Fault Delay
  nativeEntries : Nat := 0
  authoredEntries : Nat := 0

/-- Admission observes the logical entrance world. Only invocation commits
native work. An entered call can deliver any source, including failure or
interruption. Allocator bookkeeping and native lifetimes are outside this
world-preservation result. -/
structure Program (Input Call World Value Fault Delay : Type*) where
  admission : World → Input → Option Call
  invoke : World → Call → World × Source Value Fault Delay

def step (program : Program Input Call World Value Fault Delay)
    (frame : Frame Input Call World Value Fault Delay) :
    Frame Input Call World Value Fault Delay :=
  match frame.control with
  | .inspect input =>
      match program.admission frame.world input with
      | none => {frame with control := .authored input,
                            authoredEntries := frame.authoredEntries + 1}
      | some call => {frame with control := .invoke call}
  | .invoke call =>
      let result := program.invoke frame.world call
      {frame with world := result.1, control := .deliver result.2,
                  nativeEntries := frame.nativeEntries + 1}
  | .deliver _ | .authored _ => frame

def initial (world : World) (input : Input) :
    Frame Input Call World Value Fault Delay := ⟨world, .inspect input, 0, 0⟩

/-- Direct reference: admission selects authored execution or one committed
native result. It never consults the result's cardinality to select fallback. -/
def reference (program : Program Input Call World Value Fault Delay)
    (world : World) (input : Input) :
    World × (Input ⊕ Source Value Fault Delay) :=
  match program.admission world input with
  | none => (world, .inl input)
  | some call =>
      let result := program.invoke world call
      (result.1, .inr result.2)

def readback (frame : Frame Input Call World Value Fault Delay) :
    Option (World × (Input ⊕ Source Value Fault Delay)) :=
  match frame.control with
  | .deliver source => some (frame.world, .inr source)
  | .authored input => some (frame.world, .inl input)
  | .inspect _ | .invoke _ => none

theorem two_steps_refine (program : Program Input Call World Value Fault Delay)
    (world : World) (input : Input) :
    readback (step program (step program (initial world input))) =
      some (reference program world input) := by
  cases admitted : program.admission world input <;>
    simp [step, initial, readback, reference, admitted]

/-- Committed effects and the complete tagged result survive the return
boundary. Empty results cannot schedule another authored entrance. -/
theorem entered_call_exact (program : Program Input Call World Value Fault Delay)
    (world : World) (input : Input) (call : Call)
    (admitted : program.admission world input = some call) :
    step program (step program (initial world input)) =
      ⟨(program.invoke world call).1, .deliver (program.invoke world call).2, 1, 0⟩ := by
  simp [step, initial, admitted]

theorem refusal_preserves_world (program : Program Input Call World Value Fault Delay)
    (world : World) (input : Input)
    (refused : program.admission world input = none) :
    step program (initial world input) = ⟨world, .authored input, 0, 1⟩ := by
  simp [step, initial, refused]

/-- The lossy projection that conflates an executed failure with refusal. -/
def eraseFailure : Option (Source Value Fault Delay) → Option (Source Value Fault Delay)
  | some .failure => none
  | result => result

/-- No decision based on that projection can recover admission for every call.
This is why a Boolean admission result must accompany the tagged outcome. -/
theorem admission_not_recoverable :
    ¬ ∃ decide : Option (Source Value Fault Delay) → Bool,
      ∀ result, decide (eraseFailure result) = result.isSome := by
  rintro ⟨decide, correct⟩
  have declined := correct none
  have failed := correct (some .failure)
  simp only [eraseFailure, Option.isSome_none] at declined
  simp only [eraseFailure, Option.isSome_some] at failed
  rw [declined] at failed
  contradiction

inductive Term (Literal Code : Type*) where
  | literal (value : Literal)
  | code (body : Code)
  deriving DecidableEq

/-- Interpretation is confined to expression-role code. The world can contain
fuel, effects and bindings; literal completion changes none of them. -/
def finish {Literal Code : Type*}
    (interpret : World → Code → World × List (Term Literal Code))
    (world : World) (role : ValueRole) (term : Term Literal Code) :
    World × List (Term Literal Code) :=
  match role, term with
  | .expression, .code body => interpret world body
  | _, _ => (world, [term])

/-- Closed literals need no executable value delimiter. This normalization is
invalid for arbitrary code-shaped payloads, as the separating control shows. -/
theorem literal_completion_role {Literal Code : Type*}
    (interpret : World → Code → World × List (Term Literal Code))
    (world : World) (literal : Literal) :
    finish interpret world .completed (.literal literal) =
      finish interpret world .expression (.literal literal) := rfl

example :
    let program : Program Unit Unit Nat Nat Unit Unit :=
      ⟨fun _ _ => some (), fun world _ => (world + 1, .failure)⟩
    let result := step program (step program (initial 0 ()))
    result.world = 1 ∧ result.nativeEntries = 1 ∧ result.authoredEntries = 0 := by
  decide

example :
    finish (fun world (_ : Unit) => (world + 1, [.literal 7])) 0
      .completed (.code ()) ≠
    finish (fun world (_ : Unit) => (world + 1, [.literal 7])) 0
      .expression (.code ()) := by decide

end Invocation

namespace InvocationSlice

variable {Input Call World Datum Raised Obligation : Type}

/-- The invocation protocol as a resumable machine. Inspecting admission and
invoking are actual transitions; delivery and authored handoff are terminal
for this machine, whose consumer owns the next computation. Transition counts
here are protocol steps, not native activations or another dialect's fuel. -/
def core (program : Invocation.Program Input Call World Datum Raised Obligation) :
    MachineCore (World × Input) where
  State := Invocation.Frame Input Call World Datum Raised Obligation
  load := fun entrance => Invocation.initial entrance.1 entrance.2
  step := fun frame => match frame.control with
    | .inspect _ | .invoke _ => some (Invocation.step program frame)
    | .deliver _ | .authored _ => none

theorem slice_entered
    (program : Invocation.Program Input Call World Datum Raised Obligation)
    (world : World) (input : Input) (call : Call)
    (admitted : program.admission world input = some call) :
    MachineCore.runSlice (core program) 2 (Invocation.initial world input) =
      (⟨(program.invoke world call).1, .deliver (program.invoke world call).2, 1, 0⟩, 2) := by
  simp [MachineCore.runSlice, core, Invocation.initial, Invocation.step, admitted]

theorem slice_refused
    (program : Invocation.Program Input Call World Datum Raised Obligation)
    (world : World) (input : Input)
    (refused : program.admission world input = none) :
    MachineCore.runSlice (core program) 2 (Invocation.initial world input) =
      (⟨world, .authored input, 0, 1⟩, 1) := by
  simp [MachineCore.runSlice, core, Invocation.initial, Invocation.step, refused]

/-- The shared slicing law retains the complete invocation state, including
its actual post-call world and its debit. It does not reload source input. -/
theorem split_resume
    (program : Invocation.Program Input Call World Datum Raised Obligation)
    (first extra : Nat) (frame : Invocation.Frame Input Call World Datum Raised Obligation) :
    MachineCore.runSlice (core program) (first + extra) frame =
      let earlier := MachineCore.runSlice (core program) first frame
      let later := MachineCore.runSlice (core program) extra earlier.1
      (later.1, earlier.2 + later.2) :=
  MachineCore.runSlice_add (core program) first extra frame

theorem delivered_slice
    (program : Invocation.Program Input Call World Datum Raised Obligation)
    (frame : Invocation.Frame Input Call World Datum Raised Obligation)
    (source : Source Datum Raised Obligation)
    (delivered : frame.control = .deliver source) (extra : Nat) :
    MachineCore.runSlice (core program) extra frame = (frame, 0) := by
  apply MachineCore.runSlice_of_final
  simp [core, delivered]

/-- Any result, including an entered failure, stays entered after more work
is offered. The invocation cannot become authored fallback or run again. -/
theorem entered_resume
    (program : Invocation.Program Input Call World Datum Raised Obligation)
    (world : World) (input : Input) (call : Call)
    (admitted : program.admission world input = some call) (extra : Nat) :
    MachineCore.runSlice (core program) extra
        (MachineCore.runSlice (core program) 2 (Invocation.initial world input)).1 =
      (⟨(program.invoke world call).1, .deliver (program.invoke world call).2, 1, 0⟩, 0) := by
  rw [slice_entered program world input call admitted]
  exact delivered_slice program _ _ rfl extra

private def effectThenFail : Invocation.Program Unit Unit Nat Nat String Unit where
  admission := fun _ _ => some ()
  invoke := fun world _ => (world + 1, .failure)

/-- Restarting from the post-call world repeats the effect. Resuming the
actual machine preserves the one committed effect even though it failed. -/
example :
    let machine := core effectThenFail
    let entered := (MachineCore.runSlice machine 2 (Invocation.initial 0 ())).1
    (MachineCore.runSlice machine 5 entered).1.world = 1 ∧
      (MachineCore.runSlice machine 2 (Invocation.initial entered.world ())).1.world = 2 := by
  decide

example :
    let machine := core effectThenFail
    let paused := MachineCore.runSlice machine 1 (Invocation.initial 0 ())
    paused.2 = 1 ∧ (machine.step paused.1).isSome = true := by
  decide

end InvocationSlice

namespace NativeDelivery

/-- Native admission has already succeeded. Immediate delivery and a retained
return cursor are physical realizations of that entered call, never a refusal. -/
inductive Route (Value : Type u) (Fault : Type v) (Delay : Type w)
    (Context : Type x) where
  | ready (item : Returned Value Fault Delay Context)
  | stopped (reason : Stop)
  | pending (cursor : Cursor Value Fault Delay Context)

def lower (source : Source Value Fault Delay) (context : Context) :
    Route Value Fault Delay Context :=
  match source with
  | .one (.value role value) => .ready (context, .value role value)
  | .one (.raised fault) => .ready (context, .raised fault)
  | .failure => .stopped .complete
  | .invalid => .stopped .hostFailure
  | .one (.conditional _ _) | .frontier _ | .interrupted =>
      .pending ⟨source, context, 0⟩

/-- A physical return step: an inline register, an exact stop, or the existing
array/offset reader. No operation in this interface can invoke the callee. -/
def read : Route Value Fault Delay Context →
    Pull (Returned Value Fault Delay Context) (Route Value Fault Delay Context)
  | .ready item => .returned item (.stopped .complete)
  | .stopped reason => .stopped reason
  | .pending cursor =>
      match NativeCallReturn.read cursor with
      | .returned item next => .returned item (.pending next)
      | .stopped reason => .stopped reason

def image : Route Value Fault Delay Context →
    List (Returned Value Fault Delay Context) × Stop
  | .ready item => ([item], .complete)
  | .stopped reason => ([], reason)
  | .pending cursor => residual cursor

/-- The two physical return routes have the same ordered observations,
including control provenance, conditional roots and the terminal reason. -/
theorem read_refines (route : Route Value Fault Delay Context) :
    (read route).mapState image = referenceRead (image route) := by
  cases route with
  | ready item => rfl
  | stopped reason => rfl
  | pending cursor =>
      have exactRead := NativeCallReturn.read_refines cursor
      cases step : NativeCallReturn.read cursor <;>
        simpa [read, image, Pull.mapState, step] using exactRead

theorem lower_image (source : Source Value Fault Delay) (context : Context) :
    image (lower source context) = meaning source context := by
  cases source with
  | one packet => cases packet <;> simp [lower, image, residual, meaning]
  | frontier values => simp [lower, image, residual]
  | failure => rfl
  | interrupted => simp [lower, image, residual]
  | invalid => rfl

theorem initial_read_refines (source : Source Value Fault Delay) (context : Context) :
    (read (lower source context)).mapState image =
      referenceRead (meaning source context) := by
  rw [read_refines, lower_image]

/-- Observe the actual entered frame after native execution, preserving its
post-call world. A pending handoff is visible here; it cannot become authored
execution merely because its first read is a stop or an empty frontier. -/
def entered {Input Call World : Type*}
    (frame : Invocation.Frame Input Call World Value Fault Delay) (context : Context) :
    Option (World × Pull (Returned Value Fault Delay Context)
      (List (Returned Value Fault Delay Context) × Stop)) :=
  match frame.control with
  | .deliver source => some (frame.world, (read (lower source context)).mapState image)
  | _ => none

theorem entered_refines {Input Call World : Type*}
    (program : Invocation.Program Input Call World Value Fault Delay)
    (world : World) (input : Input) (call : Call) (context : Context)
    (admitted : program.admission world input = some call) :
    entered (Invocation.step program (Invocation.step program
        (Invocation.initial world input))) context =
      some ((program.invoke world call).1,
        referenceRead (meaning (program.invoke world call).2 context)) := by
  rw [Invocation.entered_call_exact program world input call admitted]
  simp [entered, initial_read_refines]

example :
    let frame : Invocation.Frame Unit Unit Nat Nat Unit Unit :=
      ⟨7, .deliver (.frontier #[]), 1, 0⟩
    entered frame () = some (7, .stopped .complete) := by rfl

example :
    let frame : Invocation.Frame Unit Unit Nat Nat Unit Unit :=
      ⟨7, .authored (), 0, 1⟩
    entered frame () = none := by rfl

end NativeDelivery

namespace Controls

inductive Payload where
  | code
  | errorData
  | emptyData
  deriving DecidableEq, Repr

abbrev TestSource := Source Payload String String

example : meaning (.one (.value .completed .errorData) : TestSource) () ≠
    meaning (.one (.raised "error") : TestSource) () := by decide

example : meaning (.one (.value .completed .emptyData) : TestSource) () ≠
    meaning (.failure : TestSource) () := by decide

example : (advance 2 ⟨(.frontier #[.code, .code] : TestSource), (), 0⟩).1 =
    [((), .value .completed .code), ((), .value .completed .code)] := by decide

example : (read ⟨(.one (.conditional .code "later") : TestSource), (), 0⟩) =
    .returned ((), .conditional .code "later")
      ⟨(.one (.conditional .code "later") : TestSource), (), 1⟩ := rfl

example : read (⟨(.invalid : TestSource), (), 0⟩) ≠
    read (⟨(.failure : TestSource), (), 0⟩) := by decide

example : recordCompletion (some Stop.cancelled) (some Stop.hostFailure) ≠
    recordCompletion (some Stop.hostFailure) (some Stop.cancelled) := by decide

end Controls

#print axioms record_completion_assoc
#print axioms recorded_cause_survives
#print axioms read_refines
#print axioms advance_exact
#print axioms advance_add
#print axioms advance_length_le
#print axioms final_return_exact
#print axioms publication_allowance_attained
#print axioms publication_allowance_minimal
#print axioms returned_context
#print axioms later_world_observation
#print axioms Arguments.prepare_exact
#print axioms Arguments.borrow_iff_unchanged
#print axioms Arguments.Input.arguments_length
#print axioms Arguments.Input.read_refines
#print axioms Arguments.Input.read_outside
#print axioms Arguments.Input.field_refines
#print axioms Arguments.Input.observe_current_world
#print axioms Arguments.Input.gather_refines
#print axioms Arguments.Input.gather_full
#print axioms Invocation.two_steps_refine
#print axioms Invocation.entered_call_exact
#print axioms Invocation.refusal_preserves_world
#print axioms Invocation.admission_not_recoverable
#print axioms Invocation.literal_completion_role

#print axioms NativeDelivery.read_refines
#print axioms NativeDelivery.lower_image
#print axioms NativeDelivery.initial_read_refines
#print axioms NativeDelivery.entered_refines

#print axioms InvocationSlice.slice_entered
#print axioms InvocationSlice.slice_refused
#print axioms InvocationSlice.split_resume
#print axioms InvocationSlice.delivered_slice
#print axioms InvocationSlice.entered_resume

end Mettapedia.Machines.NativeCallReturn
