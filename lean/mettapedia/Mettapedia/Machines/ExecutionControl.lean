import Mathlib.Init
import Mathlib.Tactic
import Mettapedia.Machines.NativeCallReturn
import Mettapedia.Machines.ContextualCBPV
import Mettapedia.Machines.ContextualInvocation

/-!
# Operand plans for contextual execution control

An admitted source head elaborates into a control operation and operand
coordinates. The array reader is independent of the source interpreter below,
which destructures an ordered list. Their agreement preserves the opaque
operands themselves: elaboration neither evaluates a producer nor inspects a
pattern or continuation. In particular, a missing branch is not an Empty datum.

Source-layout laws are joined to a reverse-stack sequence lowering in the
contextual execution kernel. Native C correspondence, dialect admission and
physical ownership remain separate obligations. An ordinary force and a function return
scope are different operations even if one admitted lowering executes both
through the same direct body entry. Memoized Need is not introduced here.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ExecutionControl

inductive Head where
  | letBinding
  | chain
  | branch
  | bindings
  | evaluate
  | function
  | alternatives
  | empty
  | commit
  | handler
  | sequenceFirst
  | sequenceLast
  | collect
  | matchBranches
  deriving DecidableEq, Repr

inductive Operation where
  | sequence
  | branch
  | sequenceMany
  | force
  | returnScope
  | orderedChoice
  | failure
  | scopedCommit
  | handle
  | returnValue
  | construct
  | invoke
  | sequenceFirst
  | sequenceLast
  | collect
  | matchBranches
  deriving DecidableEq, Repr

structure Plan where
  operation : Operation
  source : Option Nat
  first : Option Nat
  last : Option Nat
  deriving DecidableEq, Repr

/-- Arity is checked before any operand is read. Coordinates exclude the head. -/
def elaborate (head : Head) (arity : Nat) : Option Plan :=
  match head, arity with
  | .letBinding, 3 => some ⟨.sequence, some 1, some 0, some 2⟩
  | .chain, 3 => some ⟨.sequence, some 0, some 1, some 2⟩
  | .branch, 2 => some ⟨.branch, some 0, some 1, none⟩
  | .branch, 3 => some ⟨.branch, some 0, some 1, some 2⟩
  | .bindings, 2 => some ⟨.sequenceMany, some 0, none, some 1⟩
  | .evaluate, 1 => some ⟨.force, some 0, none, none⟩
  | .function, 1 => some ⟨.returnScope, some 0, none, none⟩
  | .alternatives, 1 => some ⟨.orderedChoice, some 0, none, none⟩
  | .empty, 0 => some ⟨.failure, none, none, none⟩
  | .commit, 0 => some ⟨.scopedCommit, none, none, none⟩
  | .handler, 1 => some ⟨.handle, some 0, none, none⟩
  | .sequenceFirst, 0 | .sequenceLast, 0 => some ⟨.failure, none, none, none⟩
  | .sequenceFirst, _ => some ⟨.sequenceFirst, none, none, none⟩
  | .sequenceLast, _ => some ⟨.sequenceLast, none, none, none⟩
  | .collect, 1 => some ⟨.collect, some 0, none, none⟩
  | .matchBranches, 2 => some ⟨.matchBranches, some 0, some 1, none⟩
  | _, _ => none

def Plan.InBounds (plan : Plan) (arity : Nat) : Prop :=
  (∀ index, plan.source = some index → index < arity) ∧
    (∀ index, plan.first = some index → index < arity) ∧
    (∀ index, plan.last = some index → index < arity)

/-- Admission establishes every coordinate the reader may subsequently use. -/
theorem elaborate_inBounds {head : Head} {arity : Nat} {plan : Plan}
    (admitted : elaborate head arity = some plan) : plan.InBounds arity := by
  cases head <;>
    (rcases arity with _ | (_ | (_ | (_ | arity))) <;>
      simp_all [elaborate])
  all_goals subst plan; simp [Plan.InBounds]

inductive SeriesResult where
  | first
  | last
  deriving DecidableEq, Repr

inductive Request (Operand : Type*) where
  | sequence (producer pattern body : Operand)
  | branch (condition yes : Operand) (no : Option Operand)
  | sequenceMany (bindings body : Operand)
  | force (source : Operand)
  | returnScope (body : Operand)
  | orderedChoice (alternatives : Operand)
  | failure
  | scopedCommit
  | handle (body : Operand)
  | series (result : SeriesResult) (computations : List Operand)
  | collect (body : Operand)
  | matchBranches (key arms : Operand)
  deriving DecidableEq, Repr

variable {Operand : Type*}

private def required (fields : Array Operand) (position : Option Nat) : Option Operand :=
  position.bind (fields[·]?)

/-- The lowered reader observes a fixed number of array coordinates. It has no
operation for evaluating, copying or comparing an operand. -/
def read (plan : Plan) (fields : Array Operand) : Option (Request Operand) := do
  if plan.operation == .failure then return .failure
  if plan.operation == .scopedCommit then return .scopedCommit
  if plan.operation == .sequenceFirst then
    if fields.isEmpty then none else return .series .first fields.toList
  if plan.operation == .sequenceLast then
    if fields.isEmpty then none else return .series .last fields.toList
  let source ← required fields plan.source
  match plan.operation with
  | .sequence =>
      let pattern ← required fields plan.first
      let body ← required fields plan.last
      return .sequence source pattern body
  | .branch =>
      let yes ← required fields plan.first
      match plan.last with
      | none => return .branch source yes none
      | some position =>
          let no ← fields[position]?
          return .branch source yes (some no)
  | .sequenceMany =>
      let body ← required fields plan.last
      return .sequenceMany source body
  | .force => return .force source
  | .returnScope => return .returnScope source
  | .orderedChoice => return .orderedChoice source
  | .failure => return .failure
  | .scopedCommit => return .scopedCommit
  | .handle => return .handle source
  | .collect => return .collect source
  | .matchBranches =>
      let arms ← required fields plan.first
      return .matchBranches source arms
  | .returnValue | .construct | .invoke | .sequenceFirst | .sequenceLast => none

/-- Independent source destructuring, before an execution strategy consumes
the request. This explicitly distinguishes the two binding operand orders. -/
def reference (head : Head) (fields : List Operand) : Option (Request Operand) :=
  match head, fields with
  | .letBinding, [pattern, producer, body] => some (.sequence producer pattern body)
  | .chain, [producer, pattern, body] => some (.sequence producer pattern body)
  | .branch, [condition, yes] => some (.branch condition yes none)
  | .branch, [condition, yes, no] => some (.branch condition yes (some no))
  | .bindings, [bindings, body] => some (.sequenceMany bindings body)
  | .evaluate, [source] => some (.force source)
  | .function, [body] => some (.returnScope body)
  | .alternatives, [alternatives] => some (.orderedChoice alternatives)
  | .empty, [] => some .failure
  | .commit, [] => some .scopedCommit
  | .handler, [body] => some (.handle body)
  | .sequenceFirst, [] | .sequenceLast, [] => some .failure
  | .sequenceFirst, fields => some (.series .first fields)
  | .sequenceLast, fields => some (.series .last fields)
  | .collect, [body] => some (.collect body)
  | .matchBranches, [key, arms] => some (.matchBranches key arms)
  | _, _ => none

theorem matchBranches_missing_arms (position : Nat) (fields : Array Operand) :
    read ⟨.matchBranches, some position, none, none⟩ fields = none := by
  simp [read, required]

/-- Reading an elaborated operand plan agrees with independent source layout,
including under/over-application and the missing-branch distinction. -/
theorem read_elaborate (head : Head) (fields : List Operand) :
    (elaborate head fields.length).bind (fun plan => read plan fields.toArray) =
      reference head fields := by
  cases fields with
  | nil => cases head <;> rfl
  | cons a fields =>
      cases fields with
      | nil => cases head <;> rfl
      | cons b fields =>
          cases fields with
          | nil => cases head <;> rfl
          | cons c fields =>
              cases fields with
              | nil => cases head <;> rfl
              | cons d rest => cases head <;> rfl

/-- The core sequence is shared, while the source layouts are not confused. -/
theorem binding_layouts_agree (pattern producer body : Operand) :
    (elaborate .letBinding 3).bind (fun plan => read plan #[pattern, producer, body]) =
      (elaborate .chain 3).bind (fun plan => read plan #[producer, pattern, body]) := by
  change (elaborate .letBinding [pattern, producer, body].length).bind
      (fun plan => read plan [pattern, producer, body].toArray) =
    (elaborate .chain [producer, pattern, body].length).bind
      (fun plan => read plan [producer, pattern, body].toArray)
  rw [read_elaborate, read_elaborate]
  rfl

theorem force_is_not_return_scope (source : Operand) :
    reference .evaluate [source] ≠ reference .function [source] := by
  simp [reference]

theorem handler_is_not_return_scope (body : Operand) :
    reference .handler [body] ≠ reference .function [body] := by
  simp [reference]

theorem commit_has_no_operand (value : Operand) :
    (elaborate .commit 0).bind (fun plan => read plan (#[] : Array Operand)) = some .scopedCommit ∧
      reference .commit [value] = none := by
  simp [elaborate, read, reference]

example : reference .letBinding [7, 7, 9] = some (.sequence 7 7 9) := rfl
example : (elaborate .letBinding 2 : Option Plan) = none := rfl
example : reference .branch [1, 2] ≠ reference .branch [1, 2, 0] := by decide

namespace Computation

/-- Fixed-layout control and native-call descriptors have distinct entries.
Basic value/construction/invocation authority is handled by `Occurrence`. -/
inductive Description where
  | control (head : Head)
  | native (descriptor : ContextualInvocation.InvocationLayout.Descriptor)
  deriving DecidableEq, Repr

structure Word where
  control : Option Plan
  native : Option ContextualInvocation.InvocationLayout.Plan
  deriving DecidableEq, Repr

def compile (description : Description) (arity : Nat) : Word :=
  match description with
  | .control head => ⟨elaborate head arity, none⟩
  | .native descriptor => ⟨none, ContextualInvocation.InvocationLayout.elaborate descriptor arity⟩

def Word.Exclusive (word : Word) : Prop := word.control = none ∨ word.native = none

theorem compile_exclusive (description : Description) (arity : Nat) :
    (compile description arity).Exclusive := by
  cases description <;> simp [compile, Word.Exclusive]

variable {Field : Type}

abbrev Entry (Field : Type) := Sum (Request Field) (Nat × List Field)

/-- An executable word selects its entry before reading operands. Native and
control entries cannot both be present in an elaborated source word. -/
def read (word : Word) (fields : Array Field) : Option (Entry Field) :=
  if fields.size = 0 then none
  else match word.native with
  | some native => (ContextualInvocation.InvocationLayout.read native fields).map Sum.inr
  | none => (word.control.bind fun control =>
      ExecutionControl.read control (fields.extract 1 fields.size)).map Sum.inl

/-- Independent source interpretation keeps wrapper syntax out of arguments. -/
def reference (description : Description) : List Field → Option (Entry Field)
  | [] => none
  | wrapper :: arguments => match description with
    | .control head => (ExecutionControl.reference head arguments).map Sum.inl
    | .native descriptor =>
        (ContextualInvocation.InvocationLayout.reference descriptor (wrapper :: arguments)).map Sum.inr

private theorem arguments_extract (wrapper : Field) (arguments : List Field) :
    (wrapper :: arguments).toArray.extract 1 (wrapper :: arguments).length = arguments.toArray := by
  apply Array.toList_inj.mp
  simp [List.extract_eq_take_drop]

theorem read_refines (description : Description) (wrapper : Field) (arguments : List Field) :
    read (compile description arguments.length) (wrapper :: arguments).toArray =
      reference description (wrapper :: arguments) := by
  cases description with
  | control head =>
      simpa [read, compile, reference, arguments_extract] using
        congrArg (Option.map Sum.inl) (ExecutionControl.read_elaborate head arguments)
  | native descriptor =>
      simp only [read, compile, List.size_toArray, List.length_cons,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, reference]
      cases result : ContextualInvocation.InvocationLayout.elaborate descriptor arguments.length with
      | none =>
          simpa [result] using congrArg (Option.map (Sum.inr : (Nat × List Field) → Entry Field))
            (ContextualInvocation.InvocationLayout.read_elaborate descriptor wrapper arguments)
      | some native =>
          simpa [result] using congrArg (Option.map (Sum.inr : (Nat × List Field) → Entry Field))
            (ContextualInvocation.InvocationLayout.read_elaborate descriptor wrapper arguments)

/-- Reordering operand storage carries coordinates with the computation. -/
theorem branch_storage_normalization (wrapper condition yes no : Field) :
    read ⟨some ⟨.branch, some 0, some 2, some 1⟩, none⟩ #[wrapper, condition, no, yes] =
      reference (.control .branch) [wrapper, condition, yes, no] := by
  simp [read, ExecutionControl.read, required, reference, ExecutionControl.reference]

/-- Raw wrapper decoding would undo a valid storage normalization. -/
theorem syntax_is_not_normalized_code :
    read ⟨some ⟨.branch, some 0, some 2, some 1⟩, none⟩ #[99, 1, 7, 8] ≠
      reference (.control .branch) [99, 1, 7, 8] := by decide

/-- Payload-independent word refinement preserves complete metered residuals,
including the same source occurrence/debit, effects, alternatives and frames. -/
theorem metered_refines {Value Call Effect Fault Delay Suspension Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (state : ContextualCBPV.State Value Call Effect Fault Delay Suspension Context World Worker)
    (context : Context) (description : Description) (wrapper : Field) (arguments : List Field)
    (interpret : Entry Field → ContextualCBPV.Code Value Call Effect Fault Delay Suspension)
    (occurrence debit sourceFuel physicalSteps : Nat) :
    let machine := ContextualCBPV.meteredCore sem state.world context sourceFuel
    (read (compile description arguments.length) (wrapper :: arguments).toArray).map
      (fun entry => machine.runSlice physicalSteps
        ⟨{state with focus := ⟨.compute context (.source occurrence debit (interpret entry)),
            state.focus.frames⟩}, sourceFuel⟩) =
      (reference description (wrapper :: arguments)).map
      (fun entry => machine.runSlice physicalSteps
        ⟨{state with focus := ⟨.compute context (.source occurrence debit (interpret entry)),
            state.focus.frames⟩}, sourceFuel⟩) := by
  rw [read_refines]

end Computation

namespace SequenceExecution

inductive Order where
  | sourceFirst
  | binderFirst
  deriving DecidableEq, Repr

/-- A normalized sequence lists its three source coordinates in execution
order. Admission restricts the descriptor to one of the two source layouts. -/
def coordinates (plan : Plan) (order : Order) : Option (List Nat) :=
  if plan.operation != .sequence then none
  else match plan.source, plan.first, plan.last with
    | some 0, some 1, some 2 => some (match order with
        | .sourceFirst => [0, 1, 2]
        | .binderFirst => [1, 0, 2])
    | some 1, some 0, some 2 => some (match order with
        | .sourceFirst => [1, 0, 2]
        | .binderFirst => [0, 1, 2])
    | _, _, _ => none

variable {Value Call Effect Fault Delay Suspension : Type}
local notation "Code" => ContextualCBPV.Code Value Call Effect Fault Delay Suspension

/-- Source semantics states which of the two computations precedes the body.
Each computation owns its matching or unification action in the live context. -/
def reference (order : Order) (producer binder body : Code) : Code :=
  match order with
  | .sourceFirst => .sequence producer (fun _ => .sequence binder (fun _ => body))
  | .binderFirst => .sequence binder (fun _ => .sequence producer (fun _ => body))

/-- The lowerer emits the body's frame first. The physical stack is stored
bottom-to-top; subsequent pushes become the next computation to execute. -/
def executeStack : List Code → Option Code
  | [] => none
  | body :: frames => some (frames.foldl
      (fun continuation code => .sequence code (fun _ => continuation)) body)

def lower (plan : Plan) (order : Order) (fields : Array Code) : Option Code := do
  let indices ← coordinates plan order
  let code ← indices.reverse.mapM (fun index => fields[index]?)
  executeStack code

/-- Independently encoded source layouts and reverse stack construction
produce the same computation, including the final body's return packet. -/
theorem let_lowering (order : Order) (producer binder body : Code) :
    (elaborate .letBinding 3).bind (fun plan => lower plan order #[binder, producer, body]) =
      some (reference order producer binder body) := by
  cases order <;> rfl

theorem chain_lowering (order : Order) (producer binder body : Code) :
    (elaborate .chain 3).bind (fun plan => lower plan order #[producer, binder, body]) =
      some (reference order producer binder body) := by
  cases order <;> rfl

/-- The shared normalized plan retains the actual context and every older
frame, alternative, published answer and source debit at execution entry. -/
theorem entry_refines {Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (state : ContextualCBPV.State Value Call Effect Fault Delay Suspension Context World Worker)
    (context : Context) (order : Order) (producer binder body : Code) :
    ((elaborate .letBinding 3).bind
      (fun plan => lower plan order #[binder, producer, body])).bind (fun code =>
        ContextualCBPV.step sem {state with focus := ⟨.compute context code, state.focus.frames⟩}) =
      ContextualCBPV.step sem {state with focus :=
        ⟨.compute context (reference order producer binder body), state.focus.frames⟩} := by
  rw [let_lowering]
  rfl

/-- The complete metered continuation is the same at every physical budget;
this includes a stop immediately before any child source charge. -/
theorem metered_refines {Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (state : ContextualCBPV.Metered (Value := Value) (Call := Call) (Effect := Effect)
      (Fault := Fault) (Delay := Delay) (Suspension := Suspension)
      (Context := Context) (World := World) (Worker := Worker))
    (world : World) (context : Context) (sourceFuel physical : Nat)
    (order : Order) (producer binder body : Code) :
    ((elaborate .chain 3).bind
      (fun plan => lower plan order #[producer, binder, body])).map (fun code =>
        (ContextualCBPV.meteredCore sem world context sourceFuel).runSlice physical
          {state with state := {state.state with focus :=
            ⟨.compute context code, state.state.focus.frames⟩}}) =
      some ((ContextualCBPV.meteredCore sem world context sourceFuel).runSlice physical
        {state with state := {state.state with focus :=
          ⟨.compute context (reference order producer binder body), state.state.focus.frames⟩}}) := by
  rw [chain_lowering]
  rfl

example : coordinates ⟨.sequence, some 0, some 0, some 2⟩ .sourceFirst = none := rfl
example : coordinates ⟨.force, some 0, none, none⟩ .sourceFirst = none := rfl

/-- The same final value does not license swapping the source visits. -/
theorem order_changes_source_trace :
    let producer : ContextualCBPV.Controls.TestCode := .source 11 1 (.returned (.number 7))
    let binder : ContextualCBPV.Controls.TestCode := .source 22 1 (.returned (.number 8))
    let body : ContextualCBPV.Controls.TestCode := .returned (.number 9)
    (ContextualCBPV.Controls.run 0 (reference .sourceFirst producer binder body)).sourceTrace = [11, 22] ∧
      (ContextualCBPV.Controls.run 0 (reference .binderFirst producer binder body)).sourceTrace = [22, 11] := by
  decide

/-- Failure stops later work; moving an effect before it is observable. -/
theorem failure_keeps_prior_effects_only :
    let producer : ContextualCBPV.Controls.TestCode := .failure
    let binder : ContextualCBPV.Controls.TestCode := .native 1
    let body : ContextualCBPV.Controls.TestCode := .native 1
    (ContextualCBPV.Controls.run 0 (reference .sourceFirst producer binder body)).world = 0 ∧
      (ContextualCBPV.Controls.run 0 (reference .binderFirst producer binder body)).world = 1 := by
  decide

end SequenceExecution

namespace SeriesExecution

inductive Destination where
  | result
  | saved
  | discard (position : Nat)
  deriving DecidableEq, Repr

inductive Goal (Operand : Type) where
  | solve (source : Operand) (destination : Destination) (inheritResult : Bool)
  | publishSaved
  deriving DecidableEq, Repr

variable {Field : Type}

def selected (result : SeriesResult) (arity : Nat) : Nat :=
  match result with
  | .first => 0
  | .last => arity - 1

def deferred (result : SeriesResult) (direct : Bool) (fields : List Field) : Bool :=
  result == .first && !direct && !fields.isEmpty

def visit (resultIndex : Nat) (save : Bool) (source : Field) (index : Nat) : Goal Field :=
  if index = resultIndex then .solve source (if save then .saved else .result) true
  else .solve source (.discard index) false

/-- Independent source order: each child meets its own destination before the
remaining children run; a retained first value can have a later publication. -/
def sourceVisits (resultIndex : Nat) (save : Bool) : Nat → List Field → List (Goal Field)
  | _, [] => []
  | index, first :: rest => visit resultIndex save first index ::
      sourceVisits resultIndex save (index + 1) rest

def source (result : SeriesResult) (direct : Bool) (fields : List Field) : List (Goal Field) :=
  let save := deferred result direct fields
  sourceVisits (selected result fields.length) save 0 fields ++
    (if save then [.publishSaved] else [])

/-- The implementation walks indexed children backwards, pushing one selected
result goal and independent discard destinations onto its continuation stack. -/
def lower (result : SeriesResult) (direct : Bool) (fields : List Field) : List (Goal Field) :=
  let save := deferred result direct fields
  fields.zipIdx.reverse.foldl
    (fun pending (field, index) => visit (selected result fields.length) save field index :: pending)
    (if save then [.publishSaved] else [])

private theorem indexed_source (resultIndex : Nat) (save : Bool) (fields : List Field)
    (start : Nat) :
    (fields.zipIdx start).map (fun (field, index) => visit resultIndex save field index) =
      sourceVisits resultIndex save start fields := by
  induction fields generalizing start with
  | nil => rfl
  | cons first rest ih => simp [List.zipIdx_cons, sourceVisits, ih]

private theorem reverse_push {Item : Type} (items : List Item) (emit : Item → Goal Field)
    (pending : List (Goal Field)) :
    items.reverse.foldl (fun pending item => emit item :: pending) pending =
      items.map emit ++ pending := by
  rw [List.foldl_reverse]
  induction items with
  | nil => rfl
  | cons first rest ih => simp [ih]

theorem lowering_refines (result : SeriesResult) (direct : Bool) (fields : List Field) :
    lower result direct fields = source result direct fields := by
  unfold lower source
  rw [reverse_push, indexed_source]

private theorem sourceVisits_length (resultIndex : Nat) (save : Bool) (start : Nat)
    (fields : List Field) :
    (sourceVisits resultIndex save start fields).length = fields.length := by
  induction fields generalizing start with
  | nil => rfl
  | cons first rest ih => simp [sourceVisits, ih]

/-- Goal count, hence the retained unit-debit sequence, includes exactly one
extra publication only for a nonempty deferred first-result series. -/
theorem exact_goal_count (result : SeriesResult) (direct : Bool) (fields : List Field) :
    (lower result direct fields).length = fields.length +
      (if deferred result direct fields then 1 else 0) := by
  rw [lowering_refines]
  simp [source, sourceVisits_length]
  split <;> rfl

theorem single_operand_policies_differ :
    source .first false [7] = [.solve 7 .saved true, .publishSaved] ∧
      source .last false [7] = [.solve 7 .result true] := by decide

theorem ignored_values_keep_distinct_destinations :
    source .first true [7, 8, 8] =
      [.solve 7 .result true, .solve 8 (.discard 1) false, .solve 8 (.discard 2) false] := by decide

/-- The goal interpreter uses one contextual branch/store. The equality above
retains its operand scopes, result-demand receipts, effects and source debits. -/
def interpret {Value Call Effect Fault Delay Suspension : Type}
    (run : Field → Destination → Bool → ContextualCBPV.Code Value Call Effect Fault Delay Suspension)
    (publish : ContextualCBPV.Code Value Call Effect Fault Delay Suspension)
    (origin : Goal Field → Nat) (goals : List (Goal Field))
    (finish : ContextualCBPV.Code Value Call Effect Fault Delay Suspension) :=
  goals.foldr (fun goal rest => .sequence (.source (origin goal) 1 (match goal with
    | .solve field destination matched => run field destination matched
    | .publishSaved => publish)) (fun _ => rest)) finish

theorem metered_refines {Value Call Effect Fault Delay Suspension Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (state : ContextualCBPV.State Value Call Effect Fault Delay Suspension Context World Worker)
    (context : Context) (result : SeriesResult) (direct : Bool) (fields : List Field)
    (run : Field → Destination → Bool → ContextualCBPV.Code Value Call Effect Fault Delay Suspension)
    (publish finish : ContextualCBPV.Code Value Call Effect Fault Delay Suspension)
    (origin : Goal Field → Nat) (sourceFuel physicalSteps : Nat) :
    let machine := ContextualCBPV.meteredCore sem state.world context sourceFuel
    machine.runSlice physicalSteps
      ⟨{state with focus := ⟨.compute context
        (interpret run publish origin (lower result direct fields) finish), state.focus.frames⟩}, sourceFuel⟩ =
      machine.runSlice physicalSteps
      ⟨{state with focus := ⟨.compute context
        (interpret run publish origin (source result direct fields) finish), state.focus.frames⟩}, sourceFuel⟩ := by
  rw [lowering_refines]

end SeriesExecution

namespace Occurrence

inductive Authority where
  | value
  | constructor
  | staticCall
  | dynamicCall
  deriving DecidableEq, Repr

/-- The dialect supplies source authority. No current registry lookup can
turn a compiled value or constructor occurrence into a call. -/
def elaborate : Authority → Plan
  | .value => ⟨.returnValue, none, none, none⟩
  | .constructor => ⟨.construct, none, none, none⟩
  | .staticCall | .dynamicCall => ⟨.invoke, none, none, none⟩

variable {Value Call Effect Fault Delay Suspension : Type}
local notation "Code" => ContextualCBPV.Code Value Call Effect Fault Delay Suspension

/-- Interpret an occurrence plan using the existing contextual kernel.
Constructor decomposition and callee obligations remain dialect services;
the completed-value case has no operation for entering a callable. -/
def lower (value : Operand → Value) (constructor : Operand → Code)
    (call : Operand → Call) (plan : Plan) (operand : Operand) : Option Code :=
  match plan.operation with
  | .returnValue => some (.returned (value operand))
  | .construct => some (constructor operand)
  | .invoke => some (.invoke (call operand))
  | _ => none

/-- Independent source-role dispatch, before encoding a computation plan. -/
def reference (value : Operand → Value) (constructor : Operand → Code)
    (call : Operand → Call) : Authority → Operand → Code
  | .value, operand => .returned (value operand)
  | .constructor, operand => constructor operand
  | .staticCall, operand | .dynamicCall, operand => .invoke (call operand)

theorem elaboration_refines (value : Operand → Value) (constructor : Operand → Code)
    (call : Operand → Call) (authority : Authority) (operand : Operand) :
    lower value constructor call (elaborate authority) operand =
      some (reference value constructor call authority operand) := by
  cases authority <;> rfl

/-- Refinement preserves the actual next computation and every older frame,
alternative, branch context, publication and semantic source debit. -/
theorem contextual_step_refines {Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (state : ContextualCBPV.State Value Call Effect Fault Delay Suspension Context World Worker)
    (context : Context) (value : Operand → Value) (constructor : Operand → Code)
    (call : Operand → Call) (authority : Authority) (operand : Operand) :
    (lower value constructor call (elaborate authority) operand).bind (fun code =>
      ContextualCBPV.step sem {state with focus := ⟨.compute context code, state.focus.frames⟩}) =
      ContextualCBPV.step sem {state with focus :=
        ⟨.compute context (reference value constructor call authority operand), state.focus.frames⟩} := by
  rw [elaboration_refines]
  rfl

theorem value_does_not_acquire_call_authority :
    (elaborate .value).operation ≠ (elaborate .staticCall).operation ∧
      (elaborate .constructor).operation ≠ (elaborate .staticCall).operation := by
  decide

theorem basic_plans_do_not_read_operand_coordinates (authority : Authority) :
    (elaborate authority).source = none ∧ (elaborate authority).first = none ∧
      (elaborate authority).last = none := by
  cases authority <;> decide

namespace Invocation

variable {Argument Observed Context World Worker : Type}
variable (base : ContextualCBPV.Semantics Value (ContextualInvocation.Call Argument)
    Effect Fault Delay Suspension Context World Worker)
    (resolve : World → Context → Argument → Option Observed)
    (enter : World → Context → Argument → List Observed → Context ×
      ContextualInvocation.Code (Argument := Argument) (Value := Value) (Effect := Effect)
        (Fault := Fault) (Delay := Delay) (Suspension := Suspension))
    (fallback : World → Context → Argument → List Argument → Context ×
      ContextualInvocation.Code (Argument := Argument) (Value := Value) (Effect := Effect)
        (Fault := Fault) (Delay := Delay) (Suspension := Suspension))
/-- Ordinary plans enter through the same live callee obligations as the
source's expanded invocation. The post-entry continuation and logical world
are preserved for static and dynamic source calls. -/
theorem step_refines (state : ContextualCBPV.State Value (ContextualInvocation.Call Argument)
    Effect Fault Delay Suspension Context World Worker) (context : Context)
    (value : ContextualInvocation.Input Argument → Value)
    (constructor : ContextualInvocation.Input Argument → ContextualInvocation.Code
      (Argument := Argument) (Value := Value) (Effect := Effect) (Fault := Fault)
      (Delay := Delay) (Suspension := Suspension))
    (dynamic : Bool) (input : ContextualInvocation.Input Argument) :
    let sem := ContextualInvocation.withCalls base resolve enter fallback
    (lower value constructor ContextualInvocation.Call.borrowed
      (elaborate
        (if dynamic then .dynamicCall else .staticCall)) input).bind
      (fun code => ContextualCBPV.step sem
        {state with focus := ⟨.compute context code, state.focus.frames⟩}) =
      ContextualCBPV.step sem {state with focus := ⟨.compute context
        (.invoke (.expanded input.head input.arguments)), state.focus.frames⟩} := by
  cases dynamic <;>
    exact ContextualInvocation.step_refines base resolve enter fallback state context input

/-- Charge admission and call entry produce the same purse and actual
residual, including failed resolution. A denied charge enters neither callee. -/
theorem metered_entry_refines (state : ContextualCBPV.State Value (ContextualInvocation.Call Argument)
    Effect Fault Delay Suspension Context World Worker) (context : Context)
    (value : ContextualInvocation.Input Argument → Value)
    (constructor : ContextualInvocation.Input Argument → ContextualInvocation.Code
      (Argument := Argument) (Value := Value) (Effect := Effect) (Fault := Fault)
      (Delay := Delay) (Suspension := Suspension))
    (dynamic : Bool) (input : ContextualInvocation.Input Argument)
    (occurrence debit sourceFuel : Nat) :
    let sem := ContextualInvocation.withCalls base resolve enter fallback
    (lower value constructor ContextualInvocation.Call.borrowed
      (elaborate (if dynamic then .dynamicCall else .staticCall)) input).bind
      (fun code => (ContextualCBPV.meteredStep sem
        ⟨{state with focus := ⟨.compute context (.source occurrence debit code),
            state.focus.frames⟩}, sourceFuel⟩).bind (ContextualCBPV.meteredStep sem)) =
      (ContextualCBPV.meteredStep sem
        ⟨{state with focus := ⟨.compute context
          (.source occurrence debit (.invoke (.expanded input.head input.arguments))),
            state.focus.frames⟩}, sourceFuel⟩).bind (ContextualCBPV.meteredStep sem) := by
  by_cases enough : debit ≤ sourceFuel
  all_goals cases dynamic <;>
    simp [elaborate, lower, ContextualCBPV.meteredStep, ContextualCBPV.step,
      ContextualCBPV.advance, ContextualCBPV.debit, ContextualCBPV.origin,
      ContextualInvocation.entry_refines, enough]

end Invocation

namespace Controls

open ContextualCBPV NativeCallReturn

abbrev Datum := ContextualCBPV.Controls.Datum
abbrev FixtureCode := ContextualCBPV.Code Datum Unit Nat Nat Unit Nat
abbrev FixtureSemantics := ContextualCBPV.Semantics Datum Unit Nat Nat Unit Nat Nat Nat
  (Cursor Datum Nat Unit Nat)

def value (source : Nat) : Datum := .suspended 5 source

/-- The constructor fixture executes one active child, then returns its
retained data. Call entry instead produces the callee's own native answer. -/
def constructor (source : Nat) : FixtureCode :=
  .sequence (.native 1) (fun _ => .returned (value source))

def run (sem : FixtureSemantics) (authority : Authority) :=
  let code := (lower value constructor (fun _ => ()) (elaborate authority) 17).getD .failure
  ((ContextualCBPV.core sem 0 4).runSlice 40 (ContextualCBPV.initial 0 4 code)).1

theorem completed_value_is_not_entered_or_forced :
    (run ContextualCBPV.Controls.semantics .value).world = 0 ∧
      (run ContextualCBPV.Controls.semantics .value).nativeEntries = 0 ∧
      (run ContextualCBPV.Controls.semantics .value).published =
        [(4, .value .completed (.suspended 5 17))] := by
  decide

theorem constructor_children_and_call_entry_remain_distinct :
    (run ContextualCBPV.Controls.semantics .constructor).world = 1 ∧
      (run ContextualCBPV.Controls.semantics .constructor).published =
        [(4, .value .completed (.suspended 5 17))] ∧
      (run ContextualCBPV.Controls.semantics .staticCall).published =
        [(4, .value .completed (.number 5))] := by
  decide

theorem changing_call_entry_does_not_reclassify_value :
    (run {ContextualCBPV.Controls.semantics with
      enter := fun _ context _ => (context, .native 2)} .value).published =
      (run ContextualCBPV.Controls.semantics .value).published := by
  decide

end Controls

end Occurrence

namespace Scoped

variable {Value Call Effect Fault Delay Suspension : Type}

local notation "ScopeCode" => ContextualCBPV.Code Value Call Effect Fault Delay Suspension

/-- Source operands remain computations until the common kernel enters them.
The dialect supplies its truth value and Error datum representation. -/
def lower (truth : Value) (compute : Operand → ScopeCode)
    (errorValue : Fault → Value) : Request Operand → Option ScopeCode
  | .scopedCommit => some (.commit truth)
  | .handle body => some (.handle (compute body)
      (fun fault => .returned (errorValue fault)))
  | _ => none

/-- The source interpreter destructures authored syntax independently of the
coordinate reader and of the contextual kernel's continuation transitions. -/
def source (truth : Value) (compute : Operand → ScopeCode)
    (errorValue : Fault → Value) : Head → List Operand → Option ScopeCode
  | .commit, [] => some (.commit truth)
  | .handler, [body] => some (.handle (compute body)
      (fun fault => .returned (errorValue fault)))
  | _, _ => none

theorem elaboration_refines (truth : Value) (compute : Operand → ScopeCode)
    (errorValue : Fault → Value) (head : Head) (fields : List Operand) :
    ((elaborate head fields.length).bind (fun plan => read plan fields.toArray)).bind
        (lower truth compute errorValue) = source truth compute errorValue head fields := by
  rw [read_elaborate]
  cases fields with
  | nil => cases head <;> rfl
  | cons a rest =>
      cases rest with
      | nil => cases head <;> rfl
      | cons b rest =>
          cases rest with
          | nil => cases head <;> rfl
          | cons c rest =>
              cases rest with
              | nil => cases head <;> rfl
              | cons d rest => cases head <;> rfl

/-- Handler installation precedes execution of the protected source. Its
saved choice floor is the live outside continuation, not a cut delimiter. -/
theorem handler_enters_before_body {Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (state : ContextualCBPV.State Value Call Effect Fault Delay Suspension Context World Worker)
    (context : Context) (compute : Operand → ScopeCode) (operand : Operand)
    (errorValue : Fault → Value) :
    ContextualCBPV.advance sem {state with focus := ⟨.compute context
      (.handle (compute operand) (fun fault => .returned (errorValue fault))), state.focus.frames⟩} =
      some {state with focus := ⟨.compute context (compute operand),
        .handler context state.alternatives.length
          (fun fault => .returned (errorValue fault)) :: state.focus.frames⟩} := rfl

end Scoped

namespace Selection

open NativeCallReturn

variable {Value : Type*} {Fault : Type*} {Delay : Type*} {Context : Type*}

/-- The dialect has qualified the alternative view and its element role.
The common worker receives the original array, without executing an element. -/
def lower (role : ValueRole) : Request (Array Value) → Option (Source Value Fault Delay)
  | .orderedChoice values => some (.frontier role values)
  | .failure => some .failure
  | _ => none

/-- Independent source interpretation for this control fragment. Operand
views, quotation and interpretation of expression packets belong to the dialect. -/
def source (head : Head) (fields : List (Array Value)) (role : ValueRole)
    (context : Context) : Option (List (Returned Value Fault Delay Context) × Stop) :=
  match head, fields with
  | .alternatives, [values] =>
      some (values.toList.map (fun value => (context, .value role value)), .complete)
  | .empty, [] | .sequenceFirst, [] | .sequenceLast, [] => some ([], .complete)
  | _, _ => none

/-- Decoding a source layout and lowering its request preserves the whole
ordered occurrence stream, its lexical identity and its provenance. -/
theorem elaborate_refines (head : Head) (fields : List (Array Value))
    (role : ValueRole) (context : Context) :
    (((elaborate head fields.length).bind (fun plan => read plan fields.toArray)).bind
      (lower (Fault := Fault) (Delay := Delay) role)).map
        (fun produced => meaning produced context) = source head fields role context := by
  rw [read_elaborate]
  cases fields with
  | nil => cases head <;> rfl
  | cons first rest =>
      cases rest with
      | nil => cases head <;> rfl
      | cons second rest =>
          cases rest with
          | nil => cases head <;> rfl
          | cons third rest =>
              cases rest with
              | nil => cases head <;> rfl
              | cons fourth rest => cases head <;> rfl

/-- This allowance counts cursor publications, not semantic source fuel.
Each selected expression still needs its dialect's execution and charging. -/
theorem delivery_prefix (role : ValueRole) (values : Array Value)
    (context : Context) (allowance : Nat) :
    (advance allowance (⟨.frontier role values, context, 0⟩ :
      Cursor Value Fault Delay Context)).1 =
      (values.toList.take allowance).map (fun value => (context, .value role value)) := by
  simpa [NativeCallReturn.residual, meaning] using
    (advance_exact allowance (⟨.frontier role values, context, 0⟩ :
      Cursor Value Fault Delay Context)).1

theorem failure_is_not_a_value (role : ValueRole) (context : Context) (value : Value) :
    source .empty [] role context ≠
      some ([(context, Packet.value (Fault := Fault) (Delay := Delay) role value)], .complete) := by
  simp [source]

end Selection

namespace Forcing

inductive SourceHead where
  | evaluate | reduce
  deriving DecidableEq, Repr

def continuation : SourceHead → Operation
  | .evaluate => .force
  | .reduce => .invoke

variable {Value Effect Fault Delay Suspension : Type}
local notation "Code" => ContextualCBPV.Code Value Value Effect Fault Delay Suspension

/-- The source protocol reads an operand beside its wrapper. A held source
passed to eval and a value dispatched by reduce have different meanings. -/
def reference (head : SourceHead) : List Value → Option Code
  | [_, value] => some (match head with
      | .evaluate => .force value
      | .reduce => .invoke value)
  | _ => none

/-- The ready continuation carries its operation from elaboration. Payload
syntax is not inspected to recover it after argument preparation. -/
def readReady (operation : Operation) (fields : Array Value) : Option Code := do
  if fields.size != 2 then none
  else
    let value ← fields[1]?
    match operation with
    | .force => some (.force value)
    | .invoke => some (.invoke value)
    | _ => none

theorem continuation_refines (head : SourceHead) (fields : List Value) :
    (readReady (continuation head) fields.toArray : Option Code) = reference head fields := by
  cases fields with
  | nil => cases head <;> rfl
  | cons first fields =>
      cases fields with
      | nil => cases head <;> rfl
      | cons value rest =>
          cases rest with
          | nil => cases head <;> rfl
          | cons next rest => cases head <;> simp [readReady, reference]

theorem wrapper_is_not_authority (operation : Operation) (first later value : Value) :
    (readReady operation #[first, value] : Option Code) = readReady operation #[later, value] := by
  cases operation <;> rfl

theorem contextual_refines {Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Value Effect Fault Delay Suspension Context World Worker)
    (state : ContextualCBPV.State Value Value Effect Fault Delay Suspension Context World Worker)
    (context : Context) (head : SourceHead) (fields : List Value) :
    (readReady (continuation head) fields.toArray).map (fun code =>
      ContextualCBPV.step sem {state with focus := ⟨.compute context code, state.focus.frames⟩}) =
      (reference head fields).map (fun code =>
        ContextualCBPV.step sem {state with focus := ⟨.compute context code, state.focus.frames⟩}) := by
  rw [continuation_refines]

private def separating : ContextualCBPV.Semantics Nat Nat Unit Unit Unit Unit Unit Nat Unit where
  enter := fun _ context value => (context, .returned value)
  suspend := fun _ _ => 0
  force := fun context value => (context, .returned (value + 1))
  native := fun _ world _ => (world, ())
  pull := fun world _ => (world, .stopped .complete)
  resume := fun _ returned => returned

/-- Conflating the two continuation operations changes completed answers. -/
theorem force_is_not_dispatch :
    ((ContextualCBPV.core separating 0 ()).runSlice 8
      (ContextualCBPV.initial 0 () (.force 0))).1.published ≠
    ((ContextualCBPV.core separating 0 ()).runSlice 8
      (ContextualCBPV.initial 0 () (.invoke 0))).1.published := by decide

end Forcing

end Mettapedia.Machines.ExecutionControl

#print axioms Mettapedia.Machines.ExecutionControl.handler_is_not_return_scope
#print axioms Mettapedia.Machines.ExecutionControl.matchBranches_missing_arms
#print axioms Mettapedia.Machines.ExecutionControl.commit_has_no_operand
#print axioms Mettapedia.Machines.ExecutionControl.Scoped.elaboration_refines
#print axioms Mettapedia.Machines.ExecutionControl.Scoped.handler_enters_before_body
#print axioms Mettapedia.Machines.ExecutionControl.Occurrence.elaboration_refines
#print axioms Mettapedia.Machines.ExecutionControl.Occurrence.contextual_step_refines
#print axioms Mettapedia.Machines.ExecutionControl.Occurrence.value_does_not_acquire_call_authority
#print axioms Mettapedia.Machines.ExecutionControl.Occurrence.basic_plans_do_not_read_operand_coordinates
#print axioms Mettapedia.Machines.ExecutionControl.Occurrence.Controls.completed_value_is_not_entered_or_forced
#print axioms Mettapedia.Machines.ExecutionControl.Occurrence.Controls.constructor_children_and_call_entry_remain_distinct
#print axioms Mettapedia.Machines.ExecutionControl.Occurrence.Controls.changing_call_entry_does_not_reclassify_value

#print axioms Mettapedia.Machines.ExecutionControl.read_elaborate
#print axioms Mettapedia.Machines.ExecutionControl.elaborate_inBounds
#print axioms Mettapedia.Machines.ExecutionControl.binding_layouts_agree
#print axioms Mettapedia.Machines.ExecutionControl.force_is_not_return_scope
#print axioms Mettapedia.Machines.ExecutionControl.Selection.elaborate_refines
#print axioms Mettapedia.Machines.ExecutionControl.Selection.delivery_prefix
#print axioms Mettapedia.Machines.ExecutionControl.Selection.failure_is_not_a_value

#print axioms Mettapedia.Machines.ExecutionControl.SequenceExecution.let_lowering

#print axioms Mettapedia.Machines.ExecutionControl.SequenceExecution.chain_lowering

#print axioms Mettapedia.Machines.ExecutionControl.SequenceExecution.entry_refines

#print axioms Mettapedia.Machines.ExecutionControl.SequenceExecution.metered_refines
#print axioms Mettapedia.Machines.ExecutionControl.SequenceExecution.order_changes_source_trace
#print axioms Mettapedia.Machines.ExecutionControl.SequenceExecution.failure_keeps_prior_effects_only

#print axioms Mettapedia.Machines.ExecutionControl.Forcing.continuation_refines
#print axioms Mettapedia.Machines.ExecutionControl.Forcing.wrapper_is_not_authority
#print axioms Mettapedia.Machines.ExecutionControl.Forcing.contextual_refines
#print axioms Mettapedia.Machines.ExecutionControl.Forcing.force_is_not_dispatch

#print axioms Mettapedia.Machines.ExecutionControl.Computation.compile_exclusive

#print axioms Mettapedia.Machines.ExecutionControl.Computation.read_refines

#print axioms Mettapedia.Machines.ExecutionControl.Computation.branch_storage_normalization

#print axioms Mettapedia.Machines.ExecutionControl.Computation.syntax_is_not_normalized_code

#print axioms Mettapedia.Machines.ExecutionControl.Computation.metered_refines

#print axioms Mettapedia.Machines.ExecutionControl.SeriesExecution.lowering_refines

#print axioms Mettapedia.Machines.ExecutionControl.SeriesExecution.exact_goal_count

#print axioms Mettapedia.Machines.ExecutionControl.SeriesExecution.single_operand_policies_differ

#print axioms Mettapedia.Machines.ExecutionControl.SeriesExecution.ignored_values_keep_distinct_destinations

#print axioms Mettapedia.Machines.ExecutionControl.SeriesExecution.metered_refines

#print axioms Mettapedia.Machines.ExecutionControl.Occurrence.Invocation.step_refines
#print axioms Mettapedia.Machines.ExecutionControl.Occurrence.Invocation.metered_entry_refines
