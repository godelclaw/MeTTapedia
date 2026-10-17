import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
import Mettapedia.Languages.MeTTa.PeTTa.CettaDFSProducer
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.Machines.CMemory.EffectStatements
import Mettapedia.Machines.CMemory.Tactic
import Mettapedia.Machines.CMemory.ProductiveBlocks
import Mettapedia.GSLT.LanguageDef.NativeOpsCLexSegments
import Mettapedia.GSLT.LanguageDef.NativeOpsCStatement

/-!
# Streaming source execution through labelled finite runs

The existing eager depth-first source machine instantiates the existing
productive-block run interface. A root answer is an ordered occurrence;
steps producing no root answer are silent to this observer. Output, input,
store, bindings, alternatives and caller frames remain in the saved source
configuration. Faults and malformed stopped configurations are handoffs
retaining that configuration, rather than successful exhaustion.

The adapter's readback is the actual source runner, and its event list is
exactly the extension of the source answer history. Budget splitting, prefix
growth and account splitting then use the generic labelled-run laws. No
global productivity rank, equivalence with the batch evaluator, native C
refinement or validity of a changed shared world is asserted by that adapter.

`NativePull` and `NativeGoals` then connect selected actual C blocks and
physical retained records to the shared run interface and the independent
destination component. They preserve whole child binding records, native
goal identities, older storage and the original output slot. The physical
ABI, native atom/binding reader, allocation and primitive services remain
explicit component boundaries. ARGUMENT_RETURN retains its saved height,
interpreted as a saved continuation delimiter; native choice and
collection completion are not consequences of these local squares.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev Configuration := CettaEagerDFS.Configuration
abbrev Barrier := CettaDFSProducer.Barrier

/-- Select the existing eager evaluator or the retained finite Destination
component explicitly. The default retains historical eager collection behavior. -/
inductive ExecutionProfile : Type 1 where
  | eager
  | scopedDestination (Context : Type) (policy : CettaEagerDFS.Destination.Policy)

namespace ExecutionProfile

abbrev State : ExecutionProfile → Type
  | .eager => Configuration
  | .scopedDestination context _ => CettaEagerDFS.Destination.ScopedCursor context

abbrev Event : ExecutionProfile → Type
  | .eager => Atom
  | .scopedDestination _ _ => CettaEagerDFS.Destination.CollectedAnswer

abbrev Request : ExecutionProfile → Type
  | .eager => Barrier
  | .scopedDestination _ _ => CettaEagerDFS.Destination.ScopeBoundary

end ExecutionProfile

/-- One existing driver supplies budgeting and resumption for both explicit
profiles. The scoped case retains allocator authority and every source scope;
it does not identify its component admission with the default eager language. -/
def machine (program : Program) (profile : ExecutionProfile := .eager) :
    Machine profile.State profile.Event profile.State profile.Request :=
  match profile with
  | .eager => {
    step configuration := some <|
      match CettaEagerDFS.step program configuration with
      | some next =>
          match CettaDFSProducer.emission configuration with
          | [] => .silent next
          | values => .publish values next
      | none =>
          if CettaEagerDFS.completed configuration then .finish configuration
          else match CettaEagerDFS.fault configuration with
            | some reason => .call (.fault reason) configuration
            | none => .call .stopped configuration }
  | .scopedDestination _ policy => {
    step source := some (CettaEagerDFS.Destination.scopeStep policy program source) }

/-- Read back every retained or completed configuration. A generic faulted
outcome has no configuration; this adapter never produces that outcome. -/
def readback : Outcome Configuration Configuration Barrier → Option Configuration
  | .finished configuration | .stuck configuration | .exhausted configuration =>
      some configuration
  | .suspended _ configuration => some configuration
  | .faulted => none

/-- Readback of any finite labelled run is the independently executable
source runner, including its world and complete control state. -/
theorem run_readback (program : Program) (fuel : Nat) (source : Configuration) :
    readback ((machine program).run fuel source).2 =
      some (CettaEagerDFS.advance program fuel source) := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      cases stepped : CettaEagerDFS.step program source with
      | none =>
          by_cases finished : CettaEagerDFS.completed source = true
          · simp [Machine.run, machine, stepped, finished, readback, CettaEagerDFS.advance]
          · cases failed : CettaEagerDFS.fault source <;>
              simp [Machine.run, machine, stepped, finished, failed, readback,
                CettaEagerDFS.advance]
      | some next =>
          cases emitted : CettaDFSProducer.emission source with
          | nil =>
              simpa [Machine.run, machine, stepped, emitted, CettaEagerDFS.advance] using ih next
          | cons value rest =>
              simpa [Machine.run, machine, stepped, emitted, CettaEagerDFS.advance] using ih next

/-- The observed prefix is exactly the new source answer occurrences. Equal
values at different positions remain different list entries. -/
theorem run_answer_history (program : Program) (fuel : Nat) (source : Configuration)
    (valid : CettaEagerDFS.ScopesValid source.scopes) :
    CettaEagerDFS.answers (CettaEagerDFS.advance program fuel source) =
      CettaEagerDFS.answers source ++ ((machine program).run fuel source).1 := by
  induction fuel generalizing source with
  | zero => simp [CettaEagerDFS.advance, Machine.run]
  | succ fuel ih =>
      cases stepped : CettaEagerDFS.step program source with
      | none =>
          by_cases finished : CettaEagerDFS.completed source = true
          · simp [Machine.run, machine, stepped, finished, CettaEagerDFS.advance]
          · cases failed : CettaEagerDFS.fault source <;>
              simp [Machine.run, machine, stepped, finished, failed, CettaEagerDFS.advance]
      | some next =>
          have transition := CettaEagerDFS.step_transition stepped
          have retained := CettaEagerDFS.transition_scopes_valid transition valid
          have appended := CettaDFSProducer.transition_answers transition valid
          have later := ih next retained
          cases emitted : CettaDFSProducer.emission source with
          | nil =>
              simpa [Machine.run, machine, stepped, emitted, CettaEagerDFS.advance,
                appended] using later
          | cons value rest =>
              simpa [Machine.run, machine, stepped, emitted, CettaEagerDFS.advance,
                appended, List.append_assoc] using later

/-- Every bounded prefix has a genuine path in the independent source rules,
with at most one source transition per scheduler inspection. -/
theorem run_source (program : Program) (fuel : Nat) (source : Configuration)
    (valid : CettaEagerDFS.ScopesValid source.scopes) :
    ∃ target count, count ≤ fuel ∧
      readback ((machine program).run fuel source).2 = some target ∧
      CettaEagerDFS.SourceRun program count source target ∧
      CettaEagerDFS.ScopesValid target.scopes ∧
      CettaEagerDFS.answers target =
        CettaEagerDFS.answers source ++ ((machine program).run fuel source).1 := by
  obtain ⟨count, bound, path⟩ := CettaEagerDFS.advance_has_source_run program fuel source
  exact ⟨_, count, bound, run_readback program fuel source, path,
    CettaEagerDFS.advance_scopes_valid program fuel source valid,
    run_answer_history program fuel source valid⟩

/-- The owned producer log and the labelled run observe the same actual
source prefix. Capture and admission microsteps need not have the same count
as source transitions; the earned source path supplies the matching budget. -/
theorem producer_log_correspondence {Stored Context Output : Type} {clients : Nat}
    (program : Program) (capture : Atom → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (packet : CettaDFSProducer.Packet Stored Context Output clients)
    (execution : Mettapedia.Machines.Cursor.ProducerOccurrenceLog.Execution
      Configuration Atom Empty Barrier)
    (attached : packet.execution = some execution)
    (valid : CettaEagerDFS.ScopesValid execution.producer.scopes) :
    let result := Mettapedia.Machines.Cursor.ProducerOccurrenceLog.run
      (CettaDFSProducer.step program) capture capacity compatible ticks packet
    ∃ next sourceSteps, result.2.execution = some next ∧
      CettaEagerDFS.SourceRun program sourceSteps execution.producer next.producer ∧
      readback ((machine program).run sourceSteps execution.producer).2 = some next.producer ∧
      ((machine program).run sourceSteps execution.producer).1 =
        result.1.flatMap Mettapedia.Machines.Cursor.ProducerOccurrenceLog.returned := by
  dsimp only
  obtain ⟨next, count, retained, path, _, answers⟩ :=
    CettaDFSProducer.run_source capture capacity compatible ticks packet execution attached valid
  have advances := CettaEagerDFS.source_run_advances path
  have observed := run_answer_history program count execution.producer valid
  rw [advances] at observed
  refine ⟨next, count, retained, path, ?_, ?_⟩
  · rw [run_readback, advances]
  · exact List.append_cancel_left (observed.symm.trans answers)

/-- The generic resumption law applies to the actual streaming evaluator,
preserving established occurrences and the complete saved configuration. -/
theorem resume_after_prefix (program : Program) (first second : Nat)
    (source residual : Configuration) (events : List Atom)
    (paused : (machine program).run first source = (events, .exhausted residual)) :
    (machine program).run (first + second) source =
      (events ++ ((machine program).run second residual).1,
        ((machine program).run second residual).2) :=
  (machine program).established_and_pending first second source residual events paused

/-- Longer budgets extend the ordered answer prefix without revising a final
status. Changing the strategy or source is not covered by this law. -/
theorem observation_prefix (program : Program) (first second : Nat)
    (source : Configuration) :
    ((machine program).observe first source).Prefix
      ((machine program).observe (first + second) source) :=
  (machine program).observe_prefix first second source

/-- A supplied price account splits at the exact saved state. Its physical
meaning and bounds require separate implementation evidence. -/
theorem account_split (program : Program) (price : Configuration → Nat)
    (first second : Nat) (source : Configuration) :
    (machine program).spent price (first + second) source =
      (machine program).spent price first source +
        (machine program).spentAfter price second ((machine program).run first source).2 :=
  (machine program).spent_add price first second source

namespace Controls

open CettaDFSProducer.Controls (program ready a b printReady)

def firstAnswer : Configuration :=
  CettaEagerDFS.advance program 1 ready

theorem pause_after_one_answer :
    (machine program).run 1 ready = ([a], .exhausted firstAnswer) := rfl

theorem resume_keeps_both_remaining_occurrences :
    (machine program).run 2 firstAnswer =
      ([a, b], .exhausted (CettaEagerDFS.advance program 3 ready)) := rfl

theorem split_after_an_observed_answer :
    (machine program).run 3 ready =
      ([a] ++ ((machine program).run 2 firstAnswer).1,
        ((machine program).run 2 firstAnswer).2) :=
  resume_after_prefix program 1 2 ready firstAnswer [a] pause_after_one_answer

/-- Restarting the initial computation repeats the established occurrence. -/
theorem restarting_repeats_an_answer :
    [a] ++ ((machine program).run 3 ready).1 ≠ ((machine program).run 3 ready).1 := by
  decide

theorem performed_output_survives_pause :
    (CettaEagerDFS.advance program 1 printReady).world.output = [a] ∧
      ((machine program).run 1 printReady).1 = [] := ⟨rfl, rfl⟩

theorem resumption_does_not_repeat_output :
    (CettaEagerDFS.advance program 2
      (CettaEagerDFS.advance program 1 printReady)).world.output = [a] := rfl

theorem stopped_fault_is_not_completion (reason : Effects.Fault) :
    let source : Configuration :=
      ⟨ready.world, [{frontier := [⟨.fault reason, []⟩]}]⟩
    (machine program).run 1 source = ([], .suspended (.fault reason) source) := rfl

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming

/-! ## Native retained child and goal-array components -/

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativePull

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/- The selected PettaPullFrame fields are logical typed C cells. The embedded
Bindings record is copied in full; its byte layout and its interpretation as
a source substitution are separate obligations. No source step is used by
the memory operations. -/
def pullLayout : ReadExpressions.Layout := fun name =>
  if name = "machine".toList then some ⟨0, .pointer⟩
  else if name = "requested_child".toList then some ⟨1, .pointer⟩
  else if name = "completed_child".toList then some ⟨2, .pointer⟩
  else if name = "answer".toList then some ⟨3, .pointer⟩
  else if name = "step".toList then some ⟨4, .word⟩
  else if name = "environment".toList then some ⟨5, .embedded⟩
  else none

def ident (name : String) : CExpr := .identifier name.toList
def field (owner name : String) : CExpr := .field (ident owner) name.toList true

def requestBody : List CStatement :=
  [.assign (field "frame" "requested_child") (ident "child")]

def handoffBody : List CStatement :=
  [.assign (field "parent" "completed_child") (ident "child"),
   .assign (field "parent" "answer") (ident "result"),
   .assign (field "parent" "environment") (ident "bindings"),
   .assign (field "parent" "step") (ident "step")]

def consumeBody : List CStatement :=
  [.assign (.unary .dereference (ident "answer")) (field "frame" "answer"),
   .assign (.unary .dereference (ident "environment")) (field "frame" "environment"),
   .effect (.call "bindings_init".toList
     [.unary .address (field "frame" "environment")]),
   .assign (field "frame" "answer") .null,
   .assign (field "frame" "completed_child") .null]

def requestSource : String := "{ frame->requested_child = child; }"
def handoffSource : String := "{ parent->completed_child = child; parent->answer = result; parent->environment = bindings; parent->step = step; }"
def consumeSource : String := "{ *answer = frame->answer; *environment = frame->environment; bindings_init(&frame->environment); frame->answer = NULL; frame->completed_child = NULL; }"

def requestTokens : List Token := [.punctuation "{".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "requested_child".toList, .punctuation "=".toList, .identifier "child".toList, .punctuation ";".toList, .punctuation "}".toList]
theorem request_lex : lex requestSource.toList = .ok requestTokens := by
  apply lex_of_completed
  decide +kernel
theorem request_parsed : blockText? [] requestSource.toList = some requestBody :=
  block_text_of_parts [] _ requestTokens _ request_lex (by rfl)
def handoffTokens : List Token := [.punctuation "{".toList, .identifier "parent".toList, .punctuation "->".toList, .identifier "completed_child".toList, .punctuation "=".toList, .identifier "child".toList, .punctuation ";".toList, .identifier "parent".toList, .punctuation "->".toList, .identifier "answer".toList, .punctuation "=".toList, .identifier "result".toList, .punctuation ";".toList, .identifier "parent".toList, .punctuation "->".toList, .identifier "environment".toList, .punctuation "=".toList, .identifier "bindings".toList, .punctuation ";".toList, .identifier "parent".toList, .punctuation "->".toList, .identifier "step".toList, .punctuation "=".toList, .identifier "step".toList, .punctuation ";".toList, .punctuation "}".toList]
theorem handoff_lex : lex handoffSource.toList = .ok handoffTokens := by
  apply lex_of_completed
  decide +kernel
theorem handoff_parsed : blockText? [] handoffSource.toList = some handoffBody :=
  block_text_of_parts [] _ handoffTokens _ handoff_lex (by rfl)
def consumeTokens : List Token := [.punctuation "{".toList, .punctuation "*".toList, .identifier "answer".toList, .punctuation "=".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "answer".toList, .punctuation ";".toList, .punctuation "*".toList, .identifier "environment".toList, .punctuation "=".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "environment".toList, .punctuation ";".toList, .identifier "bindings_init".toList, .punctuation "(".toList, .punctuation "&".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "environment".toList, .punctuation ")".toList, .punctuation ";".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "answer".toList, .punctuation "=".toList, .identifier "NULL".toList, .punctuation ";".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "completed_child".toList, .punctuation "=".toList, .identifier "NULL".toList, .punctuation ";".toList, .punctuation "}".toList]
theorem consume_lex : lex consumeSource.toList = .ok consumeTokens := by
  apply lex_of_completed
  decide +kernel
theorem consume_parsed : blockText? [] consumeSource.toList = some consumeBody :=
  block_text_of_parts [] _ consumeTokens _ consume_lex (by rfl)

def requestEnvironment (frame child : Ptr) : ReadExpressions.Environment := fun name =>
  if name = "frame".toList then some (.ptr (some frame))
  else if name = "child".toList then some (.ptr (some child)) else none

def handoffEnvironment (parent child : Ptr) (answer : Option Ptr) (step : UInt32) :
    ReadExpressions.Environment := fun name =>
  if name = "parent".toList then some (.ptr (some parent))
  else if name = "child".toList then some (.ptr (some child))
  else if name = "result".toList then some (.ptr answer)
  else if name = "step".toList then some (.u32 step) else none

def consumeEnvironment (frame answer environment : Ptr) : ReadExpressions.Environment := fun name =>
  if name = "frame".toList then some (.ptr (some frame))
  else if name = "answer".toList then some (.ptr (some answer))
  else if name = "environment".toList then some (.ptr (some environment)) else none

/- C's aggregate assignment is a copy of the supplied whole embedded record,
not a read of an invented pointer-valued environment field. Scalar statements
continue through the existing field assignment interpreter. -/
def handoffAssignment (bindingSource : Ptr) (bindingWidth : Nat) : StatementBlock.Assignment :=
  fun layout environment statement =>
    match statement with
    | .assign (.field owner name true) (.identifier source) =>
      if name = "environment".toList ∧ source = "bindings".toList then do
        let actual ← ReadExpressions.expression layout environment owner
        let destination ← ReadExpressions.fieldAddress layout actual name
        CProg.copyCells bindingSource destination bindingWidth
        pure environment
      else StatementBlock.fieldAssignment ReadExpressions.expression layout environment statement
    | _ => StatementBlock.fieldAssignment ReadExpressions.expression layout environment statement

def consumeAssignment (bindingWidth : Nat) : StatementBlock.Assignment :=
  fun layout environment statement =>
    match statement with
    | .assign (.unary .dereference (.identifier destination))
        (.field owner name true) => do
      let address ← ReadExpressions.resolved (environment destination) >>= ReadExpressions.pointer
      match address with
      | none => CProg.undefined
      | some address =>
        if name = "environment".toList then do
          let actual ← ReadExpressions.expression layout environment owner
          let source ← ReadExpressions.fieldAddress layout actual name
          CProg.copyCells source address bindingWidth
          pure environment
        else do
          let value ← ReadExpressions.expression layout environment (.field owner name true)
          CProg.store address value
          pure environment
    | _ => StatementBlock.fieldAssignment ReadExpressions.expression layout environment statement

def bindingInitializer (empty : List CVal) : StatementBlock.Effect :=
  fun layout environment expression =>
    match expression with
    | .call name [address] =>
      if name = "bindings_init".toList then do
        let actual ← ReadExpressions.expression layout environment address >>= ReadExpressions.pointer
        match actual with
        | some destination => CProg.initializeCells destination empty
        | none => CProg.undefined
      else CProg.undefined
    | _ => CProg.undefined

def requestProgram (frame child : Ptr) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith {} (StatementBlock.fieldAssignment ReadExpressions.expression)
    pullLayout 0 2 (requestEnvironment frame child) requestBody

def handoffProgram (parent child bindingSource : Ptr) (answer : Option Ptr)
    (step : UInt32) (bindingWidth : Nat) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith {} (handoffAssignment bindingSource bindingWidth)
    pullLayout 0 5 (handoffEnvironment parent child answer step) handoffBody

def consumeProgram (frame answer environment : Ptr) (empty : List CVal) :
    CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith { effect := bindingInitializer empty }
    (consumeAssignment empty.length) pullLayout 0 6
    (consumeEnvironment frame answer environment) consumeBody

def requestOperations (frame child : Ptr) : CProg CVal ReadBlock.Result := do
  CProg.store (frame + 1) (.ptr (some child))
  pure (.finished (.next (requestEnvironment frame child)))

def handoffOperations (parent child bindingSource : Ptr) (answer : Option Ptr)
    (step : UInt32) (bindingWidth : Nat) : CProg CVal ReadBlock.Result := do
  CProg.store (parent + 2) (.ptr (some child))
  CProg.store (parent + 3) (.ptr answer)
  CProg.copyCells bindingSource (parent + 5) bindingWidth
  CProg.store (parent + 4) (.u32 step)
  pure (.finished (.next (handoffEnvironment parent child answer step)))

def consumeOperations (frame answer environment : Ptr) (empty : List CVal) :
    CProg CVal ReadBlock.Result := do
  let value ← CProg.loadPtr (frame + 3)
  CProg.store answer (.ptr value)
  CProg.copyCells (frame + 5) environment empty.length
  CProg.initializeCells (frame + 5) empty
  CProg.store (frame + 3) (.ptr none)
  CProg.store (frame + 2) (.ptr none)
  pure (.finished (.next (consumeEnvironment frame answer environment)))

theorem request_uses_memory (frame child : Ptr) :
    requestProgram frame child = requestOperations frame child := by
  simp [requestProgram, requestBody, ident, field, requestEnvironment,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, StatementBlock.fieldAssignment,
    ReadExpressions.expression, ReadExpressions.expressionWith,
    ReadExpressions.expressionWithNames,
    ReadExpressions.storeField, ReadExpressions.pointer, ReadExpressions.resolved,
    ReadExpressions.fieldAddress, pullLayout,
    ReadExpressions.valueKind, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    Prog.bind_assoc, requestOperations]

theorem handoff_uses_memory (parent child bindingSource : Ptr) (answer : Option Ptr)
    (step : UInt32) (width : Nat) :
    handoffProgram parent child bindingSource answer step width =
      handoffOperations parent child bindingSource answer step width := by
  simp [handoffProgram, handoffBody, ident, field, handoffEnvironment,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, handoffAssignment, StatementBlock.fieldAssignment,
    ReadExpressions.expression, ReadExpressions.expressionWith,
    ReadExpressions.expressionWithNames,
    ReadExpressions.storeField, ReadExpressions.pointer, ReadExpressions.resolved,
    ReadExpressions.fieldAddress, pullLayout,
    ReadExpressions.valueKind, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    Prog.bind_assoc, handoffOperations]

theorem consume_uses_memory (frame answer environment : Ptr) (empty : List CVal) :
    consumeProgram frame answer environment empty =
      consumeOperations frame answer environment empty := by
  simp [consumeProgram, consumeBody, ident, field, consumeEnvironment,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, consumeAssignment, bindingInitializer,
    StatementBlock.fieldAssignment, ReadExpressions.expression,
    ReadExpressions.expressionWith, ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.storeField, ReadExpressions.pointer,
    ReadExpressions.resolved, ReadExpressions.fieldAddress, pullLayout,
    ReadExpressions.ObjectReads.fieldLayout, ReadExpressions.valueKind,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc, consumeOperations]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem request_owned (frame child : Ptr) (prior : Option Ptr) (rest : Heap L → Prop) :
    CTriple (PointsTo (frame + 1) (.ptr prior) ∗ rest) (requestProgram frame child)
      (fun result heap => result = .finished (.next (requestEnvironment frame child)) ∧
        (PointsTo (frame + 1) (.ptr (some child)) ∗ rest) heap) := by
  rw [request_uses_memory]
  cmem_start heap held
  unfold requestOperations
  cmem_vcgen
  cmem_exact

theorem handoff_owned (parent child bindingSource : Ptr) (answer oldChild oldAnswer : Option Ptr)
    (step oldStep : UInt32) (bindings : List CVal) (old : List (Option CVal))
    (width : old.length = bindings.length) (rest : Heap L → Prop) :
    CTriple (PointsTo (parent + 2) (.ptr oldChild) ∗
      PointsTo (parent + 3) (.ptr oldAnswer) ∗ PointsTo (parent + 4) (.u32 oldStep) ∗
      Cells bindingSource (bindings.map some) ∗ Cells (parent + 5) old ∗ rest)
      (handoffProgram parent child bindingSource answer step bindings.length)
      (fun result heap => result = .finished (.next (handoffEnvironment parent child answer step)) ∧
        (PointsTo (parent + 2) (.ptr (some child)) ∗
          PointsTo (parent + 3) (.ptr answer) ∗ PointsTo (parent + 4) (.u32 step) ∗
          Cells bindingSource (bindings.map some) ∗
          Cells (parent + 5) (bindings.map some) ∗ rest) heap) := by
  rw [handoff_uses_memory]
  cmem_start heap held
  unfold handoffOperations
  cmem_vcgen
  cmem_call copy_cells bindingSource (parent + 5) old bindings width
  rintro _ heap copied
  cmem_vcgen
  cmem_exact

theorem consume_owned (frame answer environment : Ptr) (value child oldAnswer : Option Ptr)
    (bindings empty : List CVal) (old : List (Option CVal))
    (width : empty.length = bindings.length) (destinationWidth : old.length = bindings.length)
    (rest : Heap L → Prop) :
    CTriple (PointsTo (frame + 3) (.ptr value) ∗ PointsTo (frame + 2) (.ptr child) ∗
      PointsTo answer (.ptr oldAnswer) ∗ Cells (frame + 5) (bindings.map some) ∗
      Cells environment old ∗ rest) (consumeProgram frame answer environment empty)
      (fun result heap => result = .finished (.next (consumeEnvironment frame answer environment)) ∧
        (PointsTo (frame + 3) (.ptr none) ∗ PointsTo (frame + 2) (.ptr none) ∗
          PointsTo answer (.ptr value) ∗ Cells (frame + 5) (empty.map some) ∗
          Cells environment (bindings.map some) ∗ rest) heap) := by
  rw [consume_uses_memory]
  cmem_start heap held
  unfold consumeOperations
  simp only [CProg.loadPtr, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  rw [width]
  cmem_call copy_cells (frame + 5) environment old bindings destinationWidth
  rintro _ heap copied
  cmem_call initialize_cells (frame + 5) (bindings.map some) empty
    (by simpa using width.symm)
  rintro _ heap initialized
  cmem_vcgen
  cmem_exact

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativePull

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativePull

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

/-- The actual public status tags. A private child request shares the suspended
status tag but is distinguished by the native `requested` field. -/
inductive StepTag where
  | answer | exhausted | declined | invalidated | stack | capacity | hostError | suspended
  deriving DecidableEq, Repr

def StepTag.encode : StepTag → UInt32
  | .answer => 0 | .exhausted => 1 | .declined => 2 | .invalidated => 3
  | .stack => 4 | .capacity => 5 | .hostError => 6 | .suspended => 7

def StepTag.decode : UInt32 → Option StepTag
  | 0 => some .answer | 1 => some .exhausted | 2 => some .declined
  | 3 => some .invalidated | 4 => some .stack | 5 => some .capacity
  | 6 => some .hostError | 7 => some .suspended | _ => none

theorem StepTag.decode_encode (tag : StepTag) : StepTag.decode tag.encode = some tag := by
  cases tag <;> decide +kernel

structure Reply where
  step : UInt32
  requested : Bool
  deriving DecidableEq, Repr

/-- The selected valid-parent branch of `petta_machine_pull_child`. The parsed
transfer and request blocks are used verbatim. Initial invalid pointer checks,
C byte layout and the allocator's object identities remain admission boundaries.
The equality test here is object identity, not equality of child results. -/
def pull (frame child answer environment : Ptr) (empty : List CVal) : CProg CVal Reply := do
  CProg.store answer (.ptr none)
  let completed ← CProg.loadPtr (frame + 2)
  match completed with
  | none =>
      let _ ← requestProgram frame child
      pure ⟨7, true⟩
  | some completed =>
      if completed = child then
        let _ ← consumeProgram frame answer environment empty
        let step ← CProg.loadU32 (frame + 4)
        pure ⟨step, false⟩
      else
        CProg.initializeCells environment empty
        pure ⟨5, false⟩

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem pull_requested (frame child answer environment : Ptr) (empty : List CVal)
    (oldAnswer oldRequest : Option Ptr) (rest : Heap L → Prop) :
    CTriple (PointsTo answer (.ptr oldAnswer) ∗ PointsTo (frame + 2) (.ptr none) ∗
      PointsTo (frame + 1) (.ptr oldRequest) ∗ rest)
      (pull frame child answer environment empty)
      (fun result heap => result = ⟨7, true⟩ ∧
        (PointsTo answer (.ptr none) ∗ PointsTo (frame + 2) (.ptr none) ∗
          PointsTo (frame + 1) (.ptr (some child)) ∗ rest) heap) := by
  cmem_start heap held
  unfold pull
  rw [request_uses_memory]
  unfold requestOperations
  cmem_vcgen
  cmem_exact

theorem pull_completed (frame child answer environment : Ptr) (value oldAnswer : Option Ptr)
    (step : UInt32) (bindings empty : List CVal) (old : List (Option CVal))
    (width : empty.length = bindings.length) (destinationWidth : old.length = bindings.length)
    (rest : Heap L → Prop) :
    CTriple (PointsTo answer (.ptr oldAnswer) ∗ PointsTo (frame + 2) (.ptr (some child)) ∗
      PointsTo (frame + 3) (.ptr value) ∗ PointsTo (frame + 4) (.u32 step) ∗
      Cells (frame + 5) (bindings.map some) ∗ Cells environment old ∗ rest)
      (pull frame child answer environment empty)
      (fun result heap => result = ⟨step, false⟩ ∧
        (PointsTo answer (.ptr value) ∗ PointsTo (frame + 2) (.ptr none) ∗
          PointsTo (frame + 3) (.ptr none) ∗ PointsTo (frame + 4) (.u32 step) ∗
          Cells (frame + 5) (empty.map some) ∗
          Cells environment (bindings.map some) ∗ rest) heap) := by
  cmem_start heap held
  unfold pull
  cmem_vcgen
  cmem_call consume_owned frame answer environment value (some child) none
    bindings empty old width destinationWidth (PointsTo (frame + 4) (.u32 step) ∗ rest)
  rintro _ heap ⟨rfl, copied⟩
  cmem_vcgen
  cmem_exact

theorem pull_wrong_child (frame expected actual answer environment : Ptr)
    (different : actual ≠ expected) (empty : List CVal) (oldAnswer : Option Ptr)
    (old : List (Option CVal)) (width : old.length = empty.length)
    (rest : Heap L → Prop) :
    CTriple (PointsTo answer (.ptr oldAnswer) ∗ PointsTo (frame + 2) (.ptr (some actual)) ∗
      Cells environment old ∗ rest)
      (pull frame expected answer environment empty)
      (fun result heap => result = ⟨5, false⟩ ∧
        (PointsTo answer (.ptr none) ∗ PointsTo (frame + 2) (.ptr (some actual)) ∗
          Cells environment (empty.map some) ∗ rest) heap) := by
  cmem_start heap held
  unfold pull
  cmem_vcgen
  simp only [if_neg different]
  cmem_call initialize_cells environment old empty width
  rintro _ heap cleared
  cmem_exact

/-! Executable controls use the existing finite-storage primitive interpreter.
The extra cell represents already performed shared work; transfer does not undo
or repeat it. The child evaluator remains a separate source obligation. -/
namespace Controls
open ExecutableStorage
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def frame : Ptr := ⟨1, 0⟩
def child : Ptr := ⟨2, 0⟩
def answer : Ptr := ⟨3, 0⟩
def environment : Ptr := ⟨4, 0⟩
def value : Ptr := ⟨5, 0⟩
def world : Ptr := ⟨6, 0⟩
def empty : List CVal := [.ptr none, .u32 0, .ptr none]
def bindings : List CVal := [.ptr (some ⟨7, 0⟩), .u32 2, .ptr (some ⟨8, 0⟩)]

def saved (tag : StepTag := .answer) : Storage CVal :=
  [(1, ⟨true, ([(CVal.ptr (some ⟨9, 0⟩)), .ptr none, .ptr (some child),
      .ptr (if tag = .answer then some value else none), .u32 tag.encode] ++
        (if tag = .answer then bindings else empty)).map some⟩),
   (2, ⟨true, [some (.u32 1)]⟩), (3, ⟨true, [some (.ptr none)]⟩),
   (4, ⟨true, empty.map some⟩), (5, ⟨true, [some (.u32 42)]⟩),
   (6, ⟨true, [some (.u32 1)]⟩)]

def completed? (fuel : Nat) (program : CProg CVal Reply) (storage : Storage CVal) :
    Option (Reply × Storage CVal) :=
  match (ProductiveBlocks.machine.run fuel ⟨program, storage, []⟩).2 with
  | .finished (.returned result) => some (result.answer, result.storage)
  | _ => none

def observation (result : Option (Reply × Storage CVal)) :
    Option (Reply × Option CVal × Option CVal × List (Option CVal) × Option CVal) := do
  let (reply, store) ← result
  pure (reply, load store answer, load store (frame + 2),
    (List.range 3).map (fun index => load store (environment + index)), load store world)

theorem completed_row_preserves_bindings_and_world :
    observation (completed? 40 (pull frame child answer environment empty) saved) =
      some (⟨0, false⟩, some (.ptr (some value)), some (.ptr none),
        bindings.map some, some (.u32 1)) := by rfl

theorem completed_pause_is_not_a_private_request :
    observation (completed? 40 (pull frame child answer environment empty) (saved .suspended)) =
      some (⟨7, false⟩, some (.ptr none), some (.ptr none),
        empty.map some, some (.u32 1)) := by rfl

theorem wrong_child_does_not_consume :
    observation (completed? 40 (pull frame ⟨20, 0⟩ answer environment empty) saved) =
      some (⟨5, false⟩, some (.ptr none), some (.ptr (some child)),
        empty.map some, some (.u32 1)) := by rfl

def twice : CProg CVal Reply := do
  let _ ← pull frame child answer environment empty
  pull frame child answer environment empty

theorem consumed_row_cannot_replay :
    observation (completed? 80 twice saved) =
      some (⟨7, true⟩, some (.ptr none), some (.ptr none),
        bindings.map some, some (.u32 1)) := by rfl

theorem unfinished_transfer_is_pending :
    match (ProductiveBlocks.machine.run 3
        ⟨pull frame child answer environment empty, saved, []⟩).2 with
    | .exhausted _ => True
    | _ => False := by trivial

/-- Arbitrary scheduler cuts retain the unfinished primitive program and exact
chronological receipts. Resumption does not invoke a child producer. -/
theorem resume_transfer (first second : Nat) (initial savedState :
    ProductiveBlocks.State CVal Reply) (receipts : List (ProductiveBlocks.Receipt CVal))
    (paused : ProductiveBlocks.machine.run first initial = (receipts, .exhausted savedState)) :
    ProductiveBlocks.machine.run (first + second) initial =
      (receipts ++ (ProductiveBlocks.machine.run second savedState).1,
        (ProductiveBlocks.machine.run second savedState).2) :=
  ProductiveBlocks.resume_after_prefix first second initial savedState receipts paused

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativePull

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativeGoals

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Logical cell offsets for the selected PettaGoal fields. The opaque suffix
contains every remaining plan, scope, activation and control field. Native byte
layout is an explicit representation boundary, not this cell enumeration. -/
structure Row where
  kind : UInt32
  barrier : UInt32
  instanceId : UInt64
  first : Option Ptr
  second : Option Ptr
  third : Option Ptr
  fourth : Option Ptr
  suffix : List CVal
  deriving Repr, DecidableEq

def Row.cells (row : Row) : List CVal :=
  [.u32 row.kind, .u32 row.barrier, .u64 row.instanceId,
    .ptr row.first, .ptr row.second, .ptr row.third, .ptr row.fourth] ++ row.suffix

/-- Source-facing requests retain their destination. They are not complete
source evaluations, and no eager or relational policy is selected here. -/
inductive Request where
  | solve (expression destination : Atom)
  | unify (left right : Atom)
  | callReady (invocation destination : Atom)
  | argumentReturn (value destination : Atom) (returnHeight : UInt64)
  deriving DecidableEq, Repr

/-- The actual enum tags read from petta_search_machine.c. An unsupported kind
is refused by this component rather than interpreted as a solver step. -/
def Row.request (atoms : Ptr → Option Atom) (row : Row) : Option Request := do
  let first ← row.first >>= atoms
  let second ← row.second >>= atoms
  if row.kind = 0 then some (.solve first second)
  else if row.kind = 4 then some (.callReady first second)
  else if row.kind = 25 then some (.unify first second)
  else if row.kind = 23 then
    match (row.suffix[6]? : Option CVal) with
    | some (CVal.u64 height) => some (.argumentReturn first second height)
    | _ => none
  else none

structure Occurrence where
  identity : UInt64
  barrier : UInt32
  request : Request
  deriving DecidableEq, Repr

def Row.observe (atoms : Ptr → Option Atom) (row : Row) : Option Occurrence := do
  pure ⟨row.instanceId, row.barrier, ← row.request atoms⟩

/-- The native array's live prefix is bottom-to-top; the source continuation
front is its reverse. Rows outside the live prefix remain protected by the
choice/overwrite trail, a separate part of the machine representation. -/
def readback (atoms : Ptr → Option Atom) (active : List Row) : Option (List Occurrence) :=
  active.reverse.mapM (Row.observe atoms)

theorem readback_push (atoms : Ptr → Option Atom) (active : List Row) (row : Row) :
    readback atoms (active ++ [row]) = (do
      let nextOccurrence ← row.observe atoms
      let older ← readback atoms active
      pure (nextOccurrence :: older)) := by
  simp [readback, List.reverse_append]

theorem readback_push_iff (atoms : Ptr → Option Atom) (active : List Row) (row : Row)
    (nextOccurrence : Occurrence) (older : List Occurrence) :
    row.observe atoms = some nextOccurrence →
    (readback atoms (active ++ [row]) = some (nextOccurrence :: older) ↔ readback atoms active = some older) := by
  intro selected
  rw [readback_push, selected]
  cases readback atoms active <;> simp

/-- The aggregate-copy portion of the admitted native push: reserve, protected
slot logging and epoch retention have already succeeded. The store increments
the live length before copying, exactly as the C post-increment does. -/
def push (length source base : Ptr) (width : Nat) : CProg CVal Unit := do
  let index ← CProg.loadU64 length
  CProg.store length (.u64 (index + 1))
  CProg.copyCells source (base + index.toNat * width) width

/-- The scheduler removes a live top row before dispatch. An empty live prefix
is not read; the native scheduler treats it as completion before this block. -/
def pop (length base : Ptr) (width : Nat) : CProg CVal (List CVal) := do
  let index ← CProg.loadU64 length
  if index = 0 then CProg.undefined else do
    let prior := index - 1
    CProg.store length (.u64 prior)
    CProg.loadCells (base + prior.toNat * width) width

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem push_preserves_older (length source base : Ptr) (index : UInt64)
    (priorCells row : List CVal) (old : List (Option CVal))
    (position : index.toNat * row.length = priorCells.length)
    (width : old.length = row.length) (rest : Heap L → Prop) :
    CTriple (PointsTo length (.u64 index) ∗ Cells source (row.map some) ∗
      Cells base (priorCells.map some ++ old) ∗ rest)
      (push length source base row.length)
      (fun _ => PointsTo length (.u64 (index + 1)) ∗ Cells source (row.map some) ∗
        Cells base ((priorCells ++ row).map some) ∗ rest) := by
  cmem_start heap held
  simp only [cells_append, List.length_map] at held
  unfold push
  simp only [CProg.loadU64, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  rw [position]
  cmem_call copy_cells source (base + priorCells.length) old row width
  rintro _ heap copied
  simp only [List.map_append, cells_append, List.length_map]
  cmem_exact

theorem pop_preserves_older (length base : Ptr) (index : UInt64)
    (nonempty : index ≠ 0) (priorCells row : List CVal)
    (position : (index - 1).toNat * row.length = priorCells.length) (rest : Heap L → Prop) :
    CTriple (PointsTo length (.u64 index) ∗ Cells base ((priorCells ++ row).map some) ∗ rest)
      (pop length base row.length)
      (fun result heap => result = row ∧
        (PointsTo length (.u64 (index - 1)) ∗
          Cells base ((priorCells ++ row).map some) ∗ rest) heap) := by
  cmem_start heap held
  simp only [List.map_append, cells_append, List.length_map] at held
  unfold pop
  simp only [CProg.loadU64, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  simp only [if_neg nonempty]
  cmem_vcgen
  rw [position]
  cmem_call load_cells (base + priorCells.length) row
  rintro _ heap ⟨rfl, loaded⟩
  simp only [List.map_append, cells_append, List.length_map]
  exact ⟨trivial, by cmem_exact⟩

/-- The two independently written boundaries compose: actual aggregate push
preserves the physical prefix, and the source-facing readback adds exactly one
occurrence with its original destination and barrier. -/
theorem pushed_occurrence_readback (atoms : Ptr → Option Atom) (active : List Row) (row : Row)
    (occurrence : Occurrence) (older : List Occurrence)
    (selected : row.observe atoms = some occurrence) (prior : readback atoms active = some older) :
    readback atoms (active ++ [row]) = some (occurrence :: older) := by
  exact (readback_push_iff atoms active row occurrence older selected).mpr prior

/-! Source-independent scheduling data from the actual admitted control branch.
The branch policy is explicit. Execution of these destination-bearing requests
requires the relational source service; it is not identified with eager DFS. -/
inductive BindingPolicy where
  | eagerValue | relationalLeft | relationalRight
  deriving DecidableEq, Repr

/-- Authored local schedules retain the intermediate destination and final
body destination. This is an admission judgment for control construction. -/
inductive LetSchedule : BindingPolicy → Atom → Atom → Atom → Atom → Atom → List Request → Prop where
  | eager (pattern producer body output hole : Atom) :
      LetSchedule .eagerValue pattern producer body output hole
        [.solve producer hole, .unify pattern hole, .solve body output]
  | relationalLeft (pattern producer body output hole : Atom) :
      LetSchedule .relationalLeft pattern producer body output hole
        [.solve pattern hole, .solve producer hole, .solve body output]
  | relationalRight (pattern producer body output hole : Atom) :
      LetSchedule .relationalRight pattern producer body output hole
        [.solve producer hole, .solve pattern hole, .solve body output]

/-- This is the actual order of pushes in each selected C branch. It is
independent of the source judgment and of the array readback. -/
def letPushes (policy : BindingPolicy) (pattern producer body output hole : Atom) : List Request :=
  match policy with
  | .eagerValue => [.solve body output, .unify pattern hole, .solve producer hole]
  | .relationalLeft => [.solve body output, .solve producer hole, .solve pattern hole]
  | .relationalRight => [.solve body output, .solve pattern hole, .solve producer hole]

theorem let_schedule_iff (policy : BindingPolicy) (pattern producer body output hole : Atom)
    (requests : List Request) :
    LetSchedule policy pattern producer body output hole requests ↔
      (letPushes policy pattern producer body output hole).reverse = requests := by
  constructor
  · intro source
    cases source <;> rfl
  · intro selected
    subst requests
    cases policy
    · exact .eager _ _ _ _ _
    · exact .relationalLeft _ _ _ _ _
    · exact .relationalRight _ _ _ _ _

/-- The existing scalar source has precisely the eager producer-first entry.
This theorem does not turn a relational scheduling witness into that entry. -/
theorem eager_source_entry (program : SpaceSemantics.Program) (world : CettaEagerDFS.World)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (pattern producer body : Atom) (older : List CettaEagerDFS.Frame) :
    CettaEagerDFS.LocalTransition program world
      ⟨.evaluate bindings (.expression [.symbol "let", pattern, producer, body]), older⟩ world
      (.next ⟨.evaluate bindings producer, .bind bindings pattern body :: older⟩) :=
  .let_enter

/-- Actual argument rows retain the producer syntax, its fresh result slot,
the native evaluation flag and the error-control test. The latter decides
whether a return-height guard is pushed; it never changes the producer order. -/
structure Argument where
  expression : Atom
  destination : Atom
  evaluate : Bool
  knownError : Bool
  deriving DecidableEq, Repr

def argumentRowPushes (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (argument : Argument) : List Request :=
  (if eagerFaults && (argument.evaluate || argument.knownError) then
    [.argumentReturn argument.destination output height] else []) ++
  (if argument.evaluate then [.solve argument.expression argument.destination] else [])

/-- Direct translation of the native descending index loop, following the
already-pushed final call/data/unification row. -/
def argumentPushes (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (arguments : List Argument) : List Request :=
  arguments.reverse.flatMap (argumentRowPushes eagerFaults output height)

def argumentExecution (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (arguments : List Argument) : List Request :=
  arguments.flatMap fun argument =>
    (if argument.evaluate then [.solve argument.expression argument.destination] else []) ++
    (if eagerFaults && (argument.evaluate || argument.knownError) then
      [.argumentReturn argument.destination output height] else [])

/-- Reversing the actual goal-array pushes gives left-to-right producer
execution, with each enabled fault guard immediately after its producer.
Every guard retains the same older-frame boundary, rather than an inferred
boundary based on the current number of answers. -/
theorem argument_order (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (arguments : List Argument) :
    (argumentPushes eagerFaults output height arguments).reverse =
      argumentExecution eagerFaults output height arguments := by
  induction arguments with
  | nil => simp [argumentPushes, argumentExecution]
  | cons argument arguments ih =>
      simp only [argumentPushes, List.reverse_cons, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.reverse_append,
        argumentExecution, List.flatMap_cons]
      rw [show (List.flatMap (argumentRowPushes eagerFaults output height) arguments.reverse).reverse =
        argumentExecution eagerFaults output height arguments from ih]
      simp only [argumentRowPushes, List.reverse_append]
      cases eagerFaults <;> cases argument.evaluate <;> cases argument.knownError <;> rfl

namespace Controls

def atoms : Ptr → Option Atom := fun pointer => some (.symbol (toString pointer.block))
def row (identity : UInt64) (tag : UInt32 := 0) : Row :=
  ⟨tag, 17, identity, some ⟨1, 0⟩, some ⟨2, 0⟩, none, none, [.bool false]⟩

theorem two_equal_payloads_keep_occurrences :
    readback atoms [row 10, row 11] = some
      [⟨11, 17, .solve (.symbol "1") (.symbol "2")⟩,
       ⟨10, 17, .solve (.symbol "1") (.symbol "2")⟩] := by decide +kernel

theorem unsupported_tag_not_a_solve : (row 10 77).request atoms = none := by decide +kernel

theorem eager_and_relational_keep_different_requests :
    letPushes .eagerValue (.symbol "A") (.symbol "effect") (.symbol "C") (.var "out") (.var "join") ≠
    letPushes .relationalLeft (.symbol "A") (.symbol "effect") (.symbol "C") (.var "out") (.var "join") := by
  decide +kernel


theorem call_ready_keeps_original_destination :
    (row 21 4).observe atoms = some
      ⟨21, 17, .callReady (.symbol "1") (.symbol "2")⟩ := by decide +kernel

theorem argument_return_requires_saved_height :
    (row 22 23).request atoms = none := by decide +kernel

theorem argument_return_retains_height :
    ({ row 22 23 with suffix := List.replicate 6 (CVal.ptr none) ++ [CVal.u64 5] }).request atoms =
      some (.argumentReturn (.symbol "1") (.symbol "2") 5) := by decide +kernel

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativeGoals

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativeGoals

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

private def id (name : String) : CExpr := .identifier name.toList
private def sourceElement (index : CExpr) : CExpr :=
  .index (.field (.field (id "expression") "expr".toList true) "elems".toList false) index
private def barrier : CExpr := .field (id "goal") "barrier".toList true
private def planChild (index : CExpr) : CExpr :=
  .call "petta_plan_child".toList [id "plan", index]

def solveCall (index destination : CExpr) : CExpr :=
  .call "petta_push_solve_planned".toList
    [id "machine", sourceElement (match index with | .unsignedInteger n => .decimal n | other => other), destination, barrier, planChild index]

def unifyCall : CExpr :=
  .call "petta_push_unify".toList
    [id "machine", sourceElement (id "binder_index"), id "value", barrier]

def eagerFailure : CExpr := .binary .or
  (.binary .or (.binary .or (.unary .not (id "value"))
    (.unary .not (solveCall (.unsignedInteger 3) (id "expected"))))
    (.unary .not unifyCall))
  (.unary .not (solveCall (id "source_index") (id "value")))

def relationalLeftFailure : CExpr := .binary .or
  (.unary .not (solveCall (.unsignedInteger 2) (id "joined")))
  (.unary .not (solveCall (.unsignedInteger 1) (id "joined")))

def relationalRightFailure : CExpr := .binary .or
  (.unary .not (solveCall (.unsignedInteger 1) (id "joined")))
  (.unary .not (solveCall (.unsignedInteger 2) (id "joined")))

def eagerFailureSource : String := "!value || !petta_push_solve_planned(machine, expression->expr.elems[3], expected, goal->barrier, petta_plan_child(plan, 3u)) || !petta_push_unify(machine, expression->expr.elems[binder_index], value, goal->barrier) || !petta_push_solve_planned(machine, expression->expr.elems[source_index], value, goal->barrier, petta_plan_child(plan, source_index))"
def eagerFailureTokens : List Token := [.punctuation "!".toList, .identifier "value".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .number "3".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "expected".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .number "3u".toList, .punctuation ")".toList, .punctuation ")".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "petta_push_unify".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .identifier "binder_index".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "value".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ")".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .identifier "source_index".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "value".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .identifier "source_index".toList, .punctuation ")".toList, .punctuation ")".toList]
theorem eagerFailure_lex : lex eagerFailureSource.toList = .ok eagerFailureTokens := by
  apply lex_of_completed
  decide +kernel
theorem eagerFailure_parsed : expressionText? [] eagerFailureSource.toList = some eagerFailure := by
  unfold expressionText?
  rw [eagerFailure_lex]
  rfl

def relationalLeftFailureSource : String := "!petta_push_solve_planned(machine, expression->expr.elems[2], joined, goal->barrier, petta_plan_child(plan, 2u)) || !petta_push_solve_planned(machine, expression->expr.elems[1], joined, goal->barrier, petta_plan_child(plan, 1u))"
def relationalLeftFailureTokens : List Token := [.punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .number "2".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "joined".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .number "2u".toList, .punctuation ")".toList, .punctuation ")".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .number "1".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "joined".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .number "1u".toList, .punctuation ")".toList, .punctuation ")".toList]
theorem relationalLeftFailure_lex : lex relationalLeftFailureSource.toList = .ok relationalLeftFailureTokens := by
  apply lex_of_completed
  decide +kernel
theorem relationalLeftFailure_parsed : expressionText? [] relationalLeftFailureSource.toList = some relationalLeftFailure := by
  unfold expressionText?
  rw [relationalLeftFailure_lex]
  rfl

def relationalRightFailureSource : String := "!petta_push_solve_planned(machine, expression->expr.elems[1], joined, goal->barrier, petta_plan_child(plan, 1u)) || !petta_push_solve_planned(machine, expression->expr.elems[2], joined, goal->barrier, petta_plan_child(plan, 2u))"
def relationalRightFailureTokens : List Token := [.punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .number "1".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "joined".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .number "1u".toList, .punctuation ")".toList, .punctuation ")".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .number "2".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "joined".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .number "2u".toList, .punctuation ")".toList, .punctuation ")".toList]
theorem relationalRightFailure_lex : lex relationalRightFailureSource.toList = .ok relationalRightFailureTokens := by
  apply lex_of_completed
  decide +kernel
theorem relationalRightFailure_parsed : expressionText? [] relationalRightFailureSource.toList = some relationalRightFailure := by
  unfold expressionText?
  rw [relationalRightFailure_lex]
  rfl


structure PushOperands where
  kind : UInt32
  expression : CExpr
  destination : CExpr
  barrier : CExpr
  plan : Option CExpr
  deriving Repr

/-- Extract only the two admitted native helper calls. The machine receiver,
arity and full operand syntax are checked. Execution remains the C call service. -/
def pushOperands? : CExpr → Option PushOperands
  | .call name [.identifier machine, expression, destination, barrier, plan] =>
      if name = "petta_push_solve_planned".toList ∧ machine = "machine".toList then
        some ⟨0, expression, destination, barrier, some plan⟩
      else none
  | .call name [.identifier machine, expression, destination, barrier] =>
      if name = "petta_push_unify".toList ∧ machine = "machine".toList then
        some ⟨25, expression, destination, barrier, none⟩
      else none
  | _ => none

/-- Potential calls are listed in their C short-circuit order. The pointer
allocation guard contributes no call. A failed prefix does not execute the
remaining list; that execution fact is proved below using the C interpreter. -/
def constructionCalls? : CExpr → Option (List PushOperands)
  | .binary .or left right => do
      pure ((← constructionCalls? left) ++ (← constructionCalls? right))
  | .unary .not (.identifier name) =>
      if name = "value".toList then some [] else none
  | .unary .not call => (pushOperands? call).map List.singleton
  | _ => none

theorem eager_call_operands : constructionCalls? eagerFailure = some
    [⟨0, sourceElement (.decimal 3), id "expected", barrier,
       some (planChild (.unsignedInteger 3))⟩,
     ⟨25, sourceElement (id "binder_index"), id "value", barrier, none⟩,
     ⟨0, sourceElement (id "source_index"), id "value", barrier,
       some (planChild (id "source_index"))⟩] := by rfl

theorem relational_left_call_operands : constructionCalls? relationalLeftFailure = some
    [⟨0, sourceElement (.decimal 2), id "joined", barrier,
       some (planChild (.unsignedInteger 2))⟩,
     ⟨0, sourceElement (.decimal 1), id "joined", barrier,
       some (planChild (.unsignedInteger 1))⟩] := by rfl

theorem relational_right_call_operands : constructionCalls? relationalRightFailure = some
    [⟨0, sourceElement (.decimal 1), id "joined", barrier,
       some (planChild (.unsignedInteger 1))⟩,
     ⟨0, sourceElement (.decimal 2), id "joined", barrier,
       some (planChild (.unsignedInteger 2))⟩] := by rfl

/-- Negation and short-circuiting retain the actual physical CProg effects. -/
def failureOf (operation : CProg CVal CVal) : CProg CVal CVal := do
  let value ← operation
  let succeeded ← ReadExpressions.truth value
  pure (.bool (!succeeded))

def eitherFailure (left right : CProg CVal CVal) : CProg CVal CVal := do
  let value ← left
  let failed ← ReadExpressions.truth value
  if failed then pure (.bool true) else do
    let value ← right
    let failed ← ReadExpressions.truth value
    pure (.bool failed)

theorem relational_left_executes_actual_calls (names : ReadExpressions.NameReads)
    (calls : ReadExpressions.Calls) (layout : ReadExpressions.Layout)
    (objects : ReadExpressions.ObjectReads := {}) :
    ReadExpressions.expressionWithNames names calls layout relationalLeftFailure objects =
      eitherFailure
        (failureOf (ReadExpressions.expressionWithNames names calls layout
          (solveCall (.unsignedInteger 2) (id "joined")) objects))
        (failureOf (ReadExpressions.expressionWithNames names calls layout
          (solveCall (.unsignedInteger 1) (id "joined")) objects)) := by rfl

theorem relational_right_executes_actual_calls (names : ReadExpressions.NameReads)
    (calls : ReadExpressions.Calls) (layout : ReadExpressions.Layout)
    (objects : ReadExpressions.ObjectReads := {}) :
    ReadExpressions.expressionWithNames names calls layout relationalRightFailure objects =
      eitherFailure
        (failureOf (ReadExpressions.expressionWithNames names calls layout
          (solveCall (.unsignedInteger 1) (id "joined")) objects))
        (failureOf (ReadExpressions.expressionWithNames names calls layout
          (solveCall (.unsignedInteger 2) (id "joined")) objects)) := by rfl

theorem successful_pushes_keep_order (first second : CProg CVal Unit) :
    eitherFailure
      (failureOf (first >>= fun _ => pure (.bool true)))
      (failureOf (second >>= fun _ => pure (.bool true))) =
      (first >>= fun _ => second >>= fun _ => pure (.bool false)) := by
  simp [eitherFailure, failureOf, ReadExpressions.truth,
    Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]

theorem failed_push_keeps_prefix (first : CProg CVal Unit) (second : CProg CVal CVal) :
    eitherFailure (failureOf (first >>= fun _ => pure (.bool false))) second =
      (first >>= fun _ => pure (.bool true)) := by
  simp [eitherFailure, failureOf, ReadExpressions.truth,
    Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]

/-- Once the body has been pushed, the admitted relational-left C branch
executes producer-push before binder-push. The reverse live-array readback
therefore places the binder first, retaining their one shared destination. -/
theorem relational_left_physical_sequence (body producer binder : CProg CVal Unit) :
    (do body
        eitherFailure (failureOf (producer >>= fun _ => pure (.bool true)))
          (failureOf (binder >>= fun _ => pure (.bool true)))) =
      (body >>= fun _ => producer >>= fun _ => binder >>= fun _ => pure (.bool false)) := by
  rw [successful_pushes_keep_order]

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativeGoals

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativeGoals

open Mettapedia.Machines.CMemory
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS.Destination

/-- Understood native phases enter the independently stated destination
component. An argument return retains its saved continuation delimiter; the
source step separately validates that the designated caller suffix exists. -/
def Request.goal : Request → Option Goal
  | .solve expression destination => some (.evaluate expression destination)
  | .unify value destination => some (.equate value destination)
  | .callReady (.expression (.symbol head :: arguments)) destination =>
      some (.invoke head arguments destination)
  | .argumentReturn value destination height =>
      some (.argumentReturn value destination height.toNat)
  | .callReady _ _ => none

def sourceGoals (occurrences : List Occurrence) : Option (List Goal) :=
  occurrences.mapM (fun occurrence => occurrence.request.goal)

def rowsToGoals (atoms : Ptr → Option Atom) (active : List Row) : Option (List Goal) := do
  sourceGoals (← readback atoms active)

theorem rowsToGoals_push (atoms : Ptr → Option Atom) (active : List Row) (row : Row)
    (occurrence : Occurrence) (goal : Goal)
    (decoded : row.observe atoms = some occurrence) (understood : occurrence.request.goal = some goal) :
    rowsToGoals atoms (active ++ [row]) = (goal :: ·) <$> rowsToGoals atoms active := by
  simp only [rowsToGoals, readback_push, decoded]
  cases old : readback atoms active with
  | none => rfl
  | some occurrences =>
      cases pending : sourceGoals occurrences <;> simp_all [sourceGoals]

/-- The raw native checkpoint retains the complete binding record, all goal
fields, occurrence identities and enclosing scope state. A supplied scalar/
atom representation reads values; it is not a native-unifier adequacy premise. -/
structure Saved (Context : Type) where
  bindings : List CVal
  active : List Row
  output : Ptr
  world : CettaEagerDFS.World
  enclosing : Context
  reserved : Finset String := ∅

/-- The binding reader must account for the actual current-value authority of
SearchContext (including contextual frame slots), not reinterpret historical
Binding entries as simultaneous assignments. Its correctness is a separate
representation obligation. These control squares do not assume it. -/
def Saved.readback {Context : Type} (atoms : Ptr → Option Atom)
    (readBindings : List CVal → Option Equations) (saved : Saved Context) :
    Option (Cursor Context) := do
  let bindings ← readBindings saved.bindings
  let goals ← rowsToGoals atoms saved.active
  let destination ← atoms saved.output
  pure ⟨saved.world, ⟨bindings, goals, destination, saved.reserved⟩,
    saved.enclosing⟩

/-- The admitted native view makes the finite structural boundary testable.
A missing atom/phase/binding representation or an unsupported scalar retains
the native checkpoint; it does not authorize a source completion. -/
def Saved.readbackFinite {Context : Type} (atoms : Ptr → Option Atom)
    (readBindings : List CVal → Option Equations) (saved : Saved Context) :
    Option (Cursor Context) := do
  let cursor ← saved.readback atoms readBindings
  if cursor.control.finiteStructural then some cursor else none

theorem readbackFinite_iff {Context : Type} (atoms : Ptr → Option Atom)
    (readBindings : List CVal → Option Equations) (saved : Saved Context)
    (cursor : Cursor Context) :
    saved.readbackFinite atoms readBindings = some cursor ↔
      saved.readback atoms readBindings = some cursor ∧
        FiniteStructuralAdmission cursor.control := by
  simp only [Saved.readbackFinite, FiniteStructuralAdmission]
  cases read : saved.readback atoms readBindings with
  | none => simp
  | some actual =>
      change (if actual.control.finiteStructural then some actual else none) = some cursor ↔
        some actual = some cursor ∧ cursor.control.finiteStructural = true
      split <;> simp_all
      all_goals
        intro same
        cases same
        assumption

/-- Adding a goal changes only the continuation. The reached binding record,
world, original destination and older scope are read from the same checkpoint. -/
theorem saved_push_readback {Context : Type} (atoms : Ptr → Option Atom)
    (readBindings : List CVal → Option Equations) (saved : Saved Context)
    (row : Row) (occurrence : Occurrence) (goal : Goal)
    (bindings : Equations) (goals : List Goal) (destination : Atom)
    (bound : readBindings saved.bindings = some bindings)
    (before : rowsToGoals atoms saved.active = some goals)
    (output : atoms saved.output = some destination)
    (decoded : row.observe atoms = some occurrence) (understood : occurrence.request.goal = some goal) :
    ({ saved with active := saved.active ++ [row] }).readback atoms readBindings =
      some ⟨saved.world, ⟨bindings, goal :: goals, destination, saved.reserved⟩,
        saved.enclosing⟩ := by
  simp [Saved.readback, bound, rowsToGoals_push atoms saved.active row occurrence goal decoded understood,
    before, output]

def requestGoals (requests : List Request) : Option (List Goal) := requests.mapM Request.goal

/-- Exact push-order interpretation of the actual native let alternatives.
These use the source profile's reached bindings through `Control`; they do not
identify the default relational branch with eager value binding. -/
theorem relational_left_goals (pattern producer body output joined : Atom) :
    requestGoals ((letPushes .relationalLeft pattern producer body output joined).reverse) =
      some [.evaluate pattern joined, .evaluate producer joined, .evaluate body output] := by rfl

theorem relational_right_goals (pattern producer body output joined : Atom) :
    requestGoals ((letPushes .relationalRight pattern producer body output joined).reverse) =
      some [.evaluate producer joined, .evaluate pattern joined, .evaluate body output] := by rfl

theorem eager_value_goals (pattern producer body output joined : Atom) :
    requestGoals ((letPushes .eagerValue pattern producer body output joined).reverse) =
      some [.evaluate producer joined, .equate pattern joined, .evaluate body output] := by rfl

/-- The complete relational let continuation, including arbitrary older
requests, is the source continuation selected by the corresponding native
branch. Native plan/rigidity admission is the condition selecting that branch. -/
theorem let_goals_square (program : SpaceSemantics.Program) (policy : Policy)
    (pattern producer body output joined : Atom) :
    requestGoals ((letPushes
      (match policy with
       | .eagerValue => .eagerValue
       | .relational => if rigid program producer && !rigid program pattern
           then .relationalRight else .relationalLeft)
      pattern producer body output joined).reverse) =
      some (letGoals policy program pattern producer body output joined) := by
  cases policy with
  | eagerValue => rfl
  | relational =>
      simp only [letGoals]
      split <;> rfl

/-- This composed local square includes the reached bindings, world, outer
output and arbitrary older requests. The parsed C branches above determine
`letPushes`; the source branch computes its own destination continuation. -/
theorem let_cursor_square {Context : Type} (program : SpaceSemantics.Program)
    (policy : Policy) (cursor : Cursor Context) (pattern producer body output : Atom)
    (older : List Goal)
    (atLet : cursor.control.goals =
      .evaluate (.expression [.symbol "let", pattern, producer, body]) output :: older)
    (work : List Goal)
    (nativeGoals : requestGoals ((letPushes
      (match policy with
       | .eagerValue => .eagerValue
       | .relational => if rigid program producer && !rigid program pattern
           then .relationalRight else .relationalLeft)
      pattern producer body output (.var (freshName cursor.control 0))).reverse) = some work) :
    (CettaEagerDFS.Destination.machine policy program).step cursor = some (.silent
      { cursor with control := { cursor.control with goals := work ++ older } }) := by
  have exactWork := (let_goals_square program policy pattern producer body output
    (.var (freshName cursor.control 0))).symm.trans nativeGoals
  have same := Option.some.inj exactWork
  subst work
  simp [CettaEagerDFS.Destination.machine, atLet, prepare, replace]

/-- Exact instruction request map for an ordinary prepared native call. The
ready argument cells and the original destination remain shared with all of
its pending producer goals. -/
theorem callReady_source (head : String) (arguments : List Atom) (destination : Atom) :
    (Request.callReady (.expression (.symbol head :: arguments)) destination).goal =
      some (.invoke head arguments destination) := rfl

/-- Every decoded goal occurrence remains at its original position. Equal
values and equal request syntax are not evidence for identifying occurrences. -/
theorem decoded_occurrence_count (occurrences : List Occurrence) (goals : List Goal)
    (decoded : sourceGoals occurrences = some goals) : goals.length = occurrences.length := by
  induction occurrences generalizing goals with
  | nil => simp [sourceGoals] at decoded; subst goals; rfl
  | cons occurrence rest ih =>
      simp only [sourceGoals, List.mapM_cons] at decoded
      cases first : occurrence.request.goal with
      | none => simp [first] at decoded
      | some goal =>
          cases later : sourceGoals rest with
          | none =>
              simp only [sourceGoals] at later
              simp [first, later] at decoded
          | some tail =>
              simp only [sourceGoals] at later
              simp [first, later] at decoded
              subst goals
              simpa using ih tail later

namespace Controls

open CettaEagerDFS.Destination.Controls (program world)

def callAtoms : Ptr → Option Atom
  | ⟨1, 0⟩ => some (.expression [.symbol "f", .var "slot", .var "slot"])
  | ⟨2, 0⟩ => some (.var "result")
  | _ => none

theorem call_retains_argument_sharing_and_destination :
    rowsToGoals callAtoms [row 27 4] = some
      [.invoke "f" [.var "slot", .var "slot"] (.var "result")] := by decide +kernel

theorem height_guard_preserves_delimiter :
    Request.goal (.argumentReturn (.symbol "A") (.var "out") 5) =
      some (.argumentReturn (.symbol "A") (.var "out") 5) := by rfl

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativeGoals

/-! ## Finite current-store presentation and retained destination returns

The source destination machine remains independently stated. A whole
scope-checked contextual store snapshot constructs one finite substitution
for the return, output destination and older operand positions. Globals are
declared explicitly; unlisted private names do not gain shared identity.
The local accepted/refused square and saved-cursor laws do not assert a
bisimulation of arbitrary future primitives or whole default-PeTTa coverage.
-/


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS.Destination
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- A successful source return consumes exactly its current equate goal.
All later work executes from the reached cursor, with its world and context. -/
theorem accepted_run {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (after : Equations) (accepted : Refinement cursor.control.bindings value destination (some after))
    (later : Nat) :
    (CettaEagerDFS.Destination.machine policy program).run (later + 1) cursor =
      (CettaEagerDFS.Destination.machine policy program).run later
        { cursor with control := { cursor.control with bindings := after, goals := older } } :=
  (CettaEagerDFS.Destination.machine policy program).run_succ_silent
    ((return_square policy program cursor value destination older atReturn after).mp accepted)

/-- The selected presentation is consumed by the existing source machine.
This is an earned return square, not another transition implementation. -/
theorem certified_accepted_run {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement (bindingAtomEquations bindings) value destination
      (some (bindingAtomEquations bindings ++ [(value, destination)]))) (later : Nat) :
    (CettaEagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      (CettaEagerDFS.Destination.machine policy program).run later
        { cursor.readout table with control := { (cursor.readout table).control with
          bindings := bindingAtomEquations bindings ++ [(table.apply value, table.apply destination)],
          goals := older.map (Goal.readout table) } } := by
  apply (CettaEagerDFS.Destination.machine policy program).run_succ_silent
  apply (certified_return_step policy program cursor certified record value destination older atReturn).mp
  apply (return_square policy program cursor value destination older atReturn _).mp
  simpa only [record] using accepted

/-- A scheduler cut immediately after return keeps the complete resulting
cursor; no later goal is rerun, dropped or published as already completed. -/
theorem certified_return_pause {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement (bindingAtomEquations bindings) value destination
      (some (bindingAtomEquations bindings ++ [(value, destination)]))) :
    (CettaEagerDFS.Destination.machine policy program).run 1 (cursor.readout table) =
      ([], .exhausted
        { cursor.readout table with control := { (cursor.readout table).control with
          bindings := bindingAtomEquations bindings ++ [(table.apply value, table.apply destination)],
          goals := older.map (Goal.readout table) } }) :=
  certified_accepted_run policy program cursor certified record value destination older atReturn accepted 0

/-- Actual earlier work is retained. The certified return and remaining
budget compose after the saved cursor, without restarting its prefix. -/
theorem certified_return_after_prefix {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement (bindingAtomEquations bindings) value destination
      (some (bindingAtomEquations bindings ++ [(value, destination)])))
    (first later : Nat) (events : List Empty)
    (paused : (CettaEagerDFS.Destination.machine policy program).run first source =
      (events, .exhausted (cursor.readout table))) :
    (CettaEagerDFS.Destination.machine policy program).run (first + (later + 1)) source =
      (events ++ ((CettaEagerDFS.Destination.machine policy program).run later
        { cursor.readout table with control := { (cursor.readout table).control with
          bindings := bindingAtomEquations bindings ++ [(table.apply value, table.apply destination)],
          goals := older.map (Goal.readout table) } }).1,
        ((CettaEagerDFS.Destination.machine policy program).run later
        { cursor.readout table with control := { (cursor.readout table).control with
          bindings := bindingAtomEquations bindings ++ [(table.apply value, table.apply destination)],
          goals := older.map (Goal.readout table) } }).2) := by
  rw [CettaEagerDFS.Destination.resume policy program first (later + 1)
    source (cursor.readout table) events paused]
  rw [certified_accepted_run policy program cursor certified record value destination older atReturn accepted]

/-- Refusal completes the current branch with its reached world and cursor.
It is deliberately distinct from budget exhaustion and operation handoff. -/
theorem certified_refused_run {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (refused : Refinement (bindingAtomEquations bindings) value destination none) (later : Nat) :
    (CettaEagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      ([], .finished (.noValue cursor.control.bindings, cursor.readout table)) := by
  apply (CettaEagerDFS.Destination.machine policy program).run_succ_finish
  apply (certified_refused_step policy program cursor certified record value destination older atReturn).mp
  apply (refused_return_square policy program cursor value destination older atReturn).mp
  simpa only [record] using refused

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS.Destination
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

/-- The complete contextual request is read with one computed table. The
output destination, older goals and further caller operands keep their order
and repeated occurrences. The retained slot snapshot is obtained by actual
scope-checked preparation with explicitly declared global names, not by a
callback supplying an expected equation record. -/
theorem current_store_live_readout
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    (value destination output : Atom) (older : List Goal) (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands =
      some (snapshot, value :: destination :: output :: older.flatMap Goal.atoms ++ contextual)) :
    CurrentStore.readout? image operands =
      some (let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
        table.apply value :: table.apply destination :: table.apply output ::
          (older.map (Goal.readout table)).flatMap Goal.atoms ++ contextual.map table.apply) := by
  rw [CurrentStore.readout?_prepared (CurrentStore.prepareScoped?_success prepared)]
  simp only [goals_readout_atoms, List.map_cons, List.map_append]

/-- Actual scope-checked whole-store preparation and strict finite dependency rank earn the
return simulation and its reflection. The independent destination machine
retains its original world, caller context and raw equation record. -/
theorem current_store_return_square {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .equate value destination :: older) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (CettaEagerDFS.Destination.machine policy program).step cursor = some (.silent
      { cursor with control := { cursor.control with
        bindings := cursor.control.bindings ++ [(value, destination)], goals := older } }) ↔
    (CettaEagerDFS.Destination.machine policy program).step (cursor.readout table) = some (.silent
      { cursor.readout table with control := { (cursor.readout table).control with
        bindings := cursor.control.bindings ++ [(table.apply value, table.apply destination)],
        goals := older.map (Goal.readout table) } }) := by
  simpa only [record] using certified_return_step policy program cursor
    (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked) record value destination older atReturn

/-- Failure is transported through the same computed readout. It finishes the
current branch with the reached world; it neither exhausts a budget nor asks
for an unsupported service. -/
theorem current_store_refused_square {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .equate value destination :: older) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (CettaEagerDFS.Destination.machine policy program).step cursor =
        some (.finish (.noValue cursor.control.bindings, cursor)) ↔
    (CettaEagerDFS.Destination.machine policy program).step (cursor.readout table) =
        some (.finish (.noValue cursor.control.bindings, cursor.readout table)) :=
  certified_refused_step policy program cursor
    (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked) record value destination older atReturn

/-- Actual source resolution constructs the corresponding presented solution.
One residual permutation compares the entire live continuation tuple. The
ranked profile is finite first-order substitution, not cyclic PeTTa values. -/
theorem current_store_return_resolves
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination output : Atom)
    (older : List Goal) (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: output :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    {environment : Environment}
    (resolved : resolve (bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩ ++
      [(value, destination)]) = some environment) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    ∃ presented, resolve (bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩ ++
        [(table.apply value, table.apply destination)]) = some presented ∧
      ∃ permutation : Equiv.Perm String,
        (table.apply output :: (older.map (Goal.readout table)).flatMap Goal.atoms ++
          contextual.map table.apply).map (read presented) =
        ((output :: older.flatMap Goal.atoms ++ contextual).map (read environment)).map
          (renameTypeVars permutation) := by
  simpa only [List.map_cons, List.map_append, goals_readout_atoms] using
    certified_return_resolve (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked)
      value destination resolved (output :: older.flatMap Goal.atoms ++ contextual)

/-- A successful prepared return has an exact one-step saved cursor. The
snapshot certificate is constructed here from the current logical store. -/
theorem current_store_return_pause {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement cursor.control.bindings value destination
      (some (cursor.control.bindings ++ [(value, destination)]))) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (CettaEagerDFS.Destination.machine policy program).run 1 (cursor.readout table) =
      ([], .exhausted { cursor.readout table with
        control := { (cursor.readout table).control with
          bindings := cursor.control.bindings ++ [(table.apply value, table.apply destination)],
          goals := older.map (Goal.readout table) } }) := by
  simpa only [record] using certified_return_pause policy program cursor
    (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked) record value destination older atReturn
    (by simpa only [record] using accepted)

/-- Earlier work is consumed once. A pause at the actual prepared return
resumes from its full reached cursor, including its already performed effects. -/
theorem current_store_return_after_prefix {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (source cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement cursor.control.bindings value destination
      (some (cursor.control.bindings ++ [(value, destination)])))
    (first later : Nat) (events : List Empty)
    (paused : (CettaEagerDFS.Destination.machine policy program).run first source =
      (events, .exhausted (cursor.readout
        (CurrentStore.normalize (CurrentStore.assignments snapshot))))) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    let reached := { cursor.readout table with control := { (cursor.readout table).control with
      bindings := cursor.control.bindings ++ [(table.apply value, table.apply destination)],
      goals := older.map (Goal.readout table) } }
    (CettaEagerDFS.Destination.machine policy program).run (first + (later + 1)) source =
      (events ++ ((CettaEagerDFS.Destination.machine policy program).run later reached).1,
        ((CettaEagerDFS.Destination.machine policy program).run later reached).2) := by
  simpa only [record] using certified_return_after_prefix policy program source cursor
    (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked) record value destination older atReturn
    (by simpa only [record] using accepted) first later events paused

/-- Inconsistent equations reject the prepared return at any positive budget,
while retaining the reached state. No current-store failure is reinterpreted
as a successful empty result. -/
theorem current_store_refused_run {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (refused : Refinement cursor.control.bindings value destination none) (later : Nat) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (CettaEagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      ([], .finished (.noValue cursor.control.bindings, cursor.readout table)) :=
  certified_refused_run policy program cursor (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked)
    record value destination older atReturn (by simpa only [record] using refused) later

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaEagerDFS.Destination.PresentationControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Logic.LP

private def bindings : Bindings := ⟨[], [("x", "y")]⟩
private def table : TypeSubst := [("x", .var "y")]

private theorem certified : ReadoutCertificate bindings table := by
  apply ReadoutCertificate.of_fold
  change EquationListPresentationRel [(.var "x", .var "y")] [] [("x", .var "y")]
  refine .cons (.ordinary (TypeSubst.apply_empty _) (TypeSubst.apply_empty _) ?_) (.nil _)
  simpa [TypeSubst.bind, TypeSubst.erase] using
    (AppliedReducedTypeMatchRel.bindLeft (substitution := []) (name := "x")
      (right := .var "y") (by decide))

def pair (first second : Atom) : Atom := .expression [.symbol "Pair", first, second]
def program : SpaceSemantics.Program := { equations := [], declarations := [] }
def world : World := ⟨Effects.empty, [], [.symbol "earlier"]⟩
def older : List Goal := [.invoke "println!" [pair (.var "x") (.var "x")] (.var "unit")]
def cursor : Cursor String :=
  ⟨world,
    { bindings := bindingAtomEquations bindings
      goals := .equate (.symbol "A") (.var "x") :: older
      destination := pair (.var "x") (.var "x")
      reserved := {"sibling"} },
    "outer-caller"⟩
def afterReturn : Cursor String :=
  { cursor.readout table with control := { (cursor.readout table).control with
    bindings := bindingAtomEquations bindings ++ [(.symbol "A", .var "y")],
    goals := older.map (Goal.readout table) } }

private theorem accepted : Refinement (bindingAtomEquations bindings) (.symbol "A") (.var "x")
    (some (bindingAtomEquations bindings ++ [(.symbol "A", .var "x")])) := by
  let environment : Environment := fun name =>
    if name = "x" ∨ name = "y" then encode (.symbol "A") else .var name
  refine .accepted environment ?_ ?_
  · simp [Solves, bindings, bindingAtomEquations, read, environment, decode, encode, Subst.applyTerm]
  · simp [read, environment, decode, encode, Subst.applyTerm]

theorem repeated_variable_readout :
    (cursor.readout table).control.destination = pair (.var "y") (.var "y") := by
  simp [cursor, Cursor.readout, table, pair, TypeSubst.apply, TypeSubst.lookup]

theorem independent_variables_are_not_shared_readout :
    (cursor.readout table).control.destination ≠ pair (.var "y") (.var "z") := by
  rw [repeated_variable_readout]
  decide

theorem return_pause_keeps_full_cursor :
    (machine .relational program).run 1 (cursor.readout table) = ([], .exhausted afterReturn) := by
  simpa [afterReturn, table, TypeSubst.apply, TypeSubst.lookup] using
    certified_return_pause .relational program cursor certified rfl
      (.symbol "A") (.var "x") older rfl accepted

theorem return_keeps_world_and_outer_work :
    afterReturn.world = world ∧ afterReturn.context = "outer-caller" ∧
      afterReturn.control.reserved = {"sibling"} ∧
      afterReturn.control.goals = [.invoke "println!" [pair (.var "y") (.var "y")] (.var "unit")] := by
  simp [afterReturn, cursor, Cursor.readout, older, Goal.readout, table,
    TypeSubst.apply, TypeSubst.lookup, pair]

def printed (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (Cursor String) (Result × Cursor String) Boundary) : Option (List Atom) :=
  (observed result).map (fun state => state.1.output)

def value (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (Cursor String) (Result × Cursor String) Boundary) : Option Atom :=
  match result with
  | .finished (.value atom _, _) => some atom
  | _ => none

def resumeAfterEffect : Option (List Atom) := do
  match ((machine .relational program).run 2 (cursor.readout table)).2 with
  | .exhausted saved => printed ((machine .relational program).run 2 saved).2
  | _ => none

def restartAfterEffect : Option (List Atom) := do
  match ((machine .relational program).run 2 (cursor.readout table)).2 with
  | .exhausted saved =>
      let restarted := { cursor.readout table with world := saved.world }
      printed ((machine .relational program).run 4 restarted).2
  | _ => none

/- Executable controls use the actual total unifier and retained machine. -/
#guard value ((machine .relational program).run 4 (cursor.readout table)).2 ==
  some (pair (.symbol "A") (.symbol "A"))
#guard resumeAfterEffect == some [.symbol "earlier", pair (.symbol "A") (.symbol "A")]
#guard restartAfterEffect == some [.symbol "earlier", pair (.symbol "A") (.symbol "A"),
  pair (.symbol "A") (.symbol "A")]

private theorem incompatible : Refinement (bindingAtomEquations bindings)
    (.symbol "A") (.symbol "B") none := by
  apply Refinement.refused
  rintro ⟨environment, _, impossible⟩
  simp only [read_eq_applyTypeValuation, applyTypeValuation] at impossible
  exact (by decide : Atom.symbol "A" ≠ .symbol "B") impossible

def refusedCursor : Cursor String :=
  { cursor with control := { cursor.control with
      goals := .equate (.symbol "A") (.symbol "B") :: older } }

theorem inconsistent_equation_refuses_and_keeps_world :
    (machine .relational program).run 8 (refusedCursor.readout table) =
      ([], .finished (.noValue (bindingAtomEquations bindings), refusedCursor.readout table)) := by
  exact certified_refused_run .relational program refusedCursor certified rfl
    (.symbol "A") (.symbol "B") older rfl incompatible 7

theorem refused_return_is_not_budget_exhaustion :
    ((machine .relational program).run 8 (refusedCursor.readout table)).2 ≠
      .exhausted (refusedCursor.readout table) := by
  rw [inconsistent_equation_refuses_and_keeps_world]
  intro impossible
  cases impossible

theorem refusal_does_not_execute_the_pending_print :
    printed ((machine .relational program).run 8 (refusedCursor.readout table)).2 =
      some [.symbol "earlier"] := by
  rw [inconsistent_equation_refuses_and_keeps_world]
  rfl

/-- Structural readout of written syntax does not invoke it. -/
theorem readout_does_not_force_written_call :
    table.apply (.expression [.symbol "println!", .var "x"]) =
      .expression [.symbol "println!", .var "y"] := by
  simp [table, TypeSubst.apply, TypeSubst.lookup]

end Mettapedia.Languages.MeTTa.PeTTa.CettaEagerDFS.Destination.PresentationControls


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn.CurrentStoreControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS.Destination
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared
open Mettapedia.Logic.LP

private def caller : Token := ⟨0, 3⟩
private def child : Token := ⟨1, 8⟩
private def callerName : String := CurrentStore.referenceName (caller.ref 0)
private def childName : String := CurrentStore.referenceName (child.ref 0)
private def unitName : String := CurrentStore.referenceName (child.ref 1)
private def pair (first second : Atom) : Atom := .expression [.symbol "pair", first, second]
private def image : ImageOf CurrentStore.ContextualOperand :=
  ⟨#[some (EntryOf.initial 3 ["x"] (fun _ => some (child, .var "x"))),
     some (EntryOf.initial 8 ["x", "unit"] (fun _ => none))], 11⟩
attribute [local simp] CurrentStore.prepareScoped? CurrentStore.operandScope
  TypeSubst.typeVars TypeSubst.typeVarsList CurrentStore.readout? CurrentStore.prepare? CurrentStore.contextualRows?
  CurrentStore.qualifyRowsFrom? CurrentStore.qualifyRow? CurrentStore.qualify?
  MetavariableFrameStore.Snapshot.rows MetavariableFrameStore.Snapshot.entryRows MetavariableFrameStore.Snapshot.Row.ofEntry EntryOf.initial entryEnv
  MetavariableFrameStore.Snapshot.image_frameAt List.range_succ List.ofFn_succ CurrentStore.assignments
  CurrentStore.normalize CurrentStore.normalizeFrom TypeSubst.bind TypeSubst.apply
  TypeSubst.applyAssignment TypeSubst.lookup TypeSubst.erase renameTypeVars CurrentStore.nameIn
  MetavariableFrame.indexOf CurrentStore.referenceName CurrentStore.freeName Token.ref
  caller child callerName childName unitName image pair

private def snapshot : List CurrentStore.Row := (CurrentStore.contextualRows? image).get (by decide)
attribute [local simp] snapshot

private def table : TypeSubst := CurrentStore.normalize (CurrentStore.assignments snapshot)
private def older : List Goal :=
  [.invoke "println!" [pair (.var callerName) (.var callerName)] (.var unitName)]
private def operands : List CurrentStore.ContextualOperand :=
  [(caller, .symbol "A"), (caller, .var "x"),
    (caller, pair (.var "x") (.var "x")), (child, .var "unit"),
    (caller, pair (.var "x") (.var "x"))]
private def world : CettaEagerDFS.World := ⟨Effects.empty, [], [.symbol "earlier"]⟩
private def program : SpaceSemantics.Program := { equations := [], declarations := [] }
private def cursor : Cursor String :=
  ⟨world,
    { bindings := bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩
      goals := .equate (.symbol "A") (.var callerName) :: older
      destination := pair (.var callerName) (.var callerName)
      reserved := {"sibling"} },
    "outer-caller"⟩

private theorem actual_assignments :
    CurrentStore.assignments snapshot = [(callerName, .var childName)] := by simp

private def rank (name : String) : Nat := if name = callerName then 1 else 0

private theorem ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot) := by
  rw [actual_assignments]
  intro name value member
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩
  intro varName occurs
  simp only [TypeSubst.typeVars, List.mem_singleton] at occurs
  subst varName
  simp [rank]

private theorem actual_table : table = [(callerName, .var childName)] := by simp [table]

private theorem prepared : CurrentStore.prepareScoped? [] image operands = some
    (snapshot, .symbol "A" :: .var callerName :: cursor.control.destination ::
      older.flatMap Goal.atoms ++ []) := by simp [operands, cursor, older, Goal.atoms]

private theorem accepted : Refinement cursor.control.bindings (.symbol "A") (.var callerName)
    (some (cursor.control.bindings ++ [(.symbol "A", .var callerName)])) := by
  let environment : Environment := fun _ => encode (.symbol "A")
  refine .accepted environment ?_ ?_
  · simp [cursor, bindingAtomEquations, Solves, CettaEagerDFS.Destination.read,
      environment, encode, decode, Subst.applyTerm]
  · simp [CettaEagerDFS.Destination.read, environment, encode, decode, Subst.applyTerm]

/-- Two authored x names in distinct live frames retain distinct references;
the alias is an explicit current assignment rather than a spelling collision. -/
theorem authored_names_keep_context :
    CurrentStore.qualify? image (caller, .var "x") = some (.var callerName) ∧
      CurrentStore.qualify? image (child, .var "x") = some (.var childName) ∧
      callerName ≠ childName := by simp

theorem actual_joint_preparation :
    CurrentStore.readout? image operands = some
      [.symbol "A", .var childName, pair (.var childName) (.var childName),
        .var unitName, pair (.var childName) (.var childName)] := by
  have result := current_store_live_readout (.symbol "A") (.var callerName)
    cursor.control.destination older [] [] prepared
  simpa [cursor, older, Goal.readout, Goal.atoms] using result

/-- The open target is a live slot, while an old incarnation is not a free variable. -/
theorem open_and_stale_are_not_interchanged :
    (MetavariableFrameStore.Snapshot.readRow? image (child.ref 0)).map (fun row => row.observed.value) = some none ∧
      CurrentStore.prepare? image [(⟨1, 9⟩, .var "x")] = none := by decide

/-- Equal undeclared spellings in different frames do not create a global variable. -/
theorem undeclared_private_name_refused :
    CurrentStore.prepareScoped? [] image
      [(caller, .var "private"), (child, .var "private")] = none := by
  simp

/-- Shared external identity is available only when the source context declares it. -/
theorem declared_global_name_shared :
    (CurrentStore.prepareScoped? ["ambient"] image
      [(caller, .var "ambient"), (child, .var "ambient")]).isSome = true ∧
    CurrentStore.readout? image [(caller, .var "ambient"), (child, .var "ambient")] =
      some [.var (CurrentStore.freeName "ambient"), .var (CurrentStore.freeName "ambient")] := by
  simp
  decide +kernel

theorem current_store_pause_preserves_parent :
    (CettaEagerDFS.Destination.machine .relational program).run 1 (cursor.readout table) =
      ([], .exhausted { cursor.readout table with control := { (cursor.readout table).control with
        bindings := cursor.control.bindings ++ [(table.apply (.symbol "A"), table.apply (.var callerName))],
        goals := older.map (Goal.readout table) } }) :=
  current_store_return_pause .relational program cursor (.symbol "A") (.var callerName)
    older [] [] prepared ranked rfl rfl accepted

private def printed (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
    (Cursor String) (Result × Cursor String) Boundary) : Option (List Atom) :=
  (observed result).map (fun state => state.1.output)

private def answer (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
    (Cursor String) (Result × Cursor String) Boundary) : Option Atom :=
  match result with
  | .finished (.value atom _, _) => some atom
  | _ => none

private def resumeAfterPrint : Option (List Atom) := do
  match ((CettaEagerDFS.Destination.machine .relational program).run 2 (cursor.readout table)).2 with
  | .exhausted saved => printed ((CettaEagerDFS.Destination.machine .relational program).run 2 saved).2
  | _ => none

private def restartAfterPrint : Option (List Atom) := do
  match ((CettaEagerDFS.Destination.machine .relational program).run 2 (cursor.readout table)).2 with
  | .exhausted saved =>
      let restarted := { cursor.readout table with world := saved.world }
      printed ((CettaEagerDFS.Destination.machine .relational program).run 4 restarted).2
  | _ => none

#guard answer ((CettaEagerDFS.Destination.machine .relational program).run 4
  (cursor.readout table)).2 == some (pair (.symbol "A") (.symbol "A"))
#guard resumeAfterPrint == some [.symbol "earlier", pair (.symbol "A") (.symbol "A")]
#guard restartAfterPrint == some [.symbol "earlier", pair (.symbol "A") (.symbol "A"),
  pair (.symbol "A") (.symbol "A")]

private def badCursor : Cursor String :=
  { cursor with control := { cursor.control with
      goals := .equate (.symbol "A") (.symbol "B") :: older } }
private def badOperands : List CurrentStore.ContextualOperand :=
  [(caller, .symbol "A"), (caller, .symbol "B"),
    (caller, pair (.var "x") (.var "x")), (child, .var "unit"),
    (caller, pair (.var "x") (.var "x"))]
private theorem badPrepared : CurrentStore.prepareScoped? [] image badOperands = some
    (snapshot, .symbol "A" :: .symbol "B" :: badCursor.control.destination ::
      older.flatMap Goal.atoms ++ []) := by simp [badOperands, badCursor, cursor, older, Goal.atoms]
private theorem incompatible : Refinement badCursor.control.bindings (.symbol "A") (.symbol "B") none := by
  apply Refinement.refused
  rintro ⟨environment, _, impossible⟩
  simp only [read_eq_applyTypeValuation, applyTypeValuation] at impossible
  exact (by decide : Atom.symbol "A" ≠ .symbol "B") impossible

theorem actual_inconsistent_return_refused :
    (CettaEagerDFS.Destination.machine .relational program).run 8 (badCursor.readout table) =
      ([], .finished (.noValue badCursor.control.bindings, badCursor.readout table)) :=
  current_store_refused_run .relational program badCursor (.symbol "A") (.symbol "B")
    older [] [] badPrepared ranked rfl rfl incompatible 7

theorem refused_preserves_world_and_pending_occurrence :
    printed ((CettaEagerDFS.Destination.machine .relational program).run 8
      (badCursor.readout table)).2 = some [.symbol "earlier"] ∧
      (badCursor.readout table).context = "outer-caller" ∧
      (badCursor.readout table).control.goals.length = 2 := by
  rw [actual_inconsistent_return_refused]
  simp [printed, observed, badCursor, cursor, Cursor.readout, older, world]

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn.CurrentStoreControls

/-! ## Retained invocation and argument-return boundaries -/


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativeGoals
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS.Destination

/-- The admitted argument plan schedules a producer followed by its optional
error delimiter. The Boolean flags are the existing argument-plan boundary;
this list does not claim to classify every typed or specialized operation. -/
def argumentWork (eagerFaults : Bool) (output : Atom) (callerDepth : Nat)
    (arguments : List Argument) : List Goal :=
  arguments.flatMap fun argument =>
    (if argument.evaluate then [.evaluate argument.expression argument.destination] else []) ++
    (if eagerFaults && (argument.evaluate || argument.knownError) then
      [.argumentReturn argument.destination output callerDepth] else [])

theorem argumentExecution_source (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (arguments : List Argument) :
    requestGoals (argumentExecution eagerFaults output height arguments) =
      some (argumentWork eagerFaults output height.toNat arguments) := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
      simp only [argumentExecution, argumentWork, List.flatMap_cons] at ih ⊢
      cases eagerFaults <;> cases argument.evaluate <;> cases argument.knownError <;>
        simp_all [requestGoals, Request.goal]

/-- This composes the actual descending push order with the source goal map.
Repeated identical argument requests remain repeated positions. -/
theorem argumentPushes_source (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (arguments : List Argument) :
    requestGoals ((argumentPushes eagerFaults output height arguments).reverse) =
      some (argumentWork eagerFaults output height.toNat arguments) := by
  rw [argument_order]
  exact argumentExecution_source eagerFaults output height arguments

/-- All argument guards share the caller delimiter. The final invocation is
younger than that delimiter, so a reached error also bypasses the invocation. -/
theorem argumentWork_wellDelimited (eagerFaults : Bool) (output : Atom) (depth : Nat)
    (arguments : List Argument) (following : List Goal)
    (bound : depth ≤ following.length) (valid : WellDelimited following) :
    WellDelimited (argumentWork eagerFaults output depth arguments ++ following) := by
  induction arguments with
  | nil => exact valid
  | cons argument rest ih =>
      have larger : depth ≤ (argumentWork eagerFaults output depth rest ++ following).length := by
        simp only [List.length_append]
        omega
      simp only [argumentWork, List.flatMap_cons, List.append_assoc]
      cases eagerFaults <;> cases argument.evaluate <;> cases argument.knownError <;>
        simp_all only [Bool.false_and, Bool.true_and,
          Bool.or_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte,
          List.nil_append, List.cons_append, WellDelimited]
      all_goals first | exact ih | exact ⟨larger, ih⟩

/-- A saved native height is one representation of the source delimiter.
The exact source schedule proves the represented state well formed. -/
theorem prepared_call_wellDelimited (eagerFaults : Bool) (head : String)
    (arguments : List Argument) (ready : List Atom) (output : Atom) (height : UInt64)
    (older : List Goal) (delimiter : height.toNat = older.length)
    (valid : WellDelimited older) :
    WellDelimited (argumentWork eagerFaults output height.toNat arguments ++
      (.invoke head ready output :: older)) := by
  apply argumentWork_wellDelimited
  · simp only [delimiter, List.length_cons]; omega
  · exact valid

/-- For an ordinary prepared call the actual goal map preserves every
argument occurrence and the final invocation before the older caller suffix. -/
theorem prepared_call_goals (eagerFaults : Bool) (head : String)
    (arguments : List Argument) (ready : List Atom) (output : Atom) (height : UInt64) :
    requestGoals ((argumentPushes eagerFaults output height arguments).reverse ++
      [.callReady (.expression (.symbol head :: ready)) output]) =
      some (argumentWork eagerFaults output height.toNat arguments ++ [.invoke head ready output]) := by
  have mapped := argumentPushes_source eagerFaults output height arguments
  unfold requestGoals at mapped ⊢
  rw [List.mapM_append, mapped]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.NativeGoals


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS.Destination
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The actual current-store snapshot supplies one table for the produced
value, outer destination, complete younger/older continuation and context. -/
theorem current_store_argument_return_square {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (younger older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: (younger ++ older).flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length :: (younger ++ older))
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (CettaEagerDFS.Destination.machine policy program).step cursor = some (.silent
      { cursor with control := { cursor.control with
        bindings := cursor.control.bindings ++ [(read environment value, destination)], goals := older } }) ↔
    (CettaEagerDFS.Destination.machine policy program).step (cursor.readout table) = some (.silent
      { cursor.readout table with control := { (cursor.readout table).control with
        bindings := cursor.control.bindings ++ [(read environment value, table.apply destination)],
        goals := older.map (Goal.readout table) } }) :=
  certified_argumentReturn_propagated policy program cursor
    (CurrentStore.prepareScoped?_certified prepared ranked) record value destination younger older
    atReturn resolved error

/-- Post-binding refusal is transported by the same table as success. The
reached world remains available at the terminal branch result. -/
theorem current_store_argument_refused_square {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (younger older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: (younger ++ older).flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length :: (younger ++ older))
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (CettaEagerDFS.Destination.machine policy program).step cursor = some (.finish (.noValue cursor.control.bindings, cursor)) ↔
    (CettaEagerDFS.Destination.machine policy program).step (cursor.readout table) =
      some (.finish (.noValue cursor.control.bindings, cursor.readout table)) :=
  certified_argumentReturn_refused policy program cursor
    (CurrentStore.prepareScoped?_certified prepared ranked) record value destination younger older
    atReturn resolved error

/-- A normal return resumes the exact pending caller work for every later
budget. No child or prior effect is restarted. -/
theorem current_store_argument_normal_run {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (younger older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: (younger ++ older).flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length :: (younger ++ older))
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (normal : (read environment value).isError = false) (later : Nat) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (CettaEagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      (CettaEagerDFS.Destination.machine policy program).run later
        ({ cursor with control := replace cursor.control (younger ++ older) }.readout table) :=
  (CettaEagerDFS.Destination.machine policy program).run_succ_silent
    (certified_argumentReturn_ordinary policy program cursor
      (CurrentStore.prepareScoped?_certified prepared ranked) record value destination younger older
      atReturn resolved normal)

/-- Successful error delivery pauses after the constraint was added and the
younger work was removed. Its parent world/context and older suffix are exact. -/
theorem current_store_argument_error_pause {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (younger older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: (younger ++ older).flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length :: (younger ++ older))
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true)
    (accepted : Refinement cursor.control.bindings (read environment value) destination
      (some (cursor.control.bindings ++ [(read environment value, destination)]))) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (CettaEagerDFS.Destination.machine policy program).run 1 (cursor.readout table) = ([], .exhausted
      { cursor.readout table with control := { (cursor.readout table).control with
        bindings := cursor.control.bindings ++ [(read environment value, table.apply destination)],
        goals := older.map (Goal.readout table) } }) := by
  apply (CettaEagerDFS.Destination.machine policy program).run_succ_silent (fuel := 0)
  apply (current_store_argument_return_square policy program cursor value destination younger older
    globals contextual prepared ranked record atReturn resolved error).mp
  exact (argumentReturn_propagated_square policy program cursor value destination younger older
    atReturn resolved error _).mp accepted

/-- An arbitrary already-executed prefix composes with the retained error
return. This preserves the reached world, even when the prefix performed IO. -/
theorem current_store_argument_after_prefix {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (source cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (younger older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: (younger ++ older).flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length :: (younger ++ older))
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true)
    (accepted : Refinement cursor.control.bindings (read environment value) destination
      (some (cursor.control.bindings ++ [(read environment value, destination)])))
    (first later : Nat) (events : List Empty)
    (paused : (CettaEagerDFS.Destination.machine policy program).run first source =
      (events, .exhausted (cursor.readout (CurrentStore.normalize (CurrentStore.assignments snapshot))))) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    let reached := { cursor.readout table with control := { (cursor.readout table).control with
      bindings := cursor.control.bindings ++ [(read environment value, table.apply destination)],
      goals := older.map (Goal.readout table) } }
    (CettaEagerDFS.Destination.machine policy program).run (first + 1 + later) source =
      (events ++ ((CettaEagerDFS.Destination.machine policy program).run later reached).1,
        ((CettaEagerDFS.Destination.machine policy program).run later reached).2) := by
  dsimp only
  rw [Nat.add_assoc, CettaEagerDFS.Destination.resume policy program first (1 + later)
    source _ events paused]
  rw [(CettaEagerDFS.Destination.machine policy program).run_add 1 later,
    current_store_argument_error_pause policy program cursor value destination younger older
      globals contextual prepared ranked record atReturn resolved error accepted]
  rfl

/-- A real print operation reads its argument through the certified reached
store and appends exactly one output before its pending return check. -/
theorem current_store_print_pause {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (argument destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      argument :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atPrint : cursor.control.goals = .invoke "println!" [argument] destination :: older)
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (CettaEagerDFS.Destination.machine policy program).run 1 (cursor.readout table) = ([], .exhausted
      ({ cursor with
        world := { cursor.world with output := cursor.world.output ++ [read environment argument] }
        control := replace cursor.control (.equate (Effects.boolean true) destination :: older) }.readout table)) :=
  certified_print_resume policy program cursor
    (CurrentStore.prepareScoped?_certified prepared ranked) record argument destination older atPrint resolved 0

/-- Calls not handled by this local component retain their actual resolved
argument occurrences and the whole saved continuation. The theorem does not
count an unserved request as an executed equation or primitive. -/
theorem current_store_invocation_request {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      arguments ++ destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atCall : cursor.control.goals = .invoke head arguments destination :: older)
    (notPrint : head ≠ "println!") {environment : Environment}
    (resolved : resolve cursor.control.bindings = some environment) (later : Nat) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (CettaEagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      ([], .suspended (.invoke head (arguments.map (read environment)) (table.apply destination))
        (cursor.readout table)) :=
  (CettaEagerDFS.Destination.machine policy program).run_succ_call
    (certified_invoke_request_step policy program cursor
      (CurrentStore.prepareScoped?_certified prepared ranked) record head arguments destination older
      atCall notPrint resolved)

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn


namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn.CurrentStoreControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS.Destination
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared
open Mettapedia.Logic.LP

attribute [local simp] CurrentStore.prepareScoped? CurrentStore.operandScope
  TypeSubst.typeVars TypeSubst.typeVarsList CurrentStore.readout? CurrentStore.prepare? CurrentStore.contextualRows?
  CurrentStore.qualifyRowsFrom? CurrentStore.qualifyRow? CurrentStore.qualify?
  MetavariableFrameStore.Snapshot.rows MetavariableFrameStore.Snapshot.entryRows MetavariableFrameStore.Snapshot.Row.ofEntry EntryOf.initial entryEnv
  MetavariableFrameStore.Snapshot.image_frameAt List.range_succ List.ofFn_succ CurrentStore.assignments
  CurrentStore.normalize CurrentStore.normalizeFrom TypeSubst.bind TypeSubst.apply
  TypeSubst.applyAssignment TypeSubst.lookup TypeSubst.erase renameTypeVars CurrentStore.nameIn
  MetavariableFrame.indexOf CurrentStore.referenceName CurrentStore.freeName Token.ref
  caller child callerName childName unitName image pair snapshot

private def argumentError : Atom := .expression [.symbol "Error", pair (.var callerName) (.var callerName)]
private def argumentOlder : List Goal :=
  [.invoke "later" [pair (.var callerName) (.var callerName)] (.symbol "ok")]
private def argumentYounger : List Goal :=
  [.invoke "println!" [.symbol "skipped"] (.var unitName)]
private def argumentCursor : Cursor String :=
  {cursor with control := {cursor.control with goals :=
      (.argumentReturn argumentError (.var unitName) argumentOlder.length ::
        (argumentYounger ++ argumentOlder))}}
private def argumentOperands : List CurrentStore.ContextualOperand :=
  [(caller, .expression [.symbol "Error", pair (.var "x") (.var "x")]),
   (child, .var "unit"), (caller, pair (.var "x") (.var "x")),
   (child, .var "unit"), (caller, .symbol "skipped"),
   (caller, .symbol "ok"), (caller, pair (.var "x") (.var "x"))]

private theorem argumentPrepared : CurrentStore.prepareScoped? [] image argumentOperands = some
    (snapshot, argumentError :: .var unitName :: argumentCursor.control.destination ::
      (argumentYounger ++ argumentOlder).flatMap Goal.atoms ++ []) := by
  simp [argumentOperands, argumentCursor, cursor, argumentError, argumentOlder, argumentYounger, Goal.atoms]

private def argumentEnvironment : Environment :=
  Subst.single callerName (encode (.var childName))
private theorem argumentResolved : resolve argumentCursor.control.bindings = some argumentEnvironment := by
  simp [argumentCursor, cursor, bindingAtomEquations, argumentEnvironment, resolve, equations,
    encode, unifyTotal, Subst.applyEqs, Subst.comp_id_left]
private theorem argumentIsError : (CettaEagerDFS.Destination.read argumentEnvironment argumentError).isError = true := by
  simp [argumentEnvironment, argumentError, CettaEagerDFS.Destination.read, encode, decode,
    Subst.single, Atom.isError]
private theorem argumentAccepted : Refinement argumentCursor.control.bindings
    (CettaEagerDFS.Destination.read argumentEnvironment argumentError) (.var unitName)
    (some (argumentCursor.control.bindings ++
      [(CettaEagerDFS.Destination.read argumentEnvironment argumentError, .var unitName)])) := by
  apply (refinement_iff _ _ _ _).mpr
  simp [argumentCursor, cursor, argumentEnvironment, argumentError, bindingAtomEquations,
    CettaEagerDFS.Destination.read, refine, resolve, equations, encode, decode, unifyTotal,
    Subst.applyEqs, Subst.single, Subst.applyTerm, Term.occursIn, Fin.exists_fin_succ]

/-- The actual two-frame alias snapshot prepares and executes the error guard.
Its full older continuation shares the same qualified open variable twice. -/
theorem scoped_argument_pause_keeps_open_correlation :
    (CettaEagerDFS.Destination.machine .relational program).run 1 (argumentCursor.readout table) =
      ([], .exhausted { argumentCursor.readout table with
        control := { (argumentCursor.readout table).control with
          bindings := argumentCursor.control.bindings ++
            [(CettaEagerDFS.Destination.read argumentEnvironment argumentError, table.apply (.var unitName))],
          goals := argumentOlder.map (Goal.readout table) } }) :=
  current_store_argument_error_pause .relational program argumentCursor argumentError (.var unitName)
    argumentYounger argumentOlder [] [] argumentPrepared ranked rfl rfl argumentResolved argumentIsError argumentAccepted

theorem scoped_argument_readout_keeps_correlation :
    table.apply argumentError = .expression [.symbol "Error", pair (.var childName) (.var childName)] ∧
      argumentOlder.map (Goal.readout table) =
        [.invoke "later" [pair (.var childName) (.var childName)] (.symbol "ok")] := by
  simp [table, argumentError, argumentOlder, Goal.readout]

theorem scoped_guard_keeps_parent_and_effect_prefix :
    (argumentCursor.readout table).context = "outer-caller" ∧
      (argumentCursor.readout table).control.reserved = {"sibling"} ∧
      (argumentCursor.readout table).world.output = [.symbol "earlier"] := by
  exact ⟨rfl, rfl, rfl⟩

private def cyclicArgumentCursor : Cursor String :=
  {argumentCursor with control := {argumentCursor.control with goals :=
      (.argumentReturn argumentError (.var callerName) argumentOlder.length ::
        (argumentYounger ++ argumentOlder))}}
private def cyclicArgumentOperands : List CurrentStore.ContextualOperand :=
  [(caller, .expression [.symbol "Error", pair (.var "x") (.var "x")]),
   (caller, .var "x"), (caller, pair (.var "x") (.var "x")),
   (child, .var "unit"), (caller, .symbol "skipped"),
   (caller, .symbol "ok"), (caller, pair (.var "x") (.var "x"))]
private theorem cyclicArgumentPrepared : CurrentStore.prepareScoped? [] image cyclicArgumentOperands = some
    (snapshot, argumentError :: .var callerName :: cyclicArgumentCursor.control.destination ::
      (argumentYounger ++ argumentOlder).flatMap Goal.atoms ++ []) := by
  simp [cyclicArgumentOperands, cyclicArgumentCursor, argumentCursor, cursor, argumentError,
    argumentOlder, argumentYounger, Goal.atoms]

/-- Binding the returned error to its own open argument is refused after the
reached alias equations. Refusal retains the already performed world. -/
theorem scoped_argument_occurs_refusal :
    (CettaEagerDFS.Destination.machine .relational program).run 1 (cyclicArgumentCursor.readout table) =
      ([], .finished (.noValue cyclicArgumentCursor.control.bindings, cyclicArgumentCursor.readout table)) := by
  apply (CettaEagerDFS.Destination.machine .relational program).run_succ_finish (fuel := 0)
  apply (current_store_argument_refused_square .relational program cyclicArgumentCursor argumentError
    (.var callerName) argumentYounger argumentOlder [] [] cyclicArgumentPrepared ranked rfl rfl
    argumentResolved argumentIsError).mp
  apply (argumentReturn_refused_square .relational program cyclicArgumentCursor argumentError
    (.var callerName) argumentYounger argumentOlder rfl argumentResolved argumentIsError).mp
  apply (refinement_iff _ _ _ _).mpr
  simp [cyclicArgumentCursor, argumentCursor, cursor, argumentEnvironment, argumentError,
    bindingAtomEquations, CettaEagerDFS.Destination.read, refine, resolve, equations,
    encode, decode, unifyTotal, Subst.applyEqs, Subst.single, Subst.applyTerm,
    Term.occursIn, Fin.exists_fin_succ]

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn.CurrentStoreControls


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open CettaEagerDFS.Destination
open CettaEagerDFS.Destination.ClauseChoice

/-- A scope-checked complete current-store tuple reaches the existing
invocation request. Each actually computed source-equation occurrence earns
its fresh body, a solvable reached constraint store, and one later readout
for all pending observations. Body execution remains saved work. -/
theorem current_store_clause_selection {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (head : String) (arguments : List Atom) (destination : Atom)
    (older : List Goal) (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      arguments ++ destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atCall : cursor.control.goals = .invoke head arguments destination :: older)
    (ordinary : Eval.ioHead head = false ∧ StdLib.known head = false)
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (occurrence : Nat) (next : Control)
    (selected : (occurrence, next) ∈ choices program
      (cursor.readout (CurrentStore.normalize (CurrentStore.assignments snapshot))).control head
      (arguments.map (read environment))
      ((CurrentStore.normalize (CurrentStore.assignments snapshot)).apply destination)
      (older.map (Goal.readout (CurrentStore.normalize (CurrentStore.assignments snapshot)))))
    (later : Nat) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (CettaEagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      ([], .suspended (.invoke head (arguments.map (read environment)) (table.apply destination))
        (cursor.readout table)) ∧
    ∃ equation reached,
      program.equations[occurrence]? = some equation ∧
      Selection program (cursor.readout table).control head (arguments.map (read environment))
        (table.apply destination) (older.map (Goal.readout table)) occurrence
        (freshPattern (cursor.readout table).control occurrence equation)
        (freshBody (cursor.readout table).control occurrence equation) next ∧
      resolve next.bindings = some reached ∧
      (∀ pending : List Atom,
        (pending.map table.apply).map (read reached) = pending.map (read reached)) ∧
      ({cursor with control := next} : Cursor Context).world = cursor.world ∧
      ({cursor with control := next} : Cursor Context).context = cursor.context := by
  dsimp only
  have notPrint : head ≠ "println!" := by
    intro same
    subst head
    simpa [Eval.ioHead] using ordinary.1
  refine ⟨current_store_invocation_request policy program cursor head arguments destination older
    globals contextual prepared ranked record atCall notPrint resolved later, ?_⟩
  obtain ⟨equation, row, source⟩ := (choices_source_iff _ _ _ _ _ _ _ _).mp selected
  obtain ⟨reached, solved⟩ := selected_resolves source
  refine ⟨equation, reached, row, source, solved, ?_, rfl, rfl⟩
  exact selected_pending_absorbed
    (control := (cursor.readout (CurrentStore.normalize (CurrentStore.assignments snapshot))).control)
    (CurrentStore.prepareScoped?_certified prepared ranked)
    record source solved

/-- The same occurrence can be refused after earlier constraints are reached.
Presenting all operands through the prepared table cannot turn that refusal
into acceptance. The old world and pending alternatives are not rolled back. -/
theorem current_store_clause_refusal {Context : Type}
    (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (head : String) (arguments : List Atom) (destination : Atom)
    (older : List Goal) (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      arguments ++ destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (sameHead : equation.head = head) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    attempt cursor.control head arguments destination older occurrence equation = none ↔
      refine cursor.control.bindings (table.apply (.expression (.symbol head :: arguments)))
        (table.apply (freshPattern cursor.control occurrence equation)) = none :=
  presented_refusal_iff cursor.control head arguments destination older occurrence equation sameHead
    (CurrentStore.prepareScoped?_certified prepared ranked) record

/-- Once this selected branch has actually run to a scheduler cut, resumption
uses its reached cursor. No equation re-selection or world replay occurs. -/
theorem current_store_selected_pause {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program)
    (cursor residual : Cursor Context) (next : Control) (first second : Nat)
    (events : List Empty)
    (paused : (CettaEagerDFS.Destination.machine policy program).run first
      {cursor with control := next} = (events, .exhausted residual)) :
    (CettaEagerDFS.Destination.machine policy program).run (first + second)
      {cursor with control := next} =
      (events ++ ((CettaEagerDFS.Destination.machine policy program).run second residual).1,
        ((CettaEagerDFS.Destination.machine policy program).run second residual).2) :=
  selected_resume policy program cursor residual next first second events paused

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn.ChoiceStoreControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open CettaEagerDFS.Destination
open CettaEagerDFS.Destination.ClauseChoice
open Mettapedia.Logic.LP

private def pair (x y : Atom) : Atom := .expression [.symbol "Pair", x, y]
private def argument := Atom.var (CurrentStore.referenceName CurrentStore.Controls.callerX)
private def destination := Atom.var (CurrentStore.referenceName CurrentStore.Controls.callerOpen)
private def equation : SpaceSemantics.Equation := ⟨"f", [.var "x"], pair (.var "x") (.var "x")⟩
private def program : SpaceSemantics.Program := {equations := [equation, equation], declarations := []}
private def older : List Goal := [.invoke "println!" [pair argument argument] (Effects.boolean true)]
private def cursor : Cursor String :=
  { world := ⟨Effects.empty, [], [.symbol "earlier-effect"]⟩
    control :=
      { bindings := bindingAtomEquations ⟨CurrentStore.assignments CurrentStore.Controls.snapshot, []⟩
        goals := .invoke "f" [argument] destination :: older
        destination := destination
        reserved := {"older-sibling"} }
    context := "parent" }
private def table := CurrentStore.normalize (CurrentStore.assignments CurrentStore.Controls.snapshot)
private def operands : List CurrentStore.ContextualOperand :=
  [(CurrentStore.Controls.caller, .var "x"), (CurrentStore.Controls.caller, .var "open"),
   (CurrentStore.Controls.caller, .var "open"), (CurrentStore.Controls.caller, Effects.boolean true),
   (CurrentStore.Controls.caller, pair (.var "x") (.var "x"))]

attribute [local simp] CurrentStore.prepareScoped? CurrentStore.operandScope
  TypeSubst.typeVars TypeSubst.typeVarsList CurrentStore.prepare? CurrentStore.contextualRows?
  CurrentStore.qualifyRowsFrom? CurrentStore.qualifyRow? CurrentStore.qualify?
  Snapshot.rows Snapshot.entryRows Snapshot.Row.ofEntry EntryOf.initial entryEnv
  Snapshot.image_frameAt List.range_succ List.ofFn_succ CurrentStore.assignments
  CurrentStore.normalize CurrentStore.normalizeFrom TypeSubst.bind TypeSubst.apply
  TypeSubst.applyAssignment TypeSubst.lookup TypeSubst.erase renameTypeVars CurrentStore.nameIn
  MetavariableFrame.indexOf CurrentStore.referenceName CurrentStore.freeName Token.ref
  CurrentStore.Controls.caller CurrentStore.Controls.child CurrentStore.Controls.callerX
  CurrentStore.Controls.callerOpen CurrentStore.Controls.childX CurrentStore.Controls.image
  CurrentStore.Controls.snapshot

private theorem prepared : CurrentStore.prepareScoped? [] CurrentStore.Controls.image operands =
    some (CurrentStore.Controls.snapshot,
      [argument] ++ destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ []) := by
  simp [operands, argument, destination, cursor, older, pair, Goal.atoms, Effects.boolean]

private def environment := (resolve cursor.control.bindings).getD (Subst.id signature)
private theorem resolved : resolve cursor.control.bindings = some environment := by
  obtain ⟨actual, result⟩ := certified_resolves CurrentStore.Controls.actual_certificate
  change resolve cursor.control.bindings = some actual at result
  simp [environment, result]

private def alternatives := choices program (cursor.readout table).control "f"
  ([argument].map (CettaEagerDFS.Destination.read environment)) (table.apply destination)
  (older.map (Goal.readout table))
private def first := (alternatives.head?.map Prod.snd).getD cursor.control
private def execution (budget : Nat) :=
  (CettaEagerDFS.Destination.machine .relational program).run budget {cursor with control := first}
private def answer := match (execution 48).2 with
  | .finished (.value value _, _) => some value
  | _ => none
private def output := ((observed (execution 48).2).map fun (state : CettaEagerDFS.World × Control) => state.1.output)
private def resumedOutput := match (execution 5).2 with
  | .exhausted saved => ((observed
      ((CettaEagerDFS.Destination.machine .relational program).run 43 saved).2).map fun (state : CettaEagerDFS.World × Control) => state.1.output)
  | _ => none

#guard alternatives.map Prod.fst == [0, 1]
#guard answer == some (pair (.symbol "A") (.symbol "A"))
#guard output == some [.symbol "earlier-effect", pair (.symbol "A") (.symbol "A")]
#guard resumedOutput == output
#guard first.reserved == cursor.control.reserved
#guard CurrentStore.prepareScoped? [] CurrentStore.Controls.image
  [(⟨0, 4⟩, .var "x")] == none

theorem actual_scoped_invocation_request (later : Nat) :
    (CettaEagerDFS.Destination.machine .relational program).run (later + 1) (cursor.readout table) =
      ([], .suspended (.invoke "f" ([argument].map (CettaEagerDFS.Destination.read environment))
        (table.apply destination)) (cursor.readout table)) :=
  current_store_invocation_request .relational program cursor "f" [argument] destination older [] []
    prepared CurrentStore.Controls.actual_rank rfl rfl (by decide) resolved later

theorem every_actual_occurrence_has_joint_source_readout (occurrence : Nat) (next : Control)
    (selected : (occurrence, next) ∈ alternatives) :
    ∃ reached, resolve next.bindings = some reached ∧
      ∀ pending : List Atom,
        (pending.map table.apply).map (CettaEagerDFS.Destination.read reached) =
          pending.map (CettaEagerDFS.Destination.read reached) := by
  obtain ⟨_, equation, reached, _row, _source, solved, absorbed, _world, _context⟩ :=
    current_store_clause_selection .relational program cursor "f" [argument] destination older [] []
      prepared CurrentStore.Controls.actual_rank rfl rfl (by decide) resolved occurrence next selected 0
  exact ⟨reached, solved, absorbed⟩

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.DestinationReturn.ChoiceStoreControls



set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.Scoped

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS (World)
open CettaEagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Inspection keeps the complete saved allocator/scope pair. Source control
faults are suspended requests, never an erased `faulted` configuration. -/
def readback {Context : Type} : Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary →
    Option (ScopedCursor Context)
  | .finished cursor | .exhausted cursor | .stuck cursor | .suspended _ cursor => some cursor
  | .faulted => none

/-- This compatibility equation identifies the unchanged historical profile.
It does not validate its old open-answer collection behavior. -/
theorem eager_step_unchanged (program : SpaceSemantics.Program) (source : CettaEagerDFS.Configuration) :
    (CettaDFSStreaming.machine program .eager).step source = some (
      match CettaEagerDFS.step program source with
      | some next => match CettaDFSProducer.emission source with
        | [] => .silent next
        | values => .publish values next
      | none => if CettaEagerDFS.completed source then .finish source
        else match CettaEagerDFS.fault source with
          | some reason => .call (.fault reason) source
          | none => .call .stopped source) := rfl

/-- The scheduler inspection is the constructed scope operation, with all
children and primitive requests retained by the one existing driver. -/
theorem step_scope {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) :
    (CettaDFSStreaming.machine program (.scopedDestination Context policy)).step source =
      some (scopeStep policy program source) := rfl

/-- A budget split resumes the entire reached source cursor. Allocation,
collected occurrences, world updates and older scopes are not restarted. -/
theorem resume {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (first second : Nat) (source saved : ScopedCursor Context) (events : List CollectedAnswer)
    (paused : (CettaDFSStreaming.machine program (.scopedDestination Context policy)).run first source =
      (events, .exhausted saved)) :
    (CettaDFSStreaming.machine program (.scopedDestination Context policy)).run (first + second) source =
      (events ++ ((CettaDFSStreaming.machine program (.scopedDestination Context policy)).run second saved).1,
        ((CettaDFSStreaming.machine program (.scopedDestination Context policy)).run second saved).2) :=
  (CettaDFSStreaming.machine program (.scopedDestination Context policy)).established_and_pending
    first second source saved events paused

/-- Completion of an empty root is distinct from an exhausted budget. The
already collected answer history and reached world remain in the verdict. -/
theorem empty_root_finishes {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (answers : List CollectedAnswer) (fuel : Nat) :
    (CettaDFSStreaming.machine program (.scopedDestination Context policy)).run (fuel + 1)
      (allocator, ⟨world, [⟨[], answers, none⟩]⟩) =
      ([], .finished (allocator, ⟨world, [⟨[], answers, none⟩]⟩)) := rfl

/-- A refused return consumes one alternative while retaining every older
choice. The premise is independent joint satisfiability, not a target result. -/
theorem refused_return {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (value destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .equate value destination :: older) :
    Refinement control.bindings value destination none ↔
      (CettaDFSStreaming.machine program (.scopedDestination Context policy)).run 1
        (allocator, ⟨world, scope :: parents⟩) =
        ([], .exhausted (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  rw [scope_refused_return_iff policy program allocator world scope parents control context origins
    pending value destination older frontier head]
  constructor
  · intro actual
    simp only [Machine.run, step_scope, actual]
  · intro actual
    cases refined : refine control.bindings value destination with
    | none =>
      exact scope_refused_return policy program allocator world scope parents control context origins
        pending value destination older frontier head ((refinement_iff _ _ _ _).mpr refined)
    | some bindings =>
      have stepped := scope_accepted_return policy program allocator world scope parents control context
        origins pending value destination older bindings frontier head ((refinement_iff _ _ _ _).mpr refined)
      simp only [Machine.run, step_scope, stepped] at actual
      have sizes := congrArg (fun result => readback result.2 |>.map fun next =>
        next.2.scopes.head?.map (fun (current : CollectionScope Context) => current.frontier.length)) actual
      simp [readback] at sizes

/-- A primitive source fault suspends at the exact reached world and control;
it cannot publish a partially collected list or skip a younger continuation. -/
theorem primitive_fault {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment) (reason : Effects.Fault) (fuel : Nat)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment) (known : StdLib.known head = true)
    (failed : StdLib.apply world.state head (arguments.map (read environment)) = .error reason) :
    (CettaDFSStreaming.machine program (.scopedDestination Context policy)).run (fuel + 1)
      (allocator, ⟨world, scope :: parents⟩) =
      ([], .suspended (.fault reason) (allocator, ⟨world, scope :: parents⟩)) := by
  simp only [Machine.run, step_scope,
    scope_primitive_fault policy program allocator world scope parents control context origins pending
      head arguments destination older environment reason frontier atCall resolved known failed]

/-- Every budget at an unresolved attached-work boundary retains that work,
all completed rows and the caller; it is not successful empty search. -/
theorem associated_work_retained {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (answers : List CollectedAnswer)
    (caller : CollectionCaller Context) (parent : CollectionScope Context)
    (parents : List (CollectionScope Context)) (answer : CollectedAnswer)
    (member : answer ∈ answers) (pending : answer.associated ≠ []) (fuel : Nat) :
    (CettaDFSStreaming.machine program (.scopedDestination Context policy)).run (fuel + 1)
      (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩) =
      ([], .suspended .associatedWork (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩)) := by
  simp only [Machine.run, step_scope,
    scopeStep_pending_associated policy program allocator world answers caller parent parents answer member pending]

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.Scoped


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.Scoped

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS (World ScopesValid)
open CettaEagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Every finite prefix retains a properly nested source configuration. A
fault or request still has that exact saved configuration; no state is erased. -/
theorem run_scopes_valid {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : ScopedCursor Context) (valid : ScopesValid source.2.scopes) :
    ∃ reached, readback ((CettaDFSStreaming.machine program
      (.scopedDestination Context policy)).run fuel source).2 = some reached ∧
      ScopesValid reached.2.scopes := by
  induction fuel generalizing source with
  | zero => exact ⟨source, rfl, valid⟩
  | succ fuel ih =>
    have kept := scopeStep_scopes_valid policy program source valid
    cases stepped : scopeStep policy program source with
    | silent next =>
      rw [stepped] at kept
      simpa only [Machine.run, step_scope, stepped] using ih next kept
    | publish events next =>
      rw [stepped] at kept
      simpa only [Machine.run, step_scope, stepped] using ih next kept
    | finish next =>
      rw [stepped] at kept
      exact ⟨next, by simp only [Machine.run, step_scope, stepped, readback], kept⟩
    | call request next =>
      rw [stepped] at kept
      exact ⟨next, by simp only [Machine.run, step_scope, stepped, readback], kept⟩
    | fail events =>
      rw [stepped] at kept
      exact False.elim kept

/-- Every published occurrence retains an independently satisfiable reached
constraint record. This follows the executed source branches over the whole
prefix, rather than asking a completion service for a certified answer. -/
theorem run_answer_models {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : ScopedCursor Context) (valid : ScopesValid source.2.scopes)
    (answer : CollectedAnswer) (published : answer ∈
      ((CettaDFSStreaming.machine program (.scopedDestination Context policy)).run fuel source).1) :
    ∃ environment, Solves environment answer.bindings := by
  induction fuel generalizing source with
  | zero => cases published
  | succ fuel ih =>
    have kept := scopeStep_scopes_valid policy program source valid
    cases stepped : scopeStep policy program source with
    | silent next =>
      rw [stepped] at kept
      exact ih next kept (by simpa only [Machine.run, step_scope, stepped] using published)
    | publish events next =>
      rw [stepped] at kept
      simp only [Machine.run, step_scope, stepped, List.mem_append] at published
      rcases published with here | later
      · obtain ⟨value, bindings, origins, environment, eventsEq, solved⟩ :=
          scope_published_source_model policy program source next events stepped
        rw [eventsEq] at here
        cases List.mem_singleton.mp here
        exact ⟨environment, solved⟩
      · exact ih next kept later
    | finish next => simp only [Machine.run, step_scope, stepped, List.not_mem_nil] at published
    | call request next => simp only [Machine.run, step_scope, stepped, List.not_mem_nil] at published
    | fail events =>
      rw [stepped] at kept
      exact False.elim kept

/-- Actual loading supplies the scope invariant for every later run prefix.
The loader and scheduler construct children; no completed child is an input. -/
theorem loaded_run {policy : Policy} (program : SpaceSemantics.Program)
    (allocator : Allocator) (core : List Atom) (cells : List (String × Atom))
    (input : List Atom) (control : Control) (context : List Atom)
    (source : ScopedCursor (Token × List Atom)) (fuel : Nat)
    (loaded : loadScoped? allocator core cells input control context = some source) :
    (∃ reached, readback ((CettaDFSStreaming.machine program
      (.scopedDestination (Token × List Atom) policy)).run fuel source).2 = some reached ∧
      ScopesValid reached.2.scopes) ∧
    (∀ answer ∈ ((CettaDFSStreaming.machine program
      (.scopedDestination (Token × List Atom) policy)).run fuel source).1,
      ∃ environment, Solves environment answer.bindings) := by
  have valid := loadScoped_scopes_valid allocator core cells input control context source loaded
  exact ⟨run_scopes_valid policy program fuel source valid,
    fun answer present => run_answer_models policy program fuel source valid answer present⟩

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.Scoped


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 12000

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.Scoped.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS (World)
open CettaEagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private def program : SpaceSemantics.Program := {equations := [], declarations := []}
private def x : Atom := .var "x"
private def a : Atom := .var "a"
private def b : Atom := .var "b"
private def quote (atom : Atom) : Atom := .expression [.symbol "quote", atom]
private def collapse (atom : Atom) : Atom := .expression [.symbol "collapse", atom]
private def superpose (atoms : List Atom) : Atom := .expression [.symbol "superpose", .expression atoms]
private def pair (one two : Atom) : Atom := .expression [.symbol "Pair", one, two]
private def letE (pattern value body : Atom) : Atom := .expression [.symbol "let", pattern, value, body]
private def equality (one two : Atom) : Atom := .expression [.symbol "==", one, two]
private def seed (expression : Atom) : Control :=
  {bindings := [(.var "caller", .symbol "retained")]
   goals := [.evaluate expression (.var "out")]
   destination := .var "out"}
private def loaded (expression : Atom) (capacity : Nat := 12) :=
  loadScoped? (Allocator.empty capacity 3) [] [("remember", pair x x)] [] (seed expression) [x, x]
private def execute (expression : Atom) (fuel : Nat := 150) (capacity : Nat := 12) :=
  (loaded expression capacity).map fun state =>
    (CettaDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run fuel state
private def answers (expression : Atom) (fuel : Nat := 150) :=
  (execute expression fuel).map fun result => result.1.map CollectedAnswer.value
private def saved (expression : Atom) (fuel : Nat) :=
  (execute expression fuel).bind fun result => Scoped.readback result.2
private def output (expression : Atom) (fuel : Nat := 150) :=
  (saved expression fuel).map fun state => state.2.world.output
private def finished (expression : Atom) :=
  (execute expression).map fun result => match result.2 with
    | .finished _ => true
    | _ => false

private def comparison := letE (.expression [a, b]) (collapse (superpose [x, x])) (equality a b)
#guard answers comparison == some [Effects.boolean false]
#guard finished comparison == some true

private def sharing := letE (.expression [pair a b]) (collapse (quote (pair x x))) (equality a b)
#guard answers sharing == some [Effects.boolean true]

private def nested := collapse (collapse (quote (pair x x)))
#guard (answers nested).map (fun values => match values with
  | [.expression [.expression [.expression [.symbol "Pair", .var one, .var two]]]] => one == two
  | _ => false) == some true

private def printEffect : Atom := .expression [.symbol "println!", .symbol "effect"]
private def effectful := collapse (letE (.var "unit") printEffect (quote (pair x x)))
#guard output effectful 8 == some [.symbol "effect"]
#guard output effectful 150 == some [.symbol "effect"]
private def resumedOutput : Option (List Atom) := do
  let paused ← execute effectful 8
  match paused.2 with
  | .exhausted state =>
    (Scoped.readback ((CettaDFSStreaming.machine program
      (.scopedDestination (Token × List Atom) .relational)).run 142 state).2).map fun final => final.2.world.output
  | _ => none
#guard resumedOutput == some [.symbol "effect"]

private def refusedAfterEffect := collapse (superpose [
  letE (.var "unit") printEffect (letE (.symbol "A") (.symbol "B") (.symbol "unreachable")),
  quote (.symbol "survivor")])
#guard answers refusedAfterEffect == some [.expression [.symbol "survivor"]]
#guard output refusedAfterEffect == some [.symbol "effect"]
private def emptyCollection := collapse (superpose [])
#guard answers emptyCollection == some [.expression []]
private def literalError := collapse (quote (.expression [.symbol "Error", .symbol "data", .symbol "message"]))
#guard answers literalError == some [.expression [.expression [.symbol "Error", .symbol "data", .symbol "message"]]]
private def partialFault := collapse (superpose [quote (.symbol "first"),
  .expression [.symbol "%", .grounded (.int 1), .grounded (.int 0)]])
#guard (execute partialFault).map (fun result => (result.1.length, match result.2 with
  | .suspended (.fault .zeroDivisor) _ => true
  | _ => false)) == some (0, true)
#guard (saved partialFault 150).map (fun state => state.2.scopes.head?.map fun scope =>
  scope.collected.map CollectedAnswer.value) == some (some [.symbol "first"])
#guard (execute (collapse (quote x)) 30 1).map (fun result => match result.2 with
  | .suspended .allocation _ => true
  | _ => false) == some true

/-- A restarted child repeats its output; exact saved-cursor resumption above does not. -/
private def replayedOutput : Option (List Atom) := do
  let initial ← loaded effectful
  let reached ← saved effectful 8
  let replay := (initial.1, {initial.2 with world := reached.2.world})
  (Scoped.readback ((CettaDFSStreaming.machine program
    (.scopedDestination (Token × List Atom) .relational)).run 8 replay).2).map fun final => final.2.world.output
#guard replayedOutput == some [.symbol "effect", .symbol "effect"]
#guard output effectful 7 == some []

private def remembered := letE (.expression [a]) (collapse (quote x))
  (letE (pair b b) (.expression [.symbol "get-state", .symbol "remember"]) (equality a b))
#guard answers remembered == some [Effects.boolean false]
private def syntaxAndString := collapse (quote (pair x (.grounded (.string "slot:6"))))
#guard (answers syntaxAndString).map (fun values => match values with
  | [.expression [.expression [.symbol "Pair", .var _, .grounded (.string text)]]] => text == "slot:6"
  | _ => false) == some true

private def row : SpaceSemantics.Equation := ⟨"f", [x], pair x x⟩
private def repeatedProgram : SpaceSemantics.Program := {equations := [row, row], declarations := []}
private def repeatedRun := (loaded (.expression [.symbol "f", .symbol "B"])).map fun initial =>
  (CettaDFSStreaming.machine repeatedProgram (.scopedDestination (Token × List Atom) .relational)).run 60 initial
#guard repeatedRun.map (fun result => result.1.map CollectedAnswer.value) ==
  some [pair (.symbol "B") (.symbol "B"), pair (.symbol "B") (.symbol "B")]
#guard repeatedRun.map (fun result => result.1.map CollectedAnswer.occurrences) == some [[0], [1]]

private def delayed : ScopedCursor Unit := (Allocator.empty 4 3,
  ⟨⟨NamedSpaces.Store.new [] [], [], [.symbol "before"]⟩,
    [⟨[], [⟨x, [], [2], [pair x x]⟩], some (seed x, a, (), [1])⟩,
      ⟨[(seed (.symbol "older"), (), [0])], [], none⟩]⟩)
#guard match (CettaDFSStreaming.machine program (.scopedDestination Unit .relational)).run 20 delayed with
  | ([], .suspended .associatedWork saved) => saved.1 == delayed.1 &&
      saved.2.scopes.head?.map (fun scope => scope.collected.map CollectedAnswer.associated) == some [[pair x x]]
  | _ => false
#guard (execute comparison 0).map (fun result => match result.2 with
  | .exhausted _ => result.1.isEmpty
  | _ => false) == some true

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.Scoped.Controls

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.Scoped

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS (World)
open CettaEagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The actual parse allocation consumes one transition. Every later budget
starts from its retained return constraint, so it cannot repeat the parser
or allocate another identity for the same result. -/
theorem parsed_return_run {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator next : Allocator) (token : Token) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text value destination : Atom) (older : List Goal) (environment : Environment) (fuel : Nat)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (loaded : CettaEagerDFS.Collection.SyntaxLoading.loadParsed? allocator
      (collectionSupport ⟨world, scope :: parents⟩) (read environment text) =
      .ok (some (next, token, value))) :
    (CettaDFSStreaming.machine program (.scopedDestination Context policy)).run (fuel + 1)
      (allocator, ⟨world, scope :: parents⟩) =
      (CettaDFSStreaming.machine program (.scopedDestination Context policy)).run fuel
        (next, ⟨world,
          {scope with frontier := primitiveWork control context origins destination older [value] ++ pending} :: parents⟩) := by
  simp only [Machine.run, step_scope,
    scope_parse_success policy program allocator next token world scope parents control context origins pending
      text value destination older environment frontier atCall resolved loaded]

/-- A named parse's one actual allocation remains in the saved cursor. The
next budget resumes the ordinary constraint-return path, not the parser. -/
theorem parsed_return_pending {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator next : Allocator) (token : Token) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text value destination : Atom) (older : List Goal) (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (loaded : CettaEagerDFS.Collection.SyntaxLoading.loadParsed? allocator
      (collectionSupport ⟨world, scope :: parents⟩) (read environment text) =
      .ok (some (next, token, value))) :
    (CettaDFSStreaming.machine program (.scopedDestination Context policy)).run 1
      (allocator, ⟨world, scope :: parents⟩) =
      ([], .exhausted (next, ⟨world,
        {scope with frontier := primitiveWork control context origins destination older [value] ++ pending} :: parents⟩)) := by
  simp only [Machine.run, step_scope,
    scope_parse_success policy program allocator next token world scope parents control context origins pending
      text value destination older environment frontier atCall resolved loaded]

/-- Refusing an allocation retains the exact reached request, bindings, older
frontier and world at every positive budget. No partial parse result appears. -/
theorem parse_allocation_retained {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text destination : Atom) (older : List Goal) (environment : Environment) (fuel : Nat)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (unserved : CettaEagerDFS.Collection.SyntaxLoading.loadParsed? allocator
      (collectionSupport ⟨world, scope :: parents⟩) (read environment text) = .ok none) :
    (CettaDFSStreaming.machine program (.scopedDestination Context policy)).run (fuel + 1)
      (allocator, ⟨world, scope :: parents⟩) =
      ([], .suspended .allocation (allocator, ⟨world, scope :: parents⟩)) := by
  simp only [Machine.run, step_scope,
    scope_parse_unserved policy program allocator world scope parents control context origins pending
      text destination older environment frontier atCall resolved unserved]

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.Scoped

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.Scoped.NamedParseControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CettaEagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private def program : SpaceSemantics.Program := {equations := [], declarations := []}
private def a : Atom := .var "a"
private def b : Atom := .var "b"
private def c : Atom := .var "c"
private def d : Atom := .var "d"
private def parse (text : String) : Atom := .expression [.symbol "parse", .grounded (.string text)]
private def letE (pattern value body : Atom) : Atom := .expression [.symbol "let", pattern, value, body]
private def equality (one two : Atom) : Atom := .expression [.symbol "==", one, two]
private def pair (one two : Atom) : Atom := .expression [.symbol "Pair", one, two]
private def seed (expression : Atom) : Control :=
  {bindings := [(.var "caller", .symbol "retained")], goals := [.evaluate expression (.var "out")], destination := .var "out"}
private def loaded (expression : Atom) (capacity : Nat := 12) :=
  loadScoped? (Allocator.empty capacity 4) [] [("remember", .symbol "initial")] [] (seed expression) []
private def execute (expression : Atom) (fuel : Nat := 180) (capacity : Nat := 12) := do
  let initial ← loaded expression capacity
  pure ((CettaDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run fuel initial)
private def answers (expression : Atom) :=
  (execute expression).map fun result => result.1.map CollectedAnswer.value
private def saved (expression : Atom) (fuel : Nat) (capacity : Nat := 12) :=
  (execute expression fuel capacity).bind fun result => Scoped.readback result.2
private def output (expression : Atom) (fuel : Nat := 180) :=
  (saved expression fuel).map fun state => state.2.world.output
private def separate := letE a (parse "$x") (letE b (parse "$x") (equality a b))
#guard answers separate == some [Effects.boolean false]
#guard (execute separate).map (fun result => match result.2 with | .finished _ => true | _ => false) == some true
private def authored := letE a (parse "$x") (equality a (.var "x"))
#guard answers authored == some [Effects.boolean false]
private def within := letE (.var "parsed") (parse "(Pair $x $x)")
  (letE (pair a b) (.var "parsed") (equality a b))
#guard answers within == some [Effects.boolean true]
private def twoPairs := letE (.var "p") (parse "(Pair $x $x)")
  (letE (.var "q") (parse "(Pair $x $x)")
    (letE (pair a b) (.var "p")
      (letE (pair c d) (.var "q")
        (.expression [.symbol "Checks", equality a b, equality c d, equality a c]))))
#guard answers twoPairs == some [.expression [.symbol "Checks", Effects.boolean true, Effects.boolean true, Effects.boolean false]]
private def boundOne := letE a (parse "$x") (letE b (parse "$x")
  (letE a (.symbol "A") (equality a b)))
#guard answers boundOne == some [Effects.boolean false]
private def sharedBinding := letE (.var "p") (parse "(Pair $x $x)")
  (letE (pair a b) (.var "p") (letE a (.symbol "A") (equality b (.symbol "A"))))
#guard answers sharedBinding == some [Effects.boolean true]
private def rawSpelling := letE a (parse "$slot:0") (equality a (.var "slot:0"))
#guard answers rawSpelling == some [Effects.boolean false]
private def strings := letE (.var "p") (parse "(Pair $x \"$x\")")
  (letE (pair a b) (.var "p") (equality a b))
#guard answers strings == some [Effects.boolean false]
private def quotedSyntax := letE (.var "p") (parse "(quote $x)")
  (letE (.expression [.symbol "quote", a]) (.var "p") (equality a (.var "x")))
#guard answers quotedSyntax == some [Effects.boolean false]

private def printEffect : Atom := .expression [.symbol "println!", .symbol "effect"]
private def effectful := letE (.var "unit") printEffect separate
#guard output effectful 8 == some [.symbol "effect"]
#guard output effectful == some [.symbol "effect"]
private def resumed : Option (List Atom × List Atom) := do
  let paused ← execute effectful 8
  match paused.2 with
  | .exhausted state =>
    let completed := (CettaDFSStreaming.machine program
      (.scopedDestination (Token × List Atom) .relational)).run 172 state
    let final ← Scoped.readback completed.2
    pure ((paused.1 ++ completed.1).map CollectedAnswer.value, final.2.world.output)
  | _ => none
#guard resumed == some ([Effects.boolean false], [.symbol "effect"])

private def collected := letE (.expression [a, b])
  (.expression [.symbol "collapse", .expression [.symbol "superpose",
    .expression [parse "$x", parse "$x"]]]) (equality a b)
#guard answers collected == some [Effects.boolean false]
private def stored := letE a (parse "$x")
  (letE (.var "unit") (.expression [.symbol "change-state!", .symbol "remember", a])
    (letE b (parse "$x")
      (letE c (.expression [.symbol "get-state", .symbol "remember"]) (equality b c))))
#guard answers stored == some [Effects.boolean false]

private def noCapacity := execute effectful 180 1
#guard noCapacity.map (fun result => match result.2 with
  | .suspended .allocation state => (result.1.isEmpty, state.2.world.output)
  | _ => (false, [])) == some (true, [.symbol "effect"])
#guard noCapacity.map (fun result => match result.2 with
  | .suspended .allocation state =>
    match (CettaDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run 20 state with
    | ([], .suspended .allocation same) =>
      same.1 == state.1 && same.2.world.output == state.2.world.output &&
        same.2.scopes.map (fun scope => scope.frontier.map (fun work => work.1)) ==
          state.2.scopes.map (fun scope => scope.frontier.map (fun work => work.1))
    | _ => false
  | _ => false) == some true

private def malformed := letE (.var "unit") printEffect (parse "(")
#guard (execute malformed).map (fun result => match result.2 with
  | .suspended (.fault (.invalidArguments "parse")) state => (result.1.isEmpty, state.2.world.output)
  | _ => (false, [])) == some (true, [.symbol "effect"])

/- Current raw reader keeps $_ occurrences shared. This explicit profile
control is not a claim of SWI-PeTTa anonymous-variable conformance. -/
private def anonymous := letE (.var "p") (parse "(Pair $_ $_)")
  (letE (pair a b) (.var "p") (equality a b))
#guard answers anonymous == some [Effects.boolean true]

end Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming.Scoped.NamedParseControls
