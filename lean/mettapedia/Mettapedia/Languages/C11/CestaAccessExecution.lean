import Mettapedia.Languages.C11.CestaObjectAccess
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Retained execution of sorted identifier access requests

Each successful request earns one semantic receipt and retains the complete
memory, scope environment, pending requests and occurrence counter. The
independent reduction rules use sorted source formation, binding and typed
memory judgments. History laws preserve exact connected endpoints and the
ordered number of consumed occurrences. Prefix resumption is an instance of
the common retained-state driver.

This profile executes already formed identifier reads and integer stores.
Assignment operands, declarations, expressions, calls, control flow and
source lifetime changes still require the C source machine. Receipts are
observations of semantic memory operations; they confer no host publication
authority or permission to copy externally owned resources.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.CestaAccessExecution

open ObjectAccessMemory
open Mettapedia.GSLT.Parsing.SortedCanonicalSExprCodec
open Mettapedia.GSLT.Distinction.ProductiveBlocks

inductive Request (layout : Layout) where
  | read (wire : CestaObjectAccess.Wire)
  | store (wire : CestaObjectAccess.Wire) (value : IntegerValue layout.representation.integer)
  deriving DecidableEq, Repr

inductive Response where
  | observed (outcome : IntegerObject.Outcome)
  | stored
  deriving DecidableEq, Repr

inductive Reduction (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (environment : ScopedLvalues.Environment) : SemanticState layout.representation.characters →
    Request layout → Response → SemanticState layout.representation.characters → Prop where
  | read (before : SemanticState layout.representation.characters) (wire : CestaObjectAccess.Wire)
      (outcome : IntegerObject.Outcome)
      (reading : CestaObjectAccess.Reading schema codecProfile sort layout before environment wire outcome) :
      Reduction schema codecProfile sort layout environment before (.read wire) (.observed outcome) before
  | store (before after : SemanticState layout.representation.characters) (wire : CestaObjectAccess.Wire)
      (value : IntegerValue layout.representation.integer)
      (writing : CestaObjectAccess.Writing schema codecProfile sort layout before after environment wire value) :
      Reduction schema codecProfile sort layout environment before (.store wire value) .stored after

def execute (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (before : State layout.representation.characters) (environment : ScopedLvalues.Environment) :
    Request layout → Option (Response × State layout.representation.characters)
  | .read wire => do
      let outcome ← CestaObjectAccess.read schema codecProfile sort layout before environment wire
      some (.observed outcome, before)
  | .store wire value => do
      let after ← CestaObjectAccess.store schema codecProfile sort layout before environment wire value
      some (.stored, after)

theorem execute_sound (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (before after : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (request : Request layout) (response : Response)
    (executed : execute schema codecProfile sort layout before environment request = some (response, after)) :
    Reduction schema codecProfile sort layout environment (represent before) request response (represent after) := by
  cases request with
  | read wire =>
      cases observed : CestaObjectAccess.read schema codecProfile sort layout before environment wire with
      | none => simp [execute, observed] at executed
      | some outcome =>
          simp [execute, observed] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .read _ wire outcome (CestaObjectAccess.read_sound _ _ _ _ _ _ _ _ observed)
  | store wire value =>
      cases written : CestaObjectAccess.store schema codecProfile sort layout before environment wire value with
      | none => simp [execute, written] at executed
      | some saved =>
          simp [execute, written] at executed
          obtain ⟨rfl, rfl⟩ := executed
          exact .store _ _ wire value (CestaObjectAccess.store_sound _ _ _ _ _ _ _ _ _ written)

theorem execute_complete (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (before : State layout.representation.characters) (environment : ScopedLvalues.Environment)
    (request : Request layout) (response : Response) (after : SemanticState layout.representation.characters)
    (reduced : Reduction schema codecProfile sort layout environment (represent before) request response after) :
    ∃ saved, execute schema codecProfile sort layout before environment request = some (response, saved) ∧
      represent saved = after := by
  cases reduced with
  | read wire outcome reading =>
      exact ⟨before, by simp [execute, CestaObjectAccess.read_complete _ _ _ _ _ _ _ _ reading], rfl⟩
  | store after wire value writing =>
      obtain ⟨saved, written, same⟩ := CestaObjectAccess.store_complete _ _ _ _ _ _ _ _ _ writing
      exact ⟨saved, by simp [execute, written], same⟩

structure Configuration (layout : Layout) where
  memory : State layout.representation.characters
  environment : ScopedLvalues.Environment
  pending : List (Request layout)
  ordinal : Nat
  deriving DecidableEq, Repr

inductive Advance (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout) :
    Configuration layout → Request layout → Response → Configuration layout → Prop where
  | consume (before after : State layout.representation.characters) (environment : ScopedLvalues.Environment)
      (request : Request layout) (response : Response) (rest : List (Request layout)) (ordinal : Nat)
      (reduced : Reduction schema codecProfile sort layout environment
        (represent before) request response (represent after)) :
      Advance schema codecProfile sort layout ⟨before, environment, request :: rest, ordinal⟩ request response
        ⟨after, environment, rest, ordinal + 1⟩

theorem Advance.pending_eq {schema : Schema} {codecProfile : Notation} {sort : String} {layout : Layout}
    {before after : Configuration layout} {request : Request layout} {response : Response}
    (advanced : Advance schema codecProfile sort layout before request response after) :
    before.pending = request :: after.pending := by cases advanced; rfl

theorem Advance.ordinal_eq {schema : Schema} {codecProfile : Notation} {sort : String} {layout : Layout}
    {before after : Configuration layout} {request : Request layout} {response : Response}
    (advanced : Advance schema codecProfile sort layout before request response after) :
    after.ordinal = before.ordinal + 1 := by cases advanced; rfl

theorem Advance.environment_eq {schema : Schema} {codecProfile : Notation} {sort : String} {layout : Layout}
    {before after : Configuration layout} {request : Request layout} {response : Response}
    (advanced : Advance schema codecProfile sort layout before request response after) :
    after.environment = before.environment := by cases advanced; rfl

structure Receipt (layout : Layout) where
  before : Configuration layout
  request : Request layout
  response : Response
  after : Configuration layout
  deriving DecidableEq, Repr

inductive Verdict (layout : Layout) where
  | returned (saved : Configuration layout)
  | refused (saved : Configuration layout)
  deriving DecidableEq, Repr

def machine (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout) :
    Machine (Configuration layout) (Receipt layout) (Verdict layout) Empty where
  step before := match before.pending with
    | [] => some (.finish (.returned before))
    | request :: rest =>
        match execute schema codecProfile sort layout before.memory before.environment request with
        | none => some (.finish (.refused before))
        | some (response, memory) =>
            let after := { before with memory, pending := rest, ordinal := before.ordinal + 1 }
            some (.publish [⟨before, request, response, after⟩] after)

def productive (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout) :
    (machine schema codecProfile sort layout).Productive where
  rank _ := 0
  moves before := by
    cases pending : before.pending with
    | nil => simp [machine, pending]
    | cons request rest =>
        cases executed : execute schema codecProfile sort layout before.memory before.environment request <;>
          simp [machine, pending, executed]
  silent_decreases := by
    intro before after silent
    cases pending : before.pending with
    | nil => simp [machine, pending] at silent
    | cons request rest =>
        cases executed : execute schema codecProfile sort layout before.memory before.environment request <;>
          simp [machine, pending, executed] at silent

theorem resume_after_prefix (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (first second : Nat) (initial saved : Configuration layout) (events : List (Receipt layout))
    (paused : (machine schema codecProfile sort layout).run first initial = (events, .exhausted saved)) :
    (machine schema codecProfile sort layout).run (first + second) initial =
      (events ++ ((machine schema codecProfile sort layout).run second saved).1,
        ((machine schema codecProfile sort layout).run second saved).2) :=
  (machine schema codecProfile sort layout).established_and_pending first second initial saved events paused

inductive History (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout) :
    Configuration layout → List (Receipt layout) → Configuration layout → Prop where
  | nil (state : Configuration layout) : History schema codecProfile sort layout state [] state
  | cons (receipt : Receipt layout) (events : List (Receipt layout)) (final : Configuration layout)
      (advanced : Advance schema codecProfile sort layout receipt.before receipt.request receipt.response receipt.after)
      (following : History schema codecProfile sort layout receipt.after events final) :
      History schema codecProfile sort layout receipt.before (receipt :: events) final

theorem History.account {schema : Schema} {codecProfile : Notation} {sort : String} {layout : Layout}
    {before after : Configuration layout} {events : List (Receipt layout)}
    (history : History schema codecProfile sort layout before events after) :
    after.pending.length + events.length = before.pending.length ∧
      after.ordinal = before.ordinal + events.length ∧ after.environment = before.environment := by
  induction history with
  | nil state => simp
  | cons receipt events final advanced following ih =>
      have consumed := congrArg List.length advanced.pending_eq
      have increment := advanced.ordinal_eq
      have retained := advanced.environment_eq
      simp only [List.length_cons] at consumed ⊢
      obtain ⟨count, counter, environment⟩ := ih
      exact ⟨by omega, by omega, environment.trans retained⟩

theorem History.request_prefix {schema : Schema} {codecProfile : Notation} {sort : String} {layout : Layout}
    {before after : Configuration layout} {events : List (Receipt layout)}
    (history : History schema codecProfile sort layout before events after) :
    before.pending = events.map Receipt.request ++ after.pending := by
  induction history with
  | nil state => simp
  | cons receipt events final advanced following ih =>
      simp only [List.map_cons, List.cons_append]
      rw [advanced.pending_eq, ih]

theorem History.ordinal_bounds {schema : Schema} {codecProfile : Notation} {sort : String} {layout : Layout}
    {before after : Configuration layout} {events : List (Receipt layout)}
    (history : History schema codecProfile sort layout before events after) :
    ∀ receipt ∈ events, before.ordinal ≤ receipt.before.ordinal ∧ receipt.before.ordinal < after.ordinal := by
  induction history with
  | nil state => simp
  | cons receipt events final advanced following ih =>
      have increment := advanced.ordinal_eq
      have counter := following.account.2.1
      intro emitted present
      rcases List.mem_cons.mp present with rfl | present
      · exact ⟨Nat.le_refl _, by omega⟩
      · obtain ⟨lower, upper⟩ := ih emitted present
        exact ⟨by omega, upper⟩

theorem History.unique_ordinals {schema : Schema} {codecProfile : Notation} {sort : String} {layout : Layout}
    {before after : Configuration layout} {events : List (Receipt layout)}
    (history : History schema codecProfile sort layout before events after) :
    (events.map (fun receipt => receipt.before.ordinal)).Nodup := by
  induction history with
  | nil state => simp
  | cons receipt events final advanced following ih =>
      have increment := advanced.ordinal_eq
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro repeated
      obtain ⟨later, present, same⟩ := List.mem_map.mp repeated
      have lower := (following.ordinal_bounds later present).1
      omega

def endpoint {layout : Layout} : Outcome (Configuration layout) (Verdict layout) Empty →
    Option (Configuration layout)
  | .exhausted saved | .stuck saved | .suspended _ saved => some saved
  | .finished (.returned saved) | .finished (.refused saved) => some saved
  | .faulted => none

theorem run_history (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (fuel : Nat) (initial : Configuration layout) :
    ∃ final, endpoint ((machine schema codecProfile sort layout).run fuel initial).2 = some final ∧
      History schema codecProfile sort layout initial ((machine schema codecProfile sort layout).run fuel initial).1 final := by
  induction fuel generalizing initial with
  | zero => exact ⟨initial, rfl, .nil _⟩
  | succ fuel ih =>
      cases pending : initial.pending with
      | nil =>
          have ran : (machine schema codecProfile sort layout).run (fuel + 1) initial =
              ([], .finished (.returned initial)) := by simp [Machine.run, machine, pending]
          rw [ran]
          exact ⟨initial, rfl, .nil _⟩
      | cons request rest =>
          cases executed : execute schema codecProfile sort layout initial.memory initial.environment request with
          | none =>
              have ran : (machine schema codecProfile sort layout).run (fuel + 1) initial =
                  ([], .finished (.refused initial)) := by simp [Machine.run, machine, pending, executed]
              rw [ran]
              exact ⟨initial, rfl, .nil _⟩
          | some result =>
              rcases result with ⟨response, memory⟩
              let after := { initial with memory, pending := rest, ordinal := initial.ordinal + 1 }
              let receipt : Receipt layout := ⟨initial, request, response, after⟩
              have stepped : (machine schema codecProfile sort layout).step initial =
                  some (.publish [receipt] after) := by simp [machine, pending, executed, receipt, after]
              rw [(machine schema codecProfile sort layout).run_succ_publish stepped]
              obtain ⟨final, endState, following⟩ := ih after
              refine ⟨final, endState, .cons receipt _ final ?_ following⟩
              have reduced := execute_sound schema codecProfile sort layout initial.memory memory
                initial.environment request response executed
              have initialShape : initial = ⟨initial.memory, initial.environment, request :: rest, initial.ordinal⟩ := by
                cases initial; simp_all
              change Advance schema codecProfile sort layout initial request response after
              rw [initialShape]
              exact .consume _ _ _ _ _ _ _ reduced

theorem run_account (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (fuel : Nat) (initial : Configuration layout) :
    ∃ final, endpoint ((machine schema codecProfile sort layout).run fuel initial).2 = some final ∧
      final.pending.length + ((machine schema codecProfile sort layout).run fuel initial).1.length = initial.pending.length ∧
      final.ordinal = initial.ordinal + ((machine schema codecProfile sort layout).run fuel initial).1.length ∧
      final.environment = initial.environment := by
  obtain ⟨final, endState, history⟩ := run_history schema codecProfile sort layout fuel initial
  exact ⟨final, endState, history.account⟩

theorem run_pending_prefix (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (fuel : Nat) (initial : Configuration layout) :
    ∃ final, endpoint ((machine schema codecProfile sort layout).run fuel initial).2 = some final ∧
      initial.pending = ((machine schema codecProfile sort layout).run fuel initial).1.map Receipt.request ++ final.pending := by
  obtain ⟨final, endState, history⟩ := run_history schema codecProfile sort layout fuel initial
  exact ⟨final, endState, history.request_prefix⟩

theorem run_unique_ordinals (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (fuel : Nat) (initial : Configuration layout) :
    (((machine schema codecProfile sort layout).run fuel initial).1.map (fun receipt => receipt.before.ordinal)).Nodup := by
  obtain ⟨final, _, history⟩ := run_history schema codecProfile sort layout fuel initial
  exact history.unique_ordinals

/-- Attempted access requests, including a refused request. -/
def requestCharge {layout : Layout} (configuration : Configuration layout) : Nat :=
  if configuration.pending.isEmpty then 0 else 1

def Request.bytesRead {layout : Layout} : Request layout → Nat
  | .read _ => layout.representation.byteCount
  | .store _ _ => 0

def Request.bytesWritten {layout : Layout} : Request layout → Nat
  | .read _ => 0
  | .store _ _ => layout.representation.byteCount

/-- Logical byte accesses of an admitted operation, apart from name/type
checks and physical interpreter work. -/
def byteReadCharge (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (configuration : Configuration layout) : Nat := match configuration.pending with
  | [] => 0
  | request :: _ =>
      if (execute schema codecProfile sort layout configuration.memory configuration.environment request).isSome
      then request.bytesRead else 0

def byteWriteCharge (schema : Schema) (codecProfile : Notation) (sort : String) (layout : Layout)
    (configuration : Configuration layout) : Nat := match configuration.pending with
  | [] => 0
  | request :: _ =>
      if (execute schema codecProfile sort layout configuration.memory configuration.environment request).isSome
      then request.bytesWritten else 0

end Mettapedia.Languages.C11.CestaAccessExecution
