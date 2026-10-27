import Mettapedia.GSLT.LanguageDef.BagEquationDecision
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring

/-! Complete retained producer state, including typed focuses, full authored
rows, allocation accounts and dependent continuations. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedWire

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus
open RecursiveView Retained
open InferenceCettaWire (encodePattern decodePattern encodeBinder decodeBinder encodeRest decodeRest)
open InferenceCettaWire.AuthoredRule InferenceCettaWire.ContextObservation

private def natural? : Term → Option Nat
  | .natural value => some value
  | _ => none

private def string? : Term → Option String
  | .string value => some value
  | _ => none

@[simp] private theorem natural_roundtrip (value : Nat) : natural? (.natural value) = some value := rfl

@[simp] private theorem string_roundtrip (value : String) : string? (.string value) = some value := rfl

@[simp] private theorem naturals_roundtrip (values : List Nat) :
    decodeList natural? (encodeList .natural values) = some values :=
  decodeList_encodeList natural? .natural natural_roundtrip values

@[simp] private theorem strings_roundtrip (values : List String) :
    decodeList string? (encodeList .string values) = some values :=
  decodeList_encodeList string? .string string_roundtrip values

private def optional? {α : Type} (read : Term → Option α) : Term → Option (Option α)
  | .symbol "None" => some none
  | .application "Some" [value] => (read value).map some
  | _ => none

@[simp] private theorem optional_roundtrip {α : Type} (write : α → Term) (read : Term → Option α)
    (roundtrip : ∀ value, read (write value) = some value) (value : Option α) :
    optional? read (encodeOption write value) = some value := by
  cases value <;> simp [optional?, encodeOption, roundtrip]

@[simp] private theorem optional_natural_roundtrip (value : Option Nat) :
    optional? natural? (encodeOption .natural value) = some value :=
  optional_roundtrip .natural natural? natural_roundtrip value

/-- The existing physical occurrence representation, including its original zipper. -/
def occurrenceTerm (value : SourceOccurrence) : Term :=
  .application "AlgebraSourceOccurrence"
    [encodePattern value.original, encodeList .natural value.address,
      contextTerm value.context, encodePattern value.value]

def occurrence? : Term → Option SourceOccurrence
  | .application "AlgebraSourceOccurrence" [original, address, context, value] => do
      pure ⟨← decodePattern original, ← decodeList natural? address,
        ← decodeContext? context, ← decodePattern value⟩
  | _ => none

@[simp] theorem occurrence_roundtrip (value : SourceOccurrence) :
    occurrence? (occurrenceTerm value) = some value := by
  cases value
  simp [occurrence?, occurrenceTerm]

def allocationTerm (value : List (List SourceOccurrence) × List SourceOccurrence) : Term :=
  .application "GroupingAllocation"
    [encodeList (encodeList occurrenceTerm) value.1, encodeList occurrenceTerm value.2]

def allocation? : Term → Option (List (List SourceOccurrence) × List SourceOccurrence)
  | .application "GroupingAllocation" [groups, residual] => do
      pure (← decodeList (decodeList occurrence?) groups, ← decodeList occurrence? residual)
  | _ => none

@[simp] theorem allocation_roundtrip (value : List (List SourceOccurrence) × List SourceOccurrence) :
    allocation? (allocationTerm value) = some value := by
  cases value
  simp [allocation?, allocationTerm, decodeList_encodeList]

def focusTerm : Focus → Term
  | .original bound expected source context => .application "ViewOriginal"
      [encodeList typeTerm bound, typeTerm expected, encodePattern source, contextTerm context]
  | .grouped bound components => .application "ViewGrouped"
      [encodeList typeTerm bound, encodeList occurrenceTerm components]

def focus? : Term → Option Focus
  | .application "ViewOriginal" [bound, expected, source, context] => do
      pure (.original (← decodeList decodeType? bound) (← decodeType? expected)
        (← decodePattern source) (← decodeContext? context))
  | .application "ViewGrouped" [bound, components] => do
      pure (.grouped (← decodeList decodeType? bound) (← decodeList occurrence? components))
  | _ => none

@[simp] theorem focus_roundtrip (value : Focus) : focus? (focusTerm value) = some value := by
  cases value <;> simp [focusTerm, focus?, decodeList_encodeList]

def frameTerm (value : Frame) : Term :=
  .application "ViewFrame" [encodeList .natural value.path, encodeList typeTerm value.schemaBound,
    focusTerm value.focus, encodeOption .natural value.declaration, encodeOption allocationTerm value.grouping]

def frame? : Term → Option Frame
  | .application "ViewFrame" [path, bound, focus, declaration, grouping] => do
      pure ⟨← decodeList natural? path, ← decodeList decodeType? bound, ← focus? focus,
        ← optional? natural? declaration, ← optional? allocation? grouping⟩
  | _ => none

@[simp] theorem frame_roundtrip (value : Frame) : frame? (frameTerm value) = some value := by
  cases value
  simp [frameTerm, frame?, decodeList_encodeList]

def spellingTerm (value : Spelling) : Term :=
  .application "ViewSpelling" [encodePattern value.target, encodeList frameTerm value.frames]

def spelling? : Term → Option Spelling
  | .application "ViewSpelling" [target, frames] => do
      pure ⟨← decodePattern target, ← decodeList frame? frames⟩
  | _ => none

@[simp] theorem spelling_roundtrip (value : Spelling) :
    spelling? (spellingTerm value) = some value := by
  cases value
  simp [spellingTerm, spelling?, decodeList_encodeList]

def valueTerm : {kind : Kind} → Value kind → Term
  | .spelling, value => spellingTerm value
  | .children, value => .application "ViewChildren"
      [encodeList encodePattern value.1, encodeList frameTerm value.2]

def value? : (kind : Kind) → Term → Option (Value kind)
  | .spelling, term => spelling? term
  | .children, .application "ViewChildren" [patterns, frames] => do
      pure (← decodeList decodePattern patterns, ← decodeList frame? frames)
  | .children, _ => none

@[simp] theorem value_roundtrip {kind : Kind} (value : Value kind) :
    value? kind (valueTerm value) = some value := by
  cases kind with
  | spelling => exact spelling_roundtrip value
  | children => cases value; simp [valueTerm, value?, decodeList_encodeList]

def queryTerm : {kind : Kind} → Query kind → Term
  | _, .at bound path schema focus => .application "ViewAt"
      [encodeList typeTerm bound, encodeList .natural path, encodePattern schema, focusTerm focus]
  | _, .arguments schemaBound path bound label outer originals index schemas sources parameters =>
      .application "ViewArguments" [encodeList typeTerm schemaBound, encodeList .natural path,
        encodeList typeTerm bound, .string label, encodeOption contextTerm outer,
        encodeList encodePattern originals, .natural index, encodeList encodePattern schemas,
        encodeList encodePattern sources, encodeList parameterTerm parameters]
  | _, .groups schemaBound path bound index schemas groups => .application "ViewGroups"
      [encodeList typeTerm schemaBound, encodeList .natural path, encodeList typeTerm bound,
        .natural index, encodeList encodePattern schemas, encodeList (encodeList occurrenceTerm) groups]

def query? : (kind : Kind) → Term → Option (Query kind)
  | .spelling, .application "ViewAt" [bound, path, schema, focus] => do
      pure (.at (← decodeList decodeType? bound) (← decodeList natural? path)
        (← decodePattern schema) (← focus? focus))
  | .children, .application "ViewArguments"
      [schemaBound, path, bound, .string label, outer, originals, .natural index, schemas, sources, parameters] => do
      pure (.arguments (← decodeList decodeType? schemaBound) (← decodeList natural? path)
        (← decodeList decodeType? bound) label (← optional? decodeContext? outer)
        (← decodeList decodePattern originals) index (← decodeList decodePattern schemas)
        (← decodeList decodePattern sources) (← decodeList decodeParameter? parameters))
  | .children, .application "ViewGroups" [schemaBound, path, bound, .natural index, schemas, groups] => do
      pure (.groups (← decodeList decodeType? schemaBound) (← decodeList natural? path)
        (← decodeList decodeType? bound) index (← decodeList decodePattern schemas)
        (← decodeList (decodeList occurrence?) groups))
  | _, _ => none

@[simp] theorem query_roundtrip {kind : Kind} (query : Query kind) :
    query? kind (queryTerm query) = some query := by
  cases query <;> simp [queryTerm, query?, decodeList_encodeList]

def continuationTerm : {kind : Kind} → Continuation kind → Term
  | _, .done => .symbol "ViewDone"
  | _, .application parent label next => .application "ViewApplication"
      [frameTerm parent, .string label, continuationTerm next]
  | _, .collection parent residual next => .application "ViewCollection"
      [frameTerm parent, encodeList occurrenceTerm residual, continuationTerm next]
  | _, .lambda parent binder next => .application "ViewLambda"
      [frameTerm parent, encodeBinder binder, continuationTerm next]
  | _, .multiLambda parent arity binders next => .application "ViewMultiLambda"
      [frameTerm parent, .natural arity, encodeList .string binders, continuationTerm next]
  | _, .tail query next => .application "ViewTail" [queryTerm query, continuationTerm next]
  | _, .prepend head next => .application "ViewPrepend" [spellingTerm head, continuationTerm next]

def continuation? : (kind : Kind) → Term → Option (Continuation kind)
  | .spelling, .symbol "ViewDone" => some .done
  | .children, .application "ViewApplication" [parent, .string label, next] => do
      pure (.application (← frame? parent) label (← continuation? .spelling next))
  | .children, .application "ViewCollection" [parent, residual, next] => do
      pure (.collection (← frame? parent) (← decodeList occurrence? residual) (← continuation? .spelling next))
  | .spelling, .application "ViewLambda" [parent, binder, next] => do
      pure (.lambda (← frame? parent) (← decodeBinder binder) (← continuation? .spelling next))
  | .spelling, .application "ViewMultiLambda" [parent, .natural arity, binders, next] => do
      pure (.multiLambda (← frame? parent) arity (← decodeList string? binders)
        (← continuation? .spelling next))
  | .spelling, .application "ViewTail" [query, next] => do
      pure (.tail (← query? .children query) (← continuation? .children next))
  | .children, .application "ViewPrepend" [head, next] => do
      pure (.prepend (← spelling? head) (← continuation? .children next))
  | _, _ => none
termination_by _ term => sizeOf term

@[simp] theorem continuation_roundtrip {kind : Kind} (value : Continuation kind) :
    continuation? kind (continuationTerm value) = some value := by
  induction value <;> simp_all [continuationTerm, continuation?, decodeList_encodeList]

theorem focusTerm_injective : Function.Injective focusTerm := by
  intro first second same
  simpa only [focus_roundtrip, Option.some.injEq] using congrArg focus? same

theorem frameTerm_injective : Function.Injective frameTerm := by
  intro first second same
  simpa only [frame_roundtrip, Option.some.injEq] using congrArg frame? same

theorem queryTerm_injective {kind : Kind} : Function.Injective (@queryTerm kind) := by
  intro first second same
  simpa only [query_roundtrip, Option.some.injEq] using congrArg (query? kind) same

theorem continuationTerm_injective {kind : Kind} : Function.Injective (@continuationTerm kind) := by
  intro first second same
  simpa only [continuation_roundtrip, Option.some.injEq] using congrArg (continuation? kind) same

/-- An empty local body cannot erase the types of its enclosing binders. -/
theorem distinct_bound_sorts_remain_distinct (first second : TypeExpr) (different : first ≠ second)
    (source : Pattern) (context : OneHoleContext) :
    focusTerm (.original [first] first source context) ≠
      focusTerm (.original [second] first source context) := by
  intro same
  have equal := focusTerm_injective same
  cases equal
  exact different rfl

theorem spelling_refuses_children (value : Value .children) :
    value? .spelling (valueTerm value) = none := by
  cases value
  rfl

theorem children_refuse_spelling (value : Spelling) :
    value? .children (spellingTerm value) = none := rfl

theorem continuation_refuses_wrong_done : continuation? .children (.symbol "ViewDone") = none := by
  simp [continuation?]

def workTerm : GroupedCursor.Work → Term
  | .groups slots closed selected remaining => .application "GroupingGroups"
      [.natural slots, encodeList (encodeList occurrenceTerm) closed,
        encodeList occurrenceTerm selected, encodeList occurrenceTerm remaining]
  | .selectGroup slots closed selected remaining cursor => .application "GroupingSelectGroup"
      [.natural slots, encodeList (encodeList occurrenceTerm) closed,
        encodeList occurrenceTerm selected, encodeList occurrenceTerm remaining, .natural cursor]
  | .residual closed selected remaining => .application "GroupingResidual"
      [encodeList (encodeList occurrenceTerm) closed,
        encodeList occurrenceTerm selected, encodeList occurrenceTerm remaining]
  | .selectResidual closed selected remaining cursor => .application "GroupingSelectResidual"
      [encodeList (encodeList occurrenceTerm) closed,
        encodeList occurrenceTerm selected, encodeList occurrenceTerm remaining, .natural cursor]

def work? : Term → Option GroupedCursor.Work
  | .application "GroupingGroups" [.natural slots, closed, selected, remaining] => do
      pure (.groups slots (← decodeList (decodeList occurrence?) closed)
        (← decodeList occurrence? selected) (← decodeList occurrence? remaining))
  | .application "GroupingSelectGroup" [.natural slots, closed, selected, remaining, .natural cursor] => do
      pure (.selectGroup slots (← decodeList (decodeList occurrence?) closed)
        (← decodeList occurrence? selected) (← decodeList occurrence? remaining) cursor)
  | .application "GroupingResidual" [closed, selected, remaining] => do
      pure (.residual (← decodeList (decodeList occurrence?) closed)
        (← decodeList occurrence? selected) (← decodeList occurrence? remaining))
  | .application "GroupingSelectResidual" [closed, selected, remaining, .natural cursor] => do
      pure (.selectResidual (← decodeList (decodeList occurrence?) closed)
        (← decodeList occurrence? selected) (← decodeList occurrence? remaining) cursor)
  | _ => none

@[simp] theorem work_roundtrip (value : GroupedCursor.Work) : work? (workTerm value) = some value := by
  cases value <;> simp [workTerm, work?, decodeList_encodeList]

def cursorTerm (value : GroupedCursor.State) : Term :=
  .application "GroupingState" [encodeList workTerm value.agenda, encodeList allocationTerm value.answers]

def cursor? : Term → Option GroupedCursor.State
  | .application "GroupingState" [agenda, answers] => do
      pure ⟨← decodeList work? agenda, ← decodeList allocation? answers⟩
  | _ => none

@[simp] theorem cursor_roundtrip (value : GroupedCursor.State) : cursor? (cursorTerm value) = some value := by
  cases value
  simp [cursorTerm, cursor?, decodeList_encodeList]

private def kindTerm : Kind → Term
  | .spelling => .symbol "ViewSpellingKind"
  | .children => .symbol "ViewChildrenKind"

private def kind? : Term → Option Kind
  | .symbol "ViewSpellingKind" => some .spelling
  | .symbol "ViewChildrenKind" => some .children
  | _ => none

@[simp] private theorem kind_roundtrip (kind : Kind) : kind? (kindTerm kind) = some kind := by
  cases kind <;> rfl

def taskTerm : Task → Term
  | .request (kind := kind) query next => .application "ViewRequest"
      [kindTerm kind, queryTerm query, continuationTerm next]
  | .returned (kind := kind) value next => .application "ViewReturned"
      [kindTerm kind, valueTerm value, continuationTerm next]
  | .constructors schemaBound path focus label schemas sources outer ordinal remaining next =>
      .application "ViewConstructors" [encodeList typeTerm schemaBound, encodeList .natural path,
        focusTerm focus, .string label, encodeList encodePattern schemas, encodeList encodePattern sources,
        encodeOption contextTerm outer, .natural ordinal,
        encodeList ModuleAlgebra.NativeAuthoring.Wire.grammarRule remaining, continuationTerm next]
  | .allocations schemaBound path focus schemas rest cursor published _ next =>
      .application "ViewAllocations" [encodeList typeTerm schemaBound, encodeList .natural path,
        focusTerm focus, encodeList encodePattern schemas, encodeRest rest,
        cursorTerm cursor, .natural published, continuationTerm next]

def task? : Term → Option Task
  | .application "ViewRequest" [kind, query, next] => do
      let kind ← kind? kind
      pure (.request (← query? kind query) (← continuation? kind next))
  | .application "ViewReturned" [kind, value, next] => do
      let kind ← kind? kind
      pure (.returned (← value? kind value) (← continuation? kind next))
  | .application "ViewConstructors"
      [schemaBound, path, focus, .string label, schemas, sources, outer, .natural ordinal, remaining, next] => do
      pure (.constructors (← decodeList decodeType? schemaBound) (← decodeList natural? path)
        (← focus? focus) label (← decodeList decodePattern schemas) (← decodeList decodePattern sources)
        (← optional? decodeContext? outer) ordinal
        (← decodeList ModuleAlgebra.NativeAuthoring.Wire.grammarRule? remaining) (← continuation? .spelling next))
  | .application "ViewAllocations" [schemaBound, path, focus, schemas, rest, cursor, .natural published, next] => do
      let schemaBound ← decodeList decodeType? schemaBound
      let path ← decodeList natural? path
      let focus ← focus? focus
      let schemas ← decodeList decodePattern schemas
      let rest ← decodeRest rest
      let cursor ← cursor? cursor
      let next ← continuation? .spelling next
      if within : published ≤ cursor.answers.length then
        pure (.allocations schemaBound path focus schemas rest cursor published within next)
      else none
  | _ => none

@[simp] theorem task_roundtrip (value : Task) : task? (taskTerm value) = some value := by
  cases value <;> simp [taskTerm, task?, decodeList_encodeList, *]

theorem taskTerm_injective : Function.Injective taskTerm := by
  intro first second same
  simpa only [task_roundtrip, Option.some.injEq] using congrArg task? same

def expansionTerm (value : List Task × List Spelling) : Term :=
  .application "ViewExpansion" [encodeList taskTerm value.1, encodeList spellingTerm value.2]

def expansion? : Term → Option (List Task × List Spelling)
  | .application "ViewExpansion" [tasks, answers] => do
      pure (← decodeList task? tasks, ← decodeList spelling? answers)
  | _ => none

@[simp] theorem expansion_roundtrip (value : List Task × List Spelling) :
    expansion? (expansionTerm value) = some value := by
  cases value
  simp [expansionTerm, expansion?, decodeList_encodeList]

theorem expansionTerm_injective : Function.Injective expansionTerm := by
  intro first second same
  simpa only [expansion_roundtrip, Option.some.injEq] using congrArg expansion? same

def stateTerm (value : State) : Term :=
  .application "ViewState" [encodeList taskTerm value.agenda, encodeList spellingTerm value.answers]

def state? : Term → Option State
  | .application "ViewState" [agenda, answers] => do
      pure ⟨← decodeList task? agenda, ← decodeList spelling? answers⟩
  | _ => none

@[simp] theorem state_roundtrip (value : State) : state? (stateTerm value) = some value := by
  cases value
  simp [stateTerm, state?, decodeList_encodeList]

theorem stateTerm_injective : Function.Injective stateTerm := by
  intro first second same
  simpa only [state_roundtrip, Option.some.injEq] using congrArg state? same

/-- A publication cursor cannot claim that an answer beyond its complete account was already read. -/
theorem allocation_refuses_unearned_publication (schemaBound : List TypeExpr) (path : List Nat)
    (focus : Focus) (schemas : List Pattern) (rest : Option String) (cursor : GroupedCursor.State)
    (published : Nat) (next : Continuation .spelling) (outside : ¬ published ≤ cursor.answers.length) :
    task? (.application "ViewAllocations" [encodeList typeTerm schemaBound, encodeList .natural path,
      focusTerm focus, encodeList encodePattern schemas, encodeRest rest,
      cursorTerm cursor, .natural published, continuationTerm next]) = none := by
  simp [task?, decodeList_encodeList, outside]

theorem constructor_representation_is_retained (row : GrammarRule) :
    ModuleAlgebra.NativeAuthoring.Wire.grammarRule {row with collectionRepresentation := .bare} ≠
      ModuleAlgebra.NativeAuthoring.Wire.grammarRule {row with collectionRepresentation := .wrapped} := by
  simp [ModuleAlgebra.NativeAuthoring.Wire.grammarRule]

#print axioms task_roundtrip
#print axioms taskTerm_injective
#print axioms expansion_roundtrip
#print axioms expansionTerm_injective
#print axioms state_roundtrip
#print axioms stateTerm_injective
#print axioms allocation_refuses_unearned_publication
#print axioms constructor_representation_is_retained

#print axioms occurrence_roundtrip
#print axioms allocation_roundtrip
#print axioms frame_roundtrip
#print axioms value_roundtrip
#print axioms query_roundtrip
#print axioms continuation_roundtrip
#print axioms continuationTerm_injective
#print axioms distinct_bound_sorts_remain_distinct
#print axioms spelling_refuses_children
#print axioms children_refuse_spelling
#print axioms continuation_refuses_wrong_done

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedWire
