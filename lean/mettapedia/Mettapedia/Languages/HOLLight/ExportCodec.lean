import Mettapedia.Languages.HOLLight.ExportReplay
import Mettapedia.Languages.HOLLight.ModelInterpretation

/-!
# Structured source exports through the registered HOL calculus

The codec constructs untrusted requests from the structured HOL Light export.
Receiving those requests calls `ExportReplay.apply`; syntax decoding itself
does not authorize a theorem. Constants and type operators are resolved to
the actual provenance-bearing declarations produced by earlier admissions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ExportCodec

open Mettapedia.Languages.OpenTheory Mettapedia.Logic Lean
open ProofExecution DefinitionAdapters SignatureFormation ExportReplay

structure Symbols where
  operators : List (String × TypeOp)
  constants : List (String × Const)

inductive Value where
  | text (value : String)
  | natural (value : Nat)
  | items (values : List Value)
  | type (value : Ty)
  | term (value : SourceTerm)

def Value.type? : Value → Option Ty
  | .type value => some value
  | _ => none

def Value.term? : Value → Option SourceTerm
  | .term value => some value
  | _ => none

def arrayValue (symbols : Symbols) (values : List Value) : Option Value :=
  match values with
  | [.text "var", .text name] => some (.type (.var (Name.global name)))
  | [.text "op", .text name, .items arguments] => do
    let operator ← List.lookup name symbols.operators
    let types ← arguments.mapM Value.type?
    pure (.type (.op operator types))
  | [.text "var", .text name, .type type] =>
    some (.term (.var (Name.global name) type))
  | [.text "const", .text name, .type type] => do
    let constant ← List.lookup name symbols.constants
    pure (.term (.const constant type))
  | [.text "app", .term function, .term argument] =>
    some (.term (.app function argument))
  | [.text "abs", .term (.var name type), .term body] =>
    some (.term (.abs name type body))
  | _ => some (.items values)

/-- Structural recursion accepts arbitrary finite syntax; there is no fixed
term-depth or proof-size limit in the decoder. -/
def decodeValue (symbols : Symbols) : Json → Option Value
  | .str string => some (.text string)
  | .num number => (Json.num number).getNat?.toOption.map Value.natural
  | .arr values => do
    let decoded ← values.toList.attach.mapM (fun value => decodeValue symbols value.val)
    arrayValue symbols decoded
  | _ => none
termination_by value => sizeOf value
decreasing_by
  simp_wf
  have smaller := Array.sizeOf_lt_of_mem
    (show value.val ∈ values from by simpa using value.property)
  omega

def sourceTerm? (symbols : Symbols) (json : Json) : Option SourceTerm := do
  (← decodeValue symbols json).term?

def sourceType? (symbols : Symbols) (json : Json) : Option Ty := do
  (← decodeValue symbols json).type?

def canonical? (symbols : Symbols) (json : Json) : Option CanonicalTerm := do
  (← sourceTerm? symbols json).check

def checked? (symbols : Symbols) (json : Json) : Option CheckedSourceTerm := do
  checkedSource? (← sourceTerm? symbols json)

def field? (json : Json) (name : String) : Option Json := (json.getObjVal? name).toOption
def at? (json : Json) (index : Nat) : Option Json := (json.getArrVal? index).toOption
def string? (json : Json) : Option String := json.getStr?.toOption
def natural? (json : Json) : Option Nat := json.getNat?.toOption
def array? (json : Json) : Option (List Json) := json.getArr?.toOption.map Array.toList

def sequent? (symbols : Symbols) (json : Json) : Option (Sequent × SourceTerm) := do
  let hypotheses ← array? (← field? json "hypotheses")
  let hypotheses ← hypotheses.mapM (canonical? symbols)
  let source ← sourceTerm? symbols (← field? json "conclusion")
  let conclusion ← source.check
  let sequent ← Sequent.ofObjectTerms? hypotheses conclusion
  pure (sequent, source)

structure State where
  received : ExportReplay.State
  symbols : Symbols
  sourceConclusions : Std.TreeMap Nat SourceTerm := {}
  sourceOrigin : String := "hol-light-export"

def premise? (state : State) (json : Json) : Option (Nat × Nat × Theorem) := do
  let id ← natural? json
  let index ← state.received.addresses.get? id
  let fact ← state.received.registered.cache[index]?
  pure (id, index, fact)

def termMaplet? (symbols : Symbols) (json : Json) : Option SourceSubstitution.TermMaplet := do
  match ← array? json with
  | [replacement, key] => pure (← checked? symbols replacement, ← sourceTerm? symbols key)
  | _ => none

def typeMaplet? (symbols : Symbols) (json : Json) : Option (Ty × Ty) := do
  match ← array? json with
  | [replacement, key] => pure (← sourceType? symbols replacement, ← sourceType? symbols key)
  | _ => none

/-- All ten source inference requests are constructed for the same calculus
as authored proofs. Ordered parent occurrences are not deduplicated. -/
def inference? (state : State) (rule : String) (arguments : List Json) :
    Option (List Nat × List Nat × InferenceRequest) := do
  match rule, arguments with
  | "REFL", [term] => pure ([], [], .refl (← canonical? state.symbols term))
  | "BETA", [term] => pure ([], [], .beta (← checked? state.symbols term))
  | "ASSUME", [term] => pure ([], [], .assume (← canonical? state.symbols term))
  | "TRANS", [left, right] | "MK_COMB", [left, right] |
      "EQ_MP", [left, right] | "DEDUCT_ANTISYM_RULE", [left, right] =>
    let (leftId, leftIndex, left) ← premise? state left
    let (rightId, rightIndex, right) ← premise? state right
    let request := if rule = "TRANS" then .trans left right
      else if rule = "MK_COMB" then .mkComb left right
      else if rule = "EQ_MP" then .eqMp left right else .deductAntisym left right
    pure ([leftId, rightId], [leftIndex, rightIndex], request)
  | "ABS", [input, binder] =>
    let (id, index, input) ← premise? state input
    match ← sourceTerm? state.symbols binder with
    | .var name type => pure ([id], [index], .abs ⟨name, type⟩ input)
    | _ => none
  | "INST", [input, entries] =>
    let (id, index, input) ← premise? state input
    let entries ← (← array? entries).mapM (termMaplet? state.symbols)
    pure ([id], [index], .inst entries input)
  | "INST_TYPE", [input, entries] =>
    let (id, index, input) ← premise? state input
    let entries ← (← array? entries).mapM (typeMaplet? state.symbols)
    pure ([id], [index], .instType entries input)
  | _, _ => none

structure Prepared where
  event : Event
  symbols : Symbols
  sourceConclusions : List SourceTerm

def proof? (state : State)
    (id : Nat) (rule : String) (arguments : List Json) (claim : Json) : Option Prepared := do
  let (sourceParents, parents, request) ← inference? state rule arguments
  let actual ← request.check
  let (sequent, source) ← sequent? state.symbols claim
  let node : Receipt := ⟨actual, .inference request, parents, (state.sourceOrigin, id)⟩
  pure ⟨⟨[id], sourceParents,
      .proof node (instanceCertificates state.received.registered.context.signature), [sequent]⟩,
    state.symbols, [source]⟩

def axiom? (policy : AxiomPolicy) [DecidablePred policy] (state : State)
    (id : Nat) (arguments : List Json) (claim : Json) : Option Prepared := do
  match arguments with
  | [term] =>
    let term ← canonical? state.symbols term
    let sequent : Sequent := ⟨∅, term⟩
    let request := RuleRequest.axiom sequent
    let actual ← request.check policy
    let (claim, source) ← sequent? state.symbols claim
    let node : Receipt := ⟨actual, request, [], (state.sourceOrigin, id)⟩
    pure ⟨⟨[id], [],
        .proof node (instanceCertificates state.received.registered.context.signature), [claim]⟩,
      state.symbols, [source]⟩
  | _ => none

def definitionBody? (json : Json) : Option Json := do
  match ← array? json with
  | [tag, function, right] =>
    if (← string? tag) ≠ "app" then none else do
      match ← array? function with
      | [tag, equality, _] =>
        if (← string? tag) ≠ "app" then none else do
          match ← array? equality with
          | [tag, name, _] =>
            if (← string? tag) = "const" ∧ (← string? name) = "=" then some right else none
          | _ => none
      | _ => none
  | _ => none

def constant? (state : State) (id : Nat) (arguments : List Json) (claim : Json) :
    Option Prepared := do
  match arguments with
  | [equation, name, annotation] =>
    let name ← string? name
    let annotation ← sourceType? state.symbols annotation
    let body ← sourceTerm? state.symbols (← definitionBody? equation)
    let before := state.received.registered.context
    let defined ← admitConstantInTheory before (instanceCertificates before.signature)
      (Name.global name) body
    if Ty.same defined.output.definitionTheorem.sequent.concl.ty Ty.bool ≠ true then none else do
      let symbols : Symbols := { state.symbols with
        constants := (name, defined.output.constant) :: state.symbols.constants }
      let actualBody ← checkedSource? body
      if Ty.same actualBody.ty annotation ≠ true then none else do
        let (claim, source) ← sequent? symbols claim
        let argument ← canonical? symbols equation
        if argument.same claim.concl ≠ true then none else
          pure ⟨⟨[id], [], .constant (state.sourceOrigin, id) (Name.global name) body
              (instanceCertificates defined.context.signature), [claim]⟩, symbols, [source]⟩
  | _ => none

/-- The normalizer groups the two source results of one type-definition
operation. Both conclusions are still independently compared after replay. -/
def typeDefinition? (state : State) (id mate : Nat) (arguments : List Json)
    (claims : List Json) : Option Prepared := do
  match arguments, claims with
  | [existence, typeName, absName, repName], [absClaim, repClaim] =>
    let (parentId, parentIndex, existence) ← premise? state existence
    let existenceSource ← state.sourceConclusions.get? parentId
    let predicate ← match existenceSource with
      | .app predicate _ => some predicate
      | _ => none
    let typeName ← string? typeName
    let absName ← string? absName
    let repName ← string? repName
    let request : TypeOperatorDefinitionRequest :=
      ⟨sourceOperatorName (Name.global typeName), Name.global absName, Name.global repName,
        sortedParameters predicate, predicate, existence⟩
    let before := state.received.registered.context
    let defined ← admitSourceTypeInTheory before (instanceCertificates before.signature) request
    let symbols : Symbols :=
      ⟨(typeName, defined.core.output.typeOperator) :: state.symbols.operators,
        (absName, defined.core.output.abstractionConstant) ::
        (repName, defined.core.output.representationConstant) :: state.symbols.constants⟩
    let (absClaim, absSource) ← sequent? symbols absClaim
    let (repClaim, repSource) ← sequent? symbols repClaim
    pure ⟨⟨[id, mate], [parentId],
        .typeDefinition (state.sourceOrigin, id) request parentIndex
          (instanceCertificates defined.context.signature), [absClaim, repClaim]⟩,
      symbols, [absSource, repSource]⟩
  | _, _ => none

def prepare? (policy : AxiomPolicy) [DecidablePred policy] (state : State) (json : Json) :
    Option Prepared := do
  let id ← natural? (← field? json "id")
  let rule ← string? (← field? json "rule")
  let arguments ← array? (← field? json "arguments")
  if rule = "TYPE_DEFINITION_PAIR" then
    typeDefinition? state id (← natural? (← field? json "mate")) arguments
      (← array? (← field? json "theorems"))
  else do
    let claim ← field? json "theorem"
    if rule = "DEFINITION" then constant? state id arguments claim
    else if rule = "AXIOM" then axiom? policy state id arguments claim
    else proof? state id rule arguments claim

def addConclusions (table : Std.TreeMap Nat SourceTerm) :
    List Nat → List SourceTerm → Std.TreeMap Nat SourceTerm
  | id :: ids, source :: sources => addConclusions (table.insert id source) ids sources
  | _, _ => table

def receive? (policy : AxiomPolicy) [DecidablePred policy] (before : State) (json : Json) :
    Option State := do
  let prepared ← prepare? policy before json
  let received ← ExportReplay.apply policy before.received prepared.event
  pure ⟨received, prepared.symbols,
    addConclusions before.sourceConclusions prepared.event.sourceIds prepared.sourceConclusions,
    before.sourceOrigin⟩

/-- JSON decoding cannot bypass the registered source execution relation. -/
theorem receive?_checked (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {json : Json}
    (accepted : receive? policy before json = some after) :
    ∃ event, ExportReplay.apply policy before.received event = some after.received := by
  unfold receive? at accepted
  cases prepared : prepare? policy before json with
  | none => simp [prepared] at accepted
  | some packet =>
    simp only [prepared, bind, Option.bind] at accepted
    cases received : ExportReplay.apply policy before.received packet.event with
    | none => simp [received] at accepted
    | some checked =>
      have equal := Option.some.inj (by simpa [received] using accepted)
      subst after
      exact ⟨packet.event, received⟩

theorem receive?_preserves_derivations (policy : AxiomPolicy) [DecidablePred policy]
    {before after : State} {json : Json} (valid : ExportReplay.Valid policy before.received)
    (accepted : receive? policy before json = some after) :
    ExportReplay.Valid policy after.received := by
  obtain ⟨event, checked⟩ := receive?_checked policy accepted
  exact ExportReplay.apply_preserves_derivations policy valid checked

def receiveMany? (policy : AxiomPolicy) [DecidablePred policy] :
    State → List Json → Option State
  | before, [] => some before
  | before, json :: rest => do
    let after ← receive? policy before json
    receiveMany? policy after rest

/-- Decoding an accepted finite closure constructs a finite history in the
existing proof-graph calculus, with one receipt per received source event. -/
theorem receiveMany?_to_replay (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (inputs : List Json) (after : State)
    (accepted : receiveMany? policy before inputs = some after) :
    ∃ events : List Event, events.length = inputs.length ∧
      ExportReplay.replayFrom policy before.received events = some after.received := by
  induction inputs generalizing before with
  | nil =>
    have equal := Option.some.inj accepted
    subst after
    exact ⟨[], rfl, rfl⟩
  | cons input inputs ih =>
    cases first : receive? policy before input with
    | none => simp [receiveMany?, first] at accepted
    | some middle =>
      have remaining : receiveMany? policy middle inputs = some after := by
        simpa [receiveMany?, first] using accepted
      obtain ⟨event, checked⟩ := receive?_checked policy first
      obtain ⟨events, length, replayed⟩ := ih middle remaining
      exact ⟨event :: events, by simp [length], by
        simpa [ExportReplay.replayFrom, checked] using replayed⟩

theorem receiveMany?_reachable (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (inputs : List Json) (after : State)
    (accepted : receiveMany? policy before inputs = some after) :
    (Registered.gslt policy).MultiStep before.received.registered after.received.registered := by
  obtain ⟨events, _, replayed⟩ := receiveMany?_to_replay policy before inputs after accepted
  exact ExportReplay.replayFrom_reachable policy before.received events after.received replayed

theorem receiveMany?_preserves_derivations (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (inputs : List Json) (after : State)
    (valid : ExportReplay.Valid policy before.received)
    (accepted : receiveMany? policy before inputs = some after) :
    ExportReplay.Valid policy after.received := by
  obtain ⟨events, _, replayed⟩ := receiveMany?_to_replay policy before inputs after accepted
  exact ExportReplay.replayFrom_preserves_derivations policy before.received events
    after.received valid replayed

/-- Imported roots retain actual derivations, assumptions and axiom
dependencies from replay. A printed root name is not a logical premise. -/
theorem received_root_derivation (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (inputs : List Json) (after : State)
    (valid : ExportReplay.Valid policy before.received)
    (accepted : receiveMany? policy before inputs = some after)
    {id : Nat} {claim : Sequent} {out : Theorem}
    (found : ExportReplay.root? after.received id claim = some out) :
    TheoryDerives policy after.received.registered.context out ∧ out.sequent = claim :=
  ExportReplay.root_derivation policy
    (receiveMany?_preserves_derivations policy before inputs after valid accepted) found

end Mettapedia.Languages.HOLLight.ExportCodec
