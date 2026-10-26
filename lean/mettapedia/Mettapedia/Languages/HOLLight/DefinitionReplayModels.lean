import Mettapedia.Languages.HOLLight.SourceProfile
import Mettapedia.Languages.HOLLight.DefinitionHistoryModels

/-!
# Models constructed from received constant definitions

Successful registered replay yields the original chronological definition
history and its exact ordered theorem outputs. The existing model extension
then constructs a model of every new equation at every type instance.

The same construction consumes the actual reference-definition computation
of the source-profile loader. It preserves carriers and full function domains
without assuming a final model or a semantic acceptance field. A profile's
additional axiom commitments require their own truth proofs. Carrier-changing
type definitions and implementation refinement are separate obligations.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.DefinitionReplayModels
open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open DefinitionAdapters SignatureFormation ProofExecution DefinitionHistoryModels
universe w

def isConstantDefinition : Registered.Command → Bool
  | .constant _ _ _ _ => true
  | _ => false

theorem constant_step {policy : AxiomPolicy} [DecidablePred policy]
    {before after : Registered.State} {origin : Origin} {name : Name}
    {body : SourceTerm} {instances : InstanceWitnesses}
    (accepted : Registered.apply policy before (.constant origin name body instances) = some after) :
    ∃ result : ContextConstantDefinitionResult,
      admitConstantInTheory before.context instances name body = some result ∧
      after.context = result.context ∧
      after.cache.toList = before.cache.toList ++ [result.output.definitionTheorem] := by
  cases admitted : admitConstantInTheory before.context instances name body with
  | none => simp [Registered.apply, Registered.Command.check, admitted] at accepted
  | some result =>
    cases formed : theoremFormedB result.context.signature instances result.output.definitionTheorem with
    | false => simp [Registered.apply, Registered.Command.check, admitted, formed] at accepted
    | true =>
      have same : (⟨result.context, before.cache ++ #[result.output.definitionTheorem],
          before.receipts.push ⟨.constant origin name body instances, [result.output.definitionTheorem]⟩⟩ : Registered.State) = after := by
        simpa [Registered.apply, Registered.Command.check, admitted, formed] using accepted
      cases same
      exact ⟨result, rfl, rfl, by simp⟩

private theorem records_cast {initial first second : TheoryContext}
    (same : first = second) (history : ConstantHistory initial first) :
    (same ▸ history).records = history.records := by
  cases same
  rfl

theorem replay_constant_history {policy : AxiomPolicy} [DecidablePred policy]
    (before : Registered.State) (commands : List Registered.Command) (after : Registered.State)
    (constants : ∀ command ∈ commands, isConstantDefinition command = true)
    (accepted : Registered.replayFrom policy before commands = some after) :
    ∃ history : ConstantHistory before.context after.context,
      after.cache.toList = before.cache.toList ++
        (history.records.map fun result => result.output.definitionTheorem) := by
  induction commands generalizing before with
  | nil =>
    cases Option.some.inj accepted
    exact ⟨.nil, by simp [ConstantHistory.records]⟩
  | cons command commands ih =>
    cases head : Registered.apply policy before command with
    | none => simp [Registered.replayFrom, head] at accepted
    | some middle =>
      have tail : Registered.replayFrom policy middle commands = some after := by
        simpa [Registered.replayFrom, head] using accepted
      obtain ⟨restHistory, restCache⟩ := ih middle
        (fun command member => constants command (by simp [member])) tail
      have only := constants command (by simp)
      cases command with
      | proof => simp [isConstantDefinition] at only
      | typeDefinition => simp [isConstantDefinition] at only
      | constant origin name body instances =>
        obtain ⟨result, admitted, context, cache⟩ := constant_step head
        let firstBase : ConstantHistory before.context result.context :=
          ConstantHistory.snoc ConstantHistory.nil instances name body result admitted
        let first : ConstantHistory before.context middle.context := context.symm ▸ firstBase
        have firstRecords : first.records = [result] :=
          (records_cast context.symm firstBase).trans rfl
        refine ⟨first.append restHistory, ?_⟩
        rw [ConstantHistory.records_append, firstRecords, List.map_append]
        rw [restCache, cache]
        simp [List.append_assoc]

theorem replay_constant_models {policy : AxiomPolicy} [DecidablePred policy]
    (before : Registered.State) (commands : List Registered.Command) (after : Registered.State)
    (constants : ∀ command ∈ commands, isConstantDefinition command = true)
    (accepted : Registered.replayFrom policy before commands = some after)
    (empty : before.cache = #[])
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    ∃ finalModel : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
      finalModel.Carrier = model.Carrier ∧
      (model.FullDomains → finalModel.FullDomains) ∧
      ∀ fact ∈ after.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
          finalModel.models formula := by
  obtain ⟨history, cache⟩ := replay_constant_history before commands after constants accepted
  refine ⟨history.extendModel model, history.carrier model, history.fullDomains model, ?_⟩
  intro fact member substitution
  have present : fact ∈ after.cache.toList := by simpa using member
  rw [cache, empty] at present
  simp only [List.nil_append, List.mem_map] at present
  obtain ⟨result, recorded, rfl⟩ := present
  exact history.record_equation_meaning model recorded substitution

private theorem codec_constant_prepared {state : ExportCodec.State} {id : Nat}
    {arguments : List Lean.Json} {claim : Lean.Json} {packet : ExportCodec.Prepared}
    (computed : ExportCodec.constant? state id arguments claim = some packet) :
    isConstantDefinition packet.event.command = true := by
  unfold ExportCodec.constant? at computed
  simp only [bind, Option.bind] at computed
  repeat' first | contradiction | ((try dsimp only at computed); split at computed)
  all_goals cases Option.some.inj computed; rfl

private theorem codec_definition_prepared {policy : AxiomPolicy} [DecidablePred policy]
    {state : ExportCodec.State} {json : Lean.Json} {packet : ExportCodec.Prepared}
    (tag : (ExportCodec.field? json "rule").bind ExportCodec.string? = some "DEFINITION")
    (computed : ExportCodec.prepare? policy state json = some packet) :
    isConstantDefinition packet.event.command = true := by
  cases ruleField : ExportCodec.field? json "rule" with
  | none => simp [ruleField] at tag
  | some ruleJson =>
    have ruleText : ExportCodec.string? ruleJson = some "DEFINITION" := by simpa [ruleField] using tag
    unfold ExportCodec.prepare? at computed
    simp only [ruleField, ruleText, bind, Option.bind] at computed
    repeat' first | contradiction | ((try dsimp only at computed); split at computed)
    all_goals exact codec_constant_prepared computed

private theorem codec_definition_event {policy : AxiomPolicy} [DecidablePred policy]
    {before after : ExportCodec.State} {json : Lean.Json}
    (tag : (ExportCodec.field? json "rule").bind ExportCodec.string? = some "DEFINITION")
    (accepted : ExportCodec.receive? policy before json = some after) :
    ∃ event : ExportReplay.Event, isConstantDefinition event.command = true ∧
      ExportReplay.apply policy before.received event = some after.received := by
  unfold ExportCodec.receive? at accepted
  cases prepared : ExportCodec.prepare? policy before json with
  | none => simp [prepared] at accepted
  | some packet =>
    simp only [prepared, bind, Option.bind] at accepted
    cases checked : ExportReplay.apply policy before.received packet.event with
    | none => simp [checked] at accepted
    | some received =>
      have same := Option.some.inj (by simpa [checked] using accepted)
      cases same
      exact ⟨packet.event, codec_definition_prepared tag prepared, checked⟩

theorem reference_definitions_events (before : ExportCodec.State)
    (inputs : List Lean.Json) (after : ExportCodec.State)
    (accepted : SourceProfile.referenceDefinitions? before inputs = some after) :
    ∃ events : List ExportReplay.Event,
      (∀ event ∈ events, isConstantDefinition event.command = true) ∧
      ExportReplay.replayFrom emptyAxiomPolicy before.received events = some after.received := by
  induction inputs generalizing before with
  | nil =>
    cases Option.some.inj accepted
    exact ⟨[], by simp, rfl⟩
  | cons input inputs ih =>
    unfold SourceProfile.referenceDefinitions? at accepted
    split at accepted
    · contradiction
    · rename_i tag
      have tagged : (ExportCodec.field? input "rule").bind ExportCodec.string? = some "DEFINITION" := by
        simpa only [not_not] using tag
      cases next : ExportCodec.receive? emptyAxiomPolicy before input with
      | none => simp [next] at accepted
      | some middle =>
        have tail : SourceProfile.referenceDefinitions? middle inputs = some after := by
          simpa [next] using accepted
        obtain ⟨event, constant, checked⟩ := codec_definition_event tagged next
        obtain ⟨events, constants, replayed⟩ := ih middle tail
        refine ⟨event :: events, ?_, ?_⟩
        · intro candidate member
          rcases List.mem_cons.mp member with rfl | member
          · exact constant
          · exact constants candidate member
        · simpa [ExportReplay.replayFrom, checked] using replayed

theorem replay_registered_commands {policy : AxiomPolicy} [DecidablePred policy]
    (before : ExportReplay.State) (events : List ExportReplay.Event) (after : ExportReplay.State)
    (accepted : ExportReplay.replayFrom policy before events = some after) :
    Registered.replayFrom policy before.registered (events.map ExportReplay.Event.command) = some after.registered := by
  induction events generalizing before with
  | nil => exact congrArg (Option.map ExportReplay.State.registered) accepted
  | cons event events ih =>
    cases first : ExportReplay.apply policy before event with
    | none => simp [ExportReplay.replayFrom, first] at accepted
    | some middle =>
      have tail : ExportReplay.replayFrom policy middle events = some after := by
        simpa [ExportReplay.replayFrom, first] using accepted
      have registered := (ExportReplay.apply_checked policy first).1
      simpa [Registered.replayFrom, registered] using ih middle tail

theorem reference_definitions_models (before : ExportCodec.State)
    (inputs : List Lean.Json) (after : ExportCodec.State)
    (accepted : SourceProfile.referenceDefinitions? before inputs = some after)
    (empty : before.received.registered.cache = #[])
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    ∃ finalModel : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
      finalModel.Carrier = model.Carrier ∧
      (model.FullDomains → finalModel.FullDomains) ∧
      ∀ fact ∈ after.received.registered.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
          finalModel.models formula := by
  obtain ⟨events, constants, checked⟩ := reference_definitions_events before inputs after accepted
  apply replay_constant_models before.received.registered (events.map ExportReplay.Event.command)
    after.received.registered _ (replay_registered_commands before.received events after.received checked) empty model
  intro command member
  obtain ⟨event, present, rfl⟩ := List.mem_map.mp member
  exact constants event present

private theorem loaded_reference {basis : ExportCodec.State} {document : Lean.Json}
    {profile : SourceProfile.Profile}
    (accepted : SourceProfile.load? basis document = some profile) :
    ∃ inputs, SourceProfile.referenceDefinitions? basis inputs = some profile.reference := by
  unfold SourceProfile.load? at accepted
  simp only [bind, Option.bind] at accepted
  repeat' first | contradiction | ((try dsimp only at accepted); split at accepted)
  all_goals cases Option.some.inj accepted; exact ⟨_, by assumption⟩

theorem loaded_reference_models {basis : ExportCodec.State} {document : Lean.Json}
    {profile : SourceProfile.Profile}
    (accepted : SourceProfile.load? basis document = some profile)
    (empty : basis.received.registered.cache = #[])
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    ∃ finalModel : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
      finalModel.Carrier = model.Carrier ∧
      (model.FullDomains → finalModel.FullDomains) ∧
      ∀ fact ∈ profile.reference.received.registered.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
          finalModel.models formula := by
  obtain ⟨inputs, computed⟩ := loaded_reference accepted
  exact reference_definitions_models basis inputs profile.reference computed empty model

namespace Controls

def identityBody : SourceTerm :=
  .abs (Name.global "x") Ty.bool (.var (Name.global "x") Ty.bool)

def identityName : Name := Name.global "replayedBooleanIdentity"
def aliasName : Name := Name.global "replayedBooleanIdentityAlias"
def identityConstant : Const := .mk identityName (.defined identityBody)
def identityType : Ty := Ty.function Ty.bool Ty.bool

def commands : List Registered.Command :=
  [.constant ("reference-definitions",0) identityName identityBody
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature),
   .constant ("reference-definitions",1) aliasName (.const identityConstant identityType)
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)]

def before : Registered.State := Registered.empty SourceProfile.primitiveContext

theorem commands_available :
    (Registered.replayFrom emptyAxiomPolicy before commands).isSome = true := by decide +kernel

def after : Registered.State :=
  (Registered.replayFrom emptyAxiomPolicy before commands).get commands_available

theorem commands_replayed : Registered.replayFrom emptyAxiomPolicy before commands = some after :=
  (Option.some_get commands_available).symm

theorem two_definition_outputs : after.cache.size = 2 := by decide +kernel

theorem definitions_have_model (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :
    ∃ finalModel : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
      finalModel.Carrier = model.Carrier ∧
      (model.FullDomains → finalModel.FullDomains) ∧
      ∀ fact ∈ after.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
          finalModel.models formula := by
  exact replay_constant_models before commands after
    (by intro command member; simp [commands] at member; rcases member with rfl | rfl <;> rfl)
    commands_replayed rfl model

theorem repeated_identity_refused :
    (Registered.apply emptyAxiomPolicy after (commands[0]'(by decide))).isNone = true := by decide +kernel

private def jsonArray (values : List Lean.Json) : Lean.Json := .arr values.toArray
private def jsonString (value : String) : Lean.Json := .str value
private def boolJson : Lean.Json := jsonArray [jsonString "op",jsonString "bool",jsonArray []]
private def functionJson (domain codomain : Lean.Json) : Lean.Json :=
  jsonArray [jsonString "op",jsonString "fun",jsonArray [domain,codomain]]
private def identityTypeJson : Lean.Json := functionJson boolJson boolJson
private def equalityTypeJson : Lean.Json := functionJson identityTypeJson (functionJson identityTypeJson boolJson)
private def variableJson (name : String) : Lean.Json :=
  jsonArray [jsonString "var",jsonString name,boolJson]
private def constantJson (name : String) (annotation : Lean.Json) : Lean.Json :=
  jsonArray [jsonString "const",jsonString name,annotation]
private def applicationJson (function argument : Lean.Json) : Lean.Json :=
  jsonArray [jsonString "app",function,argument]
private def identityBodyJson : Lean.Json :=
  jsonArray [jsonString "abs",variableJson "x",variableJson "x"]
private def equationJson (name : String) (body : Lean.Json) : Lean.Json :=
  applicationJson (applicationJson (constantJson "=" equalityTypeJson)
    (constantJson name identityTypeJson)) body
private def definitionJson (index : Nat) (name : String) (body conclusion : Lean.Json) : Lean.Json :=
  Lean.Json.mkObj [("id",Lean.toJson index),("rule",jsonString "DEFINITION"),
    ("arguments",jsonArray [equationJson name body,jsonString name,identityTypeJson]),
    ("theorem",Lean.Json.mkObj [("hypotheses",jsonArray []),("conclusion",conclusion)])]
private def documentInputs (changed : Bool) : List Lean.Json :=
  let first := definitionJson 0 identityName.component identityBodyJson
    (equationJson identityName.component identityBodyJson)
  let secondBody := constantJson identityName.component identityTypeJson
  let second := definitionJson 1 aliasName.component secondBody
    (if changed then variableJson "changed_definition_conclusion" else equationJson aliasName.component secondBody)
  [first,second]
private def documentJson (changed : Bool) : Lean.Json :=
  Lean.Json.mkObj [("sourceRevision",jsonString SourceProfile.sourceRevision),
    ("profile",jsonString "definition-reference-control"),
    ("definitions",jsonArray (documentInputs changed)),("commitments",jsonArray [])]

def referenceDocument : Lean.Json := documentJson false

def forgedReferenceDocument : Lean.Json := documentJson true

theorem profile_available :
    (SourceProfile.load? SourceProfile.primitiveBasis referenceDocument).isSome = true := by decide +kernel

def referenceProfile : SourceProfile.Profile :=
  (SourceProfile.load? SourceProfile.primitiveBasis referenceDocument).get profile_available

theorem profile_loaded :
    SourceProfile.load? SourceProfile.primitiveBasis referenceDocument = some referenceProfile :=
  (Option.some_get profile_available).symm

theorem profile_has_two_definitions : referenceProfile.reference.received.registered.cache.size = 2 := by decide +kernel

theorem profile_definitions_have_model :
    ∃ finalModel : HOL.HenkinModel.{0,0,1} AtomicTy Symbol,
      ∀ fact ∈ referenceProfile.reference.received.registered.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
          finalModel.models formula := by
  obtain ⟨finalModel, _, _, facts⟩ :=
    loaded_reference_models profile_loaded rfl ModelInterpretation.Controls.initialModel.{0}
  exact ⟨finalModel, facts⟩

theorem closed_reference_model :
    referenceProfile.reference.received.registered.cache.size = 2 ∧
    ∃ finalModel : HOL.HenkinModel.{0,0,1} AtomicTy Symbol,
      ∀ fact ∈ referenceProfile.reference.received.registered.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
          finalModel.models formula :=
  ⟨profile_has_two_definitions,profile_definitions_have_model⟩

theorem forged_reference_refused :
    (SourceProfile.load? SourceProfile.primitiveBasis forgedReferenceDocument).isNone = true := by decide +kernel

theorem closed_constant_history :
    ∃ history : ConstantHistory before.context after.context,
      after.cache.toList = before.cache.toList ++
        (history.records.map fun result => result.output.definitionTheorem) :=
  replay_constant_history before commands after
    (by intro command member; simp [commands] at member; rcases member with rfl | rfl <;> rfl)
    commands_replayed

theorem closed_constant_model :
    ∃ finalModel : HOL.HenkinModel.{0,0,1} AtomicTy Symbol,
      finalModel.Carrier = ModelInterpretation.Controls.initialModel.{0}.Carrier ∧
      (ModelInterpretation.Controls.initialModel.{0}.FullDomains → finalModel.FullDomains) ∧
      ∀ fact ∈ after.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
          finalModel.models formula :=
  replay_constant_models before commands after
    (by intro command member; simp [commands] at member; rcases member with rfl | rfl <;> rfl)
    commands_replayed rfl ModelInterpretation.Controls.initialModel.{0}

def referenceInputs : List Lean.Json := documentInputs false

theorem reference_available :
    (SourceProfile.referenceDefinitions? SourceProfile.primitiveBasis referenceInputs).isSome = true := by decide +kernel

def referenceAfter : ExportCodec.State :=
  (SourceProfile.referenceDefinitions? SourceProfile.primitiveBasis referenceInputs).get reference_available

theorem reference_replayed :
    SourceProfile.referenceDefinitions? SourceProfile.primitiveBasis referenceInputs = some referenceAfter :=
  (Option.some_get reference_available).symm

theorem closed_source_events :
    ∃ events : List ExportReplay.Event,
      (∀ event ∈ events, isConstantDefinition event.command = true) ∧
      ExportReplay.replayFrom emptyAxiomPolicy SourceProfile.primitiveBasis.received events = some referenceAfter.received :=
  reference_definitions_events SourceProfile.primitiveBasis referenceInputs referenceAfter reference_replayed

noncomputable def sourceEvents : List ExportReplay.Event := Classical.choose closed_source_events

theorem source_events_valid :
    ExportReplay.replayFrom emptyAxiomPolicy SourceProfile.primitiveBasis.received sourceEvents = some referenceAfter.received :=
  (Classical.choose_spec closed_source_events).2

theorem closed_registered_commands :
    Registered.replayFrom emptyAxiomPolicy SourceProfile.primitiveBasis.received.registered
      (sourceEvents.map ExportReplay.Event.command) = some referenceAfter.received.registered :=
  replay_registered_commands SourceProfile.primitiveBasis.received sourceEvents referenceAfter.received source_events_valid

theorem closed_source_model :
    ∃ finalModel : HOL.HenkinModel.{0,0,1} AtomicTy Symbol,
      finalModel.Carrier = ModelInterpretation.Controls.initialModel.{0}.Carrier ∧
      (ModelInterpretation.Controls.initialModel.{0}.FullDomains → finalModel.FullDomains) ∧
      ∀ fact ∈ referenceAfter.received.registered.cache, ∀ substitution : TypeSubst,
        ∃ formula : HOL.ClosedFormula Symbol,
          TranslatesCompositionally []
            ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
          finalModel.models formula :=
  reference_definitions_models SourceProfile.primitiveBasis referenceInputs referenceAfter
    reference_replayed rfl ModelInterpretation.Controls.initialModel.{0}

end Controls

#print axioms constant_step
#print axioms replay_constant_history
#print axioms replay_constant_models
#print axioms loaded_reference_models
#print axioms Controls.profile_definitions_have_model
#print axioms Controls.forged_reference_refused
end Mettapedia.Languages.HOLLight.DefinitionReplayModels
