import Mettapedia.OSLF.NativeTypes.Modal.Rules
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineTermination
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineCorrectness

open Mettapedia.OSLF.Framework

/-!
# Executable capture admission for base-rule modal introduction

The source presentation has empty-premise base rules. Their introductions
run the actual scoped matcher to completion, validate the resulting captures,
and compare the actual reduct to the specified RHS at the original assignment.
The captures may have a different order from that original assignment.
Neither a caller-supplied matching derivation nor an operational-step oracle
is used to construct an accepted introduction.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open Mettapedia.OSLF.NativeTypes.Modal.Rules

universe u

/-- Exhaust the finite actual matcher agenda. Its structural decrease was
proved for every scoped schema, including binders and bag choices. -/
def drain (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) : GeneralScopedMatchMachine.State :=
  if _finished : GeneralScopedMatchMachine.complete state = true then state
  else drain request (GeneralScopedMatchMachine.tick request state)
termination_by GeneralScopedMatchMachine.agendaCost request state.agenda
decreasing_by exact GeneralScopedMatchMachine.tick_cost (Bool.eq_false_iff.mpr _finished)

theorem drain_complete (request : GeneralScopedMatchMachine.Request)
    (state : GeneralScopedMatchMachine.State) :
    GeneralScopedMatchMachine.complete (drain request state) = true := by
  rw [drain]
  split
  · assumption
  · exact drain_complete request (GeneralScopedMatchMachine.tick request state)
termination_by GeneralScopedMatchMachine.agendaCost request state.agenda
decreasing_by exact GeneralScopedMatchMachine.tick_cost (Bool.eq_false_iff.mpr ‹_›)

theorem drain_reachable {request : GeneralScopedMatchMachine.Request}
    {state : GeneralScopedMatchMachine.State} (reached : GeneralScopedMatchMachine.Reachable request state) :
    GeneralScopedMatchMachine.Reachable request (drain request state) := by
  rw [drain]
  split
  · exact reached
  · exact drain_reachable (.tick reached)
termination_by GeneralScopedMatchMachine.agendaCost request state.agenda
decreasing_by exact GeneralScopedMatchMachine.tick_cost (Bool.eq_false_iff.mpr ‹_›)

def matcher {plan : Plan} (schema : Schema plan) (source : Pattern) :
    GeneralScopedMatchMachine.Request :=
  ⟨schema.declaration.rule, schema.declaration.binding.spec, schema.bound.length,
    .left, [], 0, [], schema.declaration.rule.left, source⟩

def matchAnswers {plan : Plan} (schema : Schema plan) (source : Pattern) :
    List GeneralScopedMatchMachine.Answer :=
  (drain (matcher schema source) (GeneralScopedMatchMachine.start (matcher schema source))).answers

theorem matches_spec {plan : Plan} (schema : Schema plan) (source : Pattern)
    (answer : GeneralScopedMatchMachine.Answer) :
    answer ∈ matchAnswers schema source ↔ answer.Valid (matcher schema source) :=
  GeneralScopedMatchMachine.complete_answers_iff
    (drain_reachable GeneralScopedMatchMachine.Reachable.start)
    (drain_complete _ _) answer

def job {plan : Plan} (schema : Schema plan) (source : Pattern) : GeneralRuleJobs.Job :=
  ⟨schema.ordinal, schema.declaration, SiteData.here schema.bound schema.programCarrier source⟩

structure BaseIntroduction where
  source : Pattern
  target : Pattern
  primitive : GeneralRuleJobs.Receipt
  deriving Repr

/-- Every matcher branch keeps its own trace and origin. Only a primitive
whose actual reduct agrees with the specified source RHS is admitted. -/
def baseIntroductions {plan : Plan} (schema : Schema plan) (assignment : Assignment) :
    List BaseIntroduction :=
  match instantiateWith? schema.operation schema.declaration.rule schema.declaration.binding.spec
      schema.bound.length .left [] 0 assignment schema.declaration.rule.left,
      schema.rhs? assignment with
  | some source, some target =>
      if schema.declaration.rule.premises.isEmpty && plan.permissions.sites.enabled &&
          checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
            plan.snapshot.free schema.bound schema.programCarrier source then
        (matchAnswers schema source).filterMap fun answer => do
          let receipt ← GeneralRuleJobs.finish? plan schema.bound schema.programCarrier
            (job schema source) answer.trace answer.assignment answer.assignment []
          if receipt.target == target then some ⟨source, target, receipt⟩ else none
      else []
  | _, _ => []

/-- Independent scoped matching and sorting are the precise source admission
condition. It is characterized by the executable construction below. -/
structure BaseDerivation {plan : Plan} (schema : Schema plan)
    (assignment : Assignment) (result : BaseIntroduction) : Prop where
  sourceInstance : instantiateWith? schema.operation schema.declaration.rule schema.declaration.binding.spec
    schema.bound.length .left [] 0 assignment schema.declaration.rule.left = some result.source
  rhs : schema.rhs? assignment = some result.target
  emptyPremises : schema.declaration.rule.premises = []
  enabled : plan.permissions.sites.enabled = true
  sourceTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
    plan.snapshot.free schema.bound schema.programCarrier result.source
  selectedJob : result.primitive.job = job schema result.source
  matched : GeneralScopedMatchMachine.TracedMatches schema.declaration.rule
    schema.declaration.binding.spec schema.bound.length .left [] 0 [] schema.declaration.rule.left
    result.source result.primitive.matcherTrace result.primitive.captured
  completed : result.primitive.completed = result.primitive.captured
  history : result.primitive.premiseHistory = []
  admitted : admittedFor schema.declaration.rule schema.declaration.binding.spec = true
  capturedTyped : GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan)
    schema.context result.primitive.captured
  reduct : reductWith? schema.operation schema.declaration.rule schema.declaration.binding.spec
    schema.bound.length result.primitive.completed = some result.primitive.localTarget
  targetTyped : OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
    plan.snapshot.free schema.bound schema.programCarrier result.primitive.localTarget
  endpoint : result.primitive.target = result.primitive.localTarget
  target : result.primitive.target = result.target

theorem BaseDerivation.valid {plan : Plan} {schema : Schema plan} {assignment : Assignment}
    {result : BaseIntroduction} (derived : BaseDerivation schema assignment result) :
    result.primitive.Valid plan schema.bound schema.programCarrier result.source := by
  have licensed : (job schema result.source).Valid plan schema.bound schema.programCarrier result.source :=
    ⟨schema.declared, .here derived.enabled derived.sourceTyped.2.2.1 derived.sourceTyped.1⟩
  unfold GeneralRuleJobs.Receipt.Valid
  rw [derived.selectedJob]
  refine ⟨licensed, ?_, rfl, derived.endpoint, ?_⟩
  · apply GeneralPremise.RootFiring.fire
      (GeneralRuleJobs.Job.selected_rule licensed) (GeneralRuleJobs.Job.selected_specification licensed)
      derived.admitted derived.sourceTyped derived.matched derived.capturedTyped
    · change GeneralPremise.PremisesHold _ _ schema.declaration.rule.premises _ _ _
      rw [derived.emptyPremises, derived.completed, derived.history]
      exact .nil
    · exact derived.reduct
    · exact derived.targetTyped
  · rw [derived.endpoint]
    exact derived.targetTyped

private theorem finish_shape {plan : Plan} {bound : List TypeExpr} {carrier : TypeExpr}
    {selected : GeneralRuleJobs.Job} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured : Assignment} {receipt : GeneralRuleJobs.Receipt}
    (finished : GeneralRuleJobs.finish? plan bound carrier selected trace captured captured [] = some receipt) :
    receipt.job = selected ∧ receipt.matcherTrace = trace ∧ receipt.captured = captured ∧
      receipt.completed = captured ∧ receipt.premiseHistory = [] := by
  unfold GeneralRuleJobs.finish? at finished
  dsimp only at finished
  split at finished
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at finished
    obtain ⟨_, _, finished⟩ := finished
    split at finished
    · cases Option.some.inj finished
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · contradiction
  · contradiction

theorem baseIntroductions_sound {plan : Plan} {schema : Schema plan} {assignment : Assignment}
    {result : BaseIntroduction} (generated : result ∈ baseIntroductions schema assignment) :
    BaseDerivation schema assignment result := by
  unfold baseIntroductions at generated
  cases source : instantiateWith? schema.operation schema.declaration.rule schema.declaration.binding.spec
      schema.bound.length .left [] 0 assignment schema.declaration.rule.left with
  | none => simp only [source, List.not_mem_nil] at generated
  | some sourceValue =>
      cases target : schema.rhs? assignment with
      | none => simp only [source, target, List.not_mem_nil] at generated
      | some targetValue =>
          simp only [source, target] at generated
          split at generated
          next ready =>
            obtain ⟨answer, matched, emitted⟩ := List.mem_filterMap.mp generated
            simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at emitted
            obtain ⟨receipt, finished, emitted⟩ := emitted
            split at emitted
            next same =>
              cases Option.some.inj emitted
              have conditions := Bool.and_eq_true_iff.mp ready
              have first := Bool.and_eq_true_iff.mp conditions.1
              have shape := finish_shape finished
              have emptyPremises := List.isEmpty_iff.mp first.1
              have sourceTyped := checkOpenPatternWellSorted_sound conditions.2
              have actualMatched : GeneralScopedMatchMachine.TracedMatches schema.declaration.rule
                  schema.declaration.binding.spec schema.bound.length .left [] 0 [] schema.declaration.rule.left
                  sourceValue receipt.matcherTrace receipt.captured := by
                rw [shape.2.1, shape.2.2.1]
                exact (matches_spec schema sourceValue answer).mp matched
              have licensed : (job schema sourceValue).Valid plan schema.bound schema.programCarrier sourceValue :=
                ⟨schema.declared, .here first.2 sourceTyped.2.2.1 sourceTyped.1⟩
              have primitive := GeneralRuleJobs.finish_sound licensed
                ((matches_spec schema sourceValue answer).mp matched)
                (show GeneralPremise.PremisesHold _ _ _ answer.assignment answer.assignment [] from by
                  change GeneralPremise.PremisesHold _ _ schema.declaration.rule.premises _ _ _
                  rw [emptyPremises]
                  exact .nil) finished
              have readout := GeneralRuleJobs.receipt_root_readout primitive
              refine ⟨source, target, List.isEmpty_iff.mp first.1, first.2,
                sourceTyped, shape.1, actualMatched, shape.2.2.2.1.trans shape.2.2.1.symm,
                shape.2.2.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [shape.1] at readout
                exact readout.1
              · rw [shape.1] at readout
                exact readout.2.2.1
              · rw [shape.1] at readout
                exact readout.2.2.2.1
              · rw [shape.1] at readout
                exact readout.2.2.2.2
              · have endpoint := primitive.2.2.2.1
                rw [shape.1] at endpoint
                exact endpoint
              · exact beq_iff_eq.mp same
            next => contradiction
          next => simp only [List.not_mem_nil] at generated

theorem baseIntroductions_complete {plan : Plan} {schema : Schema plan} {assignment : Assignment}
    {result : BaseIntroduction} (derived : BaseDerivation schema assignment result) :
    result ∈ baseIntroductions schema assignment := by
  unfold baseIntroductions
  simp only [derived.sourceInstance, derived.rhs]
  rw [if_pos (by
    simp only [derived.emptyPremises, List.isEmpty_nil, derived.enabled, Bool.true_and]
    exact checkOpenPatternWellSorted_complete derived.sourceTyped)]
  apply List.mem_filterMap.mpr
  refine ⟨⟨result.primitive.captured, result.primitive.matcherTrace⟩,
    (matches_spec schema result.source _).mpr derived.matched, ?_⟩
  have finished := GeneralRuleJobs.finish_complete derived.valid
  rw [derived.selectedJob, derived.completed, derived.history] at finished
  simp only [finished, Option.bind_eq_bind, Option.bind_some,
    derived.target, beq_self_eq_true, ↓reduceIte]

theorem baseIntroductions_spec {plan : Plan} (schema : Schema plan) (assignment : Assignment)
    (result : BaseIntroduction) :
    result ∈ baseIntroductions schema assignment ↔ BaseDerivation schema assignment result :=
  ⟨baseIntroductions_sound, baseIntroductions_complete⟩

/-- M-INTRO from original scoped instantiations and computed capture admission.
The source RHS certificate remains indexed by the original full assignment,
while the primitive keeps the actual canonical captures. -/
def m_intro_computed {plan : Plan} {schema : Schema plan}
    {A : String → ContextualValue → Prop} {B : Continuation.{u}} {term : Pattern}
    (typed : HasType plan.snapshot.language plan.snapshot.free schema.focusBound term schema.focusCarrier)
    (anchor : Assignment)
    (anchorTyped : GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment plan) schema.context anchor)
    (anchorPresent : ∀ name ∈ schema.matchedNames, ∃ value, lookup anchor name = some value)
    (focus : ∀ assignment, TypedRequest schema A anchor assignment →
      Mettapedia.OSLF.NativeTypes.Modal.Instantiation.FocusInstance schema.operation schema.declaration.rule
        schema.declaration.binding.spec schema.bound.length .left assignment [] 0
        schema.declaration.rule.left schema.position term)
    (accepted : ∀ assignment, TypedRequest schema A anchor assignment →
      baseIntroductions schema assignment ≠ [])
    (certificate : ∀ assignment, TypedRequest schema A anchor assignment →
      ∀ target, schema.rhs? assignment = some target → substituteContinuation B assignment target) :
    Evidence schema A B term where
  carrier := typed
  anchor := anchor
  anchorTyped := anchorTyped
  anchorPresent := anchorPresent
  respond assignment request :=
    let result := (baseIntroductions schema assignment).head (accepted assignment request)
    let derived := baseIntroductions_sound (List.head_mem (accepted assignment request))
    {source := result.source
     target := result.target
     filling := (Mettapedia.OSLF.NativeTypes.Modal.Instantiation.fill_authored (focus assignment request)).trans derived.sourceInstance
     rhs := derived.rhs
     receipt := ⟨result.source, [], result.primitive⟩
     valid := ⟨.nil _, derived.valid⟩
     targetConversion := derived.target ▸ Relation.EqvGen.refl _
     certificate := certificate assignment request result.target derived.rhs}

end Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction
