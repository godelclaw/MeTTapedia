import Mettapedia.OSLF.NativeTypes.Generation.ModalCodes
import Mettapedia.OSLF.NativeTypes.Generation.Checking
import Mettapedia.OSLF.NativeTypes.Modal.NativeEvidence

open Mettapedia.OSLF.Framework

/-!
# Executing specified-contractum modal instances

A generated modal query retains its actual computed sort parameters, typed
rely codes and assignment-indexed continuation. The query fills the selected
authored context, executes that program, and explores the specified RHS's
equation class. A successful response retains the native primitive receipt
and the target-conversion path beside its substituted continuation witness.

This checks one full rely assignment. It does not claim that finitely many
provider rows exhaust arbitrary assignments or that one successful request
inhabits a universal rely family. Decidability is supplied for the selected
type-code predicates, rather than for an operational successor relation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching (lookup)
open GeneralOccurrenceFrontier GeneralOccurrenceSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.Formation

structure ModalInstanceCodes (generated : Generated) (schema : Schema generated.plan) where
  parameters : ModalParameters schema
  computed : generated.modalParameters? schema = some parameters
  inputs : ModalInputs schema (some parameters)

def ModalInstanceCodes.actualInputs {generated : Generated} {schema : Schema generated.plan}
    (codes : ModalInstanceCodes generated schema) :
    ModalInputs schema (generated.modalParameters? schema) :=
  codes.computed.symm ▸ codes.inputs

def ModalInstanceCodes.continuation {generated : Generated} {schema : Schema generated.plan}
    (codes : ModalInstanceCodes generated schema) : Continuation :=
  continuationMeaning codes.inputs.2

structure ModalInstanceDecisions {generated : Generated} {schema : Schema generated.plan}
    (codes : ModalInstanceCodes generated schema) where
  rely : ∀ name : RelyIndex schema, ∀ value : RuleBinding.ContextualValue,
    Decidable ((codes.inputs.1 name).meaning value)
  continuation : ∀ assignment target, Decidable ((codes.inputs.2 assignment).meaning target)

def checkInstanceRely {generated : Generated} {schema : Schema generated.plan}
    (codes : ModalInstanceCodes generated schema) (decisions : ModalInstanceDecisions codes)
    (assignment : ScopedRuleMatching.Assignment) : Bool :=
  schema.relyNames.attach.all fun name =>
    match lookup assignment name.val with
    | none => false
    | some value => @decide ((codes.inputs.1 name).meaning value) (decisions.rely name value)

theorem check_instance_rely_sound {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {decisions : ModalInstanceDecisions codes}
    {assignment : ScopedRuleMatching.Assignment} (checked : checkInstanceRely codes decisions assignment = true) :
    RelySatisfied schema (relyMeaning codes.inputs.1) assignment := by
  intro name member
  let entry : RelyIndex schema := ⟨name, member⟩
  have observed := List.all_eq_true.mp checked entry (List.mem_attach _ _)
  cases found : lookup assignment name with
  | none =>
      simp only [entry, found] at observed
      cases observed
  | some value =>
      have accepted : @decide ((codes.inputs.1 entry).meaning value) (decisions.rely entry value) = true := by
        simpa only [entry, found] using observed
      exact ⟨value, rfl, member,
        @of_decide_eq_true ((codes.inputs.1 entry).meaning value) (decisions.rely entry value) accepted⟩

def checkInstanceNames {generated : Generated} (schema : Schema generated.plan)
    (assignment : ScopedRuleMatching.Assignment) : Bool :=
  (RedexPosition.fvarNames schema.declaration.rule.left ++
    RedexPosition.fvarNames schema.declaration.rule.right).all fun name => (lookup assignment name).isSome

theorem check_instance_names_sound {generated : Generated} {schema : Schema generated.plan}
    {assignment : ScopedRuleMatching.Assignment} (checked : checkInstanceNames schema assignment = true) :
    ∀ name ∈ (RedexPosition.fvarNames schema.declaration.rule.left ++
      RedexPosition.fvarNames schema.declaration.rule.right), ∃ value, lookup assignment name = some value := by
  intro name member
  exact Option.isSome_iff_exists.mp (List.all_eq_true.mp checked name member)

def checkInstanceRequest {generated : Generated} {schema : Schema generated.plan}
    (codes : ModalInstanceCodes generated schema) (decisions : ModalInstanceDecisions codes)
    (assignment : ScopedRuleMatching.Assignment) : Bool :=
  GeneralPremise.checkTypedAssignment (GeneralPlanEnvironment.environment generated.plan)
    schema.context assignment && checkInstanceRely codes decisions assignment &&
    checkInstanceNames schema assignment

theorem check_instance_request_sound {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {decisions : ModalInstanceDecisions codes}
    {assignment : ScopedRuleMatching.Assignment} (checked : checkInstanceRequest codes decisions assignment = true) :
    TypedRequest schema (relyMeaning codes.inputs.1) assignment assignment := by
  simp only [checkInstanceRequest, Bool.and_eq_true] at checked
  exact ⟨check_instance_rely_sound checked.1.2,
    GeneralPremise.checkTypedAssignment_sound checked.1.1,
    fun _ _ => rfl, check_instance_names_sound checked.2⟩

inductive ModalInstanceIssue where
  | unavailableFormer
  | unavailableFilling
  | unavailableRightHandSide
  | noncanonicalSource
  | noncanonicalTarget
  | untypedFocus
  | unsupportedAssignment
  deriving DecidableEq, Repr

structure ModalInstanceRequest {generated : Generated} {schema : Schema generated.plan}
    (codes : ModalInstanceCodes generated schema) (assignment : ScopedRuleMatching.Assignment) (term : Pattern) where
  source : Pattern
  target : Pattern
  filling : schema.fill? assignment term = some source
  rhs : schema.rhs? assignment = some target
  sourceCanonical : source.hasCanonicalBinderMetadata = true
  targetCanonical : target.hasCanonicalBinderMetadata = true
  carrier : HasType generated.plan.snapshot.language generated.plan.snapshot.free
    schema.focusBound term schema.focusCarrier
  typedRequest : TypedRequest schema (relyMeaning codes.inputs.1) assignment assignment

def admitModalInstance? {generated : Generated} {schema : Schema generated.plan}
    (codes : ModalInstanceCodes generated schema) (decisions : ModalInstanceDecisions codes)
    (assignment : ScopedRuleMatching.Assignment) (term : Pattern) :
    Except ModalInstanceIssue (ModalInstanceRequest codes assignment term) :=
  match filling : schema.fill? assignment term with
  | none => .error .unavailableFilling
  | some source =>
    match right : schema.rhs? assignment with
    | none => .error .unavailableRightHandSide
    | some target =>
      if canonicalSource : source.hasCanonicalBinderMetadata = true then
        if canonicalTarget : target.hasCanonicalBinderMetadata = true then
          if sorted : checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
              schema.focusBound schema.focusCarrier term = true then
            if supported : checkInstanceRequest codes decisions assignment = true then
              .ok ⟨source, target, filling, right, canonicalSource, canonicalTarget,
                (checkOpenPatternWellSorted_sound sorted).1, check_instance_request_sound supported⟩
            else .error .unsupportedAssignment
          else .error .untypedFocus
        else .error .noncanonicalTarget
      else .error .noncanonicalSource

def ModalInstanceRequest.sourceRequest {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (request : ModalInstanceRequest codes assignment term) : Request :=
  generated.request schema.bound schema.programCarrier request.source

def ModalInstanceRequest.targetRequest {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (request : ModalInstanceRequest codes assignment term) : Request :=
  generated.request schema.bound schema.programCarrier request.target

theorem ModalInstanceRequest.source_root {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (request : ModalInstanceRequest codes assignment term) : request.sourceRequest.root = request.source :=
  Pattern.eraseBinderMetadata_eq_self_of_canonical request.sourceCanonical

theorem ModalInstanceRequest.target_root {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (request : ModalInstanceRequest codes assignment term) : request.targetRequest.root = request.target :=
  Pattern.eraseBinderMetadata_eq_self_of_canonical request.targetCanonical

abbrev ContractumPath {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (request : ModalInstanceRequest codes assignment term) (target : Pattern) :=
  {conversions : List Conversion // ConversionPath generated.plan schema.bound schema.programCarrier
    request.target target conversions}

/-- Discovery retains an actual equation path from the requested RHS,
including inverse administrative edges. Failure means only not yet found. -/
def contractumPath? {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (request : ModalInstanceRequest codes assignment term)
    (state : State request.targetRequest) (target : Pattern) : Option (ContractumPath request target) :=
  if same : request.target = target then some ⟨[], same ▸ ConversionPath.nil request.target⟩
  else
    match visitedAt request.targetRequest state target with
    | none => none
    | some representative =>
        some ⟨representative.val.conversions, by
          have justified := representative.val.justified
          rw [request.target_root, representative.property] at justified
          exact justified⟩

structure CheckedModalInstance {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (request : ModalInstanceRequest codes assignment term) where
  outcome : Outcome schema term assignment codes.continuation
  sourceAgreement : outcome.source = request.source
  targetAgreement : outcome.target = request.target
  targetConversions : List Conversion
  targetJustification : ConversionPath generated.plan schema.bound schema.programCarrier
    request.target outcome.receipt.target targetConversions

def checkModalResponse? {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (decisions : ModalInstanceDecisions codes) (request : ModalInstanceRequest codes assignment term)
    (targetState : State request.targetRequest) (answer : Answer request.sourceRequest) :
    Option (CheckedModalInstance request) :=
  match path : contractumPath? request targetState answer.val.target with
  | none => none
  | some conversion =>
    if accepts : @decide ((codes.inputs.2 assignment).meaning request.target)
        (decisions.continuation assignment request.target) = true then
      some {
        outcome := {
          source := request.source
          target := request.target
          filling := request.filling
          rhs := request.rhs
          receipt := answer.val
          valid := by
            have actual := answer.property
            change Receipt.Valid generated.plan schema.bound schema.programCarrier
              request.sourceRequest.root answer.val at actual
            simpa only [request.source_root] using actual
          targetConversion := conversion.property.equivalent.symm
          certificate := ⟨@of_decide_eq_true ((codes.inputs.2 assignment).meaning request.target)
            (decisions.continuation assignment request.target) accepts⟩}
        sourceAgreement := rfl
        targetAgreement := rfl
        targetConversions := conversion.val
        targetJustification := conversion.property}
    else none

def modalResponses {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (decisions : ModalInstanceDecisions codes) (request : ModalInstanceRequest codes assignment term)
    (sourceState : State request.sourceRequest) (targetState : State request.targetRequest) :
    List (CheckedModalInstance request) :=
  sourceState.answers.filterMap (checkModalResponse? decisions request targetState)

def modalInstanceReadout {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {term : Pattern}
    (decisions : ModalInstanceDecisions codes) (request : ModalInstanceRequest codes assignment term)
    (sourceState : State request.sourceRequest) (targetState : State request.targetRequest) : CheckResult :=
  if !(modalResponses decisions request sourceState targetState).isEmpty then .decided true
  else if !(@decide ((codes.inputs.2 assignment).meaning request.target)
      (decisions.continuation assignment request.target)) then .decided false
  else if sourceAdmission request.sourceRequest && checkCertificate request.sourceRequest sourceState &&
      sourceAdmission request.targetRequest && checkCertificate request.targetRequest targetState then
    .decided false
  else .unknown

structure ModalInstanceRun {generated : Generated} {schema : Schema generated.plan}
    (codes : ModalInstanceCodes generated schema) (assignment : ScopedRuleMatching.Assignment) (term : Pattern) where
  request : ModalInstanceRequest codes assignment term
  sourceState : State request.sourceRequest
  targetState : State request.targetRequest
  responses : List (CheckedModalInstance request)
  result : CheckResult

/-- One generated modal instance calls the same certified frontier engine
for the filled source and the exact authored RHS. Its positive result is a
receipt-bearing response, not a truth value attached to an atom index. -/
def Generated.checkModalInstance (generated : Generated) (schema : Schema generated.plan)
    (codes : ModalInstanceCodes generated schema) (decisions : ModalInstanceDecisions codes)
    (assignment : ScopedRuleMatching.Assignment) (term : Pattern) (budget conversionBudget : Nat) :
    Except ModalInstanceIssue (ModalInstanceRun codes assignment term) :=
  if (generated.modalFormer? schema codes.actualInputs).isSome then
    match admitModalInstance? codes decisions assignment term with
    | .error reason => .error reason
    | .ok request =>
      let sourceState := generated.execute schema.bound schema.programCarrier request.source budget
      let targetState := generated.execute schema.bound schema.programCarrier request.target conversionBudget
      .ok {
        request := request
        sourceState := sourceState
        targetState := targetState
        responses := modalResponses decisions request sourceState targetState
        result := modalInstanceReadout decisions request sourceState targetState}
  else .error .unavailableFormer

end Mettapedia.OSLF.NativeTypes.Generation
