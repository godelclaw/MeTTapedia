import Mettapedia.OSLF.NativeTypes.Modal.NativeRootEvent
import Mettapedia.OSLF.NativeTypes.Modal.NativeRefinedPlan
import Mettapedia.OSLF.NativeTypes.Modal.NativeScopedParameterTypes
import Mettapedia.OSLF.NativeTypes.Modal.NativeEventInterpretation
import Mettapedia.OSLF.MeTTaIL.StructuralDescentAuthoredPlans
import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations

/-!
# Native nonroot event parameters from actual recursive lambda execution

The original four-rule language runs through the generic structural scheduler.
The generated schema selects a focus beneath a binder. Its body dependency,
complete premise history and actual specified contractum survive native fibre
interpretation and the common native certificate checker.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeScopedEventControls

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralExecutionAdmission
open Mettapedia.OSLF.NativeTypes.Generation
open NativeEventDeclarations NativeEventParameters NativeScopedParameterTypes

def language := Mettapedia.OSLF.Binding.LambdaAuthoredFullRuleProfile.language
def term : TypeExpr := .base "Term"
def snapshot : Snapshot := ⟨language, [], ⟨[], [], []⟩⟩
theorem refined_ready : StructuralDescent.Plan.structuralReady
    (GeneralExecutionAdmission.compile snapshot StructuralDescent.Controls.rootPermissions) = true := by
  simpa only [StructuralDescent.Plan.structuralReady, StructuralDescent.AuthoredPlans.lambdaPlan,
    StructuralDescent.Plan.compile, StructuralDescent.Plan.refinement_environment,
    StructuralDescent.AuthoredPlans.snapshot, snapshot, language] using
      StructuralDescent.AuthoredPlans.lambda_environment_admitted

abbrev plan : Plan := NativeRefinedPlan.normalize
  (GeneralExecutionAdmission.compile snapshot StructuralDescent.Controls.rootPermissions) refined_ready

def environment := GeneralPlanEnvironment.environment plan

theorem original_refined_plan : plan = StructuralDescent.AuthoredPlans.lambdaPlan :=
  NativeRefinedPlan.normalize_eq_refine _ _

/-- Every selected schema drives the same original scoped executor. -/
def executionAt (index : Index plan) (source : Pattern) :=
  let generated := schema plan index
  StructuralDescent.Scheduled.resume environment generated.bound generated.programCarrier source 1000
    (StructuralDescent.Scheduled.begin environment generated.bound generated.programCarrier source)

def emittedAt (index : Index plan) (source : Pattern) :
    Option (NativeEventFibre.Event (schema plan index)) :=
  (StructuralDescent.Scheduled.receipts (executionAt index source)).head?.bind
    (NativeRootEvent.at? (schema plan index) (by rfl))

abbrev GeneratedEvent := (index : Index plan) × NativeEventFibre.Event (schema plan index)

def selectedEvent (ordinal : Nat) (position : List Nat) (source : Pattern) : Option GeneratedEvent := do
  let index ← (List.finRange (schemas plan).length).find? fun candidate =>
    (schema plan candidate).ordinal == ordinal && (schema plan candidate).position == position
  let event ← emittedAt index source
  return ⟨index, event⟩

def source : Pattern := .apply "Lam" [.lambda none
  (.apply "App" [.apply "Lam" [.lambda none (.bvar 0)], .bvar 0])]
def target : Pattern := .apply "Lam" [.lambda none (.bvar 0)]

def binderEvent := selectedEvent 1 [0, 0] source

#guard binderEvent.isSome
#guard binderEvent.map (fun output => output.2.target) == some target
#guard binderEvent.map (fun output => (schema plan output.1).focusBound) == some [term]
#guard binderEvent.map (fun output => output.2.receipt.firing.premiseHistory.flatMap
  StructuralDescent.Controls.childIndices) == some [0]

structure ParameterReadout where
  name : String
  dependencies : List TypeExpr
  expected : TypeExpr
  ambient : Nat
  body : Pattern
  deriving DecidableEq

def parameterReadouts {index : Index plan} (tuple : ParameterTuple (schema plan index)) :
    List ParameterReadout :=
  (List.finRange tuple.slots.length).map fun position =>
    let slot := tuple.slots[position]
    let value := tuple.values position
    ParameterReadout.mk slot.name value.val.dependencies slot.expected value.val.ambient value.val.body

def matchedReadout (output : GeneratedEvent) := parameterReadouts (matchedParameters output.2)
def relyReadout (output : GeneratedEvent) := parameterReadouts (relyParameters output.2)

#guard binderEvent.map (fun output => (matchedReadout output).map (·.name)) == some ["B"]
#guard binderEvent.map (fun output => (matchedReadout output).map (·.dependencies)) == some [[term]]
#guard binderEvent.map (fun output => (matchedReadout output).map (·.ambient)) == some [0]
#guard binderEvent.map (fun output => (matchedReadout output).map (·.body)) ==
  some [.apply "App" [.apply "Lam" [.lambda none (.bvar 0)], .bvar 0]]
#guard binderEvent.map (fun output => (matchedReadout output).all fun value =>
  Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType language (fun _ => none) value.dependencies
    value.body value.expected) == some true
#guard binderEvent.map (fun output => (matchedReadout output).all fun value =>
  Mettapedia.GSLT.LanguageDef.WellSorted.checkHasType language (fun _ => none) []
    value.body value.expected) == some false

def parameterCertificateChecks {index : Index plan} (tuple : ParameterTuple (schema plan index)) :
    List (Option (Bool × Bool)) :=
  (List.finRange tuple.slots.length).map fun position => do
    let installed ← NativeScopedParameterTypes.install? tuple.slots[position]
    let declarations ← NativeSignature.install? plan.snapshot.language
    let certificate := installed.certificate (headers := declarations.headers) .nil
      NativeSignature.emptyContext
    let wrong ← (List.finRange plan.snapshot.language.types.length).head?
    return (Certificates.Refinement.check certificate (.type .nil installed.carrier.native),
      Certificates.Refinement.check certificate (.type .nil (NativeSignature.Carrier.sort wrong).native))

#guard binderEvent.map (fun output => parameterCertificateChecks (matchedParameters output.2)) ==
  some [some (true, false)]

/-- The same plan exposes a nonempty rely parameter in application congruence. -/
def identity : Pattern := .apply "Lam" [.lambda none (.bvar 0)]
def relySource : Pattern := .apply "App" [.apply "App" [identity, identity], identity]
def relyTarget : Pattern := .apply "App" [identity, identity]
def relyEvent := selectedEvent 2 [0] relySource

#guard relyEvent.isSome
#guard relyEvent.map (fun output => output.2.target) == some relyTarget
#guard relyEvent.map (fun output => (schema plan output.1).relyNames) == some ["A"]
#guard relyEvent.map (fun output => (relyReadout output).map (·.name)) == some ["A"]
#guard relyEvent.map (fun output => (relyReadout output).map (·.body)) == some [identity]
#guard relyEvent.map (fun output => (matchedReadout output).map (·.name)) == some ["F"]
#guard relyEvent.map (fun output => output.2.receipt.firing.premiseHistory.flatMap
  StructuralDescent.Controls.childIndices) == some [0]
#guard relyEvent.map (fun output => parameterCertificateChecks (relyParameters output.2)) ==
  some [some (true, true)]

def incorrectScopeRejected : Option Bool := do
  let index ← (List.finRange (schemas plan).length).find? fun candidate =>
    (schema plan candidate).ordinal == 1 && (schema plan candidate).position == [0, 0]
  let answer ← (StructuralDescent.Scheduled.receipts (executionAt index source)).head?
  let incorrect : Rules.Schema plan := {schema plan index with focusBound := []}
  return (NativeRootEvent.at? incorrect (by rfl) answer).isNone

#guard incorrectScopeRejected == some true

noncomputable def nativeValue (output : GeneratedEvent) (world : Discrete PUnit) :=
  NativeEventFibre.encode (schema plan output.1) world (output.2.input _) output.2 rfl

/-- The independent native fibre recovers every original emitted contractum
and its complete receipt, including at nonroot generated positions. -/
theorem native_contractum_and_receipt (output : GeneratedEvent) (world : Discrete PUnit) :
    NativeEventInterpretation.targetOutput output.1 world (output.2.input _) (nativeValue output world) =
        output.2.target ∧
      (NativeEventFibre.decode (schema plan output.1) world (output.2.input _)
        (nativeValue output world)).val.receipt = output.2.receipt := by
  rw [NativeEventInterpretation.target_output_exact]
  have recovered := NativeEventFibre.decode_encode (schema plan output.1) world
    (output.2.input _) output.2 rfl
  exact ⟨congrArg (fun result => result.val.target) recovered,
    congrArg (fun result => result.val.receipt) recovered⟩

theorem generated_parameters_preserve_the_binding_context (output : GeneratedEvent)
    (position : Fin (matchedParameters output.2).slots.length) :
    let tuple := matchedParameters output.2
    let slot := tuple.slots[position]
    let value := tuple.values position
    value.val.dependencies = slot.dependencies ∧
      value.val.ambient = (schema plan output.1).bound.length ∧
      Mettapedia.GSLT.LanguageDef.WellSorted.HasType plan.snapshot.language plan.snapshot.free
        (slot.dependencies ++ (schema plan output.1).bound) value.val.body slot.expected :=
  ⟨((matchedParameters output.2).values position).property.1,
    ((matchedParameters output.2).values position).property.2.1,
    ((matchedParameters output.2).values position).property.2.2.1⟩

end Mettapedia.OSLF.NativeTypes.Modal.NativeScopedEventControls
