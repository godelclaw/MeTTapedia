import Mettapedia.OSLF.NativeTypes.Decision.Reference.Receipts
import Mettapedia.OSLF.NativeTypes.Generation.ModalCheckingLaws

open Mettapedia.OSLF.Framework

/-!
# Complete checking of one generated modal assignment

An instance computes its actual plugged source and specified contractum and
checks the whole supplied rely assignment. Its native question combines the
specified equation class with the substituted continuation. The comparison
retains an actual primitive response, and never promotes one assignment to
membership in the universally quantified rely family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.InstanceDecision

open Mettapedia.GSLT
open GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

universe u v

/-- Computational equation-class membership is a primitive backend law. -/
structure EquationDecision (system : GSLT.{u}) where
  equivalent : system.Term → system.Term → Bool
  exact : ∀ first second, equivalent first second = true ↔ system.Equiv first second

def contractumPredicate (system : GSLT.{u}) (target : system.Term) (continuation : Prop) :
    EquationPredicate system where
  val actual := system.Equiv actual target ∧ continuation
  property := by
    intro first second related
    constructor
    · rintro ⟨represents, holds⟩
      exact ⟨system.equations.iseqv.trans (system.equations.iseqv.symm related) represents, holds⟩
    · rintro ⟨represents, holds⟩
      exact ⟨system.equations.iseqv.trans related represents, holds⟩

def contractumTest {system : GSLT.{u}} {admitted : system.Term → Prop}
    (equations : EquationDecision system) (target : system.Term) (continuation : Prop)
    (accepts : Bool) (continuationExact : accepts = true ↔ continuation) : Test system admitted :=
  Test.ofBoolean (contractumPredicate system target continuation)
    (fun actual => equations.equivalent actual target && accepts) (by
      intro actual
      simp only [Bool.and_eq_true]
      exact and_congr (equations.exact actual target) continuationExact)

def instanceFormula : Formula Unit := .possibility (.atom ())

def tests {system : GSLT.{u}} {admitted : system.Term → Prop}
    (equations : EquationDecision system) (target : system.Term) (continuation : Prop)
    (accepts : Bool) (continuationExact : accepts = true ↔ continuation) : Unit → Test system admitted :=
  fun _ => contractumTest equations target continuation accepts continuationExact

theorem instance_native_comparison {system : GSLT.{u}} {admitted : system.Term → Prop}
    (equations : EquationDecision system) (target : system.Term) (continuation : Prop)
    (accepts : Bool) (continuationExact : accepts = true ↔ continuation) (source : system.Term) :
    denotation (tests (admitted := admitted) equations target continuation accepts continuationExact)
        instanceFormula source ↔ system.Step source target ∧ continuation := by
  rw [show denotation (tests (admitted := admitted) equations target continuation accepts continuationExact)
      instanceFormula = semanticDiamond system (contractumPredicate system target continuation) from rfl]
  change gsltDiamond system (contractumPredicate system target continuation) source ↔ _
  rw [gsltDiamond_spec]
  constructor
  · rintro ⟨actual, step, related, holds⟩
    exact ⟨system.rewrites_resp_right step related, holds⟩
  · rintro ⟨step, holds⟩
    exact ⟨target, step, system.equations.iseqv.refl target, holds⟩

def check {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : Backend.{u,v} system admitted) (equations : EquationDecision system)
    (target : system.Term) (continuation : Prop) (accepts : Bool)
    (continuationExact : accepts = true ↔ continuation) (source : system.Term) (budget : Nat) :
    Outcome (system.Step source target ∧ continuation) :=
  Outcome.map (instance_native_comparison equations target continuation accepts continuationExact source)
    (Mettapedia.OSLF.NativeTypes.Decision.Reference.Core.check backend (tests equations target continuation accepts continuationExact)
      instanceFormula source budget)

theorem complete {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : Backend.{u,v} system admitted) (equations : EquationDecision system)
    (target : system.Term) (continuation : Prop) (accepts : Bool)
    (continuationExact : accepts = true ↔ continuation) (source : system.Term)
    (sourceAdmitted : admitted source) (budget : Nat)
    (enough : workBound backend (tests equations target continuation accepts continuationExact)
      instanceFormula source ≤ budget) :
    (check backend equations target continuation accepts continuationExact source budget).Decided :=
  Outcome.map_decided _ _ (checked_complete backend _ _ source sourceAdmitted budget enough)

namespace GeneratedInstance

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Modal.Rules (Schema)

def system {generated : Generated} (schema : Schema generated.plan) :=
  GeneralOccurrenceSemantics.gslt generated.plan schema.bound schema.programCarrier

theorem outcome_exact {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {focus : Pattern}
    (request : ModalInstanceRequest codes assignment focus) :
    (system schema).Step request.source request.target ∧
        (codes.inputs.2 assignment).meaning request.target ↔
      Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema focus assignment codes.continuation) := by
  constructor
  · rintro ⟨step, continuation⟩
    obtain ⟨representative, firing, equivalent, valid, targetEquivalent⟩ := step
    obtain ⟨conversions, converted⟩ :=
      (Mettapedia.OSLF.NativeTypes.Modal.Equations.conversion_iff_path generated.plan schema.bound schema.programCarrier
        request.source representative).mp equivalent
    exact ⟨{
      source := request.source
      target := request.target
      filling := request.filling
      rhs := request.rhs
      receipt := ⟨representative, conversions, firing⟩
      valid := ⟨converted, valid⟩
      targetConversion := targetEquivalent
      certificate := ⟨continuation⟩}⟩
  · rintro ⟨outcome⟩
    exact ⟨instance_outcome_step request outcome, instance_outcome_continuation request outcome⟩

def run {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {focus : Pattern}
    {admitted : Pattern → Prop} (backend : Backend (system schema) admitted)
    (equations : EquationDecision (system schema)) (decisions : ModalInstanceDecisions codes)
    (request : ModalInstanceRequest codes assignment focus) (budget : Nat) :
    Outcome (Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema focus assignment codes.continuation)) :=
  Outcome.map (outcome_exact request)
    (Mettapedia.OSLF.NativeTypes.Modal.InstanceDecision.check backend equations request.target
      ((codes.inputs.2 assignment).meaning request.target)
      (@decide ((codes.inputs.2 assignment).meaning request.target)
        (decisions.continuation assignment request.target))
      (@decide_eq_true_iff ((codes.inputs.2 assignment).meaning request.target)
        (decisions.continuation assignment request.target)) request.source budget)

structure Run {generated : Generated} {schema : Schema generated.plan}
    (codes : ModalInstanceCodes generated schema) (assignment : ScopedRuleMatching.Assignment) (focus : Pattern) where
  request : ModalInstanceRequest codes assignment focus
  result : Outcome (Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome schema focus assignment codes.continuation))

def check {generated : Generated} (schema : Schema generated.plan) (codes : ModalInstanceCodes generated schema)
    (decisions : ModalInstanceDecisions codes) {admitted : Pattern → Prop}
    (backend : Backend (system schema) admitted) (equations : EquationDecision (system schema))
    (assignment : ScopedRuleMatching.Assignment) (focus : Pattern) (budget : Nat) :
    Except ModalInstanceIssue (Run codes assignment focus) :=
  if (generated.modalFormer? schema codes.actualInputs).isSome then
    match admitModalInstance? codes decisions assignment focus with
    | .error reason => .error reason
    | .ok request => .ok ⟨request, run backend equations decisions request budget⟩
  else .error .unavailableFormer

theorem run_complete {generated : Generated} {schema : Schema generated.plan}
    {codes : ModalInstanceCodes generated schema} {assignment : ScopedRuleMatching.Assignment} {focus : Pattern}
    {admitted : Pattern → Prop} (backend : Backend (system schema) admitted)
    (equations : EquationDecision (system schema)) (decisions : ModalInstanceDecisions codes)
    (request : ModalInstanceRequest codes assignment focus) (sourceAdmitted : admitted request.source)
    (budget : Nat)
    (enough : workBound backend (tests equations request.target
      ((codes.inputs.2 assignment).meaning request.target)
      (@decide ((codes.inputs.2 assignment).meaning request.target)
        (decisions.continuation assignment request.target))
      (@decide_eq_true_iff ((codes.inputs.2 assignment).meaning request.target)
        (decisions.continuation assignment request.target))) instanceFormula request.source ≤ budget) :
    (run backend equations decisions request budget).Decided :=
  Outcome.map_decided _ _ (Mettapedia.OSLF.NativeTypes.Modal.InstanceDecision.complete backend equations _ _ _ _
    request.source sourceAdmitted budget enough)

end GeneratedInstance

end Mettapedia.OSLF.NativeTypes.Modal.InstanceDecision
