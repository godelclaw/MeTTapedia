import Mettapedia.OSLF.NativeTypes.Semantics.Modal.Root
import Mettapedia.OSLF.NativeTypes.Modal.Counterexamples

open Mettapedia.OSLF.Framework

/-!
# One successful assignment is not a complete rely family

Pair(X, Alpha) reduces to Done for both Alpha and Beta rely values. The
dependent continuation certifies only the Alpha assignment. Actual execution
supplies that instance, while the Beta request prevents full modal membership
at every focus representative.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open RuleBinding ScopedRuleMatching GeneralExecutionAdmission GeneralOccurrenceSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Semantics.Modal
open Mettapedia.OSLF.NativeTypes.Modal.Counterexamples (carrier alpha beta done)

def pair (first second : Pattern) : Pattern := .apply "Pair" [first, second]

def rule : RewriteRule where
  name := "pair-rely"
  typeContext := [("X", carrier)]
  premises := []
  left := pair (.fvar "X") alpha
  right := done

def language : LanguageDef :=
  {Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.language with
    name := "native-full-rely-separator"
    terms := Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.language.terms ++
      [{label := "Pair", category := "Term", params := [.simple "first" carrier, .simple "second" carrier],
        syntaxPattern := []}]
    equations := []
    rewrites := [rule]}

def snapshot : Snapshot := ⟨language, [], ⟨[], []⟩⟩
def permissions : Permissions := {sites := .rootOnly}
def declaration : RulePlan :=
  ⟨0, rule, ⟨GeneralRuleBindingInference.inferredSpec rule, .inferredRootInputs⟩⟩
def runtimePlan : Plan := ⟨snapshot, permissions, [declaration], [], []⟩

theorem actual_plan : compile snapshot permissions = runtimePlan := by cbv

def schema : Schema runtimePlan where
  ordinal := 0
  declaration := declaration
  declared := List.mem_cons_self
  position := (RedexPosition.positions rule.left)[2]?.getD []
  bound := []
  programCarrier := carrier
  focusBound := []
  focusCarrier := carrier

theorem generated_position : schema.position = [1] := by cbv
theorem generated_names : schema.relyNames = ["X"] ∧ schema.matchedNames = [] := by cbv

def value (body : Pattern) : ContextualValue := ⟨[], 0, body⟩
def supplied (body : Pattern) : Assignment := [("X", value body)]

def rely (_name : String) (input : ContextualValue) : Prop :=
  input.dependencies = [] ∧ input.ambient = 0 ∧ HasType language snapshot.free [] input.body carrier

def continuation : Continuation := fun assignment target =>
  PLift (lookup assignment "X" = some (value alpha) ∧ target = done)

private theorem beta_typed : HasType language snapshot.free [] beta carrier := by
  apply checkHasType_sound
  cbv

theorem beta_request (anchor : Assignment) : TypedRequest schema rely anchor (supplied beta) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro name present
    have name_eq : name = "X" := by simpa only [generated_names.1, List.mem_singleton] using present
    subst name
    exact ⟨value beta, by cbv, rfl, rfl, beta_typed⟩
  · apply GeneralPremise.checkTypedAssignment_sound
    cbv
  · intro name present
    rw [generated_names.2] at present
    exact False.elim (List.not_mem_nil present)
  · have names : RedexPosition.fvarNames schema.declaration.rule.left ++
        RedexPosition.fvarNames schema.declaration.rule.right = ["X"] := by cbv
    intro name present
    have name_eq : name = "X" := by simpa only [names, List.mem_singleton] using present
    subst name
    exact ⟨value beta, by cbv⟩

/-- A full implementation would have to answer the genuinely typed Beta
request, whose substituted continuation has no certificate. -/
theorem no_full_implementation (term : Pattern) : ¬ Inhabits schema rely continuation term := by
  rintro ⟨implementation⟩
  let outcome := implementation.respond (supplied beta) (beta_request implementation.anchor)
  have impossible := outcome.certificate.down.1
  have different : lookup (supplied beta) "X" ≠ some (value alpha) := by decide +kernel
  exact different impossible

theorem no_native_full_membership (term : Pattern) : ¬ predicate schema rely continuation term := by
  rintro ⟨representative, _, implementation⟩
  exact no_full_implementation representative implementation

def request : GeneralOccurrenceFrontier.Request :=
  ⟨runtimePlan, [], carrier, pair alpha alpha⟩

def executed : GeneralOccurrenceFrontier.State request :=
  GeneralOccurrenceFrontier.run request 35 (GeneralOccurrenceFrontier.start request)

theorem request_root : request.root = pair alpha alpha := by cbv

theorem actual_start : GeneralOccurrenceFrontier.start request =
    {agenda := [.visit ⟨pair alpha alpha, [], by rw [request_root]; exact .nil _⟩, .universe]} := by
  simp only [GeneralOccurrenceFrontier.start, request_root]
  have checked : checkOpenPatternWellSorted request.plan.snapshot.language request.plan.snapshot.free
      request.bound request.expected (pair alpha alpha) = true := by decide +kernel
  rw [checked]
  rfl

def primitive : GeneralRuleJobs.Receipt where
  job := ⟨0, declaration, GeneralTypedSites.SiteData.here [] carrier (pair alpha alpha)⟩
  matcherTrace := []
  captured := supplied alpha
  completed := supplied alpha
  premiseHistory := []
  localTarget := done
  target := done

theorem primitive_valid : primitive.Valid runtimePlan [] carrier (pair alpha alpha) := by
  apply GeneralRuleJobs.finish_sound (job := primitive.job) (trace := [])
    (captured := supplied alpha) (completed := supplied alpha) (history := [])
  · refine ⟨List.mem_cons_self, .here rfl rfl ?_⟩
    apply checkHasType_sound
    cbv
  · apply GeneralScopedMatchMachine.TracedMatches.constructor
    refine GeneralScopedMatchMachine.TracedArguments.cons
      (headTrace := []) (tailTrace := []) (middle := supplied alpha) ?_ ?_
    · apply GeneralScopedMatchMachine.TracedMatches.capture
      cbv
    · exact .cons (.constructor .nil) .nil
  · exact .nil
  · cbv

/-- The configured rule executor validates the completed primitive, including
its retained matcher and ordered premise result. -/
theorem actual_completion :
    ∃ answer, GeneralRuleJobExecution.finishRoot
      ⟨runtimePlan, [], carrier, pair alpha alpha, primitive.job⟩ primitive_valid.1
      primitive.matcherTrace primitive.captured primitive.completed primitive.premiseHistory
      primitive.localTarget primitive_valid.2.1 = some answer ∧ answer.val = primitive :=
  GeneralRuleJobExecution.finishRoot_complete primitive_valid rfl

def actualReceipt : GeneralOccurrenceNativeReceipts.ReceiptFamily runtimePlan [] carrier (pair alpha alpha) :=
  ⟨⟨pair alpha alpha, [], primitive⟩, .nil _, primitive_valid⟩

theorem actual_target : actualReceipt.val.target = done := rfl

/-- The actual executor supplies a certificate for the Alpha assignment,
without supplying a full family over the Beta assignment. -/
def alphaOutcome : Outcome schema alpha (supplied alpha) continuation where
  source := pair alpha alpha
  target := done
  filling := by cbv
  rhs := by cbv
  receipt := actualReceipt.val
  valid := actualReceipt.property
  targetConversion := by rw [actual_target]; exact .refl _
  certificate := ⟨by cbv⟩

theorem single_completed_instance_is_insufficient :
    Nonempty (Outcome schema alpha (supplied alpha) continuation) ∧
      ¬ predicate schema rely continuation alpha :=
  ⟨⟨alphaOutcome⟩, no_native_full_membership alpha⟩

theorem single_instance_retains_native_certificate :
    alphaOutcome.native.2.1 = done ∧
      Nonempty (substituteContinuation continuation (supplied alpha) alphaOutcome.native.2.1) ∧
      alphaOutcome.native.1.val = actualReceipt.val :=
  ⟨rfl, ⟨alphaOutcome.native.2.2.2⟩, rfl⟩

end Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls
