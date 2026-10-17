import Mettapedia.OSLF.NativeTypes.Modal.NativeEventTyping
import Mettapedia.OSLF.MeTTaIL.StructuralDescentScheduledReadout

/-!
# Scoped recursive execution answers enter the native event family

The public structural-descent runtime emits original RootFiring evidence.
For a generated root schema, this constructs the actual licensed occurrence
receipt, retaining its complete recursive premise history and specified RHS.
The plan may be the independently refined recursive-admission plan.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeRootEvent

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence
open Rules NativeEventFibre

variable {plan : Plan} (schema : Schema plan) {source : Pattern}

abbrev Answer := StructuralDescent.Execution.RootAnswer
  (GeneralPlanEnvironment.environment plan) schema.bound schema.programCarrier source

theorem source_sorted (answer : Answer schema (source := source)) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free schema.bound schema.programCarrier source := by
  cases answer.valid with
  | fire _ _ _ sorted _ _ _ _ _ => exact sorted

theorem target_sorted (answer : Answer schema (source := source)) :
    OpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language
      plan.snapshot.free schema.bound schema.programCarrier answer.target := by
  cases answer.valid with
  | fire _ _ _ _ _ _ _ _ sorted => exact sorted

/-- Actual rule and binding lookup recover the specified authored RHS. -/
theorem specified_rhs (answer : Answer schema (source := source))
    (ordinal : answer.index = schema.ordinal) :
    schema.rhs? answer.completed = some answer.target := by
  have selectedRule := GeneralPlanEnvironment.selected_rule plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  have selectedSpec := GeneralPlanEnvironment.selected_specification plan
    (List.mk_mem_zipIdx_iff_getElem?.mp schema.declared)
  rw [← ordinal] at selectedRule selectedSpec
  cases answer.valid with
  | @fire _ _ _ _ _ rule spec _ _ _ _ declared specified _ _ _ _ _ reduct _ =>
      have sameRule := Option.some.inj (declared.symm.trans selectedRule)
      have sameSpec := Option.some.inj (specified.symm.trans selectedSpec)
      subst rule
      subst spec
      exact reduct

def primitive (answer : Answer schema (source := source)) : GeneralRuleJobs.Receipt where
  job := ⟨schema.ordinal, schema.declaration, SiteData.here schema.bound schema.programCarrier source⟩
  matcherTrace := answer.trace
  captured := answer.captured
  completed := answer.completed
  premiseHistory := answer.history
  localTarget := answer.target
  target := answer.target

theorem primitive_valid (answer : Answer schema (source := source))
    (enabled : plan.permissions.sites.enabled = true) (ordinal : answer.index = schema.ordinal) :
    (primitive schema answer).Valid plan schema.bound schema.programCarrier source := by
  have sorted := source_sorted schema answer
  refine ⟨⟨schema.declared, .here enabled sorted.2.2.1 sorted.1⟩, ?_, rfl, rfl,
    target_sorted schema answer⟩
  simpa only [primitive, SiteData.here, ordinal,
    GeneralPlanEnvironment.environmentWith_empty] using answer.valid

/-- Only computed root metadata and the emitted answer's actual declaration
index are needed. Matching, premises and typing come from original evidence. -/
def fromAnswer (root : schema.position = [])
    (sameBound : schema.focusBound = schema.bound)
    (sameCarrier : schema.focusCarrier = schema.programCarrier)
    (enabled : plan.permissions.sites.enabled = true)
    (answer : Answer schema (source := source)) (ordinal : answer.index = schema.ordinal) :
    Event schema where
  focus := source
  assignment := answer.completed
  source := source
  target := answer.target
  focusTyped := by
    rw [sameBound, sameCarrier]
    exact ((GeneralPlanEnvironment.typing_iff plan schema.bound schema.programCarrier source).mp
      (source_sorted schema answer)).1
  filling := by simp only [Schema.fill?, root, Instantiation.fill?]
  specified := specified_rhs schema answer ordinal
  receipt := ⟨source, [], primitive schema answer⟩
  valid := ⟨.nil _, primitive_valid schema answer enabled ordinal⟩
  ordinal := rfl
  declaration := rfl
  ambient := rfl
  completed := rfl
  conversion := .refl _

theorem fromAnswer_complete_origins (root : schema.position = [])
    (sameBound : schema.focusBound = schema.bound)
    (sameCarrier : schema.focusCarrier = schema.programCarrier)
    (enabled : plan.permissions.sites.enabled = true)
    (answer : Answer schema (source := source)) (ordinal : answer.index = schema.ordinal) :
    let event := fromAnswer schema root sameBound sameCarrier enabled answer ordinal
    event.receipt.firing.matcherTrace = answer.trace ∧
      event.receipt.firing.captured = answer.captured ∧
      event.receipt.firing.completed = answer.completed ∧
      event.receipt.firing.premiseHistory = answer.history ∧
      event.target = answer.target :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem fromAnswer_semantic_step (root : schema.position = [])
    (sameBound : schema.focusBound = schema.bound)
    (sameCarrier : schema.focusCarrier = schema.programCarrier)
    (enabled : plan.permissions.sites.enabled = true)
    (answer : Answer schema (source := source)) (ordinal : answer.index = schema.ordinal) :
    (GeneralOccurrenceSemantics.gslt plan schema.bound schema.programCarrier).Step source answer.target :=
  (fromAnswer schema root sameBound sameCarrier enabled answer ordinal).semantic_step schema

/-- Select the actual authored focus from an emitted execution answer.
All nonroot scope and filling conditions are checked computationally. A
failed encoding is not a negative operational or native judgment. -/
def at? (enabled : plan.permissions.sites.enabled = true)
    (answer : Answer schema (source := source)) : Option (Event schema) :=
  if ordinal : answer.index = schema.ordinal then
    match _focused : Mettapedia.OSLF.Framework.RedexPosition.subtermAt source schema.position with
    | none => none
    | some focus =>
        if sorted : checkHasType plan.snapshot.language plan.snapshot.free
            schema.focusBound focus schema.focusCarrier = true then
          if filled : schema.fill? answer.completed focus = some source then
            some {
              focus := focus
              assignment := answer.completed
              source := source
              target := answer.target
              focusTyped := checkHasType_sound sorted
              filling := filled
              specified := specified_rhs schema answer ordinal
              receipt := ⟨source, [], primitive schema answer⟩
              valid := ⟨.nil _, primitive_valid schema answer enabled ordinal⟩
              ordinal := rfl
              declaration := rfl
              ambient := rfl
              completed := rfl
              conversion := .refl _ }
          else none
        else none
  else none

theorem at?_origins (enabled : plan.permissions.sites.enabled = true)
    (answer : Answer schema (source := source)) {event : Event schema}
    (encoded : at? schema enabled answer = some event) :
    event.source = source ∧ event.target = answer.target ∧
      event.assignment = answer.completed ∧
      Mettapedia.OSLF.Framework.RedexPosition.subtermAt source schema.position = some event.focus ∧
      event.receipt.firing.matcherTrace = answer.trace ∧
      event.receipt.firing.captured = answer.captured ∧
      event.receipt.firing.completed = answer.completed ∧
      event.receipt.firing.premiseHistory = answer.history := by
  unfold at? at encoded
  split at encoded
  · split at encoded
    · cases encoded
    · rename_i focus focused
      split at encoded
      · split at encoded
        · cases Option.some.inj encoded
          exact ⟨rfl, rfl, rfl, focused, rfl, rfl, rfl, rfl⟩
        · cases encoded
      · cases encoded
  · cases encoded

theorem at?_complete (enabled : plan.permissions.sites.enabled = true)
    (answer : Answer schema (source := source)) (ordinal : answer.index = schema.ordinal)
    (focus : Pattern)
    (focused : Mettapedia.OSLF.Framework.RedexPosition.subtermAt source schema.position = some focus)
    (typed : HasType plan.snapshot.language plan.snapshot.free schema.focusBound focus schema.focusCarrier)
    (object : isObjectPattern focus = true)
    (filled : schema.fill? answer.completed focus = some source) :
    ∃ event, at? schema enabled answer = some event := by
  have sorted := checkHasType_complete_of_object typed object
  unfold at?
  split
  · split
    · rename_i absent
      rw [focused] at absent
      cases absent
    · rename_i actual selected
      have same := Option.some.inj (selected.symm.trans focused)
      subst actual
      split
      · exact ⟨_, rfl⟩
      · contradiction
  · contradiction

end Mettapedia.OSLF.NativeTypes.Modal.NativeRootEvent
