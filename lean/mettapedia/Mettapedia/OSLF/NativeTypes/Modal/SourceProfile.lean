import Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction
import Mettapedia.OSLF.MeTTaIL.GeneralRhoBinding

open Mettapedia.OSLF.Framework

/-!
# Source introduction for every properly sorted function body

One authored base rule Box(F) to Done supplies a modality at its function
slot. Every ambient typing context and every canonical, scoped object body
of that function carrier passes the computed introduction algorithm.
Matching is derived from the actual inverse of contextual instantiation;
no matching proof or admissibility predicate is supplied by the consumer.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.SourceProfile

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Modal.Rules
open Mettapedia.OSLF.NativeTypes.Modal.SourceIntroduction

def carrier : TypeExpr := .base "Term"
def functionCarrier : TypeExpr := .arrow carrier carrier
def done : Pattern := .apply "Done" []
def box (body : Pattern) : Pattern := .apply "Box" [body]

def declarationRule : RewriteRule where
  name := "box-function-done"
  typeContext := [("F", functionCarrier)]
  premises := []
  left := box (.fvar "F")
  right := done

def doneGrammar : GrammarRule :=
  {label := "Done", category := "Term", params := [], syntaxPattern := []}
def boxGrammar : GrammarRule :=
  {label := "Box", category := "Term", params := [.simple "body" functionCarrier], syntaxPattern := []}
def language : LanguageDef where
  name := "function-slot-introduction"
  types := ["Term"]
  terms := [doneGrammar, boxGrammar]
  equations := []
  rewrites := [declarationRule]

def snapshot : Snapshot := ⟨language, [], ⟨[], []⟩⟩
def permissions : Permissions := {sites := .all}
def binding : GeneralRuleBindingInference.BindingPlan :=
  ⟨GeneralRuleBindingInference.inferredSpec declarationRule, .inferredRootInputs⟩
def declaration : RulePlan := ⟨0, declarationRule, binding⟩
def runtimePlan : Plan := ⟨snapshot, permissions, [declaration], [], []⟩

theorem actual_plan : compile snapshot permissions = runtimePlan := by cbv

def schema (bound : List TypeExpr) : Schema runtimePlan where
  ordinal := 0
  declaration := declaration
  declared := List.mem_cons_self
  position := (RedexPosition.positions declarationRule.left)[1]?.getD []
  bound := bound
  programCarrier := carrier
  focusBound := bound
  focusCarrier := functionCarrier

theorem schema_position (bound : List TypeExpr) : (schema bound).position = [0] := by cbv

def value (bound : List TypeExpr) (body : Pattern) : ContextualValue := ⟨[], bound.length, body⟩
def assignment (bound : List TypeExpr) (body : Pattern) : Assignment := [("F", value bound body)]

theorem assignment_lookup (bound : List TypeExpr) (body : Pattern) :
    lookup (assignment bound body) "F" = some (value bound body) := by
  simp only [assignment, lookup, List.find?_cons, beq_self_eq_true, Option.map_some]

private theorem dependency_lookup : dependencies? declaration.binding.spec "F" = some [] := by cbv

private theorem left_arguments : arguments? declaration.rule declaration.binding.spec "F" .left [0] = some [] := by cbv

theorem variable_instance {bound : List TypeExpr} {body : Pattern} {supplied : Assignment}
    (safe : body.isWellScopedAt bound.length = true)
    (reads : lookup supplied "F" = some (value bound body)) :
    instantiateWith? (schema bound).operation declaration.rule declaration.binding.spec bound.length
      .left [0] 0 supplied (.fvar "F") = some body := by
  simp only [instantiateWith?, reads, left_arguments, Option.bind_eq_bind, Option.bind_some]
  exact GeneralRho.instantiate_root safe

theorem source_instance {bound : List TypeExpr} {body : Pattern} {supplied : Assignment}
    (safe : body.isWellScopedAt bound.length = true)
    (reads : lookup supplied "F" = some (value bound body)) :
    instantiateWith? (schema bound).operation declaration.rule declaration.binding.spec bound.length
      .left [] 0 supplied declaration.rule.left = some (box body) := by
  have left : declaration.rule.left = box (.fvar "F") := rfl
  rw [left]
  have bodyInstance : instantiateValue? (value bound body) bound.length 0 [] = some body :=
    GeneralRho.instantiate_root safe
  simp only [box, instantiateWith?, instantiateArgsWith?, List.nil_append, reads,
    left_arguments, Option.bind_eq_bind, Option.bind_some, bodyInstance]

theorem rhs_instance (bound : List TypeExpr) (supplied : Assignment) :
    (schema bound).rhs? supplied = some done := by
  simp only [Schema.rhs?, schema, declaration, RulePlan.rule, declarationRule,
    GeneralRuleBindingInference.BindingPlan.elaborate,
    reductWith?, done, instantiateWith?, instantiateArgsWith?, Option.bind_eq_bind]
  rfl

theorem typed_box {bound : List TypeExpr} {body : Pattern}
    (typed : HasType language snapshot.free bound body functionCarrier) :
    HasType language snapshot.free bound (box body) carrier := by
  apply HasType.constructor (rule := boxGrammar)
  · change boxGrammar ∈ [doneGrammar, boxGrammar]
    exact List.mem_cons.mpr (.inr List.mem_cons_self)
  · simp [UsesBareCollection, boxGrammar, functionCarrier]
  · exact .cons (parameter := .simple "body" functionCarrier) trivial rfl typed .nil

theorem proper_box {bound : List TypeExpr} {body : Pattern}
    (proper : OpenPatternWellSorted language snapshot.free bound functionCarrier body) :
    OpenPatternWellSorted language snapshot.free bound carrier (box body) := by
  refine ⟨typed_box proper.1, ?_, ?_, ?_⟩
  · simpa only [box, Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList, Bool.and_true] using proper.2.1
  · simpa only [box, isObjectPattern, isObjectPatternList, Bool.and_true] using proper.2.2.1
  · simpa only [ScopeSafeAt, box, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, Bool.and_true] using proper.2.2.2

theorem proper_done (bound : List TypeExpr) :
    OpenPatternWellSorted language snapshot.free bound carrier done := by
  apply checkOpenPatternWellSorted_sound
  cbv

theorem assignment_typed {bound : List TypeExpr} {body : Pattern}
    (typed : HasType language snapshot.free bound body functionCarrier)
    (object : isObjectPattern body = true) :
    GeneralPremise.TypedAssignment (GeneralPlanEnvironment.environment runtimePlan)
      (schema bound).context (assignment bound body) := by
  constructor
  · intro name actual member
    have same : (name, actual) = ("F", value bound body) := by
      simpa only [assignment, List.mem_singleton] using member
    cases same
    refine ⟨[], functionCarrier, dependency_lookup, ?_, rfl, rfl, ?_⟩
    · cbv
    · exact GeneralLanguageTyping.type_transport (GeneralPlanEnvironment.grammar runtimePlan).symm typed
  · intro name actual member
    have same : (name, actual) = ("F", value bound body) := by
      simpa only [assignment, List.mem_singleton] using member
    cases same
    exact object

def primitive (bound : List TypeExpr) (body : Pattern) : GeneralRuleJobs.Receipt where
  job := job (schema bound) (box body)
  matcherTrace := []
  captured := assignment bound body
  completed := assignment bound body
  premiseHistory := []
  localTarget := done
  target := done

def result (bound : List TypeExpr) (body : Pattern) : BaseIntroduction :=
  ⟨box body, done, primitive bound body⟩

/-- The complete family computes its captures through the actual inverse of
its scoped variable occurrence. No matching is a theorem argument. -/
theorem introduction_derived {bound : List TypeExpr} {body : Pattern} {supplied : Assignment}
    (proper : OpenPatternWellSorted language snapshot.free bound functionCarrier body)
    (reads : lookup supplied "F" = some (value bound body)) :
    BaseDerivation (schema bound) supplied (result bound body) := by
  refine ⟨source_instance proper.2.2.2 reads, rhs_instance bound supplied, rfl, rfl,
    (GeneralPlanEnvironment.typing_iff runtimePlan bound carrier (box body)).mpr (proper_box proper),
    rfl, ?_, rfl, rfl, ?_, assignment_typed proper.1 proper.2.2.1,
    rhs_instance bound (assignment bound body),
    (GeneralPlanEnvironment.typing_iff runtimePlan bound carrier done).mpr (proper_done bound), rfl, rfl⟩
  · change GeneralScopedMatchMachine.TracedMatches declaration.rule declaration.binding.spec bound.length
      .left [] 0 [] (box (.fvar "F")) (box body) [] (assignment bound body)
    apply GeneralScopedMatchMachine.TracedMatches.constructor
    apply GeneralScopedMatchMachine.TracedArguments.cons (headTrace := []) (tailTrace := [])
      (middle := assignment bound body)
    · apply GeneralScopedMatchMachine.TracedMatches.capture
      simp only [capture?, dependency_lookup, List.nil_append, left_arguments, Option.bind_eq_bind, Option.bind_some,
        GeneralRho.recover_root proper.2.2.2]
      rfl
    · exact .nil
  · cbv

/-- Computed source admission succeeds for every ambient context and every
properly sorted function body, including bodies containing binders. -/
theorem all_proper_bodies_execute {bound : List TypeExpr} {body : Pattern} {supplied : Assignment}
    (proper : OpenPatternWellSorted language snapshot.free bound functionCarrier body)
    (reads : lookup supplied "F" = some (value bound body)) :
    result bound body ∈ baseIntroductions (schema bound) supplied :=
  baseIntroductions_complete (introduction_derived proper reads)

def continuation : Continuation := fun _ target => PLift (target = done)

private theorem request_reads {bound : List TypeExpr} {body : Pattern} {supplied : Assignment}
    (request : TypedRequest (schema bound) (fun _ _ => False) (assignment bound body) supplied) :
    lookup supplied "F" = some (value bound body) := by
  have agreement := request.2.2.1 "F" (by
    have names : (schema bound).matchedNames = ["F"] := by cbv
    rw [names]
    exact List.mem_cons_self)
  exact agreement.trans (assignment_lookup bound body)

/-- The source-shaped modal introduction is now obtained from the
computed capture check, rather than from a supplied matching derivation. -/
def bodyEvidence {bound : List TypeExpr} {body : Pattern}
    (proper : OpenPatternWellSorted language snapshot.free bound functionCarrier body) :
    Evidence (schema bound) (fun _ _ => False) continuation body :=
  m_intro_computed proper.1 (assignment bound body)
    (assignment_typed proper.1 proper.2.2.1)
    (by
      intro name present
      have names : (schema bound).matchedNames = ["F"] := by cbv
      have same : name = "F" := by simpa only [names, List.mem_singleton] using present
      subst name
      exact ⟨value bound body, assignment_lookup bound body⟩)
    (fun supplied request => by
      rw [schema_position]
      apply Mettapedia.OSLF.NativeTypes.Modal.Instantiation.FocusInstance.application (index := 0) (argument := .fvar "F") rfl
      exact .here (variable_instance proper.2.2.2 (request_reads request)))
    (fun supplied request => by
      intro empty
      have admitted := all_proper_bodies_execute proper (request_reads request)
      rw [empty] at admitted
      exact List.not_mem_nil admitted)
    (fun supplied _ target rhs => by
      have same : target = done := Option.some.inj (rhs.symm.trans (rhs_instance bound supplied))
      exact ⟨same⟩)

theorem all_proper_bodies_inhabit {bound : List TypeExpr} {body : Pattern}
    (proper : OpenPatternWellSorted language snapshot.free bound functionCarrier body) :
    Inhabits (schema bound) (fun _ _ => False) continuation body := ⟨bodyEvidence proper⟩

end Mettapedia.OSLF.NativeTypes.Modal.SourceProfile
