import Mettapedia.OSLF.NativeTypes.Modal.InstanceDecision
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated
import Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls
import Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls

open Mettapedia.OSLF.Framework

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls

open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.NativeTypes.Generation Mettapedia.OSLF.NativeTypes.Modal.Rules Mettapedia.OSLF.NativeTypes.Modal.Formation
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.OSLF.NativeTypes.Modal.InstanceDecision
open Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated (generated)

theorem actual_catalogue : generated.modalCatalogue = schemas generated.plan := by
  change (if (generated.equationAdmission != some false) && generated.logicFragment.core.modal
    then schemas generated.plan else []) = _
  rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_equation_admission]
  rfl

def authoredRule : RewriteRule := Mettapedia.Languages.PartrecMachine.rewrites[0]'(by decide)

def declaration : RulePlan :=
  ⟨0, authoredRule, ⟨GeneralRuleBindingInference.inferredSpec authoredRule, .inferredRootInputs⟩⟩

theorem actual_declaration : (declaration, 0) ∈ generated.plan.rules.zipIdx := by
  rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  unfold Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan
  dsimp only [compile]
  cbv

theorem actual_plan_snapshot : generated.plan.snapshot = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.snapshot := by
  rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]
  rfl

def localSites : List GeneralTypedSites.SiteData :=
  Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.generate Mettapedia.Languages.PartrecMachine.partrecMachine
    (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.ruleFree declaration.rule)
    .all [] (.base "Cfg") declaration.rule.left

def selectedSite : GeneralTypedSites.SiteData := localSites[1]'(by cbv)

def schema : Schema generated.plan where
  ordinal := 0
  declaration := declaration
  declared := actual_declaration
  position := selectedSite.address
  bound := []
  programCarrier := .base "Cfg"
  focusBound := selectedSite.focusBound
  focusCarrier := selectedSite.focusType

theorem actual_schema : schema ∈ generated.modalCatalogue := by
  rw [actual_catalogue]
  unfold schemas
  apply List.mem_flatMap.mpr
  refine ⟨⟨(declaration, 0), actual_declaration⟩, List.mem_attach _ _, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨.base "Cfg", ?_, ?_⟩
  · rw [actual_plan_snapshot]
    cbv
    exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
  · rw [actual_plan_snapshot]
    exact List.mem_map.mpr ⟨selectedSite, List.getElem_mem _, rfl⟩

theorem computed_schema : schema.position = [0] ∧ schema.relyNames = ["k", "v"] ∧
    schema.focusCarrier = .base "Code" ∧ schema.focusBound = [] ∧ schema.bound = [] ∧
    schema.programCarrier = .base "Cfg" := by cbv

theorem actual_sort_assignments : generated.sortAssignments = Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.assignments
    Mettapedia.Languages.PartrecMachine.partrecMachine (fun _ => .star, fun _ => .star) := by
  change Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.assignments Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.chosen.language
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.vertex = _
  simp only [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.chosen, selectedSnapshot,
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.fragment]
  rfl

def parameters : ModalParameters schema := (generated.modalParameters? schema).get (by
  unfold Generated.modalParameters? schemaAssignment?
  rw [actual_sort_assignments]
  cbv)

theorem actual_parameters : generated.modalParameters? schema = some parameters :=
  (Option.some_get _).symm

private theorem rely_name (name : RelyIndex schema) : name.val = "k" ∨ name.val = "v" := by
  simpa only [computed_schema.2.1, List.mem_cons, List.not_mem_nil, or_false] using name.property

def relyCarrier (name : RelyIndex schema) : TypeExpr :=
  if name.val = "k" then .base "Cont" else .base "Nats"

def relyCodes : RelyCodes schema parameters.inputs := fun name =>
  {carrier := relyCarrier name
   dependencies := []
   declaredCarrier := by
     rcases rely_name name with k | v
     · simp only [relyCarrier, k]
       cbv
     · simp only [relyCarrier, v]
       cbv
   declaredDependencies := by
     rcases rely_name name with k | v
     · rw [k]; cbv
     · rw [v]; cbv
   meaning value := value.dependencies = [] ∧ value.ambient = 0 ∧
     checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free []
       (relyCarrier name) value.body = true
   bounded value valid := by
     refine ⟨valid.1, ?_, (checkOpenPatternWellSorted_sound valid.2.2).1⟩
     rw [computed_schema.2.2.2.2.1]
     exact valid.2.1}

def supplied : ScopedRuleMatching.Assignment :=
  [("k", ⟨[], 0, Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.haltCont⟩),
   ("v", ⟨[], 0, Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.nil⟩)]

def continuationCode (permit : Bool) (assignment : ScopedRuleMatching.Assignment) :
    TypeCode generated.plan schema.bound schema.programCarrier parameters.output where
  meaning result := checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
    schema.bound schema.programCarrier result = true ∧
    lookup assignment "k" = some ⟨[], 0, Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.haltCont⟩ ∧
    lookup assignment "v" = some ⟨[], 0, Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.nil⟩ ∧ permit = true
  bounded _ valid := (checkOpenPatternWellSorted_sound valid.1).1

def codes (permit : Bool) : ModalInstanceCodes generated schema :=
  ⟨parameters, actual_parameters, relyCodes, continuationCode permit⟩

def decisions (permit : Bool) : ModalInstanceDecisions (codes permit) where
  rely _name _value := by dsimp only [codes, relyCodes]; infer_instance
  continuation _assignment _result := by dsimp only [codes, continuationCode]; infer_instance

def focus : Pattern := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.zeroCode

theorem source_filling : schema.fill? supplied focus = some Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source := by
  unfold Schema.fill? Schema.operation
  dsimp only [schema]
  rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]
  cbv

theorem specified_rhs : schema.rhs? supplied = some Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.firstTarget := by
  unfold Schema.rhs? Schema.operation
  dsimp only [schema]
  rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]
  cbv

theorem focus_checked : checkOpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free
    schema.focusBound schema.focusCarrier focus = true := by
  rw [actual_plan_snapshot]
  cbv

theorem request_checked (permit : Bool) : checkInstanceRequest (codes permit) (decisions permit) supplied = true := by
  have typed : GeneralPremise.checkTypedAssignment (GeneralPlanEnvironment.environment generated.plan)
      schema.context supplied = true := by
    dsimp only [Schema.context, schema]
    rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]
    cbv
  have rely : checkInstanceRely (codes permit) (decisions permit) supplied = true := by
    unfold checkInstanceRely
    apply List.all_eq_true.mpr
    intro name _present
    rcases rely_name name with k | v
    · have found : lookup supplied name.val = some ⟨[], 0, Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.haltCont⟩ := by
        rw [k]; rfl
      rw [found]
      apply @decide_eq_true _ ((decisions permit).rely name _)
      change _ = [] ∧ _ = 0 ∧ _ = true
      refine ⟨rfl, rfl, ?_⟩
      simp only [relyCarrier, k]
      rw [actual_plan_snapshot]
      decide +kernel
    · have found : lookup supplied name.val = some ⟨[], 0, Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.nil⟩ := by
        rw [v]; rfl
      rw [found]
      apply @decide_eq_true _ ((decisions permit).rely name _)
      change _ = [] ∧ _ = 0 ∧ _ = true
      refine ⟨rfl, rfl, ?_⟩
      simp only [relyCarrier, v]
      rw [actual_plan_snapshot]
      decide +kernel
  have names : checkInstanceNames schema supplied = true := by
    unfold checkInstanceNames
    cbv
  simp only [checkInstanceRequest, typed, rely, names, Bool.true_and]

def request (permit : Bool) : ModalInstanceRequest (codes permit) supplied focus :=
  {source := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source
   target := Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.firstTarget
   filling := source_filling
   rhs := specified_rhs
   sourceCanonical := by decide +kernel
   targetCanonical := by decide +kernel
   carrier := (checkOpenPatternWellSorted_sound focus_checked).1
   typedRequest := check_instance_request_sound (request_checked permit)}

theorem actual_plugged_source (permit : Bool) :
    (request permit).source = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.source := rfl

theorem actual_specified_contractum (permit : Bool) :
    (request permit).target = Mettapedia.OSLF.NativeTypes.Instances.Partrec.Controls.firstTarget := rfl

def Source : Pattern → Prop :=
  Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.Source generated.plan schema.bound schema.programCarrier

def backend : Backend (GeneratedInstance.system schema) Source :=
  Mettapedia.OSLF.NativeTypes.Instances.Local.Backend.backend generated.plan schema.bound schema.programCarrier rfl
    (by rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]; exact Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_foundation)
    Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_equations
    (by rw [Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_plan]; exact Mettapedia.OSLF.NativeTypes.Instances.Partrec.Backend.plan_generic)

def equations : EquationDecision (GeneratedInstance.system schema) where
  equivalent (first : Pattern) (second : Pattern) := decide (first = second)
  exact (first : Pattern) (second : Pattern) := by
    rw [decide_eq_true_iff]
    change first = second ↔ Relation.EqvGen
      (GeneralOccurrenceSemantics.Equation generated.plan schema.bound schema.programCarrier) first second
    exact (Mettapedia.OSLF.NativeTypes.Instances.Local.Structural.no_equation_iff_eq
      Mettapedia.OSLF.NativeTypes.Instances.Partrec.Generated.generated_equations schema.bound schema.programCarrier first second).symm

def result (permit : Bool) (budget : Nat) :=
  GeneratedInstance.run backend equations (decisions permit) (request permit) budget

def generatedResult (permit : Bool) (budget : Nat) : Except ModalInstanceIssue (Option Bool) :=
  (GeneratedInstance.check schema (codes permit) (decisions permit) backend equations supplied focus budget).map
    (fun run => run.result.answer)

#guard schema.position == [0]
#guard schema.relyNames == ["k", "v"]
#guard (generated.modalFormer? schema (codes true).actualInputs).isSome
#guard generatedResult true 0 == .ok none
#guard generatedResult true 300 == .ok (some true)
#guard generatedResult false 300 == .ok (some false)

theorem typed_plugged_source (permit : Bool) : Source (request permit).source := by
  apply checkOpenPatternWellSorted_sound
  rw [actual_plugged_source]
  decide +kernel

theorem complete_instantiated_question (permit : Bool) :
    (result permit (workBound backend
      (tests equations (request permit).target
        (((codes permit).inputs.2 supplied).meaning (request permit).target)
        (@decide (((codes permit).inputs.2 supplied).meaning (request permit).target)
          ((decisions permit).continuation supplied (request permit).target))
        (@decide_eq_true_iff (((codes permit).inputs.2 supplied).meaning (request permit).target)
          ((decisions permit).continuation supplied (request permit).target)))
      instanceFormula (request permit).source)).Decided :=
  GeneratedInstance.run_complete backend equations (decisions permit) (request permit)
    (typed_plugged_source permit) _ (Nat.le_refl _)

/-- The independent separator has a successful supplied rely assignment but
no full universally quantified rely implementation. -/
theorem instance_does_not_promote_to_family :
    Nonempty (Mettapedia.OSLF.NativeTypes.Modal.Rules.Outcome Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls.schema
      Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha (Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls.supplied
        Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha) Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls.continuation) ∧
      ¬ Mettapedia.OSLF.NativeTypes.Semantics.Modal.predicate Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls.schema
        Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls.rely Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls.continuation
        Mettapedia.OSLF.NativeTypes.Modal.Counterexamples.alpha :=
  Mettapedia.OSLF.NativeTypes.Semantics.Modal.RelyControls.single_completed_instance_is_insufficient

end Mettapedia.OSLF.NativeTypes.Decision.Reference.ModalControls
