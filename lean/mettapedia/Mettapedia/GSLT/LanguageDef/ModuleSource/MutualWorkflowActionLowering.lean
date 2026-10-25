import Mettapedia.GSLT.LanguageDef.ModuleSource.PositiveInductiveLowering
import Mettapedia.TypeTheory.PositiveInductiveScenarios

/-!
# Textual lowering for the mutual Workflow/Action family

The shared `.module` syntax stores a list of inductive families, while the
first registered-positive lowering selected one family.  This module checks a
genuine two-family source and joins both declarations into the existing
Boolean-indexed mutual polynomial.

The family headers remain distinct (`Workflow` and `Action`), but recursive
fields resolve through one shared index language.  A post-lowering target
check prevents a Workflow constructor from returning Action or conversely.
Constructor names must be unique across the whole mutual block.  Accepted
source data round-trips exactly and erases to the independently specified
Workflow/Action block.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.MutualWorkflowActionLowering

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.PositiveInductiveBlock
open Mettapedia.TypeTheory.PositiveInductiveScenarios
open InductiveSyntax
open PositiveInductiveLowering

abbrev registry := PositiveInductiveScenarios.Workflow.registry
abbrev interface := PositiveInductiveScenarios.Workflow.interface

def workflowTerm : Term := .name "Workflow"
def actionTerm : Term := .name "Action"
def boolTerm : Term := .name "Bool"

def classify {context : List interface.SortCode} (_scope : PUnit)
    (source : Term) : Option (FieldMeaning registry interface context) :=
  if source = boolTerm then some (.data .action)
  else if source = workflowTerm then some (.recursive false)
  else if source = actionTerm then some (.recursive true)
  else none

def quoteField {context : List interface.SortCode} (_scope : PUnit) :
    FieldMeaning registry interface context → Term
  | .data .action => boolTerm
  | .recursive false => workflowTerm
  | .recursive true => actionTerm
  | .nested name container registered index => by
      simp [PositiveInductiveScenarios.Workflow.registry] at registered

theorem classify_quote {context : List interface.SortCode} (scope : PUnit)
    (meaning : FieldMeaning registry interface context) :
    classify scope (quoteField scope meaning) = some meaning := by
  cases meaning with
  | data sort => cases sort; rfl
  | recursive index => cases index <;> rfl
  | nested name container registered index =>
      simp [PositiveInductiveScenarios.Workflow.registry] at registered

theorem quote_classify {context : List interface.SortCode} (scope : PUnit)
    (source : Term) (meaning : FieldMeaning registry interface context)
    (accepted : classify scope source = some meaning) :
    quoteField scope meaning = source := by
  by_cases isBool : source = boolTerm
  · have same : meaning = .data .action := by
      simpa [classify, isBool] using accepted.symm
    subst meaning
    exact isBool.symm
  · by_cases isWorkflow : source = workflowTerm
    · have same : meaning = .recursive false := by
        exact Option.some.inj (by
          simpa [classify, isBool, isWorkflow, boolTerm, workflowTerm]
            using accepted.symm)
      subst meaning
      exact isWorkflow.symm
    · by_cases isAction : source = actionTerm
      · have same : meaning = .recursive true := by
          exact Option.some.inj (by
            simpa [classify, isBool, isWorkflow, isAction, boolTerm,
              workflowTerm, actionTerm] using accepted.symm)
        subst meaning
        exact isAction.symm
      · simp [classify, isBool, isWorkflow, isAction] at accepted

def result? {context : List interface.SortCode} (_scope : PUnit)
    (source : Term) : Option (interface.IndexExpr context) :=
  if source = workflowTerm then some false
  else if source = actionTerm then some true
  else none

def quoteResult {context : List interface.SortCode} (_scope : PUnit) :
    interface.IndexExpr context → Term
  | false => workflowTerm
  | true => actionTerm

theorem result_quote {context : List interface.SortCode} (scope : PUnit)
    (index : interface.IndexExpr context) :
    result? scope (quoteResult scope index) = some index := by
  cases index <;> rfl

theorem quote_result {context : List interface.SortCode} (scope : PUnit)
    (source : Term) (index : interface.IndexExpr context)
    (accepted : result? scope source = some index) :
    quoteResult scope index = source := by
  by_cases isWorkflow : source = workflowTerm
  · have same : index = false := by
      exact Option.some.inj (by
        simpa [result?, isWorkflow] using accepted.symm)
    subst index
    simpa [quoteResult] using isWorkflow.symm
  · by_cases isAction : source = actionTerm
    · have same : index = true := by
        exact Option.some.inj (by
          simpa [result?, isWorkflow, isAction, workflowTerm, actionTerm]
            using accepted.symm)
      subst index
      simpa [quoteResult] using isAction.symm
    · simp [result?, isWorkflow, isAction] at accepted

def codec (familyName : String) : Codec registry interface 0 [] where
  Scope := fun _ => PUnit
  initialScope := PUnit.unit
  bindData := fun _ _ _ => PUnit.unit
  block := fun _ _ => PUnit.unit
  classify := classify
  classify_arrow := by
    intro current scope domain codomain
    simp [classify, boolTerm, workflowTerm, actionTerm]
  quoteField := quoteField
  classify_quote := classify_quote
  quote_classify := quote_classify
  result? := result?
  quoteResult := quoteResult
  result_quote := result_quote
  quote_result := quote_result
  familyName := familyName
  parameters := []
  indices := []
  sort := .name "Type"

def workflowCodec : Codec registry interface 0 [] := codec "Workflow"
def actionCodec : Codec registry interface 0 [] := codec "Action"

namespace Code

/-- The ultimate family index of a lowered constructor.  This specialization
is total because the Workflow interface uses a context-independent Boolean
index expression. -/
def targetIndex : {context : List interface.SortCode} →
    PositiveInductiveLowering.Code (registry := registry) (I := interface)
      (parameterCount := 0) context → Bool
  | _, .result index => index
  | _, .data _ _ rest => targetIndex rest
  | _, .recursive _ _ rest => targetIndex rest
  | _, .nested _ _ _ registered _ _ => by
      simp [PositiveInductiveScenarios.Workflow.registry] at registered

end Code

def targets (family : ResolvedFamily (registry := registry) (I := interface)
    (parameterCount := 0) []) (expected : Bool) : Bool :=
  family.constructors.all fun constructor =>
    Code.targetIndex constructor.body == expected

def constructorNames
    (first second : ResolvedFamily (registry := registry) (I := interface)
      (parameterCount := 0) []) : List String :=
  (first.constructors ++ second.constructors).map (·.name)

structure ResolvedMutual where
  workflow : ResolvedFamily (registry := registry) (I := interface)
    (parameterCount := 0) []
  action : ResolvedFamily (registry := registry) (I := interface)
    (parameterCount := 0) []
  workflowTargets : targets workflow false = true
  actionTargets : targets action true = true
  uniqueNames : (constructorNames workflow action).Nodup

namespace ResolvedMutual

def quote (resolved : ResolvedMutual) : List InductiveSyntax.Family :=
  [resolved.workflow.quote workflowCodec,
    resolved.action.quote actionCodec]

def erase (resolved : ResolvedMutual) :
    PositiveInductiveBlock.Admitted registry interface 0 [] where
  constructors :=
    (resolved.workflow.constructors ++ resolved.action.constructors).map
      fun constructor => ⟨constructor.name, constructor.body.erase⟩
  uniqueNames := by
    simpa [constructorNames, Function.comp_def] using resolved.uniqueNames

end ResolvedMutual

/-- Lower exactly two named families, retain their target indices, and reject
constructor-name collisions across the mutual block. -/
def lowerFamilies : List InductiveSyntax.Family → Option ResolvedMutual
  | [workflowSource, actionSource] => do
      let workflow ← lowerFamily workflowCodec workflowSource
      let action ← lowerFamily actionCodec actionSource
      if hWorkflow : targets workflow false = true then
        if hAction : targets action true = true then
          if hUnique : (constructorNames workflow action).Nodup then
            some ⟨workflow, action, hWorkflow, hAction, hUnique⟩
          else none
        else none
      else none
  | _ => none

@[simp] theorem lowerFamilies_quote (resolved : ResolvedMutual) :
    lowerFamilies resolved.quote = some resolved := by
  cases resolved with
  | mk workflow action workflowTargets actionTargets uniqueNames =>
      simp [ResolvedMutual.quote, lowerFamilies, lowerFamily_quote,
        workflowTargets, actionTargets, uniqueNames]

structure PairSource where
  moduleName : String
  theoryName : String
  families : List InductiveSyntax.Family

def PairSource.quote (source : PairSource) : Module :=
  ⟨[], source.moduleName,
    [⟨source.theoryName, [], .extend none [.inductives source.families]⟩],
    some ([source.theoryName], [])⟩

/-- The mutual lane is exact: imports, joins, theory parameters, extra blocks,
and family counts other than two are refused. -/
def selectPair : Module → Option PairSource
  | ⟨[], moduleName,
      [⟨theoryName, [], .extend none [.inductives families]⟩],
      some ([entry], [])⟩ =>
        if entry = theoryName ∧ families.length = 2 then
          some ⟨moduleName, theoryName, families⟩
        else none
  | _ => none

theorem selectPair_quote (source : PairSource)
    (two : source.families.length = 2) :
    selectPair source.quote = some source := by
  cases source with
  | mk moduleName theoryName families =>
      simp [PairSource.quote, selectPair, two]

theorem selectPair_exact (source : Module) (selected : PairSource)
    (accepted : selectPair source = some selected) :
    selected.quote = source := by
  unfold selectPair at accepted
  split at accepted
  · split at accepted
    · rename_i valid
      cases Option.some.inj accepted
      simp only [PairSource.quote, valid.1]
    · cases accepted
  · cases accepted

structure ResolvedModule where
  moduleName : String
  theoryName : String
  block : ResolvedMutual

def ResolvedModule.quote (resolved : ResolvedModule) : Module :=
  (PairSource.mk resolved.moduleName resolved.theoryName resolved.block.quote).quote

def lowerModule (source : Module) : Option ResolvedModule :=
  match selectPair source with
  | none => none
  | some selected =>
      match lowerFamilies selected.families with
      | none => none
      | some block => some ⟨selected.moduleName, selected.theoryName, block⟩

@[simp] theorem lowerModule_quote (resolved : ResolvedModule) :
    lowerModule resolved.quote = some resolved := by
  cases resolved with
  | mk moduleName theoryName block =>
      unfold ResolvedModule.quote lowerModule
      rw [selectPair_quote _ (by simp [ResolvedMutual.quote])]
      simp only
      rw [lowerFamilies_quote]

/-! ## The concrete workflow/action block -/

namespace Controls

def done : ResolvedConstructor (registry := registry) (I := interface)
    (parameterCount := 0) [] :=
  ⟨"done", .result false⟩

def schedule : ResolvedConstructor (registry := registry) (I := interface)
    (parameterCount := 0) [] :=
  ⟨"schedule", .recursive "next" true (.result false)⟩

def action : ResolvedConstructor (registry := registry) (I := interface)
    (parameterCount := 0) [] :=
  ⟨"action", .data "permitted" .action (.result true)⟩

def subworkflow : ResolvedConstructor (registry := registry) (I := interface)
    (parameterCount := 0) [] :=
  ⟨"subworkflow", .recursive "plan" false (.result true)⟩

def workflowFamily : ResolvedFamily (registry := registry) (I := interface)
    (parameterCount := 0) [] :=
  ⟨[done, schedule], by decide⟩

def actionFamily : ResolvedFamily (registry := registry) (I := interface)
    (parameterCount := 0) [] :=
  ⟨[action, subworkflow], by decide⟩

def block : ResolvedMutual :=
  ⟨workflowFamily, actionFamily, rfl, rfl, by decide⟩

def resolvedModule : ResolvedModule :=
  ⟨"AgentWorkflow", "Data", block⟩

def textualModule : Module := resolvedModule.quote

theorem module_roundtrip : lowerModule textualModule = some resolvedModule := by
  exact lowerModule_quote resolvedModule

/-- The two textual family headers erase to the independently specified
Boolean-indexed mutual block, with constructor order and child indices intact.
-/
theorem erased_eq_existing : block.erase =
    PositiveInductiveScenarios.Workflow.admitted := by
  rfl

def wrongWorkflowResult : InductiveSyntax.Family :=
  { workflowFamily.quote workflowCodec with constructors :=
      [⟨"done", [], actionTerm⟩, schedule.quote workflowCodec] }

theorem wrong_workflow_result_refused :
    lowerFamilies [wrongWorkflowResult, actionFamily.quote actionCodec] = none := by
  rfl

def duplicateAcrossFamilies : InductiveSyntax.Family :=
  { actionFamily.quote actionCodec with constructors :=
      [⟨"done", [⟨"permitted", boolTerm⟩], actionTerm⟩,
        subworkflow.quote actionCodec] }

theorem duplicate_across_families_refused :
    lowerFamilies
      [workflowFamily.quote workflowCodec, duplicateAcrossFamilies] = none := by
  rfl

theorem swapped_families_refused :
    lowerFamilies
      [actionFamily.quote actionCodec, workflowFamily.quote workflowCodec] = none := by
  rfl

def negativeWorkflow : InductiveSyntax.Family :=
  { workflowFamily.quote workflowCodec with constructors :=
      [⟨"bad", [⟨"consume", .arrow actionTerm workflowTerm⟩], workflowTerm⟩] }

theorem negative_field_refused :
    lowerFamilies [negativeWorkflow, actionFamily.quote actionCodec] = none := by
  rfl

def verdicts : List (String × Bool) :=
  [ ("mutual workflow/action module lowers",
      (lowerModule textualModule).isSome)
  , ("workflow constructor cannot return action",
      decide
        (lowerFamilies [wrongWorkflowResult, actionFamily.quote actionCodec] = none))
  , ("constructor names are unique across families",
      decide
        (lowerFamilies
          [workflowFamily.quote workflowCodec, duplicateAcrossFamilies] = none))
  , ("family order is retained",
      decide
        (lowerFamilies
          [actionFamily.quote actionCodec, workflowFamily.quote workflowCodec] = none))
  , ("negative field is refused",
      decide
        (lowerFamilies [negativeWorkflow, actionFamily.quote actionCodec] = none)) ]

theorem verdicts_all : verdicts.all Prod.snd = true := by
  decide

end Controls

section AxiomAudit

#print axioms lowerFamilies_quote
#print axioms selectPair_exact
#print axioms lowerModule_quote
#print axioms Controls.module_roundtrip
#print axioms Controls.erased_eq_existing
#print axioms Controls.wrong_workflow_result_refused
#print axioms Controls.duplicate_across_families_refused
#print axioms Controls.swapped_families_refused
#print axioms Controls.negative_field_refused
#print axioms Controls.verdicts_all

end AxiomAudit

end Mettapedia.GSLT.LanguageDef.ModuleSource.MutualWorkflowActionLowering
