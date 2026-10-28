import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogApplication
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! The ground kernel's kept membership premises can use an immutable finite
provider. The provider/store correspondence is explicit: the operation below
does not change the general execution-admission policy. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.QueryKernel

open Mettapedia.OSLF.MeTTaIL Syntax Match Engine

def relation : String := "datalog:known-fact"

def premise : Premise := .relationQuery relation [.fvar "element"]

/-- This lowering retains the actual authored left side, right side and
typing context, replacing only the kept membership operation. -/
def application : RewriteRule :=
  {Kernel.applicationRule with premises := [.forAll "B" "element" premise]}

def language : LanguageDef := {Kernel.language with rewrites := [application]}

def provider (known : List Pattern) : GeneralPremise.ProviderSnapshot where
  signatures := [⟨relation, [.base "DlGroundAtomData"], [.input]⟩]
  rows := known.map fun fact => ⟨relation, [fact]⟩

def environment (known : List Pattern) : RelationEnv where
  tuples := fun requested _ => if requested = relation then known.map (fun fact => [fact]) else []

theorem query_answers_exact (known : List Pattern) (initial result : Bindings) (element : Pattern)
    (bound : initial.lookup "element" = some element) :
    result ∈ premiseStepWithEnv (environment known) language initial premise ↔
      result = initial ∧ element ∈ known := by
  simp only [premise, premiseStepWithEnv, relationQueryStep]
  have builtin : builtinRelationTuples language relation
      ([.fvar "element"].map (applyBindings initial)) = [] := by rfl
  rw [builtin]
  simp only [environment, List.nil_append, List.mem_flatMap]
  constructor
  · rintro ⟨tuple, member, output⟩
    obtain ⟨fact, present, rfl⟩ := List.mem_map.mp member
    by_cases same : element = fact
    · subst fact
      simp [matchRelationArgs, matchRelationArgument, bound, mergeBindings] at output
      exact ⟨output, present⟩
    · simp [matchRelationArgs, matchRelationArgument, bound, same] at output
  · rintro ⟨rfl, present⟩
    refine ⟨[element], List.mem_map.mpr ⟨element, present, rfl⟩, ?_⟩
    simp [matchRelationArgs, matchRelationArgument, bound, mergeBindings]

theorem body_query_of_mem (known : List Pattern) (initial : Bindings) (element : Pattern)
    (bound : initial.lookup "element" = some element) (present : element ∈ known) (sites : Pattern) :
    ReferenceStep.PremiseValid (environment known) language sites initial premise (.base initial) initial :=
  .base rfl ((query_answers_exact known initial initial element bound).mpr ⟨rfl, present⟩)

theorem body_query_only_mem (known : List Pattern) (initial : Bindings) (element : Pattern)
    (bound : initial.lookup "element" = some element) (sites : Pattern)
    {witness : ReferenceStep.Witness} {result : Bindings}
    (valid : ReferenceStep.PremiseValid (environment known) language sites initial premise witness result) :
    result = initial ∧ element ∈ known := by
  cases valid with
  | base _ found => exact (query_answers_exact known initial result element bound).mp found
  | step endpoints _ _ _ => cases endpoints

theorem all_query_bodies (identifier grounding conclusion : Pattern)
    (premises known elements : List Pattern) (sites : Pattern)
    (present : ∀ element ∈ elements, element ∈ known) :
    ∃ witnesses, ReferenceStep.ForAllValid (environment known) language sites
      (Kernel.applicationBindings identifier grounding conclusion premises known)
      "element" premise elements witnesses := by
  induction elements with
  | nil => exact ⟨[], .nil⟩
  | cons element elements ih =>
    obtain ⟨rest, tail⟩ := ih (fun other inside => present other (List.mem_cons_of_mem _ inside))
    let bound := ReferenceStep.bindParameter
      (Kernel.applicationBindings identifier grounding conclusion premises known) "element" element
    refine ⟨.base bound :: rest, .cons (result := bound) ?_ tail⟩
    exact body_query_of_mem known bound element
      (by simp [bound, ReferenceStep.bindParameter, Bindings.lookup])
      (present element List.mem_cons_self) sites

theorem application_step_of_all (identifier grounding conclusion : Pattern) (premises known : List Pattern)
    (present : ∀ element ∈ premises, element ∈ known) :
    ReferenceStep.Step (environment known) language
      (Kernel.groundApplication identifier grounding conclusion premises known)
      (Kernel.groundResult identifier grounding conclusion premises known) := by
  obtain ⟨bodies, allValid⟩ := all_query_bodies identifier grounding conclusion premises known premises
    (ReferenceStep.captureSites application) present
  have quantified : ReferenceStep.PremiseValid (environment known) language (ReferenceStep.captureSites application)
      (Kernel.applicationBindings identifier grounding conclusion premises known)
      (.forAll "B" "element" premise) (.forAll bodies)
      (Kernel.applicationBindings identifier grounding conclusion premises known) := .forAll (by rfl) allValid
  have matched : Kernel.applicationBindings identifier grounding conclusion premises known ∈
      ReflectiveCanonical.matchPatternForRule language application
        (Kernel.groundApplication identifier grounding conclusion premises known) := by
    rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    change _ ∈ matchPattern Kernel.applicationRule.left _
    rw [Kernel.application_match]
    exact List.mem_singleton_self _
  have valid := ReferenceStep.StepValid.rule (index := 0) (rule := application) (by rfl) matched
    (show ReferenceStep.PremisesValid (environment known) language (ReferenceStep.captureSites application)
      (Kernel.applicationBindings identifier grounding conclusion premises known) application.premises
      [.forAll bodies] (Kernel.applicationBindings identifier grounding conclusion premises known) from
      .cons quantified (.nil _))
  change ReferenceStep.StepValid _ _ _ _
    (applyBindingsScoped _ _ 0 Kernel.applicationRule.right) at valid
  rw [Kernel.application_rhs_instantiated] at valid
  exact ⟨_, valid⟩

theorem all_query_bodies_only_mem (identifier grounding conclusion : Pattern)
    (premises known elements : List Pattern) (sites : Pattern)
    {witnesses : List ReferenceStep.Witness}
    (valid : ReferenceStep.ForAllValid (environment known) language sites
      (Kernel.applicationBindings identifier grounding conclusion premises known)
      "element" premise elements witnesses) :
    ∀ element ∈ elements, element ∈ known := by
  induction elements generalizing witnesses with
  | nil => simp
  | cons element elements ih =>
    cases valid with
    | cons first rest =>
      intro other inside
      rcases List.mem_cons.mp inside with rfl | later
      · exact (body_query_only_mem known _ other
          (by simp [ReferenceStep.bindParameter, Bindings.lookup]) sites first).2
      · exact ih rest other later

theorem application_step_shape (identifier grounding conclusion : Pattern)
    (premises known : List Pattern) {target : Pattern}
    (step : ReferenceStep.Step (environment known) language
      (Kernel.groundApplication identifier grounding conclusion premises known) target) :
    target = Kernel.groundResult identifier grounding conclusion premises known ∧
      ∀ element ∈ premises, element ∈ known := by
  obtain ⟨witness, valid⟩ := step
  cases valid with
  | @rule _ index rule initial final witnesses found matched validPremises =>
    have bound : index < language.rewrites.length := by
      by_contra outside
      rw [List.getElem?_eq_none (by omega)] at found
      cases found
    have zero : index = 0 := by change index < 1 at bound; omega
    subst index
    have first : language.rewrites[0]? = some application := rfl
    rw [first] at found
    cases Option.some.inj found
    simp only [ReflectiveCanonical.matchPatternForRule_eq_syntactic] at matched
    change initial ∈ matchPattern Kernel.applicationRule.left _ at matched
    rw [Kernel.application_match] at matched
    have initialEq := List.mem_singleton.mp matched
    subst initial
    change ReferenceStep.PremisesValid _ _ _ _ [.forAll "B" "element" premise] _ _ at validPremises
    cases validPremises with
    | cons quantified rest =>
      cases quantified with
      | base base _ => cases base
      | step endpoints _ _ _ => cases endpoints
      | forAll found bodies =>
        simp [Bindings.lookup, Kernel.applicationBindings] at found
        rcases found with ⟨rfl, rfl⟩
        cases rest
        exact ⟨Kernel.application_rhs_instantiated _ _ _ _ _ _,
          all_query_bodies_only_mem identifier grounding conclusion premises known _ _ bodies⟩

theorem application_step_exact (identifier grounding conclusion : Pattern)
    (premises known : List Pattern) (target : Pattern) :
    ReferenceStep.Step (environment known) language
      (Kernel.groundApplication identifier grounding conclusion premises known) target ↔
      target = Kernel.groundResult identifier grounding conclusion premises known ∧
        ∀ element ∈ premises, element ∈ known := by
  constructor
  · exact application_step_shape identifier grounding conclusion premises known
  · rintro ⟨rfl, present⟩
    exact application_step_of_all identifier grounding conclusion premises known present

theorem lowering_exact (original : RelationEnv) (identifier grounding conclusion : Pattern)
    (premises known : List Pattern) (target : Pattern) :
    ReferenceStep.Step original Kernel.language
        (Kernel.groundApplication identifier grounding conclusion premises known) target ↔
      ReferenceStep.Step (environment known) language
        (Kernel.groundApplication identifier grounding conclusion premises known) target := by
  rw [Kernel.application_step_exact, application_step_exact]

def snapshot (freeTypes : List (String × TypeExpr)) (known : List Pattern) :
    GeneralExecutionAdmission.Snapshot := ⟨language, freeTypes, provider known⟩

def permissions : GeneralExecutionAdmission.Permissions :=
  {sites := .rootOnly, includeDerivedEquations := false}

def plan (freeTypes : List (String × TypeExpr)) (known : List Pattern) : GeneralExecutionAdmission.Plan :=
  GeneralExecutionAdmission.compile (snapshot freeTypes known) permissions

#print axioms query_answers_exact
#print axioms body_query_only_mem
#print axioms application_step_of_all
#print axioms application_step_exact
#print axioms lowering_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.QueryKernel
