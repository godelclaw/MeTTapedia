import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogMembership

/-! Ground inference uses the authored quantified child-step premise. Its
premises are kept facts: repeated uses need no duplicate resource occurrence. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.Kernel

open Mettapedia.OSLF.MeTTaIL Syntax Match

def applicationRule : RewriteRule := language.rewrites[1]'(by decide +kernel)

def membershipSource : Pattern :=
  .apply "HasFact" [.apply "FactStore" [.fvar "known"], .fvar "element"]

def membershipPremise : Premise := .congruence membershipSource (.apply "FactPresent" [])

def groundApplication (identifier grounding conclusion : Pattern) (premises known : List Pattern) : Pattern :=
  .apply "ApplyGround"
    [.apply "GroundRule" [identifier, grounding, conclusion, body premises], factStore known]

def groundResult (identifier grounding conclusion : Pattern) (premises known : List Pattern) : Pattern :=
  .apply "GroundApplied"
    [.apply "GroundKey" [identifier, grounding, body premises], factStore (conclusion :: known)]

def applicationBindings (identifier grounding conclusion : Pattern)
    (premises known : List Pattern) : Bindings :=
  [("known", .collection .hashSet known none), ("grounding", grounding),
    ("B", .collection .vec premises none), ("conclusion", conclusion), ("identifier", identifier)]

theorem application_rule_left : applicationRule.left =
    .apply "ApplyGround"
      [.apply "GroundRule" [.fvar "identifier", .fvar "grounding", .fvar "conclusion",
        .apply "GroundBody" [.fvar "B"]], .apply "FactStore" [.fvar "known"]] := by decide +kernel

theorem application_rule_right : applicationRule.right =
    .apply "GroundApplied"
      [.apply "GroundKey" [.fvar "identifier", .fvar "grounding", .apply "GroundBody" [.fvar "B"]],
        .apply "FactStore" [.collection .hashSet [.fvar "conclusion"] (some "known")]] := by decide +kernel

theorem application_rule_premises : applicationRule.premises =
    [.forAll "B" "element" membershipPremise] := by decide +kernel

theorem application_rule_at : language.rewrites[1]? = some applicationRule := by simp [applicationRule]

theorem application_match (identifier grounding conclusion : Pattern) (premises known : List Pattern) :
    matchPattern applicationRule.left (groundApplication identifier grounding conclusion premises known) =
      [applicationBindings identifier grounding conclusion premises known] := by
  rw [application_rule_left]
  simp [groundApplication, body, factStore, matchPattern, matchArgs, mergeBindings, applicationBindings]

theorem membership_source_instantiated (sites identifier grounding conclusion : Pattern)
    (premises known : List Pattern) (element : Pattern) :
    applyBindingsScoped sites
      (ReferenceStep.bindParameter (applicationBindings identifier grounding conclusion premises known)
        "element" element) 0 membershipSource =
      .apply "HasFact" [factStore known, element] := by
  simp [membershipSource, applyBindingsScoped_apply,
    applyBindingsScoped_fvar_zero, applyBindings, ReferenceStep.bindParameter, applicationBindings, factStore]

theorem membership_body_of_mem (environment : Engine.RelationEnv)
    (sites identifier grounding conclusion : Pattern) (premises known : List Pattern)
    {element : Pattern} (member : element ∈ known) :
    ∃ witness result, ReferenceStep.PremiseValid environment language sites
      (ReferenceStep.bindParameter (applicationBindings identifier grounding conclusion premises known)
        "element" element) membershipPremise witness result := by
  obtain ⟨step, valid⟩ := membership_step_of_mem environment member
  refine ⟨.premiseStep step (.apply "FactPresent" []) [] _, _,
    ReferenceStep.PremiseValid.step (matched := []) rfl ?_ ?_ rfl⟩
  · change ReferenceStep.StepValid environment language
      (applyBindingsScoped sites _ 0 membershipSource) step (.apply "FactPresent" [])
    rw [membership_source_instantiated]
    exact valid
  · decide +kernel

theorem all_membership_bodies (environment : Engine.RelationEnv)
    (sites identifier grounding conclusion : Pattern) (premises known : List Pattern)
    (elements : List Pattern) (present : ∀ element ∈ elements, element ∈ known) :
    ∃ witnesses, ReferenceStep.ForAllValid environment language sites
      (applicationBindings identifier grounding conclusion premises known)
      "element" membershipPremise elements witnesses := by
  induction elements with
  | nil => exact ⟨[], .nil⟩
  | cons element elements ih =>
    obtain ⟨first, result, valid⟩ := membership_body_of_mem environment sites identifier grounding conclusion
      premises known (present element List.mem_cons_self)
    obtain ⟨rest, validRest⟩ := ih (fun other inside => present other (List.mem_cons_of_mem _ inside))
    exact ⟨first :: rest, .cons valid validRest⟩

theorem membership_body_only_mem (environment : Engine.RelationEnv)
    (sites identifier grounding conclusion : Pattern) (premises known : List Pattern)
    {element : Pattern} {witness : ReferenceStep.Witness} {result : Bindings}
    (valid : ReferenceStep.PremiseValid environment language sites
      (ReferenceStep.bindParameter (applicationBindings identifier grounding conclusion premises known)
        "element" element) membershipPremise witness result) : element ∈ known := by
  cases valid with
  | base base _ => cases base
  | step endpoints stepped _ _ =>
    simp only [membershipPremise, ReferenceStep.stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
    rcases endpoints with ⟨rfl, rfl⟩
    change ReferenceStep.StepValid environment language
      (applyBindingsScoped sites _ 0 membershipSource) _ _ at stepped
    rw [membership_source_instantiated] at stepped
    exact membership_step_only_mem environment ⟨_, stepped⟩

theorem all_membership_bodies_only_mem (environment : Engine.RelationEnv)
    (sites identifier grounding conclusion : Pattern) (premises known : List Pattern)
    (elements : List Pattern) {witnesses : List ReferenceStep.Witness}
    (valid : ReferenceStep.ForAllValid environment language sites
      (applicationBindings identifier grounding conclusion premises known)
      "element" membershipPremise elements witnesses) :
    ∀ element ∈ elements, element ∈ known := by
  induction elements generalizing witnesses with
  | nil => simp
  | cons element elements ih =>
    cases valid with
    | cons first rest =>
      intro other inside
      rcases List.mem_cons.mp inside with rfl | later
      · exact membership_body_only_mem environment sites identifier grounding conclusion premises known first
      · exact ih rest other later

theorem quantified_membership_only_mem (environment : Engine.RelationEnv)
    (sites identifier grounding conclusion : Pattern) (premises known : List Pattern)
    {witness : ReferenceStep.Witness} {result : Bindings}
    (valid : ReferenceStep.PremiseValid environment language sites
      (applicationBindings identifier grounding conclusion premises known)
      (.forAll "B" "element" membershipPremise) witness result) :
    ∀ premise ∈ premises, premise ∈ known := by
  cases valid with
  | base base _ => cases base
  | step endpoints _ _ _ => cases endpoints
  | forAll found bodies =>
    simp [Bindings.lookup, applicationBindings] at found
    rcases found with ⟨rfl, rfl⟩
    exact all_membership_bodies_only_mem environment sites identifier grounding conclusion premises known _ bodies

theorem application_rhs_instantiated (sites identifier grounding conclusion : Pattern)
    (premises known : List Pattern) :
    applyBindingsScoped sites (applicationBindings identifier grounding conclusion premises known)
      0 applicationRule.right = groundResult identifier grounding conclusion premises known := by
  rw [applyBindingsScoped_zero_of_binderFree sites _ applicationRule.right
    (by rw [application_rule_right]; decide +kernel), application_rule_right]
  simp [groundResult, applicationBindings, body, factStore, applyBindings]

theorem application_step_of_all (environment : Engine.RelationEnv)
    (identifier grounding conclusion : Pattern) (premises known : List Pattern)
    (present : ∀ premise ∈ premises, premise ∈ known) :
    ReferenceStep.Step environment language (groundApplication identifier grounding conclusion premises known)
      (groundResult identifier grounding conclusion premises known) := by
  obtain ⟨bodies, validBodies⟩ := all_membership_bodies environment
    (ReferenceStep.captureSites applicationRule) identifier grounding conclusion premises known premises present
  have allValid : ReferenceStep.PremiseValid environment language (ReferenceStep.captureSites applicationRule)
      (applicationBindings identifier grounding conclusion premises known)
      (.forAll "B" "element" membershipPremise) (.forAll bodies)
      (applicationBindings identifier grounding conclusion premises known) :=
    .forAll (by rfl) validBodies
  have premisesValid : ReferenceStep.PremisesValid environment language (ReferenceStep.captureSites applicationRule)
      (applicationBindings identifier grounding conclusion premises known) applicationRule.premises
      [.forAll bodies] (applicationBindings identifier grounding conclusion premises known) := by
    rw [application_rule_premises]
    exact .cons allValid (.nil _)
  have matched : applicationBindings identifier grounding conclusion premises known ∈
      ReflectiveCanonical.matchPatternForRule language applicationRule
        (groundApplication identifier grounding conclusion premises known) := by
    rw [ReflectiveCanonical.matchPatternForRule_eq_syntactic, application_match]
    exact List.mem_singleton_self _
  have valid := ReferenceStep.StepValid.rule application_rule_at
    matched premisesValid
  rw [application_rhs_instantiated] at valid
  exact ⟨_, valid⟩

private theorem membership_rule_has_no_application_match
    (identifier grounding conclusion : Pattern) (premises known : List Pattern) :
    matchPattern membershipRule.left (groundApplication identifier grounding conclusion premises known) = [] := by
  rw [membership_rule_left]
  simp only [groundApplication, matchPattern]
  rfl

private theorem quantified_result_eq (environment : Engine.RelationEnv)
    (sites identifier grounding conclusion : Pattern) (premises known : List Pattern)
    {witness : ReferenceStep.Witness} {result : Bindings}
    (valid : ReferenceStep.PremiseValid environment language sites
      (applicationBindings identifier grounding conclusion premises known)
      (.forAll "B" "element" membershipPremise) witness result) :
    result = applicationBindings identifier grounding conclusion premises known := by
  cases valid with
  | base base _ => cases base
  | step endpoints _ _ _ => cases endpoints
  | forAll _ _ => rfl

theorem application_step_shape (environment : Engine.RelationEnv)
    (identifier grounding conclusion : Pattern) (premises known : List Pattern) {target : Pattern}
    (step : ReferenceStep.Step environment language
      (groundApplication identifier grounding conclusion premises known) target) :
    target = groundResult identifier grounding conclusion premises known ∧
      ∀ premise ∈ premises, premise ∈ known := by
  obtain ⟨witness, valid⟩ := step
  cases valid with
  | @rule _ index rule initial final witnesses found matched validPremises =>
    have bound : index < language.rewrites.length := by
      by_contra outside
      rw [List.getElem?_eq_none (by omega)] at found
      cases found
    have length := authored_kernel_nonempty
    have possibilities : index = 0 ∨ index = 1 := by omega
    rcases possibilities with rfl | rfl
    · rw [membership_rule_at] at found
      cases Option.some.inj found
      simp only [ReflectiveCanonical.matchPatternForRule_eq_syntactic,
        membership_rule_has_no_application_match] at matched
      cases matched
    · rw [application_rule_at] at found
      cases Option.some.inj found
      simp only [ReflectiveCanonical.matchPatternForRule_eq_syntactic,
        application_match, List.mem_singleton] at matched
      subst initial
      rw [application_rule_premises] at validPremises
      cases validPremises with
      | cons quantified rest =>
        have present := quantified_membership_only_mem environment (ReferenceStep.captureSites applicationRule)
          identifier grounding conclusion premises known quantified
        cases quantified_result_eq environment (ReferenceStep.captureSites applicationRule)
          identifier grounding conclusion premises known quantified
        cases rest
        exact ⟨application_rhs_instantiated _ _ _ _ _ _, present⟩

theorem application_step_only_all (environment : Engine.RelationEnv)
    (identifier grounding conclusion : Pattern) (premises known : List Pattern) {target : Pattern}
    (step : ReferenceStep.Step environment language
      (groundApplication identifier grounding conclusion premises known) target) :
    ∀ premise ∈ premises, premise ∈ known :=
  (application_step_shape environment identifier grounding conclusion premises known step).2

theorem application_step_exact (environment : Engine.RelationEnv)
    (identifier grounding conclusion : Pattern) (premises known : List Pattern) (target : Pattern) :
    ReferenceStep.Step environment language (groundApplication identifier grounding conclusion premises known) target ↔
      target = groundResult identifier grounding conclusion premises known ∧
        ∀ premise ∈ premises, premise ∈ known := by
  constructor
  · exact application_step_shape environment identifier grounding conclusion premises known
  · rintro ⟨rfl, present⟩
    exact application_step_of_all environment identifier grounding conclusion premises known present

theorem application_step_iff (environment : Engine.RelationEnv)
    (identifier grounding conclusion : Pattern) (premises known : List Pattern) :
    ReferenceStep.Step environment language (groundApplication identifier grounding conclusion premises known)
      (groundResult identifier grounding conclusion premises known) ↔
        ∀ premise ∈ premises, premise ∈ known :=
  ⟨application_step_only_all environment identifier grounding conclusion premises known,
    application_step_of_all environment identifier grounding conclusion premises known⟩

theorem application_step_congr_known (environment : Engine.RelationEnv)
    (identifier grounding conclusion : Pattern) (premises first second : List Pattern)
    (sameFacts : ∀ fact, fact ∈ first ↔ fact ∈ second) :
    ReferenceStep.Step environment language (groundApplication identifier grounding conclusion premises first)
        (groundResult identifier grounding conclusion premises first) ↔
      ReferenceStep.Step environment language (groundApplication identifier grounding conclusion premises second)
        (groundResult identifier grounding conclusion premises second) := by
  rw [application_step_iff, application_step_iff]
  exact forall_congr' fun premise => imp_congr_right (fun _ => sameFacts premise)

#print axioms application_match
#print axioms membership_source_instantiated
#print axioms all_membership_bodies
#print axioms application_rhs_instantiated
#print axioms application_step_of_all
#print axioms membership_body_only_mem
#print axioms all_membership_bodies_only_mem
#print axioms application_step_only_all
#print axioms application_step_iff
#print axioms application_step_exact
#print axioms application_step_congr_known

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.Kernel
