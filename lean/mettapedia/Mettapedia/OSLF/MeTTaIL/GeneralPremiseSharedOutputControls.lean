import Mettapedia.OSLF.MeTTaIL.Complete.Exhaustion
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionTotalAdmission
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionCoverage
import Mettapedia.OSLF.MeTTaIL.ReferenceStepExecution
import Mettapedia.OSLF.MeTTaIL.CanonicalBags
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionHandoff

/-!
# Compiled shared provider outputs and lexical quantification

Provider declarations with identical values remain distinct occurrences.
A later output matches the retained binding rather than replacing it. The
quantified parameter shadows an outer capture only while its body runs;
preexisting outer outputs remain fixed and body outputs stay local. Empty quantification leaves an absent
output absent, and the compiler rejects relying on that output afterwards.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching Execution GeneralExecutionAdmission

def term : TypeExpr := .base "Term"
def zero : Pattern := .apply "Zero" []
def one : Pattern := .apply "Successor" [zero]

def quantifiedBody : Premise := .relationQuery "share" [.fvar "Y", .fvar "element"]
def quantified : Premise := .forAll "L" "element" quantifiedBody

def rule : RewriteRule where
  name := "shared-provider-output"
  typeContext := [("element", term), ("L", .collection .vec term), ("Y", term)]
  left := .apply "Wrap" [.fvar "element", .collection .vec [] (some "L")]
  right := .apply "Accept" [.fvar "Y", .fvar "element"]
  premises := [.relationQuery "choose" [.fvar "Y"], quantified,
    .relationQuery "confirm" [.fvar "Y"]]

def language : LanguageDef where
  name := "compiled-shared-output-quantification"
  types := ["Term"]
  terms := [
    {label := "Zero", category := "Term", params := [], syntaxPattern := []},
    {label := "Successor", category := "Term", params := [.simple "term" term], syntaxPattern := []},
    {label := "Wrap", category := "Term", params := [
      .simple "outer" term, .simple "elements" (.collection .vec term)], syntaxPattern := []},
    {label := "Accept", category := "Term", params := [
      .simple "answer" term, .simple "outer" term], syntaxPattern := []}]
  equations := []
  rewrites := [rule]

def provider : ProviderSnapshot where
  signatures := [⟨"choose", [term], [.output]⟩,
    ⟨"share", [term, term], [.output, .input]⟩,
    ⟨"confirm", [term], [.output]⟩]
  rows := [⟨"choose", [zero]⟩, ⟨"choose", [zero]⟩,
    ⟨"share", [zero, zero]⟩, ⟨"share", [one, zero]⟩,
    ⟨"confirm", [one]⟩, ⟨"confirm", [zero]⟩]

def snapshot : Snapshot := ⟨language, [], provider⟩
def permissions : Permissions where
  equationIndices := some []
  includeDerivedEquations := false

def admission : GeneralExecutionTotalAdmission.Admission :=
  GeneralExecutionTotalAdmission.compile snapshot permissions

def plan : Plan := admission.execution

def declaration : RulePlan where
  declarationIndex := 0
  authored := rule
  binding := ⟨GeneralRuleBindingInference.inferredSpec rule, .inferredRootInputs⟩

theorem compiled_binding :
    GeneralRuleBindingInference.compile? language rule = some declaration.binding := by cbv

theorem compiled_premises :
    rulePremisesAdmitted language provider (declaration.binding.elaborate rule)
      declaration.binding.spec = true := by cbv

theorem compiled_templates :
    GeneralEquationCanonicalTemplates.checkRule rule = true ∧
      GeneralEquationCanonicalTemplates.checkBinding declaration.binding.spec = true := by decide +kernel

theorem compiled_rules : plan.rules = [declaration] := by
  have selected : selectedRules snapshot permissions = [(rule, 0)] := rfl
  unfold plan admission GeneralExecutionTotalAdmission.compile GeneralExecutionAdmission.compile
    GeneralExecutionAdmission.rules
  rw [selected]
  simp only [List.filterMap_cons, List.filterMap_nil, rulePlan?, Option.bind_eq_bind,
    show snapshot.language = language from rfl, show snapshot.provider = provider from rfl,
    compiled_binding, Option.bind_some, compiled_premises, compiled_templates.1,
    compiled_templates.2, Bool.and_self, ↓reduceIte]
  rfl

def environment : Environment where
  language := {language with rewrites := [declaration.rule]}
  free := snapshot.free
  provider := snapshot.provider
  specifications := [(0, declaration.binding.spec)]
  reflection := permissions.reflection

theorem environment_actual : GeneralPlanEnvironment.environment plan = environment := by
  unfold GeneralPlanEnvironment.environment
  rw [compiled_rules]
  rfl

def source (elements : List Pattern) : Pattern :=
  .apply "Wrap" [one, .collection .vec elements none]

def rootGoal (elements : List Pattern) : Goal := .root [] term (source elements) 0
def rootState (elements : List Pattern) : State environment (rootGoal elements) :=
  run environment (rootGoal elements) 400 (start environment (rootGoal elements))

def rootTarget {executionEnvironment : Environment} (elements : List Pattern) :
    Result executionEnvironment (rootGoal elements) → Pattern
  | .root _ _ _ _ target _ => target

def rootAssignment {executionEnvironment : Environment} (elements : List Pattern) :
    Result executionEnvironment (rootGoal elements) → Assignment
  | .root _ _ completed _ _ _ => completed

def queryRow? : Event → Option Nat
  | .query _ _ row _ => some row
  | _ => none

def queryRows : Event → List Nat
  | .query _ _ row _ => [row]
  | .quantified _ _ _ elements =>
      elements.flatMap fun element => element.2.2.filterMap queryRow?
  | _ => []

def rootRows {executionEnvironment : Environment} (elements : List Pattern) :
    Result executionEnvironment (rootGoal elements) → List Nat
  | .root _ _ _ events _ _ => events.flatMap queryRows

def readBody (assignment : Assignment) (name : String) : Option Pattern :=
  (lookup assignment name).map ContextualValue.body

theorem whole_profile_accepted : admission.complete = true := by cbv

theorem actual_compiled_rule : plan.rules.map RulePlan.declarationIndex = [0] := by
  rw [compiled_rules]
  rfl

theorem root_keeps_duplicate_provider_origins :
    (rootState [zero, zero]).answers.map (rootRows [zero, zero]) =
      [[0, 2, 2, 5], [1, 2, 2, 5]] := by decide +kernel

theorem conflicting_later_rows_do_not_overwrite :
    (rootState [zero, zero]).answers.map (rootTarget [zero, zero]) =
      [.apply "Accept" [zero, one], .apply "Accept" [zero, one]] := by decide +kernel

theorem root_preserves_global_output_and_outer_parameter :
    (rootState [zero, zero]).answers.map (fun answer =>
      (readBody (rootAssignment [zero, zero] answer) "Y",
        readBody (rootAssignment [zero, zero] answer) "element")) =
      [(some zero, some one), (some zero, some one)] := by decide +kernel

theorem root_search_completed :
    complete environment (rootGoal [zero, zero]) (rootState [zero, zero]) = true := by decide +kernel

theorem root_empty_quantification_keeps_only_preexisting_output :
    (rootState []).answers.map (rootRows []) = [[0, 5], [1, 5]] ∧
      (rootState []).answers.map (rootTarget []) =
        [.apply "Accept" [zero, one], .apply "Accept" [zero, one]] := by decide +kernel

/-- The local consumer's declaration and binding plan have an exact compiled
position; no rule-name lookup or fallback is used. -/
def compiledRule : RulePlan := declaration
theorem compiled_rule_selected : plan.rules[0]? = some compiledRule := by
  rw [compiled_rules]
  rfl

def context : Context := ⟨0, compiledRule.rule, compiledRule.binding.spec, [], 1, 0⟩

def captures (elements : List Pattern) : Assignment :=
  [("L", localValue [] (.collection .vec elements none)), ("element", localValue [] one)]

theorem captures_from_actual_root_matching :
    matchRuleAt compiledRule.rule compiledRule.binding.spec 0 (source [zero, zero]) =
      [captures [zero, zero]] := by decide +kernel

def quantifierGoal (elements : List Pattern) : Goal :=
  .premise context quantified (captures elements)

def quantifierState (elements : List Pattern) : State environment (quantifierGoal elements) :=
  run environment (quantifierGoal elements) 200 (start environment (quantifierGoal elements))

def quantifierAssignment (elements : List Pattern) : Result environment (quantifierGoal elements) → Assignment
  | .premise completed _ _ => completed

def quantifierOrigins (elements : List Pattern) : Result environment (quantifierGoal elements) →
    List (Nat × Pattern × List Nat)
  | .premise _ event _ => match event with
    | .quantified _ _ _ entries => entries.map fun entry =>
        (entry.1, entry.2.1, entry.2.2.filterMap queryRow?)
    | _ => []

theorem nonempty_quantification_keeps_body_outputs_local :
    (quantifierState [zero, zero]).answers.map (fun answer =>
      (readBody (quantifierAssignment [zero, zero] answer) "Y",
        readBody (quantifierAssignment [zero, zero] answer) "element")) =
      [(none, some one), (none, some one), (none, some one), (none, some one)] := by decide +kernel

theorem quantified_duplicates_keep_independent_body_origins :
    (quantifierState [zero, zero]).answers.map (quantifierOrigins [zero, zero]) =
      [[(0, zero, [2]), (1, zero, [2])], [(0, zero, [2]), (1, zero, [3])],
        [(0, zero, [3]), (1, zero, [2])], [(0, zero, [3]), (1, zero, [3])]] := by decide +kernel

theorem empty_quantification_cannot_manufacture_a_binding :
    (quantifierState []).answers.map (fun answer =>
      (readBody (quantifierAssignment [] answer) "Y",
        readBody (quantifierAssignment [] answer) "element")) = [(none, some one)] := by decide +kernel

theorem quantifier_search_completed :
    complete environment (quantifierGoal [zero, zero]) (quantifierState [zero, zero]) = true ∧
      complete environment (quantifierGoal []) (quantifierState []) = true := by decide +kernel

def unsafeRule : RewriteRule := {rule with premises := [quantified]}
def unsafeLanguage : LanguageDef := {language with rewrites := [unsafeRule]}
def unsafeSnapshot : Snapshot := {snapshot with language := unsafeLanguage}

theorem empty_capable_output_cannot_supply_required_binding :
    (GeneralExecutionTotalAdmission.compile unsafeSnapshot permissions).complete = false := by cbv

theorem unsafe_rule_retains_actual_flow_obligation :
    GeneralExecutionAdmission.Obligation.rulePremises 0 ∈
      (GeneralExecutionAdmission.compile unsafeSnapshot permissions).obligations := by
  cbv
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem actual_compiler_executes_shared_output_origins :
    (run (GeneralPlanEnvironment.environment plan) (rootGoal [zero, zero]) 400
      (start (GeneralPlanEnvironment.environment plan) (rootGoal [zero, zero]))).answers.map
      (rootRows [zero, zero]) = [[0, 2, 2, 5], [1, 2, 2, 5]] := by
  rw [environment_actual]
  exact root_keeps_duplicate_provider_origins

#print axioms whole_profile_accepted
#print axioms root_keeps_duplicate_provider_origins
#print axioms nonempty_quantification_keeps_body_outputs_local
#print axioms empty_capable_output_cannot_supply_required_binding

namespace LocalOutputs

/-- The body introduces `Y` locally; the conclusion uses only the enclosing
parameter. Different elements can therefore require different `Y` values. -/
def authoredRule : RewriteRule :=
  {rule with
    name := "independent-quantified-outputs"
    premises := [quantified]
    right := .apply "Accept" [zero, .fvar "element"]}

def authoredLanguage : LanguageDef := {language with rewrites := [authoredRule]}

def selectedLanguage (nested : Bool) : LanguageDef :=
  if nested then {authoredLanguage with rewrites :=
    [{authoredRule with premises := [.forAll "L" "element" quantified]}]}
  else authoredLanguage

def provider (zeroRows : Nat := 1) (oneRow : Bool := true) : ProviderSnapshot where
  signatures := [⟨"share", [term, term], [.output, .input]⟩]
  rows := List.replicate zeroRows ⟨"share", [zero, zero]⟩ ++
    (if oneRow then [⟨"share", [one, one]⟩] else [])

def admission (zeroRows : Nat := 1) (oneRow : Bool := true) (nested : Bool := false) :=
  GeneralExecutionTotalAdmission.compile ⟨selectedLanguage nested, [], provider zeroRows oneRow⟩ permissions

def plan (zeroRows : Nat := 1) (oneRow : Bool := true) (nested : Bool := false) : Plan :=
  (admission zeroRows oneRow nested).execution

def environment (zeroRows : Nat := 1) (oneRow : Bool := true) (nested : Bool := false) : Environment :=
  GeneralPlanEnvironment.environment (plan zeroRows oneRow nested)

def relationEnvironment (zeroRows : Nat := 1) (oneRow : Bool := true) : Engine.RelationEnv where
  tuples := fun relation _ =>
    ((provider zeroRows oneRow).rows.filter (fun row => row.relation == relation)).map (·.values)

def origins : List Event → List (Nat × Pattern × List Nat)
  | [] => []
  | .quantified _ _ _ entries :: rest =>
      entries.map (fun entry => (entry.1, entry.2.1, entry.2.2.filterMap queryRow?)) ++ origins rest
  | _ :: rest => origins rest

def readout {env : Environment} (elements : List Pattern) : Result env (rootGoal elements) →
    Pattern × Option Pattern × Option Pattern × List (Nat × Pattern × List Nat)
  | .root _ _ completed events target _ =>
      (target, readBody completed "Y", readBody completed "element", origins events)

def completeReadout {env : Environment} (elements : List Pattern) : Result env (rootGoal elements) → String
  | .root trace captured completed events target _ => reprStr (trace, captured, completed, events, target)

def controls : IO Unit := do
  for (nested, zeroRows, oneRow, elements, expected) in [
      (false, 1, true, [zero, one], 1), (false, 2, true, [zero, one], 2),
      (false, 1, false, [zero, one], 0), (false, 0, true, [zero, one], 0),
      (false, 0, false, [zero, one], 0), (false, 0, false, [], 1),
      (true, 1, true, [zero, one], 1), (true, 2, true, [zero, one], 4),
      (true, 1, false, [zero, one], 0), (true, 0, false, [], 1)] do
    unless (admission zeroRows oneRow nested).complete do
      throw (IO.userError "Local quantified consumer was not admitted")
    let env := environment zeroRows oneRow nested
    let goal := rootGoal elements
    let whole := run env goal 400 (start env goal)
    let resumed := run env goal 360 (run env goal 40 (start env goal))
    let answers := whole.answers.map (readout elements)
    let reference := ReferenceStep.stepsAt (relationEnvironment zeroRows oneRow)
      (selectedLanguage nested) 1 (source elements)
    unless answers.length == expected && reference.length == expected &&
        decide (complete env goal whole = true) do
      throw (IO.userError "Local quantifier source/reference counts or completion disagree")
    unless answers.map (fun entry => entry.1) == reference.map Prod.snd do
      throw (IO.userError "Local quantified conclusions disagree with the source evaluator")
    unless resumed.answers.map (completeReadout elements) == whole.answers.map (completeReadout elements) do
      throw (IO.userError "Local quantifier resumption changed the complete receipt account")
    unless answers.all (fun entry => entry.1 == .apply "Accept" [zero, one] &&
        entry.2.1 == none && entry.2.2.1 == some one) do
      throw (IO.userError "A quantified output escaped or replaced the outer parameter")
    if !nested && zeroRows == 1 && oneRow && !elements.isEmpty then
      unless answers.map (fun entry => entry.2.2.2) == [[(0, zero, [0]), (1, one, [1])]] do
        throw (IO.userError "Independent quantified body origins were lost")
  IO.println "LocalQuantifierControls: source agreement, independent outputs, lexical scope, negatives and resumption passed"

#eval controls

end LocalOutputs

namespace SetValidation

/-- A direct quantified-premise control. General set admission remains
closed; these checks distinguish validation evidence from derivations. -/
def authoredRule : RewriteRule :=
  {LocalOutputs.authoredRule with
    typeContext := [("L", .collection .hashSet term), ("element", term), ("Y", term)]
    left := .apply "SetWrap" [.collection .hashSet [] (some "L")]
    right := .apply "Accept" [zero, zero]}

def language : LanguageDef :=
  {SharedOutputControls.language with
    terms := SharedOutputControls.language.terms ++
      [{label := "SetWrap", category := "Term",
        params := [.simple "elements" (.collection .hashSet term)], syntaxPattern := []}]
    rewrites := [authoredRule]}

def environment : Environment where
  language := language
  free := fun _ => none
  provider := LocalOutputs.provider 2 false
  specifications := [(0, GeneralRuleBindingInference.inferredSpec authoredRule)]

def context : Context :=
  ⟨0, authoredRule, GeneralRuleBindingInference.inferredSpec authoredRule, [], 0, 0⟩

def assignment (elements : List Pattern) : Assignment :=
  [("L", localValue [] (.collection .hashSet elements none))]

def goal (elements : List Pattern) : Goal := .premise context quantified (assignment elements)

def completed (elements : List Pattern) : State environment (goal elements) :=
  run environment (goal elements) 200 (start environment (goal elements))

theorem equivalent_sets :
    CanonicalBags.canon (.collection .hashSet [zero, zero] none) =
      CanonicalBags.canon (.collection .hashSet [zero] none) :=
  CanonicalBags.BagStep.canon_eq (.members fun _ => by simp)

theorem validation_counts_depend_on_presentation :
    (completed [zero, zero]).answers.length = 4 ∧
      (completed [zero]).answers.length = 2 := by decide +kernel

theorem missing_element_refused :
    (completed [zero, one]).answers = [] := by decide +kernel

theorem validation_searches_complete :
    complete environment (goal [zero, zero]) (completed [zero, zero]) = true ∧
      complete environment (goal [zero]) (completed [zero]) = true ∧
      complete environment (goal [zero, one]) (completed [zero, one]) = true := by decide +kernel

theorem general_set_guard_retained :
    GeneralExecutionAdmission.Obligation.setDecomposition ∈
      (GeneralExecutionAdmission.compile ⟨language, [], environment.provider⟩ permissions).obligations := by
  have rejected : GeneralExecutionAdmission.setDecompositionFree
      ⟨language, [], environment.provider⟩ permissions = false := by cbv
  simp only [GeneralExecutionAdmission.compile, rejected, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_append_right _ List.mem_cons_self

#print axioms validation_counts_depend_on_presentation
#print axioms missing_element_refused
#print axioms general_set_guard_retained

end SetValidation

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls

/-! Ordinary child matching is not invariant under set presentation. This
control states both independent source judgments, at every derivation depth. -/

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ChildPresentation
open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralPremise RuleBinding ScopedRuleMatching StructuralDescent.Scheduled

def term : TypeExpr := .base "Term"
def a : Pattern := .apply "A" []
def b : Pattern := .apply "B" []
def choice (elements : List Pattern) : Pattern := .collection .hashSet elements none
def box (value : Pattern) : Pattern := .apply "Box" [value]

def child : RewriteRule where
  name := "requires-two-matching-positions"
  typeContext := [("X", term)]
  left := choice [.fvar "X", .fvar "X"]
  right := b
  premises := []

def liftRule : RewriteRule where
  name := "conditional-lifting"
  typeContext := [("S", term), ("T", term)]
  left := box (.fvar "S")
  right := box (.fvar "T")
  premises := [.congruence (.fvar "S") (.fvar "T")]

def language : LanguageDef where
  name := "child-presentation-boundary"
  types := ["Term"]
  terms := [{label := "A", category := "Term", params := [], syntaxPattern := []},
    {label := "B", category := "Term", params := [], syntaxPattern := []},
    {label := "Box", category := "Term", params := [.simple "value" term], syntaxPattern := []},
    {label := "Choice", category := "Term", params := [.simple "elements" (.collection .hashSet term)],
      syntaxPattern := [], collectionRepresentation := .bare}]
  equations := []
  rewrites := [child, liftRule]

def environment : Environment where
  language := language
  free := fun _ => none
  provider := {signatures := [], rows := []}
  specifications := [(0, GeneralRuleBindingInference.inferredSpec child),
    (1, GeneralRuleBindingInference.inferredSpec liftRule)]

theorem default_set_guard_refuses :
    GeneralExecutionAdmission.setDecompositionFree
      ⟨language, [], environment.provider⟩
      {equationIndices := some [], includeDerivedEquations := false} = false := by
  decide +kernel

def goal (elements : List Pattern) : Goal := .root 2 [] term (box (choice elements)) 1

def completed (elements : List Pattern) : State environment (goal elements) :=
  run environment (goal elements) 300 (start environment (goal elements))

theorem same_presented_source :
    CanonicalBags.canon (box (choice [a, a])) = CanonicalBags.canon (box (choice [a])) := by
  have same := CanonicalBags.BagStep.canon_eq
    (CanonicalBags.BagStep.members (fun item => by simp) :
      CanonicalBags.BagStep (choice [a, a]) (choice [a]))
  simpa only [box, choice, CanonicalBags.canon_apply, List.map_cons, List.map_nil] using
    congrArg (fun value => Pattern.apply "Box" [value]) same

theorem ordinary_child_search_on_canonical_source :
    (completed [a]).answers.length = 0 := by decide +kernel

theorem ordinary_child_search_on_duplicate_presentation :
    (completed [a, a]).answers.length = 2 := by decide +kernel

theorem both_bounded_searches_complete :
    complete environment (goal [a]) (completed [a]) = true ∧
      complete environment (goal [a, a]) (completed [a, a]) = true := by decide +kernel

/-- No source firing exists at the canonical state, at any derivation depth.
The finite run is uncut, so the generic coverage theorem discharges all depths. -/
theorem canonical_source_has_no_firing
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completedAssignment : Assignment}
    {history : List Event} {target : Pattern}
    (fired : RootFiring environment [] term (box (choice [a])) 1
      trace captured completedAssignment history target) : False := by
  let wanted : Result environment (goal [a]) :=
    .root trace captured completedAssignment history target fired
  have initial : Complete.Exhaustion.StateCovers (start environment (goal [a])) wanted :=
    Or.inl (Or.inr ⟨_, List.mem_cons_self, wanted, rfl⟩)
  have covered := Complete.Exhaustion.run_covers 300 initial
  change Complete.Exhaustion.StateCovers (completed [a]) wanted at covered
  have emptyAnswers : (completed [a]).answers = [] :=
    List.length_eq_zero_iff.mp ordinary_child_search_on_canonical_source
  have settled : (completed [a]).agenda = [] ∧ (completed [a]).unresolved = [] := by
    simpa only [complete, GeneralPremise.Scheduler.complete, Bool.and_eq_true, List.isEmpty_iff]
      using both_bounded_searches_complete.1
  rcases covered with (found | ⟨task, pending, _⟩) | ⟨index, exhausted⟩
  · rw [emptyAnswers] at found
    exact List.not_mem_nil found
  · rw [settled.1] at pending
    exact List.not_mem_nil pending
  · rw [settled.2] at exhausted
    exact List.not_mem_nil exhausted

theorem duplicate_source_has_firing :
    ∃ trace captured completedAssignment history target,
      RootFiring environment [] term (box (choice [a, a])) 1
        trace captured completedAssignment history target := by
  have nonempty : (completed [a, a]).answers ≠ [] := by
    intro empty
    have count := ordinary_child_search_on_duplicate_presentation
    rw [empty] at count
    cases count
  obtain ⟨answer, _⟩ := List.exists_mem_of_ne_nil _ nonempty
  cases answer with
  | root trace captured completedAssignment history target valid =>
      exact ⟨trace, captured, completedAssignment, history, target, valid⟩

#print axioms default_set_guard_refuses
#print axioms canonical_source_has_no_firing
#print axioms duplicate_source_has_firing

#print axioms same_presented_source
#print axioms ordinary_child_search_on_canonical_source
#print axioms ordinary_child_search_on_duplicate_presentation
#print axioms both_bounded_searches_complete
end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ChildPresentation

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ChildPresentation

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open EquationalScopedMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

def allocationInterpretation := RecursiveCollectionHandoff.matchingInterpretation literalBodyComparison

def presentedElements (duplicates : Bool) : List Pattern := if duplicates then [a, a] else [a]
def childCaptured : Assignment := [("X", localValue [] a)]
def parentCaptured (duplicates : Bool) : Assignment :=
  [("S", localValue [] (choice (presentedElements duplicates)))]
def parentCompleted (duplicates : Bool) : Assignment :=
  ("T", localValue [] b) :: parentCaptured duplicates

/-- Allocation semantics supplies the missing child at either presentation.
This is a source judgment; the ordinary native profile remains guarded. -/
theorem allocation_child_firing (duplicates : Bool) :
    ∃ trace, Interpreted.RootFiring allocationInterpretation environment [] term
      (choice (presentedElements duplicates)) 0 trace childCaptured childCaptured [] b := by
  let spec := GeneralRuleBindingInference.inferredSpec child
  have first : Meaning literalBodyComparison child spec 0 .left [0] 0 [] (.fvar "X") a
      childCaptured := by cbv
  have second : Meaning literalBodyComparison child spec 0 .left [1] 0 childCaptured (.fvar "X") a
      childCaptured := by cbv
  have arguments : ArgumentsMeaning literalBodyComparison child spec 0 .left [] 0 [] 0
      [.fvar "X", .fvar "X"] [a, a] childCaptured := by
    simp only [ArgumentsMeaning]
    exact ⟨childCaptured, first, childCaptured, second, rfl⟩
  have presented : CanonicalBags.Presents .hashSet (presentedElements duplicates) ([a, a] ++ []) := by
    cases duplicates <;> intro item <;> simp [presentedElements]
  have meaning : Meaning literalBodyComparison child spec 0 .left [] 0 [] child.left
      (choice (presentedElements duplicates)) childCaptured := by
    rw [Meaning.eq_def]
    simp only [child, choice, reduceCtorEq, ↓reduceIte, true_and]
    change ∃ values residual middle,
      CanonicalBags.Presents .hashSet (presentedElements duplicates) (values ++ residual) ∧
      ArgumentsMeaning literalBodyComparison child spec 0 .left [] 0 [] 0
        [.fvar "X", .fvar "X"] values middle ∧
      Finished literalBodyComparison child spec 0 .left [] 0 2 none .hashSet middle
        (CanonicalBags.arrange .hashSet residual) childCaptured
    exact ⟨[a, a], [], childCaptured, presented, arguments, by cbv⟩
  obtain ⟨trace, matched⟩ := EquationalScopedReceipts.Meaning.traced meaning
  refine ⟨trace, .fire (by rfl) (by rfl) (by cbv) ?_ matched ?_ .nil (by cbv) ?_⟩
  · apply checkOpenPatternWellSorted_sound
    cases duplicates <;> cbv
  · exact checkTypedAssignment_sound (by cbv)
  · exact checkOpenPatternWellSorted_sound (by cbv)

/-- A conditional parent can use that actual child and bind its target. The
child and target traces are retained in the parent receipt, not erased. -/
theorem allocation_parent_firing (duplicates : Bool) :
    ∃ trace history, Interpreted.RootFiring allocationInterpretation environment [] term
      (box (choice (presentedElements duplicates))) 1 trace
      (parentCaptured duplicates) (parentCompleted duplicates) history (box b) := by
  let spec := GeneralRuleBindingInference.inferredSpec liftRule
  obtain ⟨childTrace, childFired⟩ := allocation_child_firing duplicates
  have captured : EquationalScopedReceipts.Matches literalBodyComparison liftRule spec 0 .left [] 0 []
      liftRule.left (box (choice (presentedElements duplicates))) [] (parentCaptured duplicates) := by
    apply EquationalScopedReceipts.Matches.constructor
    exact .cons (.capture (by cases duplicates <;> cbv)) .nil
  have targetMatched : EquationalScopedReceipts.Matches literalBodyComparison liftRule spec 0
      (.premise 0 0 1) [] 0 (parentCaptured duplicates) (.fvar "T") b []
      (parentCompleted duplicates) := .capture (by cases duplicates <;> cbv)
  have body : Interpreted.PremiseHolds allocationInterpretation environment
      ⟨1, liftRule, spec, [], 0, 0⟩ (.congruence (.fvar "S") (.fvar "T"))
      (parentCaptured duplicates) (parentCompleted duplicates)
      (.child 0 0 0 [] (choice (presentedElements duplicates)) b childTrace []
        childCaptured childCaptured []) := by
    refine .step (by cbv) ?_ childFired targetMatched ?_
    · cases duplicates <;> cbv
    · exact checkTypedAssignment_sound (by cases duplicates <;> cbv)
  refine ⟨[], _, .fire (by rfl) (by rfl) (by cbv) ?_ captured ?_
    (.cons body .nil) ?_ ?_⟩
  · apply checkOpenPatternWellSorted_sound
    cases duplicates <;> cbv
  · exact checkTypedAssignment_sound (by cases duplicates <;> cbv)
  · cases duplicates <;> cbv
  · exact checkOpenPatternWellSorted_sound (by cbv)

theorem allocation_wrong_collection_refused :
    ¬ ∃ trace final, allocationInterpretation.Matches
      ⟨child, GeneralRuleBindingInference.inferredSpec child, 0, .left, [], 0, [], child.left,
        .collection .hashBag [a] none⟩ trace final := by
  rintro ⟨trace, final, matched⟩
  change EquationalScopedReceipts.Matches literalBodyComparison child
    (GeneralRuleBindingInference.inferredSpec child) 0 .left [] 0 [] child.left
      (.collection .hashBag [a] none) trace final at matched
  cases matched

def retainedTargetRule : RewriteRule where
  name := "retained-child-target"
  typeContext := [("S", term), ("T", term)]
  left := .apply "Pair" [.fvar "S", .fvar "T"]
  right := .apply "Pair" [.fvar "S", .fvar "T"]
  premises := [.congruence (.fvar "S") (.fvar "T")]

def heldTarget : Assignment :=
  [("T", localValue [] (choice [a])), ("S", localValue [] (choice [a]))]

def heldTargetRequest (noncanonical : Bool) : RecursiveCollectionMachine.Request :=
  ⟨retainedTargetRule, GeneralRuleBindingInference.inferredSpec retainedTargetRule, 0,
    .premise 0 0 1, [], 0, heldTarget, .fvar "T", choice (presentedElements noncanonical)⟩

/-- A held canonical output distinguishes a raw child reduct from its normal
form. Collection decomposition alone does not normalize this wildcard read. -/
theorem noncanonical_held_target_refused :
    ¬ ∃ trace final, allocationInterpretation.Matches (heldTargetRequest true) trace final := by
  rintro ⟨trace, final, matched⟩
  change EquationalScopedReceipts.Matches literalBodyComparison retainedTargetRule
    (GeneralRuleBindingInference.inferredSpec retainedTargetRule) 0 (.premise 0 0 1) [] 0
    heldTarget (.fvar "T") (choice [a, a]) trace final at matched
  cases matched with
  | capture captured =>
      cbv at captured
      cases captured

theorem canonical_held_target_accepted :
    allocationInterpretation.Matches (heldTargetRequest false) [] heldTarget :=
  EquationalScopedReceipts.Matches.capture (by cbv)

theorem held_target_presentations_equivalent :
    CanonicalBags.Same (heldTargetRequest true).target (heldTargetRequest false).target := by
  change CanonicalBags.canon (choice [a, a]) = CanonicalBags.canon (choice [a])
  exact CanonicalBags.BagStep.canon_eq
    (CanonicalBags.BagStep.members (fun item => by simp) :
      CanonicalBags.BagStep (choice [a, a]) (choice [a]))

#print axioms noncanonical_held_target_refused
#print axioms canonical_held_target_accepted
#print axioms held_target_presentations_equivalent

#print axioms allocation_child_firing
#print axioms allocation_parent_firing
#print axioms allocation_wrong_collection_refused

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.ChildPresentation

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RetainedCollections

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching
open ChildPresentation
open StructuralDescent.Scheduled

def backend := RecursiveCollectionHandoff.canonicalMatchingExecution

def parentRun (elements : List Pattern) (fuel : Nat) :
    State ChildPresentation.environment (ChildPresentation.goal elements) backend :=
  run ChildPresentation.environment (ChildPresentation.goal elements) fuel
    (start ChildPresentation.environment (ChildPresentation.goal elements) backend)

def parentTargets (elements : List Pattern) : List Pattern :=
  (parentRun elements 300).answers.map fun
    | .root _ _ _ _ target _ => target

#guard parentTargets [a] == [box b]
#guard parentTargets [a, a] == [box b]
#guard parentTargets [] == []
#guard (parentRun [a] 300).work == 40
#guard complete ChildPresentation.environment (ChildPresentation.goal [a]) (parentRun [a] 300)
#guard complete ChildPresentation.environment (ChildPresentation.goal []) (parentRun [] 300)

/-- Earlier output captures are read by the next input through the same
matching interpretation. Both provider values are authored data. -/
def queryRule : RewriteRule :=
  { ChildPresentation.liftRule with
    name := "collection-output-then-input"
    premises := [.relationQuery "produce" [.fvar "T"],
      .relationQuery "consume" [.fvar "T"]] }

def queryEnvironment (present : Bool := true) : Environment where
  language := {ChildPresentation.language with rewrites := [queryRule]}
  free := fun _ => none
  provider := {
    signatures := [⟨"produce", [term], [.output]⟩, ⟨"consume", [term], [.input]⟩]
    rows := if present then [⟨"produce", [choice [a, a]]⟩, ⟨"consume", [choice [a]]⟩]
      else [⟨"produce", [choice [a, a]]⟩] }
  specifications := [(0, GeneralRuleBindingInference.inferredSpec queryRule)]

def queryGoal : Goal := .root 1 [] term (box a) 0

def queryRun (present : Bool) (fuel : Nat) :
    State (queryEnvironment present) queryGoal backend :=
  run (queryEnvironment present) queryGoal fuel
    (start (queryEnvironment present) queryGoal backend)

def queryTargets (present : Bool) : List Pattern :=
  (queryRun present 300).answers.map fun
    | .root _ _ _ _ target _ => target

#guard queryTargets true == [box (choice [a])]
#guard queryTargets false == []
#guard complete (queryEnvironment true) queryGoal (queryRun true 300)
#guard complete (queryEnvironment false) queryGoal (queryRun false 300)

def quantifiedGoal (elements : List Pattern) : Goal :=
  .root 1 [] SharedOutputControls.term
    (.apply "SetWrap" [.collection .hashSet elements none]) 0

def quantifiedEnvironment : Environment :=
  { SetValidation.environment with language :=
      { SetValidation.language with terms := SetValidation.language.terms.map fun declaration =>
          if declaration.label == "SetWrap" then
            { declaration with collectionRepresentation := .wrapped }
          else declaration } }

def quantifiedRun (elements : List Pattern) (fuel : Nat) :
    State quantifiedEnvironment (quantifiedGoal elements) backend :=
  run quantifiedEnvironment (quantifiedGoal elements) fuel
    (start quantifiedEnvironment (quantifiedGoal elements) backend)

-- These count retained validation histories. They do not identify logical
-- derivations or license a derivation-bag observation.
#guard (quantifiedRun [SharedOutputControls.zero] 600).answers.length == 2
#guard (quantifiedRun [SharedOutputControls.zero, SharedOutputControls.zero] 600).answers.length == 2
#guard (quantifiedRun [SharedOutputControls.zero, SharedOutputControls.one] 600).answers.isEmpty
#guard (quantifiedRun [] 600).answers.length == 1
#guard complete quantifiedEnvironment (quantifiedGoal [SharedOutputControls.zero])
  (quantifiedRun [SharedOutputControls.zero] 600)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.SharedOutputControls.RetainedCollections
