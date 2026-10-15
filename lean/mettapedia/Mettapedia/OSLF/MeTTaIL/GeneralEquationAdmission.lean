import Mettapedia.OSLF.MeTTaIL.GeneralEquationMeasures

/-!
# Executable balance admission for authored scoped equations

Each actual metavariable address is checked using its authored occurrence spine.
Only injective local-variable spines are admitted for equation instantiation;
explicit substitution and collection-rest splicing retain separate obligations.
The structural bound is derived from constant contributions and exact variable
multiplicities, rather than from equal raw template sizes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationAdmission

open Syntax RuleBinding ScopedRuleMatching PatternTreeSize GeneralEquationMeasures

mutual
  def checkSide (rule : RewriteRule) (spec : RuleBindingSpec)
      (site : RulePatternSite) (path : List Nat) (depth : Nat) : Pattern → Bool
    | .fvar name =>
        match arguments? rule spec name site path with
        | none => false
        | some arguments =>
            arguments.all variableArgument && (variableSpine? depth arguments).isSome
    | .bvar _ => true
    | .apply _ arguments => checkArguments rule spec site path depth 0 arguments
    | .lambda _ body => checkSide rule spec site (path ++ [0]) (depth + 1) body
    | .multiLambda arity _ body => checkSide rule spec site (path ++ [0]) (depth + arity) body
    | .subst _ _ => false
    | .collection _ elements rest =>
        rest.isNone && checkArguments rule spec site path depth 0 elements
  termination_by pattern => sizeOf pattern

  def checkArguments (rule : RewriteRule) (spec : RuleBindingSpec)
      (site : RulePatternSite) (path : List Nat) (depth index : Nat) : List Pattern → Bool
    | [] => true
    | first :: rest =>
        checkSide rule spec site (path ++ [index]) depth first &&
          checkArguments rule spec site path depth (index + 1) rest
  termination_by patterns => sizeOf patterns
end

def capturedWeight (assignment : Assignment) (name : String) : Nat :=
  ((lookup assignment name).map fun value => nodes value.body).getD 0

mutual
  theorem instantiate_nodes (rule : RewriteRule) (spec : RuleBindingSpec)
      (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (assignment : Assignment) (pattern result : Pattern)
      (supported : checkSide rule spec site path depth pattern = true)
      (instantiated : instantiateAt? rule spec ambient site path depth assignment pattern = some result) :
      nodes result = evaluate (capturedWeight assignment) pattern := by
    cases pattern with
    | fvar name =>
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨value, found, arguments, occurrence, interpreted⟩ := instantiated
        simp only [checkSide, occurrence, Bool.and_eq_true] at supported
        have count := instantiateValue_nodes value ambient depth arguments result supported.1 interpreted
        simpa only [evaluate, capturedWeight, found, Option.map_some, Option.getD_some] using count
    | bvar index =>
        simp only [instantiateAt?, instantiateWith?, Option.some.injEq] at instantiated
        cases instantiated
        rfl
    | apply constructor arguments =>
        simp only [checkSide] at supported
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨results, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have count := instantiateArguments_nodes rule spec ambient site path depth assignment 0
          arguments results supported interpreted
        simp only [nodes, evaluate, count]
    | lambda binder body =>
        simp only [checkSide] at supported
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨bodyResult, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have count := instantiate_nodes rule spec ambient site (path ++ [0]) (depth + 1)
          assignment body bodyResult supported interpreted
        simp only [nodes, evaluate, count]
    | multiLambda arity binders body =>
        simp only [checkSide] at supported
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨bodyResult, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have count := instantiate_nodes rule spec ambient site (path ++ [0]) (depth + arity)
          assignment body bodyResult supported interpreted
        simp only [nodes, evaluate, count]
    | subst body replacement => simp only [checkSide, Bool.false_eq_true] at supported
    | collection kind elements rest =>
        cases rest with
        | some name => simp only [checkSide, Option.isNone_some, Bool.false_and, Bool.false_eq_true] at supported
        | none =>
            simp only [checkSide, Option.isNone_none, Bool.true_and] at supported
            simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
            obtain ⟨results, interpreted, equal⟩ := instantiated
            cases Option.some.inj equal
            have count := instantiateArguments_nodes rule spec ambient site path depth assignment 0
              elements results supported interpreted
            simp only [nodes, evaluate, Option.toList_none, List.map_nil, List.sum_nil, Nat.add_zero, count]
  termination_by sizeOf pattern

  theorem instantiateArguments_nodes (rule : RewriteRule) (spec : RuleBindingSpec)
      (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (assignment : Assignment) (index : Nat) (patterns results : List Pattern)
      (supported : checkArguments rule spec site path depth index patterns = true)
      (instantiated : instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth
        assignment index patterns = some results) :
      listNodes results = evaluateList (capturedWeight assignment) patterns := by
    cases patterns with
    | nil =>
        simp only [instantiateArgsWith?, Option.some.injEq] at instantiated
        cases instantiated
        rfl
    | cons first rest =>
        simp only [checkArguments, Bool.and_eq_true] at supported
        simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨firstResult, firstInterpreted, restResults, restInterpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have firstCount := instantiate_nodes rule spec ambient site (path ++ [index]) depth
          assignment first firstResult supported.1 firstInterpreted
        have restCount := instantiateArguments_nodes rule spec ambient site path depth assignment (index + 1)
          rest restResults supported.2 restInterpreted
        simp only [listNodes, evaluateList, firstCount, restCount]
  termination_by sizeOf patterns
end

def checkRule (rule : RewriteRule) (spec : RuleBindingSpec) : Bool :=
  admittedFor rule spec && checkSide rule spec .left [] 0 rule.left &&
    checkSide rule spec .right [] 0 rule.right && balanced rule.left rule.right

theorem checkRule_sides (rule : RewriteRule) (spec : RuleBindingSpec)
    (accepted : checkRule rule spec = true) :
    admittedFor rule spec = true ∧
      checkSide rule spec .left [] 0 rule.left = true ∧
      checkSide rule spec .right [] 0 rule.right = true ∧ balanced rule.left rule.right = true := by
  simpa only [checkRule, Bool.and_eq_true, and_assoc] using accepted

theorem instantiated_equation_nodes (rule : RewriteRule) (spec : RuleBindingSpec)
    (accepted : checkRule rule spec = true) (ambient : Nat) (assignment : Assignment)
    (left right : Pattern)
    (before : instantiateAt? rule spec ambient .left [] 0 assignment rule.left = some left)
    (after : reduct? rule spec ambient assignment = some right) : nodes left = nodes right := by
  have ready := checkRule_sides rule spec accepted
  rw [instantiate_nodes rule spec ambient .left [] 0 assignment rule.left left ready.2.1 before,
    instantiate_nodes rule spec ambient .right [] 0 assignment rule.right right ready.2.2.1 after]
  exact balanced_evaluate rule.left rule.right ready.2.2.2 (capturedWeight assignment)

def checkEquation (equation : Equation) : Bool :=
  [ScopedEquationExecution.Orientation.forward, .reverse].all fun orientation =>
    let rule := ScopedEquationExecution.orientedRule equation orientation
    match rule.bindings with
    | none => false
    | some spec => checkRule rule spec

theorem checkEquation_orientation (equation : Equation) (accepted : checkEquation equation = true)
    (orientation : ScopedEquationExecution.Orientation) :
    ∃ spec, (ScopedEquationExecution.orientedRule equation orientation).bindings = some spec ∧
      checkRule (ScopedEquationExecution.orientedRule equation orientation) spec = true := by
  have all := List.all_eq_true.mp accepted orientation (by cases orientation <;> simp)
  cases declared : (ScopedEquationExecution.orientedRule equation orientation).bindings with
  | none => simp [declared] at all
  | some spec => exact ⟨spec, rfl, by simpa only [declared] using all⟩

def checkLanguage (language : LanguageDef) : Bool := language.equations.all checkEquation

theorem checkLanguage_equation (language : LanguageDef) (accepted : checkLanguage language = true)
    (equation : Equation) (authored : equation ∈ language.equations) : checkEquation equation = true :=
  List.all_eq_true.mp accepted equation authored

end Mettapedia.OSLF.MeTTaIL.GeneralEquationAdmission
