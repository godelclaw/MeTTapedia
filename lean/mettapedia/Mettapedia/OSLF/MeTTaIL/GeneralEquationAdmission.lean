import Mettapedia.OSLF.MeTTaIL.GeneralEquationMeasures

/-!
# Executable balance admission for authored scoped equations

Each actual metavariable address is checked using its authored occurrence spine.
Only injective local-variable spines are admitted for equation instantiation,
at ordinary metavariables and at collection rests alike; explicit substitution
retains a separate obligation. A rest splices the residual it captured, so an
instance has one node fewer per rest slot than the weighted side
(`instantiate_nodes`). The structural bound is derived from constant
contributions, exact variable multiplicities and equal rest counts, rather than
from equal raw template sizes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationAdmission

open Syntax RuleBinding ScopedRuleMatching PatternTreeSize GeneralEquationMeasures

/-- A rest slot is supported when its occurrence spine is an injective local-variable spine. -/
def restSupported (rule : RewriteRule) (spec : RuleBindingSpec)
    (site : RulePatternSite) (path : List Nat) (depth : Nat) : Option String → Bool
  | none => true
  | some name =>
      match arguments? rule spec name site path with
      | none => false
      | some arguments => arguments.all variableArgument && (variableSpine? depth arguments).isSome

mutual
  /-- The collection-rest slots of a pattern. -/
  def restCount : Pattern → Nat
    | .bvar _ | .fvar _ => 0
    | .apply _ arguments => restCountList arguments
    | .lambda _ body | .multiLambda _ _ body => restCount body
    | .subst body replacement => restCount body + restCount replacement
    | .collection _ elements rest => restCountList elements + rest.toList.length

  def restCountList : List Pattern → Nat
    | [] => 0
    | first :: rest => restCount first + restCountList rest
end

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
        restSupported rule spec site (path ++ [elements.length]) depth rest &&
          checkArguments rule spec site path depth 0 elements
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

theorem listNodes_append (first second : List Pattern) :
    listNodes (first ++ second) = listNodes first + listNodes second := by
  induction first with
  | nil => simp [listNodes]
  | cons head tail ih => simp only [List.cons_append, listNodes, ih]; omega

mutual
  theorem instantiate_nodes (rule : RewriteRule) (spec : RuleBindingSpec)
      (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (assignment : Assignment) (pattern result : Pattern)
      (supported : checkSide rule spec site path depth pattern = true)
      (instantiated : instantiateAt? rule spec ambient site path depth assignment pattern = some result) :
      nodes result + restCount pattern = evaluate (capturedWeight assignment) pattern := by
    cases pattern with
    | fvar name =>
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨value, found, arguments, occurrence, interpreted⟩ := instantiated
        simp only [checkSide, occurrence, Bool.and_eq_true] at supported
        have count := instantiateValue_nodes value ambient depth arguments result supported.1 interpreted
        simpa only [evaluate, capturedWeight, found, Option.map_some, Option.getD_some, restCount,
          Nat.add_zero] using count
    | bvar index =>
        simp only [instantiateAt?, instantiateWith?, Option.some.injEq] at instantiated
        cases instantiated
        simp [nodes, restCount, evaluate]
    | apply constructor arguments =>
        simp only [checkSide] at supported
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨results, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have count := instantiateArguments_nodes rule spec ambient site path depth assignment 0
          arguments results supported interpreted
        simp only [nodes, evaluate, restCount]
        omega
    | lambda binder body =>
        simp only [checkSide] at supported
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨bodyResult, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have count := instantiate_nodes rule spec ambient site (path ++ [0]) (depth + 1)
          assignment body bodyResult supported interpreted
        simp only [nodes, evaluate, restCount]
        omega
    | multiLambda arity binders body =>
        simp only [checkSide] at supported
        simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨bodyResult, interpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have count := instantiate_nodes rule spec ambient site (path ++ [0]) (depth + arity)
          assignment body bodyResult supported interpreted
        simp only [nodes, evaluate, restCount]
        omega
    | subst body replacement => simp only [checkSide, Bool.false_eq_true] at supported
    | collection kind elements rest =>
        simp only [checkSide, Bool.and_eq_true] at supported
        cases rest with
        | none =>
            simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
            obtain ⟨results, interpreted, equal⟩ := instantiated
            cases Option.some.inj equal
            have count := instantiateArguments_nodes rule spec ambient site path depth assignment 0
              elements results supported.2 interpreted
            simp only [nodes, evaluate, restCount, Option.toList_none, List.map_nil, List.sum_nil, List.length_nil]
            omega
        | some name =>
            simp only [instantiateAt?, instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
            obtain ⟨explicit, interpreted, value, found, arguments, occurrence, residualValue, residual, spliced⟩ :=
              instantiated
            have spine := supported.1
            simp only [restSupported, occurrence, Bool.and_eq_true] at spine
            have valueCount := instantiateValue_nodes value ambient depth arguments residualValue spine.1 residual
            have count := instantiateArguments_nodes rule spec ambient site path depth assignment 0
              elements explicit supported.2 interpreted
            split at spliced
            · rename_i actualKind items
              split at spliced
              · cases spliced
                simp only [nodes] at valueCount
                simp only [nodes, evaluate, restCount, listNodes_append, capturedWeight, found, Option.map_some,
                  Option.getD_some, Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  List.length_cons, List.length_nil]
                omega
              · cases spliced
            · cases spliced
  termination_by sizeOf pattern

  theorem instantiateArguments_nodes (rule : RewriteRule) (spec : RuleBindingSpec)
      (ambient : Nat) (site : RulePatternSite) (path : List Nat) (depth : Nat)
      (assignment : Assignment) (index : Nat) (patterns results : List Pattern)
      (supported : checkArguments rule spec site path depth index patterns = true)
      (instantiated : instantiateArgsWith? Substitution.instantiateBVar rule spec ambient site path depth
        assignment index patterns = some results) :
      listNodes results + restCountList patterns = evaluateList (capturedWeight assignment) patterns := by
    cases patterns with
    | nil =>
        simp only [instantiateArgsWith?, Option.some.injEq] at instantiated
        cases instantiated
        simp [listNodes, restCountList, evaluateList]
    | cons first rest =>
        simp only [checkArguments, Bool.and_eq_true] at supported
        simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at instantiated
        obtain ⟨firstResult, firstInterpreted, restResults, restInterpreted, equal⟩ := instantiated
        cases Option.some.inj equal
        have firstCount := instantiate_nodes rule spec ambient site (path ++ [index]) depth
          assignment first firstResult supported.1 firstInterpreted
        have restCount := instantiateArguments_nodes rule spec ambient site path depth assignment (index + 1)
          rest restResults supported.2 restInterpreted
        simp only [listNodes, evaluateList, restCountList]
        omega
  termination_by sizeOf patterns
end

/-- Balance with equal rest counts: the sides' constants, variables and rest slots agree. -/
def balancedSides (left right : Pattern) : Bool :=
  balanced left right && restCount left == restCount right

theorem balancedSides_balanced {left right : Pattern} (accepted : balancedSides left right = true) :
    balanced left right = true := (Bool.and_eq_true_iff.mp accepted).1

theorem balancedSides_rest {left right : Pattern} (accepted : balancedSides left right = true) :
    restCount left = restCount right := beq_iff_eq.mp (Bool.and_eq_true_iff.mp accepted).2

def checkRule (rule : RewriteRule) (spec : RuleBindingSpec) : Bool :=
  admittedFor rule spec && checkSide rule spec .left [] 0 rule.left &&
    checkSide rule spec .right [] 0 rule.right && balancedSides rule.left rule.right

theorem checkRule_sides (rule : RewriteRule) (spec : RuleBindingSpec)
    (accepted : checkRule rule spec = true) :
    admittedFor rule spec = true ∧
      checkSide rule spec .left [] 0 rule.left = true ∧
      checkSide rule spec .right [] 0 rule.right = true ∧ balancedSides rule.left rule.right = true := by
  simpa only [checkRule, Bool.and_eq_true, and_assoc] using accepted

theorem instantiated_equation_nodes (rule : RewriteRule) (spec : RuleBindingSpec)
    (accepted : checkRule rule spec = true) (ambient : Nat) (assignment : Assignment)
    (left right : Pattern)
    (before : instantiateAt? rule spec ambient .left [] 0 assignment rule.left = some left)
    (after : reduct? rule spec ambient assignment = some right) : nodes left = nodes right := by
  have ready := checkRule_sides rule spec accepted
  have leftCount := instantiate_nodes rule spec ambient .left [] 0 assignment rule.left left ready.2.1 before
  have rightCount := instantiate_nodes rule spec ambient .right [] 0 assignment rule.right right ready.2.2.1 after
  have same := balanced_evaluate rule.left rule.right (balancedSides_balanced ready.2.2.2) (capturedWeight assignment)
  have rests := balancedSides_rest ready.2.2.2
  omega

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
