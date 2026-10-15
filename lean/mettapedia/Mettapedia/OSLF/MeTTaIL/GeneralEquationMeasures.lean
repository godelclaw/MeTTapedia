import Mettapedia.OSLF.MeTTaIL.PatternTreeSize
import Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution
import Mathlib.Data.List.Perm.Basic

/-!
# Structural measures of scoped equation instances

Binder display metadata and de Bruijn spelling do not affect tree-node counts.
An occurrence substitution consisting of variables is a renaming and preserves
these counts. Schema sizes are affine in captured metavariable body sizes;
balancing both the constant contribution and multiplicities earns preservation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationMeasures

open Syntax RuleBinding ScopedRuleMatching PatternTreeSize

theorem listNodes_map_eq (function : Pattern → Pattern) (patterns : List Pattern)
    (same : ∀ pattern ∈ patterns, nodes (function pattern) = nodes pattern) :
    listNodes (patterns.map function) = listNodes patterns := by
  induction patterns with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.map_cons, listNodes, same first (by simp)]
    rw [ih (by intro pattern member; exact same pattern (by simp [member]))]

theorem nodes_liftBVars (cutoff shift : Nat) (pattern : Pattern) :
    nodes (Substitution.liftBVars cutoff shift pattern) = nodes pattern := by
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index => simp only [Substitution.liftBVars]; split <;> rfl
  | hfvar name => rfl
  | happly constructor arguments ih =>
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, nodes]
    rw [listNodes_map_eq _ arguments (by intro pattern member; exact ih pattern member cutoff)]
  | hlambda name body ih => simp only [Substitution.liftBVars, nodes, ih]
  | hmultiLambda arity names body ih => simp only [Substitution.liftBVars, nodes, ih]
  | hsubst body replacement bodyIH replacementIH =>
    simp only [Substitution.liftBVars, nodes, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    simp only [Substitution.liftBVars, Substitution.liftBVarsList_eq_map, nodes]
    rw [listNodes_map_eq _ elements (by intro pattern member; exact ih pattern member cutoff)]

def VariablesOnly (assignment : ContextSubstitution.Assignment) : Prop :=
  ∀ index, ∃ next, assignment index = .bvar next

theorem VariablesOnly.lift {assignment : ContextSubstitution.Assignment}
    (variableOnly : VariablesOnly assignment) (arity : Nat) :
    VariablesOnly (ContextSubstitution.lift arity assignment) := by
  intro index
  unfold ContextSubstitution.lift
  split
  · exact ⟨index, rfl⟩
  · obtain ⟨next, equal⟩ := variableOnly (index - arity)
    rw [equal]
    exact ⟨next + arity, by simp [Substitution.liftBVars]⟩

theorem nodes_substitute_variables (assignment : ContextSubstitution.Assignment)
    (variableOnly : VariablesOnly assignment) (pattern : Pattern) :
    nodes (ContextSubstitution.substitute assignment pattern) = nodes pattern := by
  induction pattern using Pattern.inductionOn generalizing assignment with
  | hbvar index =>
    obtain ⟨next, equal⟩ := variableOnly index
    simp only [ContextSubstitution.substitute, equal, nodes]
  | hfvar name => rfl
  | happly constructor arguments ih =>
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, nodes]
    rw [listNodes_map_eq _ arguments (by intro pattern member; exact ih pattern member assignment variableOnly)]
  | hlambda name body ih =>
    simp only [ContextSubstitution.substitute, nodes, ih _ (variableOnly.lift 1)]
  | hmultiLambda arity names body ih =>
    simp only [ContextSubstitution.substitute, nodes, ih _ (variableOnly.lift arity)]
  | hsubst body replacement bodyIH replacementIH =>
    simp only [ContextSubstitution.substitute, nodes, bodyIH _ (variableOnly.lift 1), replacementIH _ variableOnly]
  | hcollection kind elements rest ih =>
    simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map, nodes]
    rw [listNodes_map_eq _ elements (by intro pattern member; exact ih pattern member assignment variableOnly)]

def variableArgument : Pattern → Bool
  | .bvar _ => true
  | _ => false

theorem variableArgument_spec (argument : Pattern) :
    variableArgument argument = true ↔ ∃ index, argument = .bvar index := by
  cases argument <;> simp [variableArgument]

theorem getD_variable (arguments : List Pattern)
    (variableOnly : arguments.all variableArgument = true) (index : Nat) :
    ∃ next, arguments.getD index (.bvar 0) = .bvar next := by
  induction arguments generalizing index with
  | nil => exact ⟨0, rfl⟩
  | cons first rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at variableOnly
    cases index with
    | zero => simpa only [List.getD_cons_zero] using (variableArgument_spec first).mp variableOnly.1
    | succ index => simpa only [List.getD_cons_succ] using ih variableOnly.2 index

theorem occurrenceAssignment_variables (dependencies depth : Nat) (arguments : List Pattern)
    (variableOnly : arguments.all variableArgument = true) :
    VariablesOnly (occurrenceAssignment dependencies depth arguments) := by
  intro index
  unfold occurrenceAssignment
  split
  · exact getD_variable arguments variableOnly index
  · exact ⟨depth + (index - dependencies), rfl⟩

theorem instantiateValue_nodes (value : ContextualValue) (ambient depth : Nat)
    (arguments : List Pattern) (result : Pattern)
    (variableOnly : arguments.all variableArgument = true)
    (instantiated : instantiateValue? value ambient depth arguments = some result) :
    nodes result = nodes value.body := by
  unfold instantiateValue? at instantiated
  split at instantiated <;> try cases instantiated
  split at instantiated <;> try cases instantiated
  split at instantiated <;> try cases instantiated
  split at instantiated <;> try cases instantiated
  dsimp only at instantiated
  split at instantiated <;> try cases instantiated
  exact nodes_substitute_variables _ (occurrenceAssignment_variables _ _ arguments variableOnly) value.body

mutual
  def evaluate (weights : String → Nat) : Pattern → Nat
    | .fvar name => weights name
    | .bvar _ => 1
    | .apply _ arguments => 1 + evaluateList weights arguments
    | .lambda _ body => 1 + evaluate weights body
    | .multiLambda _ _ body => 1 + evaluate weights body
    | .subst body replacement => 1 + evaluate weights body + evaluate weights replacement
    | .collection _ elements rest =>
        1 + evaluateList weights elements + (rest.toList.map weights).sum

  def evaluateList (weights : String → Nat) : List Pattern → Nat
    | [] => 0
    | first :: rest => evaluate weights first + evaluateList weights rest
end

def constantContribution (pattern : Pattern) : Nat := evaluate (fun _ => 0) pattern

theorem evaluate_affine (weights : String → Nat) (pattern : Pattern) :
    evaluate weights pattern = constantContribution pattern + (pattern.freeFvarNames.map weights).sum := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp [evaluate, constantContribution, Pattern.freeFvarNames]
  | hfvar name => simp [evaluate, constantContribution, Pattern.freeFvarNames]
  | happly constructor arguments ih =>
    have lists : evaluateList weights arguments = evaluateList (fun _ => 0) arguments +
        ((arguments.flatMap Pattern.freeFvarNames).map weights).sum := by
      induction arguments with
      | nil => simp [evaluateList]
      | cons first rest tailIH =>
        have firstIH := ih first (by simp)
        have tail := tailIH (by intro pattern member; exact ih pattern (by simp [member]))
        simp only [evaluateList, List.flatMap_cons, List.map_append, List.sum_append,
          firstIH, constantContribution, tail]
        omega
    simp only [evaluate, constantContribution, Pattern.freeFvarNames, lists]
    omega
  | hlambda name body ih => simp only [evaluate, constantContribution, Pattern.freeFvarNames] at *; omega
  | hmultiLambda arity names body ih => simp only [evaluate, constantContribution, Pattern.freeFvarNames] at *; omega
  | hsubst body replacement bodyIH replacementIH =>
    simp only [evaluate, constantContribution, Pattern.freeFvarNames, List.map_append, List.sum_append] at *
    omega
  | hcollection kind elements rest ih =>
    have lists : evaluateList weights elements = evaluateList (fun _ => 0) elements +
        ((elements.flatMap Pattern.freeFvarNames).map weights).sum := by
      induction elements with
      | nil => simp [evaluateList]
      | cons first tail tailIH =>
        have firstIH := ih first (by simp)
        have later := tailIH (by intro pattern member; exact ih pattern (by simp [member]))
        simp only [evaluateList, List.flatMap_cons, List.map_append, List.sum_append,
          firstIH, constantContribution, later]
        omega
    simp only [evaluate, constantContribution, Pattern.freeFvarNames, List.map_append, List.sum_append, lists]
    have zero : (rest.toList.map (fun _ : String => 0)).sum = 0 := by cases rest <;> simp
    omega

def balanced (left right : Pattern) : Bool :=
  constantContribution left == constantContribution right &&
    decide (left.freeFvarNames.Perm right.freeFvarNames)

theorem balanced_evaluate (left right : Pattern) (accepted : balanced left right = true)
    (weights : String → Nat) : evaluate weights left = evaluate weights right := by
  simp only [balanced, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at accepted
  rw [evaluate_affine, evaluate_affine, accepted.1]
  exact congrArg (constantContribution right + ·) ((accepted.2.map weights).sum_eq)

theorem eraseBinderMetadata_nodes (pattern : Pattern) :
    nodes pattern.eraseBinderMetadata = nodes pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp only [Pattern.eraseBinderMetadata, nodes]
  | hfvar name => simp only [Pattern.eraseBinderMetadata, nodes]
  | happly constructor arguments ih =>
    simp only [Pattern.eraseBinderMetadata, nodes]
    rw [listNodes_map_eq _ arguments ih]
  | hlambda name body ih => simp only [Pattern.eraseBinderMetadata, nodes, ih]
  | hmultiLambda arity names body ih => simp only [Pattern.eraseBinderMetadata, nodes, ih]
  | hsubst body replacement bodyIH replacementIH => simp only [Pattern.eraseBinderMetadata, nodes, bodyIH, replacementIH]
  | hcollection kind elements rest ih =>
    simp only [Pattern.eraseBinderMetadata, nodes]
    rw [listNodes_map_eq _ elements ih]

end Mettapedia.OSLF.MeTTaIL.GeneralEquationMeasures
