import Mettapedia.Languages.Datalog.Syntax
import Mathlib.Data.Set.Basic

/-! Range checking and the active-domain law for actual matching tuples. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog

def Clause.RangeRestricted (clause : Clause) : Prop :=
  (∀ argument ∈ clause.requiredArguments, argument ≠ .anonymous) ∧
    ∀ name ∈ clause.requiredVariables, name ∈ clause.providedVariables

def Clause.checkRangeRestriction (clause : Clause) : Bool :=
  clause.requiredArguments.all (fun argument => !argument.isAnonymous) &&
    clause.requiredVariables.all clause.providedVariables.contains

theorem Clause.checkRangeRestriction_iff (clause : Clause) :
    clause.checkRangeRestriction = true ↔ clause.RangeRestricted := by
  simp [checkRangeRestriction,RangeRestricted,List.all_eq_true]

private theorem matched_argument {assignment : Assignment} {arguments : List Argument} {values : List Value}
    (matched : List.Forall₂ (Argument.Matches assignment) arguments values)
    {argument : Argument} (member : argument ∈ arguments) :
    ∃ value ∈ values, Argument.Matches assignment argument value := by
  induction matched with
  | nil => simp at member
  | @cons first value arguments values head tail recurse =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨value,List.mem_cons_self,head⟩
      · obtain ⟨other,inside,matched⟩ := recurse later
        exact ⟨other,List.mem_cons_of_mem _ inside,matched⟩

private theorem matched_value {assignment : Assignment} {arguments : List Argument} {values : List Value}
    (matched : List.Forall₂ (Argument.Matches assignment) arguments values)
    {value : Value} (member : value ∈ values) :
    ∃ argument ∈ arguments, Argument.Matches assignment argument value := by
  induction matched with
  | nil => simp at member
  | @cons first value arguments values head tail recurse =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨first,List.mem_cons_self,head⟩
      · obtain ⟨other,inside,matched⟩ := recurse later
        exact ⟨other,List.mem_cons_of_mem _ inside,matched⟩

theorem Atom.variable_has_matching_value {assignment : Assignment} {schema : Atom} {fact : GroundFact}
    (matched : schema.Matches assignment fact) {name : String} (used : name ∈ schema.variables) :
    ∃ value ∈ fact.values, assignment name = some value := by
  obtain ⟨argument,inside,used⟩ := List.mem_flatMap.mp used
  cases argument with
  | literal value => simp [Argument.vars] at used
  | anonymous => simp [Argument.vars] at used
  | var identifier =>
      have same : name = identifier := by simpa [Argument.vars] using used
      subst identifier
      exact matched_argument matched.2 inside

/-- Range restriction derives the value of every required variable from a
real positive body fact. No enumerated grounding or head conclusion is assumed. -/
theorem Clause.required_variable_from_body {clause : Clause}
    (restricted : clause.RangeRestricted) (assignment : Assignment) (known : Set GroundFact)
    (body : ∀ atom ∈ clause.positiveAtoms, ∃ fact ∈ known, atom.Matches assignment fact)
    {name : String} (used : name ∈ clause.requiredVariables) :
    ∃ fact ∈ known, ∃ value ∈ fact.values, assignment name = some value := by
  have supplied := restricted.2 name used
  obtain ⟨atom,inside,variableUsed⟩ := List.mem_flatMap.mp supplied
  obtain ⟨fact,knownFact,matched⟩ := body atom inside
  obtain ⟨value,member,bound⟩ := Atom.variable_has_matching_value matched variableUsed
  exact ⟨fact,knownFact,value,member,bound⟩

/-- Every matched head value is either a literal in the program or comes
from a positive premise. Comparisons cannot enlarge the active domain. -/
theorem Clause.head_values_in_active_domain {clause : Clause}
    (restricted : clause.RangeRestricted) (assignment : Assignment)
    (known : Set GroundFact) (domain : Set Value)
    (knownWithin : ∀ fact ∈ known, ∀ value ∈ fact.values, value ∈ domain)
    (literalsWithin : ∀ value, Argument.literal value ∈ clause.head.arguments → value ∈ domain)
    (body : ∀ atom ∈ clause.positiveAtoms, ∃ fact ∈ known, atom.Matches assignment fact)
    (conclusion : GroundFact) (matched : clause.head.Matches assignment conclusion) :
    ∀ value ∈ conclusion.values, value ∈ domain := by
  intro value member
  obtain ⟨argument,argumentIn,argumentMatches⟩ := matched_value matched.2 member
  cases argument with
  | literal literal =>
      have same : literal = value := argumentMatches
      subst literal
      exact literalsWithin value argumentIn
  | var name =>
      have neededArgument : Argument.var name ∈ clause.requiredArguments :=
        List.mem_append_left _ argumentIn
      have needed : name ∈ clause.requiredVariables :=
        List.mem_flatMap.mpr ⟨.var name,neededArgument,by simp [Argument.vars]⟩
      obtain ⟨fact,knownFact,actual,actualIn,bound⟩ :=
        Clause.required_variable_from_body restricted assignment known body needed
      have same : actual = value := Option.some.inj (bound.symm.trans argumentMatches)
      exact same ▸ knownWithin fact knownFact actual actualIn
  | anonymous =>
      exact False.elim (restricted.1 .anonymous (List.mem_append_left _ argumentIn) rfl)

namespace Controls

private def atom (relation : String) (arguments : List Argument) : Atom := ⟨[relation],arguments⟩
private def x : Argument := .var "X"
private def y : Argument := .var "Y"
private def literal : Argument := .literal (.number 1)

def good : Clause :=
  ⟨atom "Reach" [x,y],[.atom (atom "Edge" [x,y]),.comparison ⟨.different,x,literal⟩]⟩
def missingHead : Clause := ⟨atom "Reach" [x,y],[.atom (atom "Edge" [x,literal])]⟩
def missingComparison : Clause :=
  ⟨atom "Reach" [x],[.atom (atom "Edge" [x,literal]),.comparison ⟨.different,y,literal⟩]⟩
def anonymousBody : Clause := ⟨atom "Reach" [x],[.atom (atom "Edge" [x,.anonymous])]⟩
def anonymousHead : Clause := ⟨atom "Reach" [.anonymous],[.atom (atom "Edge" [x,literal])]⟩
def anonymousComparison : Clause :=
  ⟨atom "Reach" [x],[.atom (atom "Edge" [x,literal]),.comparison ⟨.equal,x,.anonymous⟩]⟩

theorem separating_checks :
    good.checkRangeRestriction = true ∧ anonymousBody.checkRangeRestriction = true ∧
      missingHead.checkRangeRestriction = false ∧ missingComparison.checkRangeRestriction = false ∧
      anonymousHead.checkRangeRestriction = false ∧ anonymousComparison.checkRangeRestriction = false := by
  decide +kernel

end Controls

#print axioms Clause.checkRangeRestriction_iff
#print axioms Clause.required_variable_from_body
#print axioms Clause.head_values_in_active_domain
#print axioms Controls.separating_checks

end Mettapedia.Languages.Datalog
