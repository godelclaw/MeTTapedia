import Mettapedia.OSLF.MeTTaIL.GeneralPremiseAdmission

/-!
# Lexical quantifier bindings and syntactic freshness

A quantified parameter is local. Its value shadows the outer parameter while
the body runs, and the original contextual value is restored afterwards.
Every other captured name survives a successful body. Freshness reads the
actual instantiated subject; it is not an equality or a step premise.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Remove every local declaration of one name. First-match lookup of every
other name is unchanged. -/
@[simp] theorem lookup_cons (key name : String) (value : ContextualValue)
    (tail : Assignment) : lookup ((key, value) :: tail) name =
      if key == name then some value else lookup tail name := by
  by_cases same : key = name
  · subst key
    simp [lookup]
  · simp [lookup, same]

def removeParameter (name : String) : Assignment → Assignment
  | [] => []
  | (key, value) :: tail =>
      if key == name then removeParameter name tail
      else (key, value) :: removeParameter name tail

theorem lookup_remove_other (assignment : Assignment) (parameter name : String)
    (different : name ≠ parameter) :
    lookup (removeParameter parameter assignment) name = lookup assignment name := by
  induction assignment with
  | nil => rfl
  | cons entry entries inductionHypothesis =>
      rcases entry with ⟨key, value⟩
      by_cases same : key = parameter
      · subst key
        simp [removeParameter, Ne.symm different, inductionHypothesis]
      · simp [removeParameter, same, inductionHypothesis]

@[simp] theorem lookup_remove_parameter (assignment : Assignment) (name : String) :
    lookup (removeParameter name assignment) name = none := by
  induction assignment with
  | nil => rfl
  | cons entry entries inductionHypothesis =>
      rcases entry with ⟨key, value⟩
      by_cases same : key = name
      · subst key
        simp [removeParameter, inductionHypothesis]
      · simp [removeParameter, same, inductionHypothesis]

def localValue (bound : List TypeExpr) (pattern : Pattern) : ContextualValue where
  dependencies := []
  ambient := bound.length
  body := pattern

def bindParameter (parameter : String) (value : ContextualValue)
    (assignment : Assignment) : Assignment :=
  (parameter, value) :: removeParameter parameter assignment

@[simp] theorem lookup_bind_parameter (assignment : Assignment) (parameter : String)
    (value : ContextualValue) :
    lookup (bindParameter parameter value assignment) parameter = some value := by
  simp only [bindParameter, lookup_cons, beq_self_eq_true, ite_true]

theorem lookup_bind_other (assignment : Assignment) (parameter name : String)
    (value : ContextualValue) (different : name ≠ parameter) :
    lookup (bindParameter parameter value assignment) name = lookup assignment name := by
  simp only [bindParameter, lookup_cons]
  simp only [show (parameter == name) = false from by simp [Ne.symm different],
    Bool.false_eq_true, if_false]
  exact lookup_remove_other assignment parameter name different

/-- Restore the outer first-match value, without discarding body outputs at
other names. An absent outer parameter remains absent. -/
def restoreParameter (parameter : String) (initial final : Assignment) : Assignment :=
  match lookup initial parameter with
  | none => removeParameter parameter final
  | some value => (parameter, value) :: removeParameter parameter final

@[simp] theorem lookup_restore_parameter (initial final : Assignment) (parameter : String) :
    lookup (restoreParameter parameter initial final) parameter = lookup initial parameter := by
  cases found : lookup initial parameter with
  | none => simp only [restoreParameter, found, lookup_remove_parameter]
  | some value => simp only [restoreParameter, found, lookup_cons, beq_self_eq_true, ite_true]

theorem lookup_restore_other (initial final : Assignment) (parameter name : String)
    (different : name ≠ parameter) :
    lookup (restoreParameter parameter initial final) name = lookup final name := by
  cases found : lookup initial parameter with
  | none =>
      simpa [restoreParameter, found] using
        lookup_remove_other final parameter name different
  | some value =>
      simpa [restoreParameter, found, bindParameter] using
        lookup_bind_other final parameter name value different

theorem restored_extension (initial final : Assignment) (parameter : String)
    (value : ContextualValue)
    (preserved : Extension (bindParameter parameter value initial) final) :
    Extension initial (restoreParameter parameter initial final) := by
  intro name stored found
  by_cases same : name = parameter
  · subst name
    simpa using found
  · rw [lookup_restore_other initial final parameter name same]
    apply preserved name stored
    rw [lookup_bind_other initial parameter name value same]
    exact found

/-- A freshness name is either the literal unbound atom or the instantiated
name stored in the assignment. A non-name value is rejected. -/
def freshnessName? (ambient : Nat) (assignment : Assignment) (name : String) : Option String :=
  match lookup assignment name with
  | none => some name
  | some value =>
      match instantiateValue? value ambient 0 [] with
      | some (.fvar atom) => some atom
      | _ => none

def freshnessSubject? (rule : RewriteRule) (spec : RuleBindingSpec)
    (bound : List TypeExpr) (premiseIndex quantifierDepth : Nat)
    (assignment : Assignment) (condition : FreshnessCondition) : Option (String × Pattern) := do
  let atom ← freshnessName? bound.length assignment condition.varName
  let subject ← instantiateAt? rule spec bound.length
    (.premise premiseIndex quantifierDepth 0) [] 0 assignment condition.term
  some (atom, subject)

/-- The independent syntactic predicate explicitly names the free atoms.
It makes no claim about a quotient without a separate invariance theorem. -/
def SyntacticallyFresh (atom : String) (subject : Pattern) : Prop :=
  atom ∉ Substitution.freeVars subject

theorem syntactic_freshness_iff (atom : String) (subject : Pattern) :
    Substitution.isFresh atom subject = true ↔ SyntacticallyFresh atom subject := by
  simp [Substitution.isFresh, SyntacticallyFresh]

/-- Read the shape of a finite, concrete collection. An unresolved rest is
refused, rather than interpreted as an empty list. -/
def concreteCollection? : Pattern → Option (CollType × List Pattern)
  | .collection kind elements none => some (kind, elements)
  | _ => none

/-- Contextual projection earns the actual body before collection shape
checking. Missing or incorrectly scoped values do not denote an empty list. -/
def finiteCollection? (ambient : Nat) (assignment : Assignment) (name : String) :
    Option (CollType × List Pattern) := do
  let value ← lookup assignment name
  let pattern ← instantiateValue? value ambient 0 []
  concreteCollection? pattern

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
