import Mettapedia.OSLF.Framework.RhoGeneratedScopeDecision
import Mettapedia.OSLF.Framework.RhoScopeGeneratorInterpretation

/-!
# Authored and native readings of the complete generated-scope guard

The two-part authored expression and the existing substitution-stable native
predicate are independently interpreted. Their established comparisons now
make the terminating guard a decision of those actual readings. Positive
answers transport whenever the atomic premises transport. Negative answers
are not asserted to remain negative under arbitrary future substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoGeneratedScopeDecisionInterpretation

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingSubstitutionAlgebra BindingConstructorPredicates
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution RhoGeneratedScopeDecision

universe u

theorem guard_authored_reading {Atom : Type u} {context : Ctx sig}
    (atoms : Atom → Process context → Prop) (left right : Atom)
    [DecidablePred (atoms left)] [DecidablePred (atoms right)]
    (env : RhoScopeExpression.Environment context) (name : Name context) :
    guard (atoms left) (atoms right) name = true ↔
      RhoScopeExpression.denote atoms (RhoScopeGeneratorInterpretation.generator left right) env name := by
  rw [RhoScopeGeneratorInterpretation.generator_denotation]
  exact guard_true_iff _ _ name

def authoredDecision {Atom : Type u} {context : Ctx sig}
    (atoms : Atom → Process context → Prop) (left right : Atom)
    [DecidablePred (atoms left)] [DecidablePred (atoms right)]
    (env : RhoScopeExpression.Environment context) (name : Name context) :
    Decidable (RhoScopeExpression.denote atoms
      (RhoScopeGeneratorInterpretation.generator left right) env name) := by
  letI := generatedDecision (atoms left) (atoms right) name
  exact decidable_of_iff _ (Iff.of_eq (congrFun
    (RhoScopeGeneratorInterpretation.generator_denotation atoms left right env) name)).symm

theorem guard_native_reading (left right : Predicate model Srt.pr)
    {context : Ctx sig} [DecidablePred (left.holds (Γ := context))]
    [DecidablePred (right.holds (Γ := context))] (name : Name context) :
    guard left.holds right.holds name = true ↔ (native left right).holds name :=
  guard_true_iff _ _ name

theorem accepted_guard_substitutes {source target : Ctx sig}
    (left right : Process source → Prop) (left' right' : Process target → Prop)
    [DecidablePred left] [DecidablePred right] [DecidablePred left'] [DecidablePred right']
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process))
    (name : Name source) (accepted : guard left right name = true) :
    guard left' right' (model.substitution.substitute env name) = true :=
  (guard_true_iff _ _ _).mpr (generated_substitute env leftMap rightMap
    ((guard_true_iff _ _ name).mp accepted))

theorem rejected_future_guard_excludes_current {source target : Ctx sig}
    (left right : Process source → Prop) (left' right' : Process target → Prop)
    [DecidablePred left] [DecidablePred right] [DecidablePred left'] [DecidablePred right']
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process))
    (name : Name source) (rejected : guard left' right'
      (model.substitution.substitute env name) = false) : guard left right name = false := by
  apply (guard_false_iff _ _ name).mpr
  intro member
  exact (guard_false_iff _ _ _).mp rejected (generated_substitute env leftMap rightMap member)

end Mettapedia.OSLF.Framework.RhoGeneratedScopeDecisionInterpretation
