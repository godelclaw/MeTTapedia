import Mettapedia.Languages.MeTTa.HE.RecursiveDataExecution
import Mettapedia.Languages.MeTTa.HE.Correctness

/-!
# Retained execution and the recursive evaluator's declarative judgments

Completed retained runs construct the existing declarative evaluation evidence
for all six entry points. Ordered executable correspondence is stronger than
membership evidence alone. These judgments retain their computable matching
and typing leaves; they do not establish the separate executable-independent
language specification or general native-runtime refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks RecursiveMachine RecursiveExecution

theorem completed_atom_sound (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel budget : Nat)
    (events : ResultSet) (final : Configuration) (result : ResultPair)
    (completed : (machine dispatch).run budget
      (Configuration.initial space (.atom value expected bindings fuel)) = (events, .finished final))
    (observed : result ∈ events) : EvalAtom space dispatch value expected bindings result := by
  have ordered := (finished_results space dispatch (.atom value expected bindings fuel)
    budget events final completed).1
  rw [ordered] at observed
  exact evalAtom_sound space dispatch value expected bindings fuel result observed

theorem completed_expression_sound (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel budget : Nat)
    (events : ResultSet) (final : Configuration) (result : ResultPair)
    (completed : (machine dispatch).run budget
      (Configuration.initial space (.expression value expected bindings fuel)) = (events, .finished final))
    (observed : result ∈ events) : InterpretExpression space dispatch value expected bindings result := by
  have ordered := (finished_results space dispatch (.expression value expected bindings fuel)
    budget events final completed).1
  rw [ordered] at observed
  exact interpretExpression_sound space dispatch value expected bindings fuel result observed

theorem completed_function_sound (space : Space) (dispatch : GroundedDispatch)
    (value operatorType : Atom) (bindings : Bindings) (fuel budget : Nat)
    (events : ResultSet) (final : Configuration) (result : ResultPair)
    (completed : (machine dispatch).run budget
      (Configuration.initial space (.func value operatorType bindings fuel)) = (events, .finished final))
    (observed : result ∈ events) :
    ∀ expected, InterpretFunction space dispatch value operatorType expected bindings result := by
  have ordered := (finished_results space dispatch (.func value operatorType bindings fuel)
    budget events final completed).1
  rw [ordered] at observed
  exact interpretFunction_sound space dispatch value operatorType bindings fuel result observed

theorem completed_arguments_sound (space : Space) (dispatch : GroundedDispatch)
    (values types : List Atom) (bindings : Bindings) (fuel budget : Nat)
    (events : ResultSet) (final : Configuration) (result : ResultPair)
    (completed : (machine dispatch).run budget
      (Configuration.initial space (.args values types bindings fuel)) = (events, .finished final))
    (observed : result ∈ events) : InterpretArgs space dispatch values types bindings result := by
  have ordered := (finished_results space dispatch (.args values types bindings fuel)
    budget events final completed).1
  rw [ordered] at observed
  exact interpretArgs_sound space dispatch values types bindings fuel result observed

theorem completed_tuple_sound (space : Space) (dispatch : GroundedDispatch)
    (value : Atom) (bindings : Bindings) (fuel budget : Nat)
    (events : ResultSet) (final : Configuration) (result : ResultPair)
    (completed : (machine dispatch).run budget
      (Configuration.initial space (.tuple value bindings fuel)) = (events, .finished final))
    (observed : result ∈ events) : InterpretTuple space dispatch value bindings result := by
  have ordered := (finished_results space dispatch (.tuple value bindings fuel)
    budget events final completed).1
  rw [ordered] at observed
  exact interpretTuple_sound space dispatch value bindings fuel result observed

theorem completed_call_sound (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (fuel budget : Nat)
    (events : ResultSet) (final : Configuration) (result : ResultPair)
    (completed : (machine dispatch).run budget
      (Configuration.initial space (.call value expected bindings fuel)) = (events, .finished final))
    (observed : result ∈ events) : MettaCall space dispatch value expected bindings result := by
  have ordered := (finished_results space dispatch (.call value expected bindings fuel)
    budget events final completed).1
  rw [ordered] at observed
  exact mettaCall_sound space dispatch value expected bindings fuel result observed

end Mettapedia.Languages.MeTTa.HE.RecursiveSemanticSoundness
