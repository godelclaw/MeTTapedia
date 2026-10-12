import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneSyntax
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementBinderSubstitution

/-!
# Capture-avoiding transport of native monotone operator formulas

The full operator type, checked monotonicity proposition and emitted
fixed-point formulas commute with the existing raw substitution and renaming
operations, including every predicate and argument binder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneSyntaxTransport

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open FixedPointSyntax (predicateType application)
open NativeMonotoneSyntax

universe v
variable {S : Symbols.{v}} {n m : Nat}

theorem predicateType_substitution (domain : TypeExpr S n) (substitution : Substitution S n m) :
    (predicateType domain).substitute substitution = predicateType (domain.substitute substitution) := rfl

theorem operatorType_substitution (domain : TypeExpr S n) (substitution : Substitution S n m) :
    (operatorType domain).substitute substitution = operatorType (domain.substitute substitution) := by
  simp only [operatorType, TypeExpr.substitute, predicateType_substitution, TypeExpr.substitute_weaken]

theorem applyOperator_substitution (domain : TypeExpr S n) (operator candidate : TermExpr S n)
    (substitution : Substitution S n m) :
    (applyOperator domain operator candidate).substitute substitution =
      applyOperator (domain.substitute substitution) (operator.substitute substitution) (candidate.substitute substitution) := by
  simp only [applyOperator, TermExpr.substitute, predicateType_substitution, TypeExpr.substitute_weaken]

theorem application_substitution (domain : TypeExpr S n) (function argument : TermExpr S n)
    (substitution : Substitution S n m) :
    (application domain function argument).substitute substitution =
      application (domain.substitute substitution) (function.substitute substitution) (argument.substitute substitution) := rfl

theorem inclusion_substitution (domain : TypeExpr S n) (first second : TermExpr S n)
    (substitution : Substitution S n m) :
    (inclusion domain first second).substitute substitution =
      inclusion (domain.substitute substitution) (first.substitute substitution) (second.substitute substitution) := by
  simp only [inclusion, PropExpr.substitute, application_substitution, TypeExpr.substitute_weaken,
    TermExpr.substitute_weaken, TermExpr.substitute, liftSubstitution_zero]

theorem monotonicityAt_substitution (domain : TypeExpr S n) (operator first second : TermExpr S n)
    (substitution : Substitution S n m) :
    (monotonicityAt domain operator first second).substitute substitution =
      monotonicityAt (domain.substitute substitution) (operator.substitute substitution)
        (first.substitute substitution) (second.substitute substitution) := by
  simp only [monotonicityAt, PropExpr.substitute, inclusion_substitution, applyOperator_substitution]

theorem monotonicityUnderPredicate_substitution (domain : TypeExpr S n) (operator : TermExpr S n)
    (substitution : Substitution S n m) :
    (monotonicityUnderPredicate domain operator).substitute (liftSubstitution substitution) =
      monotonicityUnderPredicate (domain.substitute substitution) (operator.substitute substitution) := by
  simp only [monotonicityUnderPredicate, PropExpr.substitute, predicateType_substitution,
    TypeExpr.substitute_weaken, TermExpr.substitute_weaken, monotonicityAt_substitution,
    TermExpr.substitute, liftSubstitution_zero]
  rfl

theorem monotonicity_substitution (domain : TypeExpr S n) (operator : TermExpr S n)
    (substitution : Substitution S n m) :
    (monotonicity domain operator).substitute substitution =
      monotonicity (domain.substitute substitution) (operator.substitute substitution) := by
  simp only [monotonicity, PropExpr.substitute, predicateType_substitution,
    monotonicityUnderPredicate_substitution]

theorem prefixed_substitution (domain : TypeExpr S n) (operator : TermExpr S n)
    (substitution : Substitution S n m) :
    (prefixed domain operator).substitute (liftSubstitution substitution) =
      prefixed (domain.substitute substitution) (operator.substitute substitution) := by
  simp only [prefixed, inclusion_substitution, applyOperator_substitution,
    TypeExpr.substitute_weaken, TermExpr.substitute_weaken, TermExpr.substitute, liftSubstitution_zero]

theorem postfixed_substitution (domain : TypeExpr S n) (operator : TermExpr S n)
    (substitution : Substitution S n m) :
    (postfixed domain operator).substitute (liftSubstitution substitution) =
      postfixed (domain.substitute substitution) (operator.substitute substitution) := by
  simp only [postfixed, inclusion_substitution, applyOperator_substitution,
    TypeExpr.substitute_weaken, TermExpr.substitute_weaken, TermExpr.substitute, liftSubstitution_zero]

theorem least_substitution (domain : TypeExpr S n) (operator tested : TermExpr S n)
    (substitution : Substitution S n m) :
    (least domain operator tested).substitute substitution =
      least (domain.substitute substitution) (operator.substitute substitution) (tested.substitute substitution) := by
  simp only [least, PropExpr.substitute, predicateType_substitution, prefixed_substitution,
    application_substitution, TypeExpr.substitute_weaken, TermExpr.substitute_weaken,
    TermExpr.substitute, liftSubstitution_zero]

theorem greatest_substitution (domain : TypeExpr S n) (operator tested : TermExpr S n)
    (substitution : Substitution S n m) :
    (greatest domain operator tested).substitute substitution =
      greatest (domain.substitute substitution) (operator.substitute substitution) (tested.substitute substitution) := by
  simp only [greatest, PropExpr.substitute, predicateType_substitution, postfixed_substitution,
    application_substitution, TypeExpr.substitute_weaken, TermExpr.substitute_weaken,
    TermExpr.substitute, liftSubstitution_zero]

theorem operatorType_rename (domain : TypeExpr S n) (mapping : Renaming n m) :
    (operatorType domain).rename mapping = operatorType (domain.rename mapping) := by
  simpa only [TypeExpr.substitute_variables] using
    operatorType_substitution domain (fun index => .var (mapping index))

theorem monotonicity_rename (domain : TypeExpr S n) (operator : TermExpr S n) (mapping : Renaming n m) :
    (monotonicity domain operator).rename mapping = monotonicity (domain.rename mapping) (operator.rename mapping) := by
  simpa only [TypeExpr.substitute_variables, TermExpr.substitute_variables, PropExpr.substitute_variables] using
    monotonicity_substitution domain operator (fun index => .var (mapping index))

theorem least_rename (domain : TypeExpr S n) (operator tested : TermExpr S n) (mapping : Renaming n m) :
    (least domain operator tested).rename mapping =
      least (domain.rename mapping) (operator.rename mapping) (tested.rename mapping) := by
  simpa only [TypeExpr.substitute_variables, TermExpr.substitute_variables, PropExpr.substitute_variables] using
    least_substitution domain operator tested (fun index => .var (mapping index))

theorem greatest_rename (domain : TypeExpr S n) (operator tested : TermExpr S n) (mapping : Renaming n m) :
    (greatest domain operator tested).rename mapping =
      greatest (domain.rename mapping) (operator.rename mapping) (tested.rename mapping) := by
  simpa only [TypeExpr.substitute_variables, TermExpr.substitute_variables, PropExpr.substitute_variables] using
    greatest_substitution domain operator tested (fun index => .var (mapping index))

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneSyntaxTransport
