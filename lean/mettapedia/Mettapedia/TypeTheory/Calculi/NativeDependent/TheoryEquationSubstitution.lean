import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryEquationDerivations

/-!
# Typed propagation of authored theory equations

The original native substitution rules now consume supplied trees containing
added theory equations. Type, term and predicate equations consequently act
under every admitted substitution, including data and satisfying-assumption
binders. The construction retains the rule occurrences and ordered premises;
it does not select a tree from a proof-irrelevant derivability assertion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations

universe u
variable {S : Symbols.{u}} {D : Signature S} {equations : Presentation S}

def typeSubstitute {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {type : TypeExpr S m}
    (arrow : Derivation D equations (.substitution source target substitution))
    (family : Derivation D equations (.type target type)) :
    Derivation D equations (.type source (type.substitute substitution)) :=
  deriveWith (.substituteType source target substitution type) ⟨arrow, family, ⟨⟩⟩

def termSubstitute {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {term : TermExpr S m} {type : TypeExpr S m}
    (arrow : Derivation D equations (.substitution source target substitution))
    (value : Derivation D equations (.term target term type)) :
    Derivation D equations (.term source (term.substitute substitution) (type.substitute substitution)) :=
  deriveWith (.substituteTerm source target substitution term type) ⟨arrow, value, ⟨⟩⟩

def predicateSubstitute {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {predicate : PropExpr S m}
    (arrow : Derivation D equations (.substitution source target substitution))
    (guard : Derivation D equations (.predicate target predicate)) :
    Derivation D equations (.predicate source (predicate.substitute substitution)) :=
  deriveWith (.substitutePredicate source target substitution predicate) ⟨arrow, guard, ⟨⟩⟩

def entailsSubstitute {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {predicate : PropExpr S m}
    (arrow : Derivation D equations (.substitution source target substitution))
    (guard : Derivation D equations (.entails target predicate)) :
    Derivation D equations (.entails source (predicate.substitute substitution)) :=
  deriveWith (.substituteEntailment source target substitution predicate) ⟨arrow, guard, ⟨⟩⟩

def typeEqualitySubstitute {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {first second : TypeExpr S m}
    (arrow : Derivation D equations (.substitution source target substitution))
    (equality : Derivation D equations (.typeEq target first second)) :
    Derivation D equations (.typeEq source
      (first.substitute substitution) (second.substitute substitution)) :=
  deriveWith (.substituteTypeEquality source target substitution first second) ⟨arrow, equality, ⟨⟩⟩

def termEqualitySubstitute {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {first second : TermExpr S m} {type : TypeExpr S m}
    (arrow : Derivation D equations (.substitution source target substitution))
    (equality : Derivation D equations (.termEq target first second type)) :
    Derivation D equations (.termEq source
      (first.substitute substitution) (second.substitute substitution) (type.substitute substitution)) :=
  deriveWith (.substituteTermEquality source target substitution first second type)
    ⟨arrow, equality, ⟨⟩⟩

def predicateEqualitySubstitute {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {first second : PropExpr S m}
    (arrow : Derivation D equations (.substitution source target substitution))
    (equality : Derivation D equations (.predicateEq target first second)) :
    Derivation D equations (.predicateEq source
      (first.substitute substitution) (second.substitute substitution)) :=
  deriveWith (.substitutePredicateEquality source target substitution first second)
    ⟨arrow, equality, ⟨⟩⟩

def typeSubstitutionCongruence {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {first second : Substitution S m n} {type : TypeExpr S m}
    (equality : Derivation D equations (.substitutionEq source target first second))
    (family : Derivation D equations (.type target type)) :
    Derivation D equations (.typeEq source (type.substitute first) (type.substitute second)) :=
  deriveWith (.typeSubstitutionCongruence source target first second type) ⟨equality, family, ⟨⟩⟩

def termSubstitutionCongruence {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {first second : Substitution S m n} {term : TermExpr S m} {type : TypeExpr S m}
    (equality : Derivation D equations (.substitutionEq source target first second))
    (value : Derivation D equations (.term target term type)) :
    Derivation D equations (.termEq source
      (term.substitute first) (term.substitute second) (type.substitute first)) :=
  deriveWith (.termSubstitutionCongruence source target first second term type) ⟨equality, value, ⟨⟩⟩

def predicateSubstitutionCongruence {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {first second : Substitution S m n} {predicate : PropExpr S m}
    (equality : Derivation D equations (.substitutionEq source target first second))
    (guard : Derivation D equations (.predicate target predicate)) :
    Derivation D equations (.predicateEq source
      (predicate.substitute first) (predicate.substitute second)) :=
  deriveWith (.predicateSubstitutionCongruence source target first second predicate) ⟨equality, guard, ⟨⟩⟩

def lift {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {type : TypeExpr S m}
    (arrow : Derivation D equations (.substitution source target substitution))
    (family : Derivation D equations (.type target type)) :
    Derivation D equations (.substitution (.snoc source (type.substitute substitution))
      (.snoc target type) (liftSubstitution substitution)) :=
  deriveWith (.substitutionLift source target type substitution) ⟨arrow, family, ⟨⟩⟩

def liftAssumption {n m : Nat} {source : ContextExpr S n} {target : ContextExpr S m}
    {substitution : Substitution S m n} {predicate : PropExpr S m}
    (arrow : Derivation D equations (.substitution source target substitution))
    (guard : Derivation D equations (.predicate target predicate)) :
    Derivation D equations (.substitution (.assume source (predicate.substitute substitution))
      (.assume target predicate) substitution) :=
  deriveWith (.substitutionAssumptionLift source target predicate substitution) ⟨arrow, guard, ⟨⟩⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations
