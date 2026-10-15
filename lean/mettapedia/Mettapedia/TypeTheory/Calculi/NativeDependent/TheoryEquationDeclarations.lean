import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementJudgments
import Mettapedia.TypeTheory.JudgmentDerivationExtension

/-!
# Authored theory equations in the full native judgment grammar

An equation is an independent pair of scoped expressions. Its local premises
require both sides to be formed or typed at the same context and result.
Occurrences are indexed separately from their expressions, so identical
equations can retain different authored origins. The added rules do not
create an unformed context or introduce a new type former.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations

universe u

variable (S : Symbols.{u})

inductive Declaration : Type u where
  | type {n : Nat} (context : ContextExpr S n) (first second : TypeExpr S n)
  | term {n : Nat} (context : ContextExpr S n) (type : TypeExpr S n)
      (first second : TermExpr S n)
  | predicate {n : Nat} (context : ContextExpr S n) (first second : PropExpr S n)
  | substitution {n m : Nat} (source : ContextExpr S n) (target : ContextExpr S m)
      (first second : Substitution S m n)

namespace Declaration

variable {S}

def conclusion : Declaration S → Judgment S
  | .type context first second => .typeEq context first second
  | .term context result first second => .termEq context first second result
  | .predicate context first second => .predicateEq context first second
  | .substitution source target first second => .substitutionEq source target first second

def premises : Declaration S → List (Judgment S)
  | .type context first second => [.type context first, .type context second]
  | .term context result first second => [.term context first result, .term context second result]
  | .predicate context first second => [.predicate context first, .predicate context second]
  | .substitution source target first second =>
      [.substitution source target first, .substitution source target second]

@[simp] theorem premises_length (declaration : Declaration S) : declaration.premises.length = 2 := by
  cases declaration <;> rfl

end Declaration

/-- The index retains authored occurrences independently of equation content. -/
structure Presentation where
  Origin : Type u
  declaration : Origin → Declaration S

namespace Presentation

variable {S}

def extension (equations : Presentation S) (D : Signature S) :
    JudgmentDerivation.Extension (judgmentSignature D) where
  Rule judgment := {origin : equations.Origin // (equations.declaration origin).conclusion = judgment}
  Premise rule := ULift (Fin (equations.declaration rule.val).premises.length)
  hypothesis rule position := (equations.declaration rule.val).premises.get position.down

end Presentation

/-- Ordinary declarations and independently authored equation occurrences
are distinct inputs to the relative native theory. -/
structure Theory extends Signature S where
  equations : Presentation S

instance : Coe (Theory S) (Signature S) := ⟨Theory.toSignature⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations
