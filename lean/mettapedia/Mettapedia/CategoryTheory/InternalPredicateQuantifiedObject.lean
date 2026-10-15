import Mettapedia.CategoryTheory.InternalPredicateLogicalUniqueness

/-!
# Internal predicate objects with local quantifier diagrams

An object carries truth and conjunction with their four finite diagrams.
For each actual category arrow, two complete function-object arrows carry
the three local quantifier diagrams. These data derive the adjunctions in
every generalized context. The quantifier choices are determined by the
conjunctive object; no all-context adjunction or interpretation is a field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateQuantifiedObject

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalPredicateFunctionObject InternalPredicateQuantifier

universe u v
variable (C : Type u) [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C]

structure Operations where
  predicates : InternalConjunctiveObject.Operations C
  laws : predicates.Laws
  universal {source target : C} (arrow : source ⟶ target) : Universal predicates arrow
  existential {source target : C} (arrow : source ⟶ target) :
    InternalPredicateExistential.Existential predicates arrow

namespace Operations

variable {C} (operations : Operations C)
variable {source target : C} (arrow : source ⟶ target)

theorem universal_galois (context : C) :
    letI : SemilatticeInf (context ⟶ power operations.predicates target) :=
      (functions operations.predicates target).semilattice
        (functionLaws operations.predicates operations.laws target) context
    letI : SemilatticeInf (context ⟶ power operations.predicates source) :=
      (functions operations.predicates source).semilattice
        (functionLaws operations.predicates operations.laws source) context
    GaloisConnection
      (fun predicate : context ⟶ power operations.predicates target =>
        predicate ≫ precomposition operations.predicates arrow)
      (fun predicate : context ⟶ power operations.predicates source =>
        predicate ≫ (operations.universal arrow).operation) :=
  Universal.adjunction operations.predicates operations.laws arrow
    (operations.universal arrow) context

theorem existential_galois (context : C) :
    letI : SemilatticeInf (context ⟶ power operations.predicates source) :=
      (functions operations.predicates source).semilattice
        (functionLaws operations.predicates operations.laws source) context
    letI : SemilatticeInf (context ⟶ power operations.predicates target) :=
      (functions operations.predicates target).semilattice
        (functionLaws operations.predicates operations.laws target) context
    GaloisConnection
      (fun predicate : context ⟶ power operations.predicates source =>
        predicate ≫ (operations.existential arrow).operation)
      (fun predicate : context ⟶ power operations.predicates target =>
        predicate ≫ precomposition operations.predicates arrow) :=
  InternalPredicateExistential.Existential.adjunction operations.predicates
    operations.laws arrow (operations.existential arrow) context

theorem universal_unique (candidate : Universal operations.predicates arrow) :
    candidate.operation = (operations.universal arrow).operation :=
  InternalPredicateLogicalUniqueness.universal_operation_unique
    operations.predicates operations.laws arrow candidate (operations.universal arrow)

theorem existential_unique
    (candidate : InternalPredicateExistential.Existential operations.predicates arrow) :
    candidate.operation = (operations.existential arrow).operation :=
  InternalPredicateLogicalUniqueness.existential_operation_unique
    operations.predicates operations.laws arrow candidate (operations.existential arrow)

/-- Equality of the complete conjunctive data determines every quantifier,
including its function arrow, by the independently earned adjunctions. -/
theorem ext_of_predicates (first second : Operations C)
    (same : first.predicates = second.predicates) : first = second := by
  rcases first with ⟨firstPredicates, firstLaws, firstAll, firstSome⟩
  rcases second with ⟨secondPredicates, secondLaws, secondAll, secondSome⟩
  dsimp only at same
  subst secondPredicates
  have allEqual : @firstAll = @secondAll := by
    funext source target arrow
    exact (InternalPredicateLogicalUniqueness.universal_subsingleton
      firstPredicates firstLaws arrow).allEq _ _
  have someEqual : @firstSome = @secondSome := by
    funext source target arrow
    exact (InternalPredicateLogicalUniqueness.existential_subsingleton
      firstPredicates firstLaws arrow).allEq _ _
  subst secondAll secondSome
  rfl

end Operations

end Mettapedia.CategoryTheory.InternalPredicateQuantifiedObject
