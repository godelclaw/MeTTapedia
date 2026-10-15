import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeFixedPointComparison

/-!
# Independent readout of emitted derived native fixed points

These are original evaluator equalities, through the shared higher-order
native grammar, to independently constructed least/greatest subfunctors.
Atomic declaration comparisons do not supply the bound predicate variable:
its application and both local quantifiers are derived by the evaluator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.FixedPointReadout

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open DisplayedPresheafComprehension NativeLocalTypeFormers

universe u v z
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {n : Nat} {Atom : Type z}

theorem evaluate_least_exact (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (atoms : Atom → PropExpr S (n + 1))
    (meanings : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (tested : TermExpr S n) (value : A.decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (atomRead : ∀ atom, model.evaluatePredicate (context.snoc A) (atoms atom) = some (meanings atom))
    (valueRead : model.evaluateTerm context tested = some ⟨A, value⟩) :
    model.evaluatePredicate context (FixedPointSyntax.least domain atoms body tested) =
      some ((Monotone.inductiveMeaning meanings body checked).preimage (sectionLift A.decoded value)) := by
  rw [FixedPointEvaluation.evaluate_least model context domain A atoms meanings body checked
    tested value domainRead atomRead valueRead,
    NativeFixedPointComparison.least_eq_meaning]

theorem evaluate_greatest_exact (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1)
    (atoms : Atom → PropExpr S (n + 1))
    (meanings : Atom → Subfunctor (totalSpace A.decoded))
    (body : Logic.Formula (Sum Atom Unit)) (checked : Monotone.variance true body = true)
    (tested : TermExpr S n) (value : A.decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (atomRead : ∀ atom, model.evaluatePredicate (context.snoc A) (atoms atom) = some (meanings atom))
    (valueRead : model.evaluateTerm context tested = some ⟨A, value⟩) :
    model.evaluatePredicate context (FixedPointSyntax.greatest domain atoms body tested) =
      some ((Monotone.coinductiveMeaning meanings body checked).preimage (sectionLift A.decoded value)) := by
  rw [FixedPointEvaluation.evaluate_greatest model context domain A atoms meanings body checked
    tested value domainRead atomRead valueRead,
    NativeFixedPointComparison.greatest_eq_meaning]

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.FixedPointReadout
