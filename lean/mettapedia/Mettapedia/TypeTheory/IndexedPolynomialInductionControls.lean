import Mettapedia.TypeTheory.IndexedPolynomialInduction
import Mettapedia.TypeTheory.InductionRecursionBoundary

/-!
# Controls for generic dependent polynomial induction

The vector control computes a value in an index-dependent finite type. A
method-preserving fibre map compares it with an ordinary length computation.
The negative control interprets the list constructors in a two-cycle: methods
still exist, but no section can satisfy their height equations. Thus section
existence is a property of the initial family, not of every algebra.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.InductionControls

namespace Vectors

open VectorExample

universe u

/-- The length is computed into its dependent bounded type. -/
def boundedLength {A : Type u} :
    Algebra.Displayed (Algebra.initial (polynomial A))
      (fun _ length _ => Fin (length + 1)) where
  act := by
    intro base index shape children hypotheses
    cases shape with
    | nil => exact ⟨0, Nat.zero_lt_succ 0⟩
    | cons length head =>
        exact ⟨(hypotheses .star).val + 1,
          Nat.succ_lt_succ (hypotheses .star).isLt⟩

def unboundedLength {A : Type u} :
    Algebra.Displayed (Algebra.initial (polynomial A))
      (fun _ _ _ => Nat) where
  act := by
    intro base index shape children hypotheses
    cases shape with
    | nil => exact 0
    | cons length head => exact hypotheses .star + 1

/-- Forgetting the bound before or after dependent elimination agrees. -/
theorem boundedLength_agrees {A : Type u} {length : Nat}
    (vector : VectorP A length) :
    (boundedLength.initialSection.toFun .star length vector).val =
      unboundedLength.initialSection.toFun .star length vector := by
  apply Algebra.Displayed.initialSection_naturality boundedLength unboundedLength
    (fun _ _ _ value => value.val)
  intro base index shape children hypotheses
  cases shape <;> rfl

/-- Every constructor contributes exactly one to the index-dependent result. -/
theorem boundedLength_value {A : Type u} {length : Nat}
    (vector : VectorP A length) :
    (boundedLength.initialSection.toFun .star length vector).val = length := by
  refine VectorExample.eliminate (A := A)
    (fun length vector =>
      (boundedLength.initialSection.toFun .star length vector).val = length)
    ?_ ?_ length vector
  · rfl
  · intro length head tail hypothesis
    change (boundedLength.initialSection.toFun .star length tail).val + 1 = length + 1
    rw [hypothesis]

theorem two_elements_compute (first second : Nat) :
    boundedLength.initialSection.toFun .star 2
      (cons first (cons second nil)) = (⟨2, by decide⟩ : Fin 3) := rfl

end Vectors

namespace NonInitial

open ListExample

/-- List constructors interpreted as false and Boolean negation. -/
def cyclic : Algebra (polynomial Unit) (fun _ _ => Bool) where
  act := by
    intro base index layer
    rcases layer with ⟨shape, children⟩
    cases shape with
    | nil => exact false
    | cons head => exact Bool.not (children .star)

/-- The displayed methods request a height that increments at every cons. -/
def height : Algebra.Displayed cyclic (fun _ _ _ => Nat) where
  act := fun _ _ shape _children hypotheses =>
    match shape with
    | .nil => 0
    | .cons _ => hypotheses .star + 1

/-- Predicate induction for the two-state algebra is real. -/
theorem predicate_induction :
    InductionRecursionBoundary.PredicateInduction false Bool.not :=
  InductionRecursionBoundary.boolean_induction

/-- Predicate induction does not supply the displayed section: its requested
computation equations are incompatible with the algebra's two-cycle. -/
theorem no_height_section : ¬ Nonempty height.Section := by
  rintro ⟨chosen⟩
  apply InductionRecursionBoundary.boolean_induction_does_not_admit_height
  refine ⟨chosen.toFun .star .star, ?_, ?_⟩
  · exact chosen.commutes .star .star .nil (fun position => nomatch position)
  · intro value
    exact chosen.commutes .star .star (.cons ()) (fun _ => value)

end NonInitial

#print axioms Vectors.boundedLength_agrees
#print axioms Vectors.boundedLength_value
#print axioms Vectors.two_elements_compute
#print axioms NonInitial.no_height_section

end Mettapedia.TypeTheory.IndexedPolynomial.InductionControls
