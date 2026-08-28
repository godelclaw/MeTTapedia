import KnuthSkilling.Core.TotalityImprecision

/-!
# Knuth–Skilling compatibility

The pinned public Knuth–Skilling revision uses the original `Faithful*` names
for order-reflecting point representations. MeTTapedia adopted the clearer
`OrderReflecting*` names before that external rename was published. These
aliases keep the public dependency reproducible without changing the
mathematics. Remove this module after updating the pin to a published revision
that provides the new names.
-/

namespace KnuthSkilling.TotalityImprecision

def OrderReflectingPointRepresentation (α : Type*) [PartialOrder α] : Prop :=
  ∃ Θ : α → ℝ, ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b

theorem totality_of_orderReflectingPointRepresentation {α : Type*} [PartialOrder α]
    (hΘ : OrderReflectingPointRepresentation α) :
    ∀ x y : α, x ≤ y ∨ y ≤ x := by
  apply totality_of_faithfulPointRepresentation
  simpa [OrderReflectingPointRepresentation, FaithfulPointRepresentation] using hΘ

theorem no_orderReflectingPointRepresentation_of_incomparable
    {α : Type*} [PartialOrder α]
    (hinc : ∃ x y : α, ¬ (x ≤ y) ∧ ¬ (y ≤ x)) :
    ¬ OrderReflectingPointRepresentation α := by
  intro hΘ
  apply no_faithfulPointRepresentation_of_incomparable hinc
  simpa [OrderReflectingPointRepresentation, FaithfulPointRepresentation] using hΘ

theorem no_orderReflectingPointRepresentation_with_incomparables
    {α : Type*} [PartialKnuthSkillingAlgebra α]
    (x y : α) (hxy : PartialKnuthSkillingAlgebra.Incomparable x y) :
    ¬ ∃ Θ : α → ℝ, ∀ a b : α, a ≤ b ↔ Θ a ≤ Θ b :=
  no_pointRepresentation_with_incomparables x y hxy

end KnuthSkilling.TotalityImprecision
