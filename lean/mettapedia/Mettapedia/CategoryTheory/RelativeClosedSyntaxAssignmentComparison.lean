import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretation

/-!
# Extensional comparison of independently supplied declaration meanings

The actual base functor, fresh object values and complete arrow values
determine the assignment. No realization or global expression agreement
is supplied as an extra comparison field.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.Assignment

open _root_.CategoryTheory

universe u v a w z
variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D]

theorem equal_of_components {first second : Assignment C symbols D}
    (base : first.base = second.base) (objects : first.object = second.object)
    (arrows : first.arrow = second.arrow) : first = second := by
  cases first
  cases second
  cases base
  cases objects
  cases arrows
  rfl

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.Assignment
