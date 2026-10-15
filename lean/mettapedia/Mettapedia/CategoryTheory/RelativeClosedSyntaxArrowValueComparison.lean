import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretation

/-!
# Complete arrow values through independently read endpoints

Equality of both endpoint objects and the transported entire arrow earns
equality of complete dependent arrow values. Equality of a selected output
alone is not an input to this comparison.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.ArrowValue

open _root_.CategoryTheory

universe u v
variable {D : Type u} [Category.{v} D]

theorem eq_of_cast {before after first second : D}
    (input : before = first) (output : after = second)
    (old : before ⟶ after) (next : first ⟶ second)
    (carried : eqToHom input.symm ≫ old ≫ eqToHom output = next) :
    (⟨before, after, old⟩ : ArrowValue D) = ⟨first, second, next⟩ := by
  subst first
  subst second
  have same : old = next := by
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using carried
  exact congrArg (fun arrow => (⟨before, after, arrow⟩ : ArrowValue D)) same

end Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.ArrowValue
