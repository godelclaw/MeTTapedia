import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SchemaTableConversionCode

/-!
# Constant expansion of retained schema instances

Expansion keeps the selected row and its permission witness. Each actual
argument is expanded by the existing capture-safe substitution law. The row's
literal constants must remain fixed; arbitrary constant expansion is not a
map of an unchanged rewrite presentation.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SchemaTableConversionCode
open AlgebraicSchema ConstantExpansion
variable {Head : Type} {table : SchemaTable Head} {enabled : Fin table.length → Bool}

theorem root_expand (bodies : Bodies Head)
    (fixed : ∀ index : Fin table.length,
      expand bodies (table.get index).2.1 = (table.get index).2.1 ∧
      expand bodies (table.get index).2.2 = (table.get index).2.2)
    {n : Nat} {left right : Tm Head n} (step : (root table enabled).step left right) :
    (root table enabled).step (expand bodies left) (expand bodies right) := by
  obtain ⟨evidence⟩ := step
  cases evidence with
  | instantiate index permitted substitution =>
    refine ⟨?_⟩
    have expanded := Evidence.instantiate index permitted (fun position => expand bodies (substitution position))
    simpa only [retained, expand_subst, (fixed index).1, (fixed index).2] using expanded

#print axioms root_expand
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SchemaTableConversionCode
