import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSubstitutionInterpretation

/-! # Relabelling the length of a native context preserves its actual space -/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open ContextualModelTelescopes

universe u v
variable {W : Type u} [Category.{u} W] {S : Symbols.{v}}

namespace Scope

/-- Change only the telescope's length index; retain the presheaf verbatim. -/
def resize {n m : Nat} (same : n = m) (scope : Scope W n) : Scope W m :=
  ⟨scope.1, cast (congrArg (fun length => ScopeData W length scope.1) same) scope.2⟩

@[simp] theorem resize_base {n m : Nat} (same : n = m) (scope : Scope W n) :
    (resize same scope).1 = scope.1 := rfl

@[simp] theorem resize_refl {n : Nat} (scope : Scope W n) : resize rfl scope = scope := rfl

end Scope

namespace ModelData

variable (model : ModelData S W)

theorem evaluateContext_resize {n m : Nat} (same : n = m) (context : ContextExpr S n) :
    model.evaluateContext (cast (congrArg (ContextExpr S) same) context) =
      (model.evaluateContext context).map (Scope.resize same) := by
  cases same
  change model.evaluateContext context = (model.evaluateContext context).map (Scope.resize rfl)
  cases model.evaluateContext context <;> rfl

theorem evaluateSubstitution_resize_target {n m k : Nat} (same : n = m)
    (source : Scope W k) (target : Scope W n) (mapping : Substitution S n k) :
    model.evaluateSubstitution source (Scope.resize same target)
      (fun position => mapping (Fin.cast same.symm position)) =
      model.evaluateSubstitution source target mapping := by
  cases same
  rfl


theorem evaluateTerm_resize_source {n m : Nat} (same : n = m)
    (source : Scope W n) (term : TermExpr S n) :
    model.evaluateTerm (Scope.resize same source)
      (cast (congrArg (TermExpr S) same) term) = model.evaluateTerm source term := by
  cases same
  rfl

theorem evaluateSubstitution_resize_source {n m k : Nat} (same : n = m)
    (source : Scope W n) (target : Scope W k) (mapping : Substitution S k n) :
    model.evaluateSubstitution (Scope.resize same source) target
      (fun position => cast (congrArg (TermExpr S) same) (mapping position)) =
      model.evaluateSubstitution source target mapping := by
  cases same
  rfl

theorem evaluateSubstitution_source_eq {n k : Nat} (source changed : Scope W n)
    (target : Scope W k) (same : source = changed) (mapping : Substitution S k n)
    (arrow : source.1 ⟶ target.1)
    (evaluated : model.evaluateSubstitution source target mapping = some arrow) :
    model.evaluateSubstitution changed target mapping =
      some (eqToHom (congrArg (fun scope : Scope W n => scope.1) same.symm) ≫ arrow) := by
  cases same
  simpa only [eqToHom_refl, Category.id_comp] using evaluated

theorem evaluateSubstitution_target_eq {n k : Nat} (source : Scope W n)
    (target changed : Scope W k) (same : target = changed) (mapping : Substitution S k n)
    (arrow : source.1 ⟶ target.1)
    (evaluated : model.evaluateSubstitution source target mapping = some arrow) :
    model.evaluateSubstitution source changed mapping =
      some (arrow ≫ eqToHom (congrArg (fun scope : Scope W k => scope.1) same)) := by
  cases same
  simpa only [eqToHom_refl, Category.comp_id] using evaluated

end ModelData
end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
