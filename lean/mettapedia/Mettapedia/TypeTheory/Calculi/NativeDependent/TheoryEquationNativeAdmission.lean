import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryEquationSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison

/-!
# Native admission of independently declared theory equations

Admission compares the complete native expression outputs at the declared
mixed scopes. The earned native/abstract parser comparison then transports
that local condition to the arbitrary-model rule interpretation. No global
interpreter or equation-closure soundness is an admission field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations

open _root_.CategoryTheory

universe u
variable {C : Type u} [Category.{u} C] {S : Symbols.{u}}

namespace Declaration

def NativeAdmitted (model : ModelData S C) : Declaration S → Prop
  | .type context first second =>
      ∀ Γ, model.evaluateContext context = some Γ →
        model.evaluateType Γ first = model.evaluateType Γ second
  | .term context _ first second =>
      ∀ Γ, model.evaluateContext context = some Γ →
        model.evaluateTerm Γ first = model.evaluateTerm Γ second
  | .predicate context first second =>
      ∀ Γ, model.evaluateContext context = some Γ →
        model.evaluatePredicate Γ first = model.evaluatePredicate Γ second
  | .substitution source target first second =>
      ∀ Γ Δ, model.evaluateContext source = some Γ → model.evaluateContext target = some Δ →
        model.evaluateSubstitution Γ Δ first = model.evaluateSubstitution Γ Δ second

theorem toAbstract (model : ModelData S C) (declaration : Declaration S)
    (admitted : declaration.NativeAdmitted model) : declaration.Admitted model.toAbstract := by
  cases declaration with
  | type context first second =>
      intro Γ contextRead
      rw [model.evaluateContext_compare] at contextRead
      rcases Option.map_eq_some_iff.mp contextRead with ⟨native, nativeRead, rfl⟩
      rw [model.evaluateType_compare, model.evaluateType_compare]
      exact admitted native nativeRead
  | term context result first second =>
      intro Γ contextRead
      rw [model.evaluateContext_compare] at contextRead
      rcases Option.map_eq_some_iff.mp contextRead with ⟨native, nativeRead, rfl⟩
      rw [model.evaluateTerm_compare, model.evaluateTerm_compare]
      exact admitted native nativeRead
  | predicate context first second =>
      intro Γ contextRead
      rw [model.evaluateContext_compare] at contextRead
      rcases Option.map_eq_some_iff.mp contextRead with ⟨native, nativeRead, rfl⟩
      rw [model.evaluatePredicate_compare, model.evaluatePredicate_compare]
      exact admitted native nativeRead
  | substitution source target first second =>
      intro Γ Δ sourceRead targetRead
      rw [model.evaluateContext_compare] at sourceRead targetRead
      rcases Option.map_eq_some_iff.mp sourceRead with ⟨nativeSource, nativeSourceRead, rfl⟩
      rcases Option.map_eq_some_iff.mp targetRead with ⟨nativeTarget, nativeTargetRead, rfl⟩
      rw [model.evaluateSubstitution_compare, model.evaluateSubstitution_compare]
      exact admitted nativeSource nativeTarget nativeSourceRead nativeTargetRead

end Declaration

def NativeAdmitted (model : ModelData S C) (equations : Presentation S) : Prop :=
  ∀ origin, (equations.declaration origin).NativeAdmitted model

theorem nativeAdmission_toAbstract (model : ModelData S C) (equations : Presentation S)
    (admitted : NativeAdmitted model equations) : Admitted model.toAbstract equations :=
  fun origin => (equations.declaration origin).toAbstract model (admitted origin)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations
