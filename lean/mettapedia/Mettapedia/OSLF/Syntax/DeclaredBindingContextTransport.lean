import Mettapedia.OSLF.Syntax.DeclaredBindingInterpretation
import Mettapedia.GSLT.LanguageDef.MultiSortedCloneOperationPresheaf

/-!
# Coherent contextual transport for the declared binding interpretation

The constructed interpretation is a translation of the established clones,
not a strict map sending each source operator to one target operator.
It induces the established finite-product context functor. Target model
morphisms act on the derived source model, so interpretation, further model
transport and simultaneous substitution form commuting squares.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Binding.DeclaredBindingInterpretation

open CategoryTheory FreeBindingTerms BindingCloneFoldSubstitution
open Mettapedia.GSLT.LanguageDef

universe u v w

/-- A target-model morphism preserves the constructed derived operations,
including the abstraction/application composite denoting `where`. -/
def modelHom {A : BindingCloneAlgebra.Algebra.{u} Target.sig}
    {B : BindingCloneAlgebra.Algebra.{v} Target.sig}
    (h : FreeBindingClone.Hom A B) : FreeBindingClone.Hom (model A) (model B) where
  raw :=
    { map := h.raw.map
      map_variable := h.raw.map_variable
      map_operation := by
        intro Γ s op args
        cases op with
        | baseApp =>
            simp only [model, BindingCloneAlgebra.Algebra.toRaw, operation,
              argumentHead_map, argumentTail_map]
            exact h.raw.map_operation .app
              (.cons (argumentHead args) (.cons (argumentHead (argumentTail args)) .nil))
        | baseLam =>
            simp only [model, BindingCloneAlgebra.Algebra.toRaw, operation, argumentHead_map]
            exact h.raw.map_operation .lam (.cons (argumentHead args) .nil)
        | lambda =>
            simp only [model, BindingCloneAlgebra.Algebra.toRaw, operation, argumentHead_map]
            exact h.raw.map_operation .lam (.cons (argumentHead args) .nil)
        | whereBinding =>
            simp only [model, BindingCloneAlgebra.Algebra.toRaw, operation,
              argumentHead_map, argumentTail_map]
            have appLaw := h.raw.map_operation .app
              (.cons (A.operation .lam (.cons (argumentHead (argumentTail args)) .nil))
                (.cons (argumentHead args) .nil))
            have lamLaw := h.raw.map_operation .lam (.cons (argumentHead (argumentTail args)) .nil)
            exact appLaw.trans (congrArg (fun body => B.operation .app
              (.cons body (.cons (h.raw.map (argumentHead args)) .nil))) lamLaw)
        | result =>
            simp only [model, BindingCloneAlgebra.Algebra.toRaw, operation, argumentHead_map] }

  map_substitute := h.map_substitute

theorem modelHom_identity (A : BindingCloneAlgebra.Algebra.{u} Target.sig) :
    modelHom (FreeBindingClone.Hom.id A) = FreeBindingClone.Hom.id (model A) := by
  apply FreeBindingClone.Hom.ext
  exact FreeBindingTerms.Hom.ext (fun _ => rfl)

theorem modelHom_composition {A : BindingCloneAlgebra.Algebra.{u} Target.sig}
    {B : BindingCloneAlgebra.Algebra.{v} Target.sig}
    {C : BindingCloneAlgebra.Algebra.{w} Target.sig}
    (first : FreeBindingClone.Hom A B) (second : FreeBindingClone.Hom B C) :
    modelHom (FreeBindingClone.Hom.comp first second) =
      FreeBindingClone.Hom.comp (modelHom first) (modelHom second) := by
  apply FreeBindingClone.Hom.ext
  exact FreeBindingTerms.Hom.ext (fun _ => rfl)

/-- The interpretation square is inherited from initiality only after the
actual derived-operation morphism has been constructed. -/
theorem interpretation_naturality
    {A : BindingCloneAlgebra.Algebra.{u} Target.sig}
    {B : BindingCloneAlgebra.Algebra.{v} Target.sig}
    (h : FreeBindingClone.Hom A B) {Γ : Ctx sig} {s : sig.Srt}
    (term : Term sig Γ s) :
    h.raw.map (interpret (model A) term) = interpret (model B) term :=
  BindingCloneEquationTransport.interpret_naturality (modelHom h) term

/-- Arbitrary target semantic environments, including values outside a
model map's image, act on the transported interpretation. -/
theorem interpretation_target_environment
    {A : BindingCloneAlgebra.Algebra.{u} Target.sig}
    {B : BindingCloneAlgebra.Algebra.{v} Target.sig}
    (h : FreeBindingClone.Hom A B) {Γ Δ : Ctx sig} {s : sig.Srt}
    {left right : Term sig Γ s}
    (equality : interpret (model A) left = interpret (model A) right)
    (env : BindingSubstitutionAlgebra.Environment sig B.substitution.Carrier Γ Δ) :
    B.substitution.substitute env (interpret (model B) left) =
      B.substitution.substitute env (interpret (model B) right) :=
  BindingCloneEquationTransport.target_environment_equation (modelHom h) equality env

/-- Positional environments in the source and target signatures have the
same contextual reading, even though their constructor vocabularies differ. -/
theorem interpret_fromPositions (A : BindingCloneAlgebra.Algebra.{u} Target.sig) :
    ∀ (Γ : Ctx sig) {Δ : Ctx sig}
      (env : (i : Fin Γ.length) → Term sig Δ (Γ.get i))
      {s : sig.Srt} (x : Var Γ s),
      interpret (model A) (BindingSubstitutionAlgebra.fromPositions (S := sig) Γ env s x) =
        BindingSubstitutionAlgebra.fromPositions (S := Target.sig) Γ
          (fun i => interpret (model A) (env i)) s x
  | _ :: _, _, _, _, .zero => rfl
  | _ :: Γ, _, env, _, .succ x =>
      interpret_fromPositions A Γ (fun i => env i.succ) x

theorem variablePosition_same : ∀ (Γ : Ctx sig) (i : Fin Γ.length),
    varOfIdx (S := sig) Γ i = varOfIdx (S := Target.sig) Γ i
  | _ :: _, ⟨0, _⟩ => rfl
  | _ :: Γ, ⟨k + 1, h⟩ => by
      exact congrArg Var.succ (variablePosition_same Γ ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- Interpret a signature whose operators may denote derived target terms.
This is a translation of the existing clones, with positional substitution
preservation proved from the constructed source model. -/
def interpretingClone (A : BindingCloneAlgebra.Algebra.{u} Target.sig) : CloneTranslation
    (BindingCloneAlgebra.terms sig).substitution.toClone
    A.substitution.toClone where
  map := interpret (model A)
  map_project := by
    intro Γ i
    change A.substitution.injectVar (varOfIdx (S := sig) Γ i) =
      A.substitution.injectVar (varOfIdx (S := Target.sig) Γ i)
    exact congrArg A.substitution.injectVar (variablePosition_same Γ i)
  map_substitute := by
    intro Γ Δ s term env
    change interpret (model A)
      (bind (BindingSubstitutionAlgebra.fromPositions (S := sig) Γ env) term) =
      A.substitution.substitute
        (BindingSubstitutionAlgebra.fromPositions (S := Target.sig) Γ
          (fun i => interpret (model A) (env i))) (interpret (model A) term)
    rw [interpret_bind]
    congr 1
    funext sort x
    exact interpret_fromPositions A Γ env x

/-- The concrete lowering uses the independent target term algebra. -/
def loweringClone : CloneTranslation
    (BindingCloneAlgebra.terms sig).substitution.toClone
    (BindingCloneAlgebra.terms Target.sig).substitution.toClone :=
  interpretingClone (BindingCloneAlgebra.terms Target.sig)

def loweringContextFunctor :
    MultiSortedClone.ContextObject (BindingCloneAlgebra.terms sig).substitution.toClone ⥤
      MultiSortedClone.ContextObject (BindingCloneAlgebra.terms Target.sig).substitution.toClone :=
  loweringClone.contextFunctor

theorem loweringContextFunctor_preservesFiniteProducts :
    CategoryTheory.Limits.PreservesFiniteProducts loweringContextFunctor :=
  loweringClone.preservesFiniteProducts

theorem loweringContextFunctor_operation {Γ : Ctx sig} {s : sig.Srt}
    (term : Term sig Γ s) :
    loweringContextFunctor.map
      ((BindingCloneAlgebra.terms sig).substitution.toClone.operationAsSingletonMorphism term) =
      (BindingCloneAlgebra.terms Target.sig).substitution.toClone.operationAsSingletonMorphism
        (lower term) := by
  funext i
  refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) i
  rfl

/-- Contextual terms travel through the established operation presheaves.
The naturality field is the proved simultaneous-substitution square. -/
def loweringContextualData (s : sig.Srt) :
    MultiSortedClone.operationPresheaf (BindingCloneAlgebra.terms sig).substitution.toClone s ⟶
      loweringContextFunctor.op ⋙
        MultiSortedClone.operationPresheaf
          (BindingCloneAlgebra.terms Target.sig).substitution.toClone s :=
  loweringClone.operationNatural s

/-- The contextual-data map and the finite-product context map agree under
the existing Yoneda representation; they do not introduce parallel context
or presheaf authorities. -/
theorem loweringContextualData_yoneda (s : sig.Srt) :
    (MultiSortedClone.operationPresheafYonedaIso
      (BindingCloneAlgebra.terms sig).substitution.toClone s).hom ≫
        yonedaMap loweringContextFunctor
          (MultiSortedClone.ContextObject.ofList
            (BindingCloneAlgebra.terms sig).substitution.toClone [s]) =
      loweringContextualData s ≫
        Functor.whiskerLeft loweringContextFunctor.op
          (MultiSortedClone.operationPresheafYonedaIso
            (BindingCloneAlgebra.terms Target.sig).substitution.toClone s).hom :=
  loweringClone.operationNatural_yoneda s

/-- Further semantic transport composes on the established clone and
context categories. No new category of contexts is introduced here. -/
theorem lowering_then_model
    (A : BindingCloneAlgebra.Algebra.{u} Target.sig) :
    CloneTranslation.comp loweringClone
      (FreeBindingClone.interpretHom A).toCloneTranslation =
      interpretingClone A := by
  apply CloneTranslation.ext
  intro Γ s term
  exact interpretation_naturality (FreeBindingClone.interpretHom A) term

theorem lowering_then_model_context
    (A : BindingCloneAlgebra.Algebra.{u} Target.sig) :
    loweringContextFunctor ⋙ (FreeBindingClone.interpretHom A).toCloneTranslation.contextFunctor =
      (interpretingClone A).contextFunctor := by
  change loweringClone.contextFunctor ⋙
    (FreeBindingClone.interpretHom A).toCloneTranslation.contextFunctor = _
  rw [← CloneTranslation.contextFunctor_comp, lowering_then_model]

end Mettapedia.OSLF.Binding.DeclaredBindingInterpretation
