import Mettapedia.OSLF.Syntax.MultiBinderPresheaf

/-!
# Contextual function points for arbitrary presheaf results

A natural function from the represented binder context into any result
presheaf is determined by its value at the extended ambient context. This
generalizes the representable-result comparison and permits iteration for
curried source binders without replacing them by arbitrary set functions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.MultiBinderPresheaf

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open BindingSubstitutionAlgebra IntrinsicScopedConditionalPresheaf

universe u
variable {S : Signature}

private def pointToTensorNat (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : ContextObject A.substitution.toClone) (scope : Ctx S)
    (result : Base A ⥤ Type u)
    (body : result.obj (Opposite.op (concat A.substitution.toClone
      (ContextObject.ofList A.substitution.toClone scope) context))) :
    (binders A scope ⊗ yoneda.obj context) ⟶ result where
  app stage := TypeCat.ofHom fun arguments =>
    result.map (Opposite.op (pair A.substitution.toClone arguments.1 arguments.2)) body
  naturality first last substitution := by
    apply ConcreteCategory.hom_ext
    rintro ⟨argument, environment⟩
    change first.unop ⟶ ContextObject.ofList A.substitution.toClone scope at argument
    change first.unop ⟶ context at environment
    have pairNaturality : pair A.substitution.toClone
        (substitution.unop ≫ argument) (substitution.unop ≫ environment) =
        substitution.unop ≫ pair A.substitution.toClone argument environment := by
      symm
      apply categorical_pair_unique A.substitution.toClone
        (substitution.unop ≫ argument) (substitution.unop ≫ environment)
      · rw [Category.assoc, categorical_pair_fst]
      · rw [Category.assoc, categorical_pair_snd]
    change result.map (Opposite.op (pair A.substitution.toClone
        (substitution.unop ≫ argument) (substitution.unop ≫ environment))) body =
      result.map substitution
        (result.map (Opposite.op (pair A.substitution.toClone argument environment)) body)
    rw [pairNaturality]
    exact result.map_comp_apply (Opposite.op (pair A.substitution.toClone argument environment))
      substitution body

private def tensorNatToPoint (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : ContextObject A.substitution.toClone) (scope : Ctx S)
    (result : Base A ⥤ Type u)
    (operation : (binders A scope ⊗ yoneda.obj context) ⟶ result) :
    result.obj (Opposite.op (concat A.substitution.toClone
      (ContextObject.ofList A.substitution.toClone scope) context)) :=
  operation.app (Opposite.op (concat A.substitution.toClone
    (ContextObject.ofList A.substitution.toClone scope) context))
      (fstProjection A.substitution.toClone _ _, sndProjection A.substitution.toClone _ _)

/-- Earned Yoneda evaluation at the ordered binder-context extension, for
arbitrary presheaf results and every finite ambient context. -/
def contextualFunctionEquiv (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : ContextObject A.substitution.toClone) (scope : Ctx S)
    (result : Base A ⥤ Type u) :
    ((binders A scope).functorHom result).obj (Opposite.op context) ≃
      result.obj (Opposite.op (concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) context)) :=
  (yonedaEquiv.symm).trans ((FunctorToTypes.functorHomEquiv
    (binders A scope) (yoneda.obj context) result).trans {
      toFun := tensorNatToPoint A context scope result
      invFun := pointToTensorNat A context scope result
      left_inv := by
        intro operation
        apply NatTrans.ext
        funext stage
        apply ConcreteCategory.hom_ext
        rintro ⟨argument, environment⟩
        let input := ContextObject.ofList A.substitution.toClone scope
        let extended := concat A.substitution.toClone input context
        change stage.unop ⟶ input at argument
        change stage.unop ⟶ context at environment
        let canonical : (binders A scope ⊗ yoneda.obj context).obj (Opposite.op extended) :=
          (fstProjection A.substitution.toClone input context,
            sndProjection A.substitution.toClone input context)
        have pointwise := operation.naturality_apply
          (Opposite.op (pair A.substitution.toClone argument environment)) canonical
        change operation.app stage
            (pair A.substitution.toClone argument environment ≫ fstProjection A.substitution.toClone input context,
              pair A.substitution.toClone argument environment ≫ sndProjection A.substitution.toClone input context) =
          result.map (Opposite.op (pair A.substitution.toClone argument environment))
            (tensorNatToPoint A context scope result operation) at pointwise
        rw [categorical_pair_fst, categorical_pair_snd] at pointwise
        exact pointwise.symm
      right_inv := by
        intro body
        change result.map (Opposite.op (pair A.substitution.toClone
          (fstProjection A.substitution.toClone _ _) (sndProjection A.substitution.toClone _ _))) body = body
        have pairIdentity := categorical_pair_eta A.substitution.toClone
          (𝟙 (concat A.substitution.toClone
            (ContextObject.ofList A.substitution.toClone scope) context))
        simp only [Category.id_comp] at pairIdentity
        exact (congrArg (fun reindex => result.map (Opposite.op reindex) body) pairIdentity).trans
          (result.map_id_apply _ body) })

theorem contextualFunctionEquiv_apply (A : BindingCloneAlgebra.Algebra.{u} S)
    (context : ContextObject A.substitution.toClone) (scope : Ctx S)
    (result : Base A ⥤ Type u)
    (function : ((binders A scope).functorHom result).obj (Opposite.op context)) :
    contextualFunctionEquiv A context scope result function =
      (function.app (Opposite.op (concat A.substitution.toClone
        (ContextObject.ofList A.substitution.toClone scope) context))
        (Quiver.Hom.op (sndProjection A.substitution.toClone _ _)))
        (fstProjection A.substitution.toClone _ _) := by
  change tensorNatToPoint A context scope result
    ((FunctorToTypes.functorHomEquiv (binders A scope) (yoneda.obj context) result)
      (yonedaEquiv.symm function)) = _
  change (function.app (Opposite.op (concat A.substitution.toClone
    (ContextObject.ofList A.substitution.toClone scope) context))
    (Quiver.Hom.op (sndProjection A.substitution.toClone _ _) ≫ 𝟙 _))
    (fstProjection A.substitution.toClone _ _) = _
  rw [Category.comp_id]

/-- Yoneda evaluation respects the actual ambient substitution, extended
under exactly the admitted ordered binder list. -/
theorem contextualFunctionEquiv_reindex (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) (result : Base A ⥤ Type u) {first last : Base A}
    (substitution : first ⟶ last)
    (function : ((binders A scope).functorHom result).obj first) :
    contextualFunctionEquiv A last.unop scope result
      (((binders A scope).functorHom result).map substitution function) =
    result.map (Opposite.op (extendScope A scope substitution.unop))
      (contextualFunctionEquiv A first.unop scope result function) := by
  rw [contextualFunctionEquiv_apply, contextualFunctionEquiv_apply]
  let input := ContextObject.ofList A.substitution.toClone scope
  let extension := extendScope A scope substitution.unop
  have naturality := function.naturality
    (Quiver.Hom.op extension)
    (Quiver.Hom.op (sndProjection A.substitution.toClone input first.unop))
  have pointwise := ConcreteCategory.congr_hom naturality
    (fstProjection A.substitution.toClone input first.unop)
  change
    (function.app (Opposite.op (concat A.substitution.toClone input last.unop))
      (Quiver.Hom.op (sndProjection A.substitution.toClone input first.unop) ≫
        Quiver.Hom.op extension))
      (extension ≫ fstProjection A.substitution.toClone input first.unop) =
    result.map (Quiver.Hom.op extension)
      ((function.app (Opposite.op (concat A.substitution.toClone input first.unop))
        (Quiver.Hom.op (sndProjection A.substitution.toClone input first.unop)))
        (fstProjection A.substitution.toClone input first.unop)) at pointwise
  have lastProjection : Quiver.Hom.op (sndProjection A.substitution.toClone input first.unop) ≫
      Quiver.Hom.op extension = substitution ≫
        Quiver.Hom.op (sndProjection A.substitution.toClone input last.unop) := by
    simpa only [op_comp, Quiver.Hom.op_unop] using congrArg Quiver.Hom.op
      (extendScope_snd A scope substitution.unop)
  rw [lastProjection, extendScope_fst] at pointwise
  exact pointwise

end Mettapedia.OSLF.Binding.MultiBinderPresheaf
