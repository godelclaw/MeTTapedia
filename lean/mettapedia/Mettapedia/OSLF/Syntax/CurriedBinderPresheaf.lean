import Mettapedia.OSLF.Syntax.ContextualFunctionEvaluation
import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Natural currying for represented ordered binder contexts

The product of two represented binder contexts is their actual concatenated
clone context. Closed-category currying then gives a natural isomorphism
between an iterated base-sort function object and the whole ordered binder
function object. Every naturality law is inherited from actual clone
composition, product pairing and closed-category adjunctions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.MultiBinderPresheaf

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open BindingSubstitutionAlgebra IntrinsicScopedConditionalPresheaf

universe u
variable {S : Signature}

noncomputable def curried (algebra : BindingCloneAlgebra.Algebra.{u} S)
    (result : S.Srt) : List S.Srt → Base algebra ⥤ Type u
  | [] => programs algebra result
  | domain :: domains => (programs algebra domain).functorHom (curried algebra result domains)

/-- The context order is earned by iteration, for every binding clone and
every finite ambient context, rather than supplied by a language adapter. -/
noncomputable def curriedBodyEquiv (algebra : BindingCloneAlgebra.Algebra.{u} S)
    (context : Ctx S) (result : S.Srt) (domains : List S.Srt) :
    (curried algebra result domains).obj
        (Opposite.op (ContextObject.ofList algebra.substitution.toClone context)) ≃
      algebra.substitution.Carrier (domains.reverse ++ context) result := by
  induction domains generalizing context with
  | nil =>
      exact programsAtEquiv algebra result
        (Opposite.op (ContextObject.ofList algebra.substitution.toClone context))
  | cons domain domains ih =>
      refine (contextualFunctionEquiv algebra
        (ContextObject.ofList algebra.substitution.toClone context) [domain]
        (curried algebra result domains)).trans ?_
      simpa only [concat, ContextObject.ofList, List.reverse_cons,
        List.append_assoc, List.singleton_append] using ih (domain :: context)


def bindersConcatIso (A : BindingCloneAlgebra.Algebra.{u} S) (first last : Ctx S) :
    binders A (first ++ last) ≅ binders A first ⊗ binders A last := by
  let firstContext := ContextObject.ofList A.substitution.toClone first
  let lastContext := ContextObject.ofList A.substitution.toClone last
  refine NatIso.ofComponents (fun stage => Equiv.toIso {
    toFun := fun environment =>
      (environment ≫ fstProjection A.substitution.toClone firstContext lastContext,
        environment ≫ sndProjection A.substitution.toClone firstContext lastContext)
    invFun := fun arguments => pair A.substitution.toClone arguments.1 arguments.2
    left_inv := fun environment => by
      change stage.unop ⟶ concat A.substitution.toClone firstContext lastContext at environment
      exact categorical_pair_eta A.substitution.toClone environment
    right_inv := fun arguments => Prod.ext
      (categorical_pair_fst A.substitution.toClone arguments.1 arguments.2)
      (categorical_pair_snd A.substitution.toClone arguments.1 arguments.2) }) ?_
  intro source target substitution
  apply ConcreteCategory.hom_ext
  intro environment
  exact Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

def bindersEmptyIso (A : BindingCloneAlgebra.Algebra.{u} S) :
    binders A [] ≅ 𝟙_ (Base A ⥤ Type u) := by
  refine NatIso.ofComponents (fun stage => Equiv.toIso {
    toFun := fun _ => PUnit.unit
    invFun := fun _ => by
      change stage.unop ⟶ ContextObject.ofList A.substitution.toClone []
      intro position
      exact Fin.elim0 position
    left_inv := fun environment => by funext position; exact Fin.elim0 position
    right_inv := fun point => by cases point; rfl }) ?_
  intro source target substitution
  apply ConcreteCategory.hom_ext
  intro environment
  rfl

noncomputable def functionDomainIso {C : Type u} [Category C]
    [MonoidalCategory C] [MonoidalClosed C] {first last : C}
    (domain : first ≅ last) (result : C) :
    (ihom first).obj result ≅ (ihom last).obj result :=
  (MonoidalClosed.internalHom.mapIso domain.symm.op).app result

/-- The complete iterated function object is naturally the whole-context
binder object. The reversal is forced by source binder nesting. -/
noncomputable def curriedBinderIso (A : BindingCloneAlgebra.Algebra.{u} S)
    (result : S.Srt) : (domains : List S.Srt) →
    curried A result domains ≅
      (binders A domains.reverse).functorHom (programs A result)
  | [] => (MonoidalClosed.unitIsoSelf (X := programs A result)).symm ≪≫
      functionDomainIso (bindersEmptyIso A).symm (programs A result)
  | domain :: domains => by
      let lifted := (FunctorToTypes.rightAdj (programs A domain)).mapIso
        (curriedBinderIso A result domains)
      let curryIso := MonoidalClosed.ihomCurryIso
        (binders A domains.reverse) (programs A domain) (programs A result)
      let combined := functionDomainIso
        (bindersConcatIso A domains.reverse [domain]).symm (programs A result)
      rw [List.reverse_cons]
      change (programs A domain).functorHom (curried A result domains) ≅
        (binders A (domains.reverse ++ [domain])).functorHom (programs A result)
      exact lifted ≪≫ curryIso.symm ≪≫ combined

end Mettapedia.OSLF.Binding.MultiBinderPresheaf
