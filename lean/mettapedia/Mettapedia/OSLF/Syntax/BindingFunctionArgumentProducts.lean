import Mettapedia.OSLF.Syntax.BindingFunctionArgumentComparison

/-!
# Product presentation of ordered contextual constructor arguments

The original function-argument tuple is naturally a finite product of its
actual whole-context function objects. This comparison preserves argument
order and uses the same clone substitution action as the constructor model.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingFunctionArgumentComparison

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open BindingSubstitutionAlgebra IntrinsicScopedConditionalPresheaf MultiBinderPresheaf

universe u
variable {S : Signature}

def nilIso (A : BindingCloneAlgebra.Algebra.{u} S) :
    functionArguments A [] ≅ 𝟙_ (Base A ⥤ Type u) := by
  refine NatIso.ofComponents (fun _ => Equiv.toIso {
    toFun := fun _ => PUnit.unit
    invFun := fun _ => .nil
    left_inv := fun argument => by cases argument; rfl
    right_inv := fun value => by cases value; rfl }) ?_
  intro first last substitution
  apply ConcreteCategory.hom_ext
  intro argument
  rfl

def consIso (A : BindingCloneAlgebra.Algebra.{u} S)
    (scope : Ctx S) (result : S.Srt) (rest : List (Ctx S × S.Srt)) :
    functionArguments A ((scope, result) :: rest) ≅
      (binders A scope).functorHom (programs A result) ⊗ functionArguments A rest := by
  refine NatIso.ofComponents (fun _ => Equiv.toIso {
    toFun := fun | .cons first last => (first, last)
    invFun := fun value => .cons value.1 value.2
    left_inv := fun argument => by cases argument; rfl
    right_inv := fun value => by cases value; rfl }) ?_
  intro first last substitution
  apply ConcreteCategory.hom_ext
  intro argument
  cases argument with
  | cons firstArgument lastArguments =>
      have recovered : environmentArrow A
          (fromPositions first.unop.context substitution.unop) = substitution.unop := by
        funext position
        exact fromPositions_varOfIdx first.unop.context substitution.unop position
      change ((((binders A scope).functorHom (programs A result)).map
          (Quiver.Hom.op (environmentArrow A
            (fromPositions first.unop.context substitution.unop)))) firstArgument,
        FunctionArgs.reindex A (fromPositions first.unop.context substitution.unop) lastArguments) =
        (((binders A scope).functorHom (programs A result)).map substitution firstArgument,
          FunctionArgs.reindex A (fromPositions first.unop.context substitution.unop) lastArguments)
      rw [recovered]
      exact Prod.ext
        (congrArg (fun arrow => ((binders A scope).functorHom
          (programs A result)).map arrow firstArgument)
          (Quiver.Hom.op_unop substitution)) rfl

end Mettapedia.OSLF.Binding.BindingFunctionArgumentComparison
