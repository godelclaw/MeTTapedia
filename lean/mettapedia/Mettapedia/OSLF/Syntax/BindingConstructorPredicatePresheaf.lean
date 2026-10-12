import Mettapedia.OSLF.Syntax.BindingConstructorPredicateMaps
import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Binding constructor predicates as actual presheaf images

The substitution-stable families define subfunctors of the established
semantic program and argument presheaves. The constructor predicate is the
image of the independently constructed binding-operation natural
transformation. Its comprehension fibre is equivalent to complete
argument receipts; different arguments can inhabit the same output fibre.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingConstructorPredicates

open _root_.CategoryTheory FreeBindingTerms BindingSubstitutionAlgebra
open IntrinsicScopedConditionalPresheaf

universe u

variable {S : Signature} {A : BindingCloneAlgebra.Algebra.{u} S}

/-- The family is a genuine subfunctor under all quotient-clone context
arrows, rather than only under renamings. -/
def Predicate.subfunctor {sort : S.Srt} (predicate : Predicate A sort) :
    Subfunctor (semanticPrograms A sort) where
  obj X := {value | predicate.holds value}
  map := by
    intro first last change value admitted
    exact predicate.substitute (fromPositions first.unop.context change.unop) value admitted

/-- The admitted argument vectors form a subfunctor of the complete
binder-sensitive argument presheaf. -/
def Arguments.subfunctor {arity : List (List S.Srt × S.Srt)}
    (inputs : Arguments A arity) : Subfunctor (BindingOperationPresheaf.arguments A arity) where
  obj X := {values | inputs.Holds values}
  map := by
    intro first last change values admitted
    exact inputs.substitute (fromPositions first.unop.context change.unop) values admitted

/-- The whole native family agrees with the actual presheaf image of the
authored operation at every context and every future restriction. -/
theorem image_subfunctor {sort : S.Srt} (operator : S.Op sort)
    (inputs : Arguments A (S.arity operator)) :
    (image A operator inputs).subfunctor =
      inputs.subfunctor.image (BindingOperationPresheaf.operation A operator) := by
  ext X value
  change Nonempty (Receipt A operator inputs value) ↔
    ∃ values, inputs.Holds values ∧ A.operation operator values = value
  exact image_iff A operator inputs value

/-- The actual argument-certificate comprehension map into programs. -/
def comprehensionMap {sort : S.Srt} (operator : S.Op sort)
    (inputs : Arguments A (S.arity operator)) :
    inputs.subfunctor.toFunctor ⟶ semanticPrograms A sort :=
  inputs.subfunctor.ι ≫ BindingOperationPresheaf.operation A operator

/-- The entire image family is the range of this comprehension map. -/
theorem image_comprehension {sort : S.Srt} (operator : S.Op sort)
    (inputs : Arguments A (S.arity operator)) :
    (image A operator inputs).subfunctor =
      Subfunctor.range (comprehensionMap operator inputs) := by
  ext X value
  change Nonempty (Receipt A operator inputs value) ↔
    ∃ values : {arguments : FamilyArgs S A.substitution.Carrier (S.arity operator)
      X.unop.context // inputs.Holds arguments}, A.operation operator values.val = value
  constructor
  · rintro ⟨receipt⟩
    exact ⟨⟨receipt.arguments, receipt.admitted⟩, receipt.output⟩
  · rintro ⟨⟨arguments, admitted⟩, output⟩
    exact ⟨⟨arguments, admitted, output⟩⟩

/-- A comprehension fibre retains precisely the argument receipt, with
the supplied program value as its dependent result index. -/
def receiptFiberEquiv {sort : S.Srt} (operator : S.Op sort)
    (inputs : Arguments A (S.arity operator)) (X : Base A)
    (value : (semanticPrograms A sort).obj X) :
    Receipt A operator inputs value ≃
      {arguments : inputs.subfunctor.toFunctor.obj X //
        (comprehensionMap operator inputs).app X arguments = value} where
  toFun receipt := ⟨⟨receipt.arguments, receipt.admitted⟩, receipt.output⟩
  invFun arguments := ⟨arguments.val.val, arguments.val.property, arguments.property⟩
  left_inv receipt := by cases receipt; rfl
  right_inv arguments := by rcases arguments with ⟨⟨values, admitted⟩, output⟩; rfl

/-- Eliminating the actual comprehension fibre recovers the complete
ordered argument vector, including each bound continuation. -/
theorem receiptFiber_arguments {sort : S.Srt} (operator : S.Op sort)
    (inputs : Arguments A (S.arity operator)) (X : Base A)
    (value : (semanticPrograms A sort).obj X)
    (receipt : Receipt A operator inputs value) :
    ((receiptFiberEquiv operator inputs X value) receipt).val.val = receipt.arguments := rfl

end Mettapedia.OSLF.Binding.BindingConstructorPredicates
