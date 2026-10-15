import Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedNormalizedQuantifiers

/-!
# Independently determined truth and binary predicate values

Canonical tuple comparisons retain both predicate inputs. The primitive
conjunctive squares determine truth and conjunction, while the finite
implication qualifications determine implication. These results compare
entire dependent arrow values, including independently formed headers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory FunctorNormalization Interpretation
open ProgramReductionTheory RelativeClosedNamedQuantifiedPresentation

universe k
variable {source : Theory.{k,k}} {Index Origins : Type k}
variable {selected : Index → RelativeClosedPositionedModalPresentation.Selection source}
variable {constructors : Origins → RelativeClosedStructuralImagePresentation.Constructor source}
variable {target : QuantifiedImplicativeProgramTheory.{k}}
variable (data : OriginComparison (source := source) (selected := selected) (constructors := constructors) target)

theorem normalized_tuple_object :
    (normalized data).obj
        ((predicates source selected constructors).proposition ⊗
          (predicates source selected constructors).proposition) =
      target.quantified.operations.predicates.proposition ⊗ target.quantified.operations.predicates.proposition :=
  (normalized_product_object (atomicFunctor data)
    (predicates source selected constructors).proposition (predicates source selected constructors).proposition).trans
    (congrArg₂ (fun first second : target.quantified.programTheory.closed.Obj => first ⊗ second)
      (normalized_proposition_object data) (normalized_proposition_object data))

private theorem tensor_cast {D : Type k} [Category.{k} D] [MonoidalCategory D]
    {first second before after : D} (left : first = before) (right : second = after) :
    eqToHom left ⊗ₘ eqToHom right = eqToHom (congrArg₂ (fun x y : D => x ⊗ y) left right) := by
  cases left
  cases right
  exact id_tensorHom_id _ _

theorem normalized_tuple_hom :
    (InternalConjunctiveOrderComparison.tupleComparison (normalizedPredicates data)).hom =
      eqToHom (normalized_tuple_object data) := by
  change CartesianMonoidalCategory.prodComparison (normalized data)
      (predicates source selected constructors).proposition (predicates source selected constructors).proposition ≫
      ((normalizedPredicates data).proposition.hom ⊗ₘ
        (normalizedPredicates data).proposition.hom) = _
  rw [normalized_proposition_hom]
  have first := normalized_productComparison (atomicFunctor data)
    (predicates source selected constructors).proposition (predicates source selected constructors).proposition
  have second := tensor_cast (normalized_proposition_object data)
    (normalized_proposition_object data)
  exact (congrArg₂ (fun before after => before ≫ after) first second).trans (eqToHom_trans _ _)

theorem normalized_tuple_inv :
    (InternalConjunctiveOrderComparison.tupleComparison (normalizedPredicates data)).inv =
      eqToHom (normalized_tuple_object data).symm :=
  congrArg Iso.inv (Iso.ext (normalized_tuple_hom data) :
    InternalConjunctiveOrderComparison.tupleComparison (normalizedPredicates data) =
      eqToIso (normalized_tuple_object data))

theorem normalized_truth_value :
    (⟨(normalized data).obj (GeneratedCategory.terminal
        (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors)),
      (normalized data).obj (predicates source selected constructors).proposition,
      (normalized data).map (predicates source selected constructors).truth⟩ :
        ArrowValue target.quantified.programTheory.closed.Obj) =
      ⟨𝟙_ target.quantified.programTheory.closed.Obj, target.quantified.operations.predicates.proposition,
        target.quantified.operations.predicates.truth⟩ := by
  let input := normalized_terminal_object (atomicFunctor data)
  let output := normalized_proposition_object data
  have primitiveSquare :
      (normalized data).map (predicates source selected constructors).truth ≫
        (normalizedPredicates data).proposition.hom =
      toUnit ((normalized data).obj (GeneratedCategory.terminal
        (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors))) ≫
        target.quantified.operations.predicates.truth := (normalizedPredicates data).truth
  have terminalCast :
      toUnit ((normalized data).obj (GeneratedCategory.terminal
        (RelativeClosedStructuralImagePresentation.nativeSignature source selected constructors))) =
      eqToHom input := Subsingleton.elim _ _
  have square :
      (normalized data).map (predicates source selected constructors).truth ≫ eqToHom output =
      eqToHom input ≫ target.quantified.operations.predicates.truth :=
    ((congrArg (fun arrow =>
      (normalized data).map (predicates source selected constructors).truth ≫ arrow)
        (normalized_proposition_hom data)).symm.trans primitiveSquare).trans
      (congrArg (fun arrow => arrow ≫ target.quantified.operations.predicates.truth) terminalCast)
  have read : eqToHom input.symm ≫
      (normalized data).map (predicates source selected constructors).truth ≫ eqToHom output =
    target.quantified.operations.predicates.truth := by
    calc
      _ = eqToHom input.symm ≫ (eqToHom input ≫ target.quantified.operations.predicates.truth) :=
        congrArg (fun arrow => eqToHom input.symm ≫ arrow) square
      _ = _ := by rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  exact ArrowValue.eq_of_cast input output _ _ read

private theorem binary_value
    (operation : (predicates source selected constructors).proposition ⊗
        (predicates source selected constructors).proposition ⟶
      (predicates source selected constructors).proposition)
    (expected : target.quantified.operations.predicates.proposition ⊗
        target.quantified.operations.predicates.proposition ⟶ target.quantified.operations.predicates.proposition)
    (forced : InternalPredicateImplicationMaps.operationImage (normalizedPredicates data)
      operation = expected) :
    (⟨(normalized data).obj
          ((predicates source selected constructors).proposition ⊗
            (predicates source selected constructors).proposition),
      (normalized data).obj (predicates source selected constructors).proposition,
      (normalized data).map operation⟩ : ArrowValue target.quantified.programTheory.closed.Obj) =
      ⟨target.quantified.operations.predicates.proposition ⊗ target.quantified.operations.predicates.proposition,
        target.quantified.operations.predicates.proposition, expected⟩ := by
  have read : eqToHom (normalized_tuple_object data).symm ≫
      (normalized data).map operation ≫ eqToHom (normalized_proposition_object data) =
    expected :=
    (congrArg₂ (fun incoming outgoing => incoming ≫ (normalized data).map operation ≫ outgoing)
      (normalized_tuple_inv data).symm (normalized_proposition_hom data).symm).trans forced
  exact ArrowValue.eq_of_cast (normalized_tuple_object data)
    (normalized_proposition_object data) _ _ read

theorem normalized_conjunction_value :
    (⟨(normalized data).obj
          ((predicates source selected constructors).proposition ⊗
            (predicates source selected constructors).proposition),
      (normalized data).obj (predicates source selected constructors).proposition,
      (normalized data).map (predicates source selected constructors).conjunction⟩ :
        ArrowValue target.quantified.programTheory.closed.Obj) =
      ⟨target.quantified.operations.predicates.proposition ⊗ target.quantified.operations.predicates.proposition,
        target.quantified.operations.predicates.proposition, target.quantified.operations.predicates.conjunction⟩ := by
  apply binary_value data
  apply (cancel_epi (InternalConjunctiveOrderComparison.tupleComparison
    (normalizedPredicates data)).hom).mp
  exact (InternalPredicateImplicationMaps.operationImage_square (normalizedPredicates data) _).trans
    (InternalConjunctiveOrderComparison.tupleComparison_conjunction (normalizedPredicates data)).symm

theorem normalized_implication_value :
    (⟨(normalized data).obj
          ((predicates source selected constructors).proposition ⊗
            (predicates source selected constructors).proposition),
      (normalized data).obj (predicates source selected constructors).proposition,
      (normalized data).map (implication source selected constructors).operation⟩ :
        ArrowValue target.quantified.programTheory.closed.Obj) =
      ⟨target.quantified.operations.predicates.proposition ⊗ target.quantified.operations.predicates.proposition,
        target.quantified.operations.predicates.proposition, target.implication.operation⟩ :=
  binary_value data _ _
    (InternalPredicateImplicationMaps.implication_image (normalizedPredicates data)
      target.quantified.operations.laws (implication source selected constructors) target.implication)

end Mettapedia.GSLT.Core.RelativeClosedNamedQuantifiedRestriction
