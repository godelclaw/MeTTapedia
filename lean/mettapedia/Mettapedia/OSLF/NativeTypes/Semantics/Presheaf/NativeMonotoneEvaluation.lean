import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneReadout

/-!
# Full native operator fixed-point formula evaluation

The generated formulas evaluate the authored function at the generic native
predicate. Both guards quantify over its entire dependent carrier, and the
outer native quantifiers retain every generalized predicate component.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneEvaluation

open _root_.CategoryTheory Mettapedia.TypeTheory Mettapedia.GSLT.Topos
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes
open NativeLocalTypeFormers NativeLocalTypeOperations
open PresheafNativePropositionReadout DisplayedPresheafComprehension
open PredicateVariables PredicateNaming NativeMonotoneFunctions NativeMonotoneReadout

universe u v
variable {C : Type u} [Category.{u} C] {P : Cᵒᵖ ⥤ Type u}
variable {S : Symbols.{v}} {n : Nat}
attribute [local irreducible] NativeLocalTypeFormers.pi PresheafNativePropositionReadout.nativeOmega

noncomputable def transformed (A : NativeType P) (operator : (operatorType A).decoded.sections) :
    Subfunctor (totalSpace (argumentType A).decoded) :=
  predicateBody (argumentType A)
    (applyValue (predicate (argumentType A))
      (weakenOperator A operator (totalProjection (predicate A).decoded)) (generic A))

noncomputable def preGuard (A : NativeType P) (operator : (operatorType A).decoded.sections) :
    Subfunctor (totalSpace (predicate A).decoded) :=
  inclusionMeaning (argumentType A)
    (applyValue (predicate (argumentType A))
      (weakenOperator A operator (totalProjection (predicate A).decoded)) (generic A)) (generic A)

noncomputable def postGuard (A : NativeType P) (operator : (operatorType A).decoded.sections) :
    Subfunctor (totalSpace (predicate A).decoded) :=
  inclusionMeaning (argumentType A) (generic A)
    (applyValue (predicate (argumentType A))
      (weakenOperator A operator (totalProjection (predicate A).decoded)) (generic A))

theorem preGuard_body (A : NativeType P) (operator : (operatorType A).decoded.sections) :
    preGuard A operator = forallAlong (totalProjection (argumentType A).decoded)
      (transformed A operator ⇨ boundMembership A) := by
  rw [preGuard, inclusionMeaning, transformed, bound_body]
  rfl

theorem postGuard_body (A : NativeType P) (operator : (operatorType A).decoded.sections) :
    postGuard A operator = forallAlong (totalProjection (argumentType A).decoded)
      (boundMembership A ⇨ transformed A operator) := by
  rw [postGuard, inclusionMeaning, transformed, bound_body]
  rfl

noncomputable def least (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (value : A.decoded.sections) : Subfunctor P :=
  forallAlong (totalProjection (predicate A).decoded)
    (preGuard A operator ⇨ FixedPointEvaluation.testedMembership A value)

noncomputable def greatest (A : NativeType P) (operator : (operatorType A).decoded.sections)
    (value : A.decoded.sections) : Subfunctor P :=
  (postGuard A operator ⊓ FixedPointEvaluation.testedMembership A value).image
    (totalProjection (predicate A).decoded)

theorem evaluate_prefixed (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩) :
    model.evaluatePredicate (context.snoc (predicate A)) (NativeMonotoneSyntax.prefixed domain operatorCode) =
      some (preGuard A operator) := by
  have domainWeak := model.evaluateType_rename (products_substitution C) domain
    (context.snoc (predicate A)) context Fin.succ (ModelRenaming.weaken context (predicate A)) A domainRead
  have applied := evaluate_applyOperator model (context.snoc (predicate A)) (domain.rename Fin.succ)
    (argumentType A) (operatorCode.rename Fin.succ) (.var 0) _ _ domainWeak
    (evaluate_operator_weaken model context operatorCode A (predicate A) operator operatorRead)
    (evaluate_generic model context A)
  apply evaluate_inclusion
  · exact domainWeak
  · exact applied
  · exact evaluate_generic model context A

theorem evaluate_postfixed (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode : TermExpr S n)
    (operator : (operatorType A).decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩) :
    model.evaluatePredicate (context.snoc (predicate A)) (NativeMonotoneSyntax.postfixed domain operatorCode) =
      some (postGuard A operator) := by
  have domainWeak := model.evaluateType_rename (products_substitution C) domain
    (context.snoc (predicate A)) context Fin.succ (ModelRenaming.weaken context (predicate A)) A domainRead
  have applied := evaluate_applyOperator model (context.snoc (predicate A)) (domain.rename Fin.succ)
    (argumentType A) (operatorCode.rename Fin.succ) (.var 0) _ _ domainWeak
    (evaluate_operator_weaken model context operatorCode A (predicate A) operator operatorRead)
    (evaluate_generic model context A)
  apply evaluate_inclusion
  · exact domainWeak
  · exact evaluate_generic model context A
  · exact applied

theorem evaluate_least (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode tested : TermExpr S n)
    (operator : (operatorType A).decoded.sections) (value : A.decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩)
    (valueRead : model.evaluateTerm context tested = some ⟨A,value⟩) :
    model.evaluatePredicate context (NativeMonotoneSyntax.least domain operatorCode tested) =
      some (least A operator value) := by
  have implication := model.evaluate_implies _ _ _ _ _
    (evaluate_prefixed model context domain A operatorCode operator domainRead operatorRead)
    (evaluate_application_under_predicate model context domain tested A value domainRead valueRead)
  rw [himpPointwise_eq_himp] at implication
  apply evaluate_universal
  · exact evaluate_predicate model context domain A domainRead
  · exact implication

theorem evaluate_greatest (model : ModelData S C) (context : Scope C n)
    (domain : TypeExpr S n) (A : NativeType context.1) (operatorCode tested : TermExpr S n)
    (operator : (operatorType A).decoded.sections) (value : A.decoded.sections)
    (domainRead : model.evaluateType context domain = some A)
    (operatorRead : model.evaluateTerm context operatorCode = some ⟨operatorType A,operator⟩)
    (valueRead : model.evaluateTerm context tested = some ⟨A,value⟩) :
    model.evaluatePredicate context (NativeMonotoneSyntax.greatest domain operatorCode tested) =
      some (greatest A operator value) := by
  exact model.evaluate_exists _ _ _ _ _ (evaluate_predicate model context domain A domainRead)
    (model.evaluate_and _ _ _ _ _
      (evaluate_postfixed model context domain A operatorCode operator domainRead operatorRead)
      (evaluate_application_under_predicate model context domain tested A value domainRead valueRead))

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.NativeMonotoneEvaluation
