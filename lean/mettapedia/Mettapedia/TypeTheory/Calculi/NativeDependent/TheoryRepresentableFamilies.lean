import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryRepresentableConservativity

/-!
# Original-arrow families in the equation-extended dependent presentation

Every original arrow declares its genuine indexed fibre type. The actual
extended-tree family readout retains a complete source inhabitant satisfying
the supplied target index. Substitution acts on these families and their
sections through the same full context quotient as the original functor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryRepresentables

open _root_.CategoryTheory
open RepresentableIndexedDeclarations
open TheoryEquations

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

def indexedFamily (index : ArrowSymbol C) :
    TheoryEquations.Contextual.TypeOver (representedContext index.target) :=
  ⟨fibreType index (.var 0), ⟨TheoryEquations.original (genericFibreFormed index)⟩⟩

def indexedFamilyClass (index : ArrowSymbol C) :
    TheoryEquations.Contextual.QType (representedContext index.target) :=
  TheoryEquations.Contextual.QType.mk (indexedFamily index)


/-- An actual original arrow equation supplies the generated indexed-type
equation (TE), with its independent original fibre-formation tree. -/
def original_type_equation {source target : C} (first second : source ⟶ target)
    (same : first = second) :
    TheoryEquations.Derivation (signature C) (equations C)
      (.typeEq (objectContext target)
        (fibreType ⟨source, target, first⟩ (.var 0))
        (fibreType ⟨source, target, second⟩ (.var 0))) := by
  cases same
  exact TheoryEquations.deriveWith
    (.typeReflexivity (objectContext target) (fibreType ⟨source, target, first⟩ (.var 0)))
    ⟨TheoryEquations.original (genericFibreFormed ⟨source, target, first⟩), PUnit.unit⟩

def indexedFamilyReadout (index : ArrowSymbol C) :=
  Evidence.typeValue (model C).toAbstract (realization C).toAbstract
    (PresheafNativePredicateModel.qualification C) admitted
    (TheoryEquations.original (genericFibreFormed index))
    (NativeAbstractScope.toGeneric (objectScope index.target)) (object_context_generic index.target)

theorem indexed_family_readout (index : ArrowSymbol C) :
    indexedFamilyReadout index = fibreMeaning index :=
  Evidence.typeValue_unique (model C).toAbstract (realization C).toAbstract
    (PresheafNativePredicateModel.qualification C) admitted
    (TheoryEquations.original (genericFibreFormed index)) _ (object_context_generic index.target) _
    (by rw [(model C).evaluateType_compare]; exact generic_fibre_read index)


theorem fibre_context_generic (index : ArrowSymbol C) :
    (model C).toAbstract.evaluateContext (fibreContext index) =
      some (NativeAbstractScope.toGeneric (fibreScope index)) := by
  rw [(model C).evaluateContext_compare, fibre_context_read]
  rfl

theorem forget_annotation_generic (index : ArrowSymbol C) :
    (model C).toAbstract.evaluateType (NativeAbstractScope.toGeneric (fibreScope index))
      (objectType index.source 2) = some (forgetType index) := by
  rw [(model C).evaluateType_compare]
  exact object_read index.source (fibreScope index)

def retainedForgetSection (index : ArrowSymbol C) :=
  Evidence.termSection (model C).toAbstract (realization C).toAbstract
    (PresheafNativePredicateModel.qualification C) admitted
    (TheoryEquations.original (genericForgetFormed index))
    (NativeAbstractScope.toGeneric (fibreScope index)) (forgetType index)
    (fibre_context_generic index) (forget_annotation_generic index)

theorem retained_forget_readout (index : ArrowSymbol C) :
    retainedForgetSection index = forgetValue index :=
  Evidence.termSection_unique (model C).toAbstract (realization C).toAbstract
    (PresheafNativePredicateModel.qualification C) admitted
    (TheoryEquations.original (genericForgetFormed index)) _ _
    (fibre_context_generic index) (forget_annotation_generic index) _
    (by rw [(model C).evaluateTerm_compare]; exact generic_forget_read index)

/-- An equation of quotient base arrows acts on every generated family,
including ones formed using added equations and logical constructors. -/
theorem complete_family_substitution {source target : C}
    (family : TheoryEquations.Contextual.QType (representedContext target))
    (arrow : source ⟶ target) :
    TheoryEquations.Contextual.Interpretation.typeValue qualifiedModel
      (TheoryEquations.Contextual.QuotientCwf.tySub family (originalFunctor.map arrow)) =
      (NativeModel C).toCwf.tySub
        (TheoryEquations.Contextual.Interpretation.typeValue qualifiedModel family)
        ((TheoryEquations.Contextual.Interpretation.quotientFunctor qualifiedModel).map
          (originalFunctor.map arrow)) :=
  TheoryEquations.Contextual.Interpretation.type_substitution qualifiedModel family (originalFunctor.map arrow)

theorem complete_term_substitution {source target : C}
    {family : TheoryEquations.Contextual.QType (representedContext target)}
    (supplied : TheoryEquations.Contextual.QuotientCwf.Tm (originalFunctor.obj target) family)
    (arrow : source ⟶ target) :
    HEq (TheoryEquations.Contextual.Interpretation.termValue qualifiedModel
      (TheoryEquations.Contextual.QuotientCwf.tmSub supplied (originalFunctor.map arrow)))
      ((NativeModel C).toCwf.tmSub
        (TheoryEquations.Contextual.Interpretation.termValue qualifiedModel supplied)
        ((TheoryEquations.Contextual.Interpretation.quotientFunctor qualifiedModel).map
          (originalFunctor.map arrow))) :=
  TheoryEquations.Contextual.Interpretation.term_substitution qualifiedModel supplied (originalFunctor.map arrow)

theorem complete_predicate_substitution {source target : C}
    (predicate : TheoryEquations.Contextual.QPredicate (representedContext target))
    (arrow : source ⟶ target) :
    TheoryEquations.Contextual.Interpretation.predicateValue qualifiedModel
      (TheoryEquations.Contextual.PredicateAction.reindex (originalFunctor.map arrow) predicate) =
      (PresheafNativePredicateModel.model C).doctrine.reindex
        ((TheoryEquations.Contextual.Interpretation.quotientFunctor qualifiedModel).map
          (originalFunctor.map arrow))
        (TheoryEquations.Contextual.Interpretation.predicateValue qualifiedModel predicate) :=
  TheoryEquations.Contextual.Interpretation.predicate_substitution qualifiedModel predicate (originalFunctor.map arrow)

/-- Identity and composition declarations now propagate through arbitrary
whole generated type fibres, rather than only identifying represented arrows. -/
theorem family_composition {source middle target : C}
    (family : TheoryEquations.Contextual.QType (representedContext target)) (earlier : source ⟶ middle) (later : middle ⟶ target) :
    TheoryEquations.Contextual.QuotientCwf.tySub family (originalFunctor.map (earlier ≫ later)) =
      TheoryEquations.Contextual.QuotientCwf.tySub
        (TheoryEquations.Contextual.QuotientCwf.tySub family (originalFunctor.map later))
        (originalFunctor.map earlier) := by
  rw [originalFunctor.map_comp]
  exact TheoryEquations.Contextual.QuotientCwf.tySub_comp family _ _

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryRepresentables
