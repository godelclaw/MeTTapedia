import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryRepresentableAdmission
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarationCategory

/-!
# Original-category conservation in the complete dependent presentation

The original category maps into the full mixed-context quotient, not a
separate quotient confined to its represented object image. Complete native
readouts of its arrows earn faithfulness by Yoneda. Type, section and
predicate quotients are formed over the same generated category.
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

abbrev representedContext (object : C) : TheoryEquations.Contextual.Context (theory C) :=
  ⟨1, objectContext object, (TheoryEquations.Contextual.formed_iff _).mpr
    ⟨TheoryEquations.original (objectContextFormed object)⟩⟩

def originalArrow {source target : C} (arrow : source ⟶ target) :
    representedContext source ⟶ representedContext target :=
  ⟨originalSubstitution arrow, ⟨TheoryEquations.original (originalSubstitutionFormed arrow)⟩⟩

def originalFunctor : C ⥤ TheoryEquations.Contextual.quotientContext (theory C) where
  obj object := (TheoryEquations.Contextual.quotientProjection (theory C)).obj (representedContext object)
  map arrow := (TheoryEquations.Contextual.quotientProjection (theory C)).map (originalArrow arrow)
  map_id object :=
    (TheoryEquations.Contextual.quotientProjection_map_eq_iff _ _).mpr ⟨equationTree (.identity object)⟩
  map_comp earlier later :=
    (TheoryEquations.Contextual.quotientProjection_map_eq_iff _ _).mpr ⟨equationTree (.composition earlier later)⟩

theorem object_context_generic (object : C) :
    (model C).toAbstract.evaluateContext (objectContext object) =
      some (NativeAbstractScope.toGeneric (objectScope object)) := by
  rw [(model C).evaluateContext_compare, object_context_read]
  rfl

def readArrow {source target : C} (arrow : representedContext source ⟶ representedContext target) :
    (objectScope source).1 ⟶ (objectScope target).1 :=
  Evidence.substitutionArrow (model C).toAbstract (realization C).toAbstract
    (PresheafNativePredicateModel.qualification C) admitted (Classical.choice arrow.admitted)
    (NativeAbstractScope.toGeneric (objectScope source)) (NativeAbstractScope.toGeneric (objectScope target))
    (object_context_generic source) (object_context_generic target)

theorem readArrow_readout {source target : C}
    (arrow : representedContext source ⟶ representedContext target) :
    (model C).evaluateSubstitution (objectScope source) (objectScope target) arrow.substitution =
      some (readArrow arrow) := by
  rw [← (model C).evaluateSubstitution_compare]
  exact Evidence.substitutionArrow_readout (model C).toAbstract (realization C).toAbstract
    (PresheafNativePredicateModel.qualification C) admitted (Classical.choice arrow.admitted)
    _ _ (object_context_generic source) (object_context_generic target)

theorem readArrow_equation {source target : C}
    {first second : representedContext source ⟶ representedContext target}
    (same : TheoryEquations.Contextual.homEquality (theory C) first second) :
    readArrow first = readArrow second :=
  Evidence.substitutionArrow_equation (model C).toAbstract (realization C).toAbstract
    (PresheafNativePredicateModel.qualification C) admitted (Classical.choice first.admitted)
    (Classical.choice second.admitted) (Classical.choice same)
    _ _ (object_context_generic source) (object_context_generic target)

def quotientReadout {source target : C}
    (arrow : originalFunctor.obj source ⟶ originalFunctor.obj target) :
    (objectScope source).1 ⟶ (objectScope target).1 :=
  Quot.liftOn arrow readArrow (fun _ _ same => readArrow_equation
    ((HomRel.compClosure_iff_self (TheoryEquations.Contextual.homEquality (theory C)) _ _).mp same))

theorem original_readout {source target : C} (arrow : source ⟶ target) :
    quotientReadout (originalFunctor.map arrow) = originalMap arrow :=
  Option.some.inj ((readArrow_readout (originalArrow arrow)).symm.trans (original_substitution_read arrow))

theorem original_map_injective {source target : C} :
    Function.Injective (fun arrow : source ⟶ target => originalFunctor.map arrow) := by
  intro first second same
  apply RepresentableDeclarations.originalPresheafArrow_injective
  exact (original_readout first).symm.trans
    ((congrArg quotientReadout same).trans (original_readout second))

instance originalFunctor_faithful : (originalFunctor (C := C)).Faithful where
  map_injective {source target} {first second} same := @original_map_injective C _ source target first second same

theorem original_equation_iff {source target : C} (first second : source ⟶ target) :
    originalFunctor.map first = originalFunctor.map second ↔ first = second :=
  ⟨fun same => original_map_injective same, congrArg originalFunctor.map⟩

theorem generalized_original_readout {source target world : C}
    (arrow : source ⟶ target) (argument : world ⟶ source) :
    (objectName target).app (Opposite.op world)
      ((quotientReadout (originalFunctor.map arrow)).app (Opposite.op world)
        ((objectNameInverse source).app (Opposite.op world) argument)) = argument ≫ arrow := by
  rw [original_readout]
  rfl

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryRepresentables
