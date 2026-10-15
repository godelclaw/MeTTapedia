import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObject
import Mettapedia.CategoryTheory.InternalPredicateQuantifierMaps
import Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence

/-!
# Weak closed maps of quantified predicate objects

An actual finite-limit closed functor and its local conjunctive-object
comparison determine every quantified operation square. Identity and
composition retain the canonical function-object comparisons and whole
function sections. There is no additional quantified-operation or
whole-expression preservation field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateQuantifiedObject

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalPredicateFunctionObject InternalPredicateFunctionObjectMaps

universe u v w k
variable {C : Type u} [Category.{k} C]
variable {D : Type v} [Category.{k} D]
variable {E : Type w} [Category.{k} E]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasEqualizers D]
variable [CartesianMonoidalCategory E] [MonoidalClosed E] [HasEqualizers E]

structure Map (source : Operations C) (target : Operations D) where
  predicates : InternalConjunctiveObject.Map source.predicates target.predicates
  finite : PreservesFiniteLimits predicates.functor
  closed : MonoidalClosedFunctor predicates.functor

attribute [instance] Map.finite Map.closed

namespace Map

variable {source : Operations C} {target : Operations D} {last : Operations E}
variable (mapping : Map source target)

abbrev functor : C ⥤ D := mapping.predicates.functor

theorem universal_image {before after : C} (route : before ⟶ after) :
    arrowImage mapping.predicates (source.universal route).operation =
      (target.universal (mapping.functor.map route)).operation :=
  InternalPredicateQuantifierMaps.universal_image mapping.predicates route target.laws
    (source.universal route) (target.universal (mapping.functor.map route))

theorem existential_image {before after : C} (route : before ⟶ after) :
    arrowImage mapping.predicates (source.existential route).operation =
      (target.existential (mapping.functor.map route)).operation :=
  InternalPredicateQuantifierMaps.existential_image mapping.predicates route target.laws
    (source.existential route) (target.existential (mapping.functor.map route))

theorem universal_square {before after : C} (route : before ⟶ after) :
    mapping.functor.map (source.universal route).operation ≫ (powerComparison mapping.predicates after).hom =
      (powerComparison mapping.predicates before).hom ≫
        (target.universal (mapping.functor.map route)).operation :=
  (arrowImage_after mapping.predicates (source.universal route).operation).symm.trans
    (congrArg (fun arrow => (powerComparison mapping.predicates before).hom ≫ arrow)
      (mapping.universal_image route))

theorem existential_square {before after : C} (route : before ⟶ after) :
    mapping.functor.map (source.existential route).operation ≫ (powerComparison mapping.predicates after).hom =
      (powerComparison mapping.predicates before).hom ≫
        (target.existential (mapping.functor.map route)).operation :=
  (arrowImage_after mapping.predicates (source.existential route).operation).symm.trans
    (congrArg (fun arrow => (powerComparison mapping.predicates before).hom ≫ arrow)
      (mapping.existential_image route))

theorem universal_section {before after parameter : C} (route : before ⟶ after)
    (predicate : parameter ⟶ power source.predicates before) :
    sectionImage mapping.predicates (predicate ≫ (source.universal route).operation) =
      sectionImage mapping.predicates predicate ≫
        (target.universal (mapping.functor.map route)).operation :=
  (arrowImage_section mapping.predicates predicate (source.universal route).operation).trans
    (congrArg (fun arrow => sectionImage mapping.predicates predicate ≫ arrow)
      (mapping.universal_image route))

theorem existential_section {before after parameter : C} (route : before ⟶ after)
    (predicate : parameter ⟶ power source.predicates before) :
    sectionImage mapping.predicates (predicate ≫ (source.existential route).operation) =
      sectionImage mapping.predicates predicate ≫
        (target.existential (mapping.functor.map route)).operation :=
  (arrowImage_section mapping.predicates predicate (source.existential route).operation).trans
    (congrArg (fun arrow => sectionImage mapping.predicates predicate ≫ arrow)
      (mapping.existential_image route))

def identity (source : Operations C) : Map source source where
  predicates := InternalConjunctiveObject.Map.identity source.predicates
  finite := by
    change PreservesFiniteLimits (𝟭 C)
    infer_instance
  closed := by
    change MonoidalClosedFunctor (𝟭 C)
    exact {
      comparison_iso value := by
        have (result : C) : IsIso ((expComparison (𝟭 C) value).natTrans.app result) := by
          rw [CartesianClosedFunctorCoherence.exponential_identity]
          exact IsIso.id ((ihom value).obj result)
        exact NatIso.isIso_of_isIso_app _ }

def comp (before : Map source target) (after : Map target last) : Map source last where
  predicates := InternalConjunctiveObject.Map.comp before.predicates after.predicates
  finite := comp_preservesFiniteLimits before.functor after.functor
  closed := CartesianClosedFunctorCoherence.closed_composition before.functor after.functor

theorem identity_functor (source : Operations C) : (identity source).functor = 𝟭 C := rfl

theorem comp_functor (before : Map source target) (after : Map target last) :
    (comp before after).functor = before.functor ⋙ after.functor := rfl

theorem powerComparison_identity (source : Operations C) (value : C) :
    powerComparison (identity source).predicates value = Iso.refl (power source.predicates value) := by
  apply Iso.ext
  change (expComparison (𝟭 C) value).natTrans.app source.predicates.proposition ≫
      (ihom value).map (𝟙 source.predicates.proposition) = 𝟙 (power source.predicates value)
  rw [CartesianClosedFunctorCoherence.exponential_identity, (ihom value).map_id]
  exact Category.id_comp _

theorem powerComparison_comp (before : Map source target) (after : Map target last) (value : C) :
    powerComparison (comp before after).predicates value =
      after.functor.mapIso (powerComparison before.predicates value) ≪≫
        powerComparison after.predicates (before.functor.obj value) := by
  apply Iso.ext
  change (expComparison (before.functor ⋙ after.functor) value).natTrans.app source.predicates.proposition ≫
      (ihom (after.functor.obj (before.functor.obj value))).map
        (after.functor.map before.predicates.proposition.hom ≫ after.predicates.proposition.hom) =
    after.functor.map ((expComparison before.functor value).natTrans.app source.predicates.proposition ≫
      (ihom (before.functor.obj value)).map before.predicates.proposition.hom) ≫
      ((expComparison after.functor (before.functor.obj value)).natTrans.app target.predicates.proposition ≫
        (ihom (after.functor.obj (before.functor.obj value))).map after.predicates.proposition.hom)
  rw [CartesianClosedFunctorCoherence.exponential_composition]
  simp only [Functor.map_comp, Category.assoc]
  have natural := (expComparison after.functor (before.functor.obj value)).natTrans.naturality
    before.predicates.proposition.hom
  change after.functor.map ((ihom (before.functor.obj value)).map before.predicates.proposition.hom) ≫
      (expComparison after.functor (before.functor.obj value)).natTrans.app target.predicates.proposition =
    (expComparison after.functor (before.functor.obj value)).natTrans.app
        (before.functor.obj source.predicates.proposition) ≫
      (ihom (after.functor.obj (before.functor.obj value))).map
        (after.functor.map before.predicates.proposition.hom) at natural
  simpa only [Category.assoc] using congrArg
    (fun arrow => after.functor.map ((expComparison before.functor value).natTrans.app
        source.predicates.proposition) ≫ arrow ≫
      (ihom (after.functor.obj (before.functor.obj value))).map after.predicates.proposition.hom)
    natural.symm

theorem sectionImage_identity {value parameter : C} (source : Operations C)
    (predicate : parameter ⟶ power source.predicates value) :
    sectionImage (identity source).predicates predicate = predicate := by
  change predicate ≫ (powerComparison (identity source).predicates value).hom = predicate
  rw [powerComparison_identity, Iso.refl_hom, Category.comp_id]

theorem sectionImage_comp (before : Map source target) (after : Map target last)
    {value parameter : C} (predicate : parameter ⟶ power source.predicates value) :
    sectionImage (comp before after).predicates predicate =
      sectionImage after.predicates (sectionImage before.predicates predicate) := by
  change after.functor.map (before.functor.map predicate) ≫
      (powerComparison (comp before after).predicates value).hom =
    after.functor.map (before.functor.map predicate ≫ (powerComparison before.predicates value).hom) ≫
      (powerComparison after.predicates (before.functor.obj value)).hom
  rw [powerComparison_comp, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

theorem arrowImage_comp (before : Map source target) (after : Map target last)
    {first second : C} (operation : power source.predicates first ⟶ power source.predicates second) :
    arrowImage (comp before after).predicates operation =
      arrowImage after.predicates (arrowImage before.predicates operation) := by
  simp only [InternalPredicateFunctionObjectMaps.arrowImage, powerComparison_comp,
    Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rfl

end Map

end Mettapedia.CategoryTheory.InternalPredicateQuantifiedObject
