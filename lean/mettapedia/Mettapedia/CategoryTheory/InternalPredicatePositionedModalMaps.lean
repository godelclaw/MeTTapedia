import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObjectMaps
import Mettapedia.CategoryTheory.InternalPredicateImplicationFunctionMaps

/-!
# Complete positioned-modal operators under weak theory maps

The two supplied predicate functions remain independent. Their actual
instance maps form a conditional function; universal quantification binds
the complete instance context and existential quantification follows the
focus map. Finite-limit closed maps preserving the local truth/conjunction
data earn preservation of the entire operator and every supplied input.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicatePositionedModalMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalPredicateFunctionObject InternalPredicateFunctionObjectMaps

universe u v k
variable {C : Type u} [Category.{k} C] [CartesianMonoidalCategory C]
variable [MonoidalClosed C] [HasEqualizers C]

def condition (predicates : InternalConjunctiveObject.Operations C)
    (implication : InternalPredicateImplication.Qualification predicates)
    {instances assay outgoing parameter : C}
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)
    (relies : parameter ⟶ power predicates assay) (post : parameter ⟶ power predicates outgoing) :
    parameter ⟶ power predicates instances :=
  curry (implication.implies predicates
    (read predicates (relies ≫ InternalPredicateQuantifier.precomposition predicates instantiate))
    (read predicates (post ≫ InternalPredicateQuantifier.precomposition predicates reduct)))

theorem condition_read (predicates : InternalConjunctiveObject.Operations C)
    (implication : InternalPredicateImplication.Qualification predicates)
    {instances assay outgoing parameter : C}
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)
    (relies : parameter ⟶ power predicates assay) (post : parameter ⟶ power predicates outgoing) :
    read predicates (condition predicates implication instantiate reduct relies post) =
      implication.implies predicates
        (read predicates (relies ≫ InternalPredicateQuantifier.precomposition predicates instantiate))
        (read predicates (post ≫ InternalPredicateQuantifier.precomposition predicates reduct)) :=
  uncurry_curry _

theorem condition_substitution (predicates : InternalConjunctiveObject.Operations C)
    (implication : InternalPredicateImplication.Qualification predicates)
    {instances assay outgoing first second : C} (incoming : first ⟶ second)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)
    (relies : second ⟶ power predicates assay) (post : second ⟶ power predicates outgoing) :
    condition predicates implication instantiate reduct (incoming ≫ relies) (incoming ≫ post) =
      incoming ≫ condition predicates implication instantiate reduct relies post := by
  apply read_injective predicates
  have relyRead : read predicates ((incoming ≫ relies) ≫
      InternalPredicateQuantifier.precomposition predicates instantiate) =
      (instances ◁ incoming) ≫ read predicates
        (relies ≫ InternalPredicateQuantifier.precomposition predicates instantiate) :=
    (congrArg (read predicates) (Category.assoc incoming relies _)).trans
      (read_substitution predicates incoming _)
  have postRead : read predicates ((incoming ≫ post) ≫
      InternalPredicateQuantifier.precomposition predicates reduct) =
      (instances ◁ incoming) ≫ read predicates
        (post ≫ InternalPredicateQuantifier.precomposition predicates reduct) :=
    (congrArg (read predicates) (Category.assoc incoming post _)).trans
      (read_substitution predicates incoming _)
  exact (condition_read predicates implication instantiate reduct (incoming ≫ relies) (incoming ≫ post)).trans
    ((congrArg₂ (implication.implies predicates) relyRead postRead).trans
      ((implication.implies_substitution predicates (instances ◁ incoming) _ _).symm.trans
        ((read_substitution predicates incoming _).trans
          (congrArg (fun arrow => (instances ◁ incoming) ≫ arrow)
            (condition_read predicates implication instantiate reduct relies post))).symm))

abbrev profiles (predicates : InternalConjunctiveObject.Operations C) (assay outgoing : C) :=
  power predicates assay ⊗ power predicates outgoing

def conditionOperator (predicates : InternalConjunctiveObject.Operations C)
    (implication : InternalPredicateImplication.Qualification predicates)
    {instances assay outgoing : C} (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    profiles predicates assay outgoing ⟶ power predicates instances :=
  condition predicates implication instantiate reduct (fst _ _) (snd _ _)

def modalityOperator (quantified : InternalPredicateQuantifiedObject.Operations C)
    (implication : InternalPredicateImplication.Qualification quantified.predicates)
    {instances assignments assay carrier outgoing : C}
    (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    profiles quantified.predicates assay outgoing ⟶ power quantified.predicates carrier :=
  (conditionOperator quantified.predicates implication instantiate reduct ≫
    (quantified.universal forget).operation) ≫ (quantified.existential focus).operation

variable {D : Type v} [Category.{k} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasEqualizers D]
variable {source : InternalPredicateQuantifiedObject.Operations C}
variable {target : InternalPredicateQuantifiedObject.Operations D}
variable (mapping : InternalPredicateQuantifiedObject.Map source target)
variable (sourceImplication : InternalPredicateImplication.Qualification source.predicates)
variable (targetImplication : InternalPredicateImplication.Qualification target.predicates)

theorem precomposition_supplied_image {before after parameter : C} (route : before ⟶ after)
    (predicate : parameter ⟶ power source.predicates after) :
    sectionImage mapping.predicates
        (predicate ≫ InternalPredicateQuantifier.precomposition source.predicates route) =
      sectionImage mapping.predicates predicate ≫
        InternalPredicateQuantifier.precomposition target.predicates (mapping.functor.map route) :=
  (arrowImage_section mapping.predicates predicate _).trans
    (congrArg (fun operation => sectionImage mapping.predicates predicate ≫ operation)
      (InternalPredicateQuantifierMaps.arrowImage_precomposition mapping.predicates route))

theorem condition_supplied_image {instances assay outgoing parameter : C}
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)
    (relies : parameter ⟶ power source.predicates assay)
    (post : parameter ⟶ power source.predicates outgoing) :
    sectionImage mapping.predicates
        (condition source.predicates sourceImplication instantiate reduct relies post) =
      condition target.predicates targetImplication (mapping.functor.map instantiate)
        (mapping.functor.map reduct)
        (sectionImage mapping.predicates relies) (sectionImage mapping.predicates post) := by
  apply read_injective target.predicates
  rw [sectionImage_read, condition_read, condition_read]
  exact (InternalPredicateImplicationFunctionMaps.supplied_read mapping.predicates target.laws
    sourceImplication targetImplication
    (relies ≫ InternalPredicateQuantifier.precomposition source.predicates instantiate)
    (post ≫ InternalPredicateQuantifier.precomposition source.predicates reduct)).trans
      (congrArg₂ (targetImplication.implies target.predicates)
        (congrArg (read target.predicates) (precomposition_supplied_image mapping instantiate relies))
        (congrArg (read target.predicates) (precomposition_supplied_image mapping reduct post)))

def profilesComparison (assay outgoing : C) :
    mapping.functor.obj (profiles source.predicates assay outgoing) ≅
      profiles target.predicates (mapping.functor.obj assay) (mapping.functor.obj outgoing) :=
  asIso (CartesianMonoidalCategory.prodComparison mapping.functor _ _) ≪≫
    tensorIso (powerComparison mapping.predicates assay) (powerComparison mapping.predicates outgoing)

theorem profilesComparison_first (assay outgoing : C) :
    (profilesComparison mapping assay outgoing).hom ≫ fst _ _ =
      sectionImage mapping.predicates (fst (power source.predicates assay) (power source.predicates outgoing)) := by
  rw [profilesComparison, Iso.trans_hom, asIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_fst, ← Category.assoc, CartesianMonoidalCategory.prodComparison_fst]
  rfl

theorem profilesComparison_second (assay outgoing : C) :
    (profilesComparison mapping assay outgoing).hom ≫ snd _ _ =
      sectionImage mapping.predicates (snd (power source.predicates assay) (power source.predicates outgoing)) := by
  rw [profilesComparison, Iso.trans_hom, asIso_hom, tensorIso_hom, Category.assoc,
    tensorHom_snd, ← Category.assoc, CartesianMonoidalCategory.prodComparison_snd]
  rfl

theorem condition_square {instances assay outgoing : C}
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    mapping.functor.map (conditionOperator source.predicates sourceImplication instantiate reduct) ≫
        (powerComparison mapping.predicates instances).hom =
      (profilesComparison mapping assay outgoing).hom ≫
        conditionOperator target.predicates targetImplication
          (mapping.functor.map instantiate) (mapping.functor.map reduct) := by
  change sectionImage mapping.predicates
    (condition source.predicates sourceImplication instantiate reduct (fst _ _) (snd _ _)) = _
  exact (condition_supplied_image mapping sourceImplication targetImplication instantiate reduct _ _).trans
    ((congrArg₂ (condition target.predicates targetImplication
      (mapping.functor.map instantiate) (mapping.functor.map reduct))
      (profilesComparison_first mapping assay outgoing).symm
      (profilesComparison_second mapping assay outgoing).symm).trans
        (condition_substitution target.predicates targetImplication
          (profilesComparison mapping assay outgoing).hom
          (mapping.functor.map instantiate) (mapping.functor.map reduct) (fst _ _) (snd _ _)))

theorem modality_square {instances assignments assay carrier outgoing : C}
    (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing) :
    mapping.functor.map (modalityOperator source sourceImplication forget focus instantiate reduct) ≫
        (powerComparison mapping.predicates carrier).hom =
      (profilesComparison mapping assay outgoing).hom ≫
        modalityOperator target targetImplication (mapping.functor.map forget) (mapping.functor.map focus)
          (mapping.functor.map instantiate) (mapping.functor.map reduct) := by
  change sectionImage mapping.predicates
    ((conditionOperator source.predicates sourceImplication instantiate reduct ≫
      (source.universal forget).operation) ≫ (source.existential focus).operation) = _
  have completeCondition : sectionImage mapping.predicates
      (conditionOperator source.predicates sourceImplication instantiate reduct) =
      (profilesComparison mapping assay outgoing).hom ≫
        conditionOperator target.predicates targetImplication
          (mapping.functor.map instantiate) (mapping.functor.map reduct) :=
    condition_square mapping sourceImplication targetImplication instantiate reduct
  rw [mapping.existential_section, mapping.universal_section, completeCondition]
  simp only [modalityOperator, Category.assoc]

theorem modality_supplied_image {instances assignments assay carrier outgoing parameter : C}
    (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)
    (inputs : parameter ⟶ profiles source.predicates assay outgoing) :
    sectionImage mapping.predicates
        (inputs ≫ modalityOperator source sourceImplication forget focus instantiate reduct) =
      mapping.functor.map inputs ≫ (profilesComparison mapping assay outgoing).hom ≫
        modalityOperator target targetImplication (mapping.functor.map forget) (mapping.functor.map focus)
          (mapping.functor.map instantiate) (mapping.functor.map reduct) := by
  change mapping.functor.map (inputs ≫ modalityOperator source sourceImplication forget focus instantiate reduct) ≫
    (powerComparison mapping.predicates carrier).hom = _
  rw [mapping.functor.map_comp, Category.assoc]
  exact congrArg (fun arrow => mapping.functor.map inputs ≫ arrow)
    (modality_square mapping sourceImplication targetImplication forget focus instantiate reduct)

theorem modality_future_image {instances assignments assay carrier outgoing first second : C}
    (forget : instances ⟶ assignments) (focus : assignments ⟶ carrier)
    (instantiate : instances ⟶ assay) (reduct : instances ⟶ outgoing)
    (incoming : first ⟶ second) (inputs : second ⟶ profiles source.predicates assay outgoing) :
    sectionImage mapping.predicates
        ((incoming ≫ inputs) ≫ modalityOperator source sourceImplication forget focus instantiate reduct) =
      mapping.functor.map incoming ≫
        (mapping.functor.map inputs ≫ (profilesComparison mapping assay outgoing).hom ≫
          modalityOperator target targetImplication (mapping.functor.map forget) (mapping.functor.map focus)
            (mapping.functor.map instantiate) (mapping.functor.map reduct)) := by
  have complete := modality_supplied_image mapping sourceImplication targetImplication
    forget focus instantiate reduct (incoming ≫ inputs)
  exact complete.trans
    ((congrArg (fun arrow => arrow ≫ (profilesComparison mapping assay outgoing).hom ≫
      modalityOperator target targetImplication (mapping.functor.map forget) (mapping.functor.map focus)
        (mapping.functor.map instantiate) (mapping.functor.map reduct))
      (mapping.functor.map_comp incoming inputs)).trans
        (Category.assoc _ _ _))

end Mettapedia.CategoryTheory.InternalPredicatePositionedModalMaps
