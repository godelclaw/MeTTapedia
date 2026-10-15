import Mettapedia.CategoryTheory.InternalConjunctiveObjectMaps

/-!
# Predicate maps through an independent functor comparison

A natural isomorphism changes the underlying interpretation while retaining
the target predicate carrier. Naturality at truth, conjunction and both
projections earns the new primitive squares. No operation preservation is
added as a separate hypothesis for the new functor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalConjunctiveObject.Map

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CartesianMonoidalCategory

universe u v k l
variable {C : Type u} [Category.{k} C] [CartesianMonoidalCategory C]
variable {D : Type v} [Category.{l} D] [CartesianMonoidalCategory D]
variable {source : Operations C} {target : Operations D}
variable (mapping : Map source target) {next : C ⥤ D}
variable (comparison : mapping.functor ≅ next)

def ofFunctorIso : Map source target where
  functor := next
  proposition := (comparison.app source.proposition).symm ≪≫ mapping.proposition
  truth := by
    change next.map source.truth ≫
        (comparison.inv.app source.proposition ≫ mapping.proposition.hom) = _
    rw [← Category.assoc, comparison.inv.naturality, Category.assoc, mapping.truth,
      ← Category.assoc]
    exact congrArg (fun arrow => arrow ≫ target.truth) (Subsingleton.elim _ _)
  conjunction := by
    change next.map source.conjunction ≫
        (comparison.inv.app source.proposition ≫ mapping.proposition.hom) =
      lift
        (next.map (fst source.proposition source.proposition) ≫
          (comparison.inv.app source.proposition ≫ mapping.proposition.hom))
        (next.map (snd source.proposition source.proposition) ≫
          (comparison.inv.app source.proposition ≫ mapping.proposition.hom)) ≫ target.conjunction
    rw [← Category.assoc, comparison.inv.naturality, Category.assoc,
      mapping.conjunction, ← Category.assoc, comp_lift]
    simp only [← Category.assoc, ← comparison.inv.naturality]

theorem proposition_square :
    comparison.hom.app source.proposition ≫
        (ofFunctorIso mapping comparison).proposition.hom = mapping.proposition.hom := by
  change comparison.hom.app source.proposition ≫
    (comparison.inv.app source.proposition ≫ mapping.proposition.hom) = _
  rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

theorem complete_image {context : C} (predicate : source.Fiber context) :
    comparison.hom.app context ≫ (ofFunctorIso mapping comparison).image predicate =
      mapping.image predicate := by
  change comparison.hom.app context ≫
      (next.map predicate ≫ (comparison.inv.app source.proposition ≫ mapping.proposition.hom)) = _
  have natural := (comparison.hom.naturality predicate).symm
  rw [← Category.assoc, natural, Category.assoc,
    ← Category.assoc (comparison.hom.app source.proposition),
    Iso.hom_inv_id_app, Category.id_comp]
  rfl

end Mettapedia.CategoryTheory.InternalConjunctiveObject.Map
