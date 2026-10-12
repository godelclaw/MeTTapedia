import Mettapedia.CategoryTheory.InternalConjunctiveObjectMaps

/-!
# Reflecting finite conjunctive laws through a faithful interpretation

An actual declaration-preserving map sends whole generalized predicates,
truth and meet to their target values. Faithfulness and the retained
proposition isomorphism make that action injective. The four target finite
laws therefore reflect to their complete source diagrams. No source law
or whole-expression reflection premise is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalConjunctiveObject.Map

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory

universe u v k l
variable {C : Type u} [Category.{k} C] [CartesianMonoidalCategory C]
variable {D : Type v} [Category.{l} D] [CartesianMonoidalCategory D]
variable {source : Operations C} {target : Operations D}
variable (mapping : Map source target) [mapping.functor.Faithful]

theorem image_injective (context : C) : Function.Injective (mapping.image (context := context)) := by
  intro first second same
  apply mapping.functor.map_injective
  exact (cancel_mono mapping.proposition.hom).mp same

variable (targetLaws : target.Laws)

include mapping targetLaws

theorem reflect_meet_comm {context : C} (first second : source.Fiber context) :
    source.meet first second = source.meet second first := by
  apply mapping.image_injective context
  rw [mapping.image_meet, mapping.image_meet]
  exact Operations.meet_comm targetLaws _ _

theorem reflect_meet_assoc {context : C} (first second third : source.Fiber context) :
    source.meet (source.meet first second) third = source.meet first (source.meet second third) := by
  apply mapping.image_injective context
  simp only [mapping.image_meet]
  exact Operations.meet_assoc targetLaws _ _ _

theorem reflect_meet_idem {context : C} (predicate : source.Fiber context) :
    source.meet predicate predicate = predicate := by
  apply mapping.image_injective context
  rw [mapping.image_meet]
  exact Operations.meet_idem targetLaws _

theorem reflect_meet_top {context : C} (predicate : source.Fiber context) :
    source.meet predicate (source.top context) = predicate := by
  apply mapping.image_injective context
  rw [mapping.image_meet, mapping.image_top]
  exact Operations.meet_top targetLaws _

theorem reflects_laws : source.Laws where
  commutativity := by
    have complete := mapping.reflect_meet_comm targetLaws
      (snd source.proposition source.proposition) (fst source.proposition source.proposition)
    simpa only [Operations.meet, Operations.swapBody, lift_fst_snd, Category.id_comp] using complete
  associativity := by
    have complete := mapping.reflect_meet_assoc targetLaws
      (fst (source.proposition ⊗ source.proposition) source.proposition ≫
        fst source.proposition source.proposition)
      (fst (source.proposition ⊗ source.proposition) source.proposition ≫
        snd source.proposition source.proposition)
      (snd (source.proposition ⊗ source.proposition) source.proposition)
    simpa only [Operations.meet, Operations.associateLeft, Operations.associateRight,
      ← comp_lift, lift_fst_snd, Category.comp_id] using complete
  idempotence := mapping.reflect_meet_idem targetLaws (𝟙 source.proposition)
  truthUnit := mapping.reflect_meet_top targetLaws (𝟙 source.proposition)

end Mettapedia.CategoryTheory.InternalConjunctiveObject.Map
