import Mettapedia.CategoryTheory.ConjunctiveClosedTheory
import Mettapedia.CategoryTheory.InternalPredicateQuantifiedObjectMaps

/-!
# Closed theories with locally qualified quantifiers at every arrow

Each object has actual internal predicate function objects and both finite
quantifier qualifications. Morphisms are weak finite-limit closed maps with
their supplied conjunctive-object comparison. The canonical exponential
comparison and operation uniqueness derive quantifier preservation; no
additional whole-operation preservation condition is imposed.

The category retains all objects and takes classes of compatible natural
isomorphisms of the actual weak maps. Its forgetful functor remembers the
underlying conjunctive closed theory and the complete map class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core

universe k

structure QuantifiedClosedTheory where
  closed : LambdaTheory.{k,k}
  operations : InternalPredicateQuantifiedObject.Operations closed.Obj

namespace QuantifiedClosedTheory

def conjunctive (theory : QuantifiedClosedTheory.{k}) : ConjunctiveClosedTheory.{k} where
  closed := theory.closed
  operations := theory.operations.predicates
  laws := theory.operations.laws

abbrev Map (source target : QuantifiedClosedTheory.{k}) :=
  ConjunctiveClosedTheory.Map source.conjunctive target.conjunctive

abbrev MapIso {source target : QuantifiedClosedTheory.{k}} (first second : Map source target) :=
  ConjunctiveClosedTheory.MapIso first second

def Map.quantified {source target : QuantifiedClosedTheory.{k}} (mapping : Map source target) :
    InternalPredicateQuantifiedObject.Map source.operations target.operations where
  predicates := mapping.declarations
  finite := mapping.finite
  closed := mapping.closed

instance category : Category (QuantifiedClosedTheory.{k}) where
  Hom source target := source.conjunctive ⟶ target.conjunctive
  id source := 𝟙 source.conjunctive
  comp before after := before ≫ after
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

def classOf {source target : QuantifiedClosedTheory.{k}} (mapping : Map source target) : source ⟶ target :=
  ConjunctiveClosedTheory.classOf mapping

theorem classOf_equal_iff {source target : QuantifiedClosedTheory.{k}} (first second : Map source target) :
    classOf first = classOf second ↔ Nonempty (MapIso first second) :=
  ConjunctiveClosedTheory.classOf_equal_iff first second

def forget : QuantifiedClosedTheory.{k} ⥤ ConjunctiveClosedTheory.{k} where
  obj := conjunctive
  map mapping := mapping
  map_id _ := rfl
  map_comp _ _ := rfl

instance forget_faithful : forget.{k}.Faithful where
  map_injective same := same

instance forget_full : forget.{k}.Full where
  map_surjective arrow := ⟨arrow, rfl⟩

theorem every_weak_map_preserves_both_quantifiers
    {source target : QuantifiedClosedTheory.{k}} (mapping : Map source target)
    {before after : source.closed.Obj} (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage mapping.declarations
        (source.operations.universal route).operation =
      (target.operations.universal (mapping.functor.map route)).operation ∧
    InternalPredicateFunctionObjectMaps.arrowImage mapping.declarations
        (source.operations.existential route).operation =
      (target.operations.existential (mapping.functor.map route)).operation :=
  ⟨mapping.quantified.universal_image route, mapping.quantified.existential_image route⟩

theorem every_weak_map_retains_complete_function_sections
    {source target : QuantifiedClosedTheory.{k}} (mapping : Map source target)
    {before after parameter : source.closed.Obj} (route : before ⟶ after)
    (predicate : parameter ⟶ InternalPredicateFunctionObject.power source.operations.predicates before) :
    InternalPredicateFunctionObjectMaps.sectionImage mapping.declarations
        (predicate ≫ (source.operations.universal route).operation) =
      InternalPredicateFunctionObjectMaps.sectionImage mapping.declarations predicate ≫
        (target.operations.universal (mapping.functor.map route)).operation ∧
    InternalPredicateFunctionObjectMaps.sectionImage mapping.declarations
        (predicate ≫ (source.operations.existential route).operation) =
      InternalPredicateFunctionObjectMaps.sectionImage mapping.declarations predicate ≫
        (target.operations.existential (mapping.functor.map route)).operation :=
  ⟨mapping.quantified.universal_section route predicate, mapping.quantified.existential_section route predicate⟩

end QuantifiedClosedTheory

end Mettapedia.CategoryTheory
