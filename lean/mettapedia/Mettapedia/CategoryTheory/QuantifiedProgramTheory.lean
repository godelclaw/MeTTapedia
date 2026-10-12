import Mettapedia.CategoryTheory.ConjunctiveProgramTheory
import Mettapedia.CategoryTheory.QuantifiedClosedTheory

/-!
# Quantified program theories with complete operational maps

An object carries an actual program reduction theory and locally qualified
quantifiers at every arrow. Morphisms are the existing weak conjunctive
program maps, retaining both proposition and program comparisons and the
whole event arrow. Their quantifier action is derived from the local
predicate diagrams and closed comparisons.

The forgetful functor retains the complete conjunctive program theory.
Its fullness records earned uniqueness of quantifier operations, rather
than omission of an independent preservation obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory
open Mettapedia.GSLT.Core

universe k

structure QuantifiedProgramTheory where
  programTheory : ProgramReductionTheory.Theory.{k,k}
  operations : InternalPredicateQuantifiedObject.Operations programTheory.closed.Obj

namespace QuantifiedProgramTheory

def conjunctive (source : QuantifiedProgramTheory.{k}) : ConjunctiveProgramTheory.{k} where
  programTheory := source.programTheory
  operations := source.operations.predicates
  laws := source.operations.laws

def quantified (source : QuantifiedProgramTheory.{k}) : QuantifiedClosedTheory.{k} where
  closed := source.programTheory.closed
  operations := source.operations

abbrev Map (source target : QuantifiedProgramTheory.{k}) :=
  ConjunctiveProgramTheory.Map source.conjunctive target.conjunctive

abbrev MapIso {source target : QuantifiedProgramTheory.{k}} (first second : Map source target) :=
  ConjunctiveProgramTheory.MapIso first second

instance Map.finite {source target : QuantifiedProgramTheory.{k}} (mapping : Map source target) :
    _root_.CategoryTheory.Limits.PreservesFiniteLimits mapping.conjunctive.declarations.functor :=
  mapping.conjunctive.finite

instance Map.closed {source target : QuantifiedProgramTheory.{k}} (mapping : Map source target) :
    MonoidalClosedFunctor mapping.conjunctive.declarations.functor := mapping.conjunctive.closed

def Map.quantifierMap {source target : QuantifiedProgramTheory.{k}} (mapping : Map source target) :
    InternalPredicateQuantifiedObject.Map source.operations target.operations :=
  QuantifiedClosedTheory.Map.quantified (source := source.quantified) (target := target.quantified)
    mapping.conjunctive

theorem complete_universal_action {source target : QuantifiedProgramTheory.{k}}
    (mapping : Map source target) {before after : source.programTheory.closed.Obj} (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage mapping.conjunctive.declarations
        (source.operations.universal route).operation =
      (target.operations.universal (mapping.functor.map route)).operation :=
  mapping.quantifierMap.universal_image route

theorem complete_existential_action {source target : QuantifiedProgramTheory.{k}}
    (mapping : Map source target) {before after : source.programTheory.closed.Obj} (route : before ⟶ after) :
    InternalPredicateFunctionObjectMaps.arrowImage mapping.conjunctive.declarations
        (source.operations.existential route).operation =
      (target.operations.existential (mapping.functor.map route)).operation :=
  mapping.quantifierMap.existential_image route

instance category : Category (QuantifiedProgramTheory.{k}) where
  Hom source target := source.conjunctive ⟶ target.conjunctive
  id source := 𝟙 source.conjunctive
  comp before after := before ≫ after
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

def classOf {source target : QuantifiedProgramTheory.{k}} (mapping : Map source target) : source ⟶ target :=
  ConjunctiveProgramTheory.classOf mapping

theorem classOf_equal_iff {source target : QuantifiedProgramTheory.{k}} (first second : Map source target) :
    classOf first = classOf second ↔ Nonempty (MapIso first second) :=
  ConjunctiveProgramTheory.classOf_equal_iff first second

def forget : QuantifiedProgramTheory.{k} ⥤ ConjunctiveProgramTheory.{k} where
  obj := conjunctive
  map mapping := mapping
  map_id _ := rfl
  map_comp _ _ := rfl

instance forget_faithful : forget.{k}.Faithful where
  map_injective same := same

instance forget_full : forget.{k}.Full where
  map_surjective arrow := ⟨arrow, rfl⟩

end QuantifiedProgramTheory

end Mettapedia.CategoryTheory
