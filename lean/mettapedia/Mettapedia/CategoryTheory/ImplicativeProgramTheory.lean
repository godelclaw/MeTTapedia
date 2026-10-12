import Mettapedia.CategoryTheory.QuantifiedProgramTheory
import Mettapedia.CategoryTheory.InternalPredicateImplicationMaps

/-!
# Implication-qualified program theories and complete quantification

The source objects carry conjunctive program theories and actual finite
implication qualifications. Complete targets additionally carry both
quantifiers at every arrow. The existing weak conjunctive program maps are
retained: their complete implication action follows from the two chosen
qualifications and operation uniqueness. Compatible map isomorphisms retain
both program and proposition readings and the derived event square.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe k

structure ImplicativeProgramTheory where
  conjunctive : ConjunctiveProgramTheory.{k}
  implication : InternalPredicateImplication.Qualification conjunctive.operations

namespace ImplicativeProgramTheory

abbrev Map (source target : ImplicativeProgramTheory.{k}) :=
  ConjunctiveProgramTheory.Map source.conjunctive target.conjunctive

abbrev MapIso {source target : ImplicativeProgramTheory.{k}} (first second : Map source target) :=
  ConjunctiveProgramTheory.MapIso first second

instance category : Category (ImplicativeProgramTheory.{k}) where
  Hom source target := source.conjunctive ⟶ target.conjunctive
  id source := 𝟙 source.conjunctive
  comp before after := before ≫ after
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

def classOf {source target : ImplicativeProgramTheory.{k}} (mapping : Map source target) : source ⟶ target :=
  ConjunctiveProgramTheory.classOf mapping

def forget : ImplicativeProgramTheory.{k} ⥤ ConjunctiveProgramTheory.{k} where
  obj := conjunctive
  map mapping := mapping
  map_id _ := rfl
  map_comp _ _ := rfl

variable {source target : ImplicativeProgramTheory.{k}} (mapping : Map source target)

local instance mapping_finite : PreservesFiniteLimits mapping.conjunctive.declarations.functor :=
  mapping.conjunctive.finite

local instance mapping_closed : MonoidalClosedFunctor mapping.conjunctive.declarations.functor :=
  mapping.conjunctive.closed

theorem implication_square :
    mapping.functor.map source.implication.operation ≫ mapping.conjunctive.declarations.proposition.hom =
      (InternalConjunctiveOrderComparison.tupleComparison mapping.conjunctive.declarations).hom ≫
        target.implication.operation :=
  InternalPredicateImplicationMaps.implication_square mapping.conjunctive.declarations
    target.conjunctive.laws source.implication target.implication

theorem complete_implication {context : source.conjunctive.closed.Obj}
    (first second : source.conjunctive.operations.Fiber context) :
    mapping.conjunctive.declarations.image
        (source.implication.implies source.conjunctive.operations first second) =
      target.implication.implies target.conjunctive.operations
        (mapping.conjunctive.declarations.image first) (mapping.conjunctive.declarations.image second) :=
  InternalPredicateImplicationMaps.implication_supplied mapping.conjunctive.declarations
    target.conjunctive.laws source.implication target.implication first second

end ImplicativeProgramTheory

structure QuantifiedImplicativeProgramTheory where
  quantified : QuantifiedProgramTheory.{k}
  implication : InternalPredicateImplication.Qualification quantified.operations.predicates

namespace QuantifiedImplicativeProgramTheory

def implicative (source : QuantifiedImplicativeProgramTheory.{k}) : ImplicativeProgramTheory.{k} where
  conjunctive := source.quantified.conjunctive
  implication := source.implication

abbrev Map (source target : QuantifiedImplicativeProgramTheory.{k}) :=
  QuantifiedProgramTheory.Map source.quantified target.quantified

abbrev MapIso {source target : QuantifiedImplicativeProgramTheory.{k}} (first second : Map source target) :=
  QuantifiedProgramTheory.MapIso first second

instance category : Category (QuantifiedImplicativeProgramTheory.{k}) where
  Hom source target := source.quantified ⟶ target.quantified
  id source := 𝟙 source.quantified
  comp before after := before ≫ after
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

def classOf {source target : QuantifiedImplicativeProgramTheory.{k}} (mapping : Map source target) : source ⟶ target :=
  QuantifiedProgramTheory.classOf mapping

def forget : QuantifiedImplicativeProgramTheory.{k} ⥤ ImplicativeProgramTheory.{k} where
  obj := implicative
  map mapping := mapping
  map_id _ := rfl
  map_comp _ _ := rfl

instance forget_faithful : forget.{k}.Faithful where
  map_injective same := same

instance forget_full : forget.{k}.Full where
  map_surjective arrow := ⟨arrow, rfl⟩

def forgetImplication : QuantifiedImplicativeProgramTheory.{k} ⥤ QuantifiedProgramTheory.{k} where
  obj := quantified
  map mapping := mapping
  map_id _ := rfl
  map_comp _ _ := rfl

theorem complete_implication {source target : QuantifiedImplicativeProgramTheory.{k}}
    (mapping : Map source target) {context : source.quantified.programTheory.closed.Obj}
    (first second : source.quantified.operations.predicates.Fiber context) :
    mapping.conjunctive.declarations.image
        (source.implication.implies source.quantified.operations.predicates first second) =
      target.implication.implies target.quantified.operations.predicates
        (mapping.conjunctive.declarations.image first) (mapping.conjunctive.declarations.image second) :=
  ImplicativeProgramTheory.complete_implication (source := source.implicative)
    (target := target.implicative) mapping first second

end QuantifiedImplicativeProgramTheory

end Mettapedia.CategoryTheory
