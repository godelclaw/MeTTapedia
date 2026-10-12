import Mettapedia.CategoryTheory.RelativeClosedGeneratedPredicateSourceOperations
import Mettapedia.CategoryTheory.ConjunctiveClosedTheory
import Mettapedia.CategoryTheory.InternalPredicateImplicationMaps

/-!
# Predicate declarations through generated signature maps

A signature map can change the underlying base category as well as the
declared names. Its earned terminal and product comparisons give an actual
map of the internal conjunctive objects. The four finite laws and the three
implication diagrams transport through that map; no whole-context
preservation condition is supplied separately.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.SourceOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k
variable {C D : Type k} [Category.{k} C] [Category.{k} D]
variable {names nextNames : Symbols.{k}}
variable {original : Signature (C := C) (symbols := names)}
variable {next : Signature (C := D) (symbols := nextNames)}
variable (language : PredicateSyntax original)
variable (truth : RawHom (terminal original) language.proposition)
variable (mapping : SignatureMap original next)

def translatedMap : InternalConjunctiveObject.Map (operations language truth)
    (operations (language.translate mapping) (mapping.rawArrow truth)) where
  functor := mapping.functor
  proposition := Iso.refl _
  truth := by
    change mapping.functor.map (classOf truth) ≫ 𝟙 _ =
      CartesianMonoidalCategory.terminalComparison mapping.functor ≫ classOf (mapping.rawArrow truth)
    exact (Category.comp_id _).trans ((mapping.functor_classOf truth).trans
      ((congrArg (fun arrow => arrow ≫ classOf (mapping.rawArrow truth))
        mapping.terminalComparison_identity).trans (Category.id_comp _)).symm)
  conjunction := by
    change mapping.functor.map (classOf language.conjunction) ≫ 𝟙 _ =
      lift (mapping.functor.map (fst language.proposition language.proposition) ≫ 𝟙 _)
        (mapping.functor.map (snd language.proposition language.proposition) ≫ 𝟙 _) ≫
          classOf (mapping.rawArrow language.conjunction)
    simp only [Category.comp_id]
    change mapping.functor.map (classOf language.conjunction) =
      CartesianMonoidalCategory.prodComparison mapping.functor language.proposition language.proposition ≫
        classOf (mapping.rawArrow language.conjunction)
    exact (mapping.functor_classOf language.conjunction).trans
      ((congrArg (fun arrow => arrow ≫ classOf (mapping.rawArrow language.conjunction))
        (mapping.productComparison_identity language.proposition language.proposition)).trans
          (Category.id_comp _)).symm

instance translatedMap_finite : PreservesFiniteLimits (translatedMap language truth mapping).functor := by
  change PreservesFiniteLimits mapping.functor
  infer_instance

instance translatedMap_closed : MonoidalClosedFunctor (translatedMap language truth mapping).functor := by
  change MonoidalClosedFunctor mapping.functor
  infer_instance

theorem translated_laws_across_bases (laws : (operations language truth).Laws) :
    (operations (language.translate mapping) (mapping.rawArrow truth)).Laws where
  commutativity := by
    have complete := congrArg mapping.functor.map laws.commutativity
    simp only [InternalConjunctiveObject.Operations.swapBody, mapping.functor.map_comp,
      mapping.functor_lift] at complete
    exact complete
  associativity := by
    have complete := congrArg mapping.functor.map laws.associativity
    simp only [InternalConjunctiveObject.Operations.associateLeft,
      InternalConjunctiveObject.Operations.associateRight, mapping.functor.map_comp,
      mapping.functor_lift] at complete
    exact complete
  idempotence := by
    have complete := congrArg mapping.functor.map laws.idempotence
    simp only [InternalConjunctiveObject.Operations.diagonalBody, mapping.functor.map_comp,
      mapping.functor.map_id, mapping.functor_lift] at complete
    exact complete
  truthUnit := by
    have complete := congrArg mapping.functor.map laws.truthUnit
    simp only [InternalConjunctiveObject.Operations.truthUnitBody, mapping.functor.map_comp,
      mapping.functor.map_id, mapping.functor_lift, mapping.functor_toUnit] at complete
    exact complete

def closedTheory (laws : (operations language truth).Laws) : ConjunctiveClosedTheory.{k} where
  closed := Mettapedia.GSLT.Core.LambdaTheory.ofCategory (Object original)
  operations := operations language truth
  laws := laws

def translatedClosedMap (laws : (operations language truth).Laws) :
    ConjunctiveClosedTheory.Map (closedTheory language truth laws)
      (closedTheory (language.translate mapping) (mapping.rawArrow truth)
        (translated_laws_across_bases language truth mapping laws)) where
  declarations := translatedMap language truth mapping
  finite := inferInstanceAs (PreservesFiniteLimits mapping.functor)
  closed := inferInstanceAs (MonoidalClosedFunctor mapping.functor)

def translatedImplication (qualified : InternalPredicateImplication.Qualification
    (operations language truth)) : InternalPredicateImplication.Qualification
      (operations (language.translate mapping) (mapping.rawArrow truth)) :=
  InternalPredicateImplicationMaps.qualificationImage (translatedMap language truth mapping) qualified

theorem translated_family {context : Object original}
    (predicate : (operations language truth).Fiber context) :
    (translatedMap language truth mapping).image predicate = mapping.functor.map predicate :=
  Category.comp_id _

theorem translated_implication {context : Object original}
    (laws : (operations language truth).Laws)
    (qualified : InternalPredicateImplication.Qualification (operations language truth))
    (first second : (operations language truth).Fiber context) :
    (translatedMap language truth mapping).image
        (qualified.implies (operations language truth) first second) =
      (translatedImplication language truth mapping qualified).implies
        (operations (language.translate mapping) (mapping.rawArrow truth))
        ((translatedMap language truth mapping).image first)
        ((translatedMap language truth mapping).image second) :=
  InternalPredicateImplicationMaps.implication_supplied (translatedMap language truth mapping)
    (translated_laws_across_bases language truth mapping laws) qualified
    (translatedImplication language truth mapping qualified) first second

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.SourceOperations
