import Mettapedia.CategoryTheory.RelativeClosedGeneratedPredicateMaps
import Mettapedia.CategoryTheory.InternalPredicateQuantifierMaps

/-!
# Complete function operations through an authored signature translation

An authored signature map preserves the chosen raw function objects. Its
canonical exponential comparison and proposition comparison are identities.
Consequently the whole quantifier image is the actual translated arrow,
including all function sections.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.SourceOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalClosed MonoidalCategory RelativeClosedSyntax GeneratedCategory
open InternalPredicateFunctionObjectMaps

universe k
variable {C D : Type k} [Category.{k} C] [Category.{k} D]
variable {names nextNames : Symbols.{k}}
variable {original : Signature (C := C) (symbols := names)}
variable {next : Signature (C := D) (symbols := nextNames)}
variable (language : PredicateSyntax original)
variable (truth : RawHom (terminal original) language.proposition)
variable (mapping : SignatureMap original next)

theorem translated_powerComparison_hom (value : Object original) :
    (powerComparison (translatedMap language truth mapping) value).hom =
      𝟙 (mapping.functor.obj (InternalPredicateFunctionObject.power (operations language truth) value)) := by
  change (expComparison mapping.functor value).natTrans.app language.proposition ≫
    (ihom (mapping.functor.obj value)).map (𝟙 _) = _
  rw [mapping.expComparison_identity, (ihom (mapping.functor.obj value)).map_id]
  exact Category.comp_id _

theorem translated_powerComparison_inv (value : Object original) :
    (powerComparison (translatedMap language truth mapping) value).inv =
      𝟙 (mapping.functor.obj (InternalPredicateFunctionObject.power (operations language truth) value)) := by
  change (powerComparison (translatedMap language truth mapping) value).inv = (Iso.refl _).inv
  exact congrArg Iso.inv (Iso.ext (translated_powerComparison_hom language truth mapping value))

theorem translated_operation {before after : Object original}
    (operation : InternalPredicateFunctionObject.power (operations language truth) before ⟶
      InternalPredicateFunctionObject.power (operations language truth) after) :
    arrowImage (translatedMap language truth mapping) operation = mapping.functor.map operation := by
  rw [arrowImage, translated_powerComparison_inv, translated_powerComparison_hom]
  change 𝟙 _ ≫ mapping.functor.map operation ≫ 𝟙 _ = mapping.functor.map operation
  exact (Category.id_comp _).trans (Category.comp_id _)

theorem translated_tupleComparison_hom :
    (InternalConjunctiveOrderComparison.tupleComparison
      (translatedMap language truth mapping)).hom =
      𝟙 (mapping.functor.obj (language.proposition ⊗ language.proposition)) := by
  change CartesianMonoidalCategory.prodComparison mapping.functor language.proposition language.proposition ≫
    (𝟙 (mapping.functor.obj language.proposition) ⊗ₘ 𝟙 (mapping.functor.obj language.proposition)) = _
  rw [mapping.productComparison_identity, tensorHom_id, id_whiskerRight]
  exact Category.comp_id _

theorem translated_tupleComparison_inv :
    (InternalConjunctiveOrderComparison.tupleComparison
      (translatedMap language truth mapping)).inv =
      𝟙 (mapping.functor.obj (language.proposition ⊗ language.proposition)) := by
  change (InternalConjunctiveOrderComparison.tupleComparison
    (translatedMap language truth mapping)).inv = (Iso.refl _).inv
  exact congrArg Iso.inv (Iso.ext (translated_tupleComparison_hom language truth mapping))

theorem translated_binary_operation
    (operation : language.proposition ⊗ language.proposition ⟶ language.proposition) :
    InternalPredicateImplicationMaps.operationImage (translatedMap language truth mapping) operation =
      mapping.functor.map operation := by
  rw [InternalPredicateImplicationMaps.operationImage, translated_tupleComparison_inv]
  change 𝟙 _ ≫ mapping.functor.map operation ≫ 𝟙 _ = mapping.functor.map operation
  exact (Category.id_comp _).trans (Category.comp_id _)

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.SourceOperations
