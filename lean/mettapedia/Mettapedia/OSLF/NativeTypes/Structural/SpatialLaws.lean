import Mettapedia.OSLF.NativeTypes.Structural.SpatialDeclarations

open Mettapedia.OSLF.Framework

/-!
# Separating laws for authored spatial formers

Commutativity comes from the declared hash-bag carrier. Association comes
from its checked flattening algebra. Both laws use typed, closed collection
introductions, including arbitrary ambient binder contexts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.ContextualStep

private theorem spatial_pair_typed {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {former : Former} {shape : SpatialShape}
    (member : former ∈ structuralFormers language)
    (checked : spatialShape? language former.declaration = some shape)
    {left right : Pattern}
    (leftTyped : HasType language free bound left (.base former.declaration.category))
    (rightTyped : HasType language free bound right (.base former.declaration.category)) :
    HasType language free bound (.collection .hashBag [left, right] none)
      (.base former.declaration.category) := by
  exact .collectionConstructor
    (List.mem_of_getElem? ((mem_structuralFormers_iff _ _).mp member))
    (by simpa only [GrammarRule.bareParams_of_bare _ (spatialShape?_bare checked)]
      using (spatialShape?_sound checked).1)
    (.cons leftTyped (.cons rightTyped (.nil bound _)))

private theorem spatial_pair_commutative {base : BasePremiseEvaluator} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {former : Former} {shape : SpatialShape}
    (member : former ∈ structuralFormers language)
    (checked : spatialShape? language former.declaration = some shape)
    {left right : Pattern}
    (leftTyped : HasType language free bound left (.base former.declaration.category))
    (rightTyped : HasType language free bound right (.base former.declaration.category)) :
    EquationEquiv base language (.collection .hashBag [left, right] none)
      (.collection .hashBag [right, left] none) := by
  apply derivedInstance_equivalent
  exact .bagPerm
    ⟨List.mem_of_getElem? ((mem_structuralFormers_iff _ _).mp member),
      shape.parameterName, .base former.declaration.category, (spatialShape?_sound checked).1⟩
    ⟨free, bound, spatial_pair_typed member checked leftTyped rightTyped⟩
    (List.Perm.swap right left [])

private theorem spatial_pair_associative {base : BasePremiseEvaluator} {language : LanguageDef}
    {free : FreeTypeContext} {bound : List TypeExpr} {former : Former} {shape : SpatialShape}
    (member : former ∈ structuralFormers language)
    (checked : spatialShape? language former.declaration = some shape)
    {first second third : Pattern}
    (firstTyped : HasType language free bound first (.base former.declaration.category))
    (secondTyped : HasType language free bound second (.base former.declaration.category))
    (thirdTyped : HasType language free bound third (.base former.declaration.category)) :
    EquationEquiv base language
      (.collection .hashBag [first, .collection .hashBag [second, third] none] none)
      (.collection .hashBag [.collection .hashBag [first, second] none, third] none) := by
  have algebra := spatialShape?_algebraRule member checked
  have flatten := (spatialShape?_sound checked).2.2.1
  have firstLaw : EquationEquiv base language
      (.collection .hashBag [first, .collection .hashBag [second, third] none] none)
      (.collection .hashBag [first, second, third] none) := by
    have witness : DerivedInstance language
        (.collection .hashBag ([first] ++ [.collection .hashBag [second, third] none]) none)
        (.collection .hashBag ([first] ++ [second, third] ++ []) none) :=
      .flatten (pre := [first]) (inner := [second, third]) (post := []) algebra flatten
        ⟨free, bound, spatial_pair_typed member checked firstTyped
          (spatial_pair_typed member checked secondTyped thirdTyped)⟩
    exact derivedInstance_equivalent witness
  have secondLaw : EquationEquiv base language
      (.collection .hashBag [.collection .hashBag [first, second] none, third] none)
      (.collection .hashBag [first, second, third] none) := by
    have witness : DerivedInstance language
        (.collection .hashBag ([] ++ .collection .hashBag [first, second] none :: [third]) none)
        (.collection .hashBag ([] ++ [first, second] ++ [third]) none) :=
      .flatten (pre := []) (inner := [first, second]) (post := [third]) algebra flatten
        ⟨free, bound, spatial_pair_typed member checked
          (spatial_pair_typed member checked firstTyped secondTyped) thirdTyped⟩
    exact derivedInstance_equivalent witness
  exact (equationSetoid base language).iseqv.trans firstLaw
    ((equationSetoid base language).iseqv.symm secondLaw)

/-- The actual bag representation gives the commutative separating reading. -/
theorem authored_spatial_commutative (base : BasePremiseEvaluator)
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr} (former : Former)
    (first second : Pattern → Prop) (term : Pattern) :
    SpatialHolds language free bound (EquationEquiv base language) former first second term ↔
      SpatialHolds language free bound (EquationEquiv base language) former second first term := by
  have forward : ∀ first second : Pattern → Prop,
      SpatialHolds language free bound (EquationEquiv base language) former first second term →
        SpatialHolds language free bound (EquationEquiv base language) former second first term := by
    intro first second
    rintro ⟨member, shape, checked, left, right, leftTyped, rightTyped, related, firstHolds, secondHolds⟩
    exact ⟨member, shape, checked, right, left, rightTyped, leftTyped,
      (equationSetoid base language).iseqv.trans related
        (spatial_pair_commutative member checked leftTyped rightTyped), secondHolds, firstHolds⟩
  exact ⟨forward first second, forward second first⟩

/-- Genuine association follows by flattening both typed presentations to the
same three-element bag; it never asserts equality of their parse trees. -/
theorem authored_spatial_associative (base : BasePremiseEvaluator)
    {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr} {former : Former}
    {shape : SpatialShape} (member : former ∈ structuralFormers language)
    (checked : spatialShape? language former.declaration = some shape)
    (first second third : Pattern → Prop) (term : Pattern) :
    SpatialHolds language free bound (EquationEquiv base language) former first
        (SpatialHolds language free bound (EquationEquiv base language) former second third) term ↔
      SpatialHolds language free bound (EquationEquiv base language) former
        (SpatialHolds language free bound (EquationEquiv base language) former first second) third term := by
  have laws := (equationSetoid base language).iseqv
  have congruent : ∀ left left' right right', EquationEquiv base language left left' →
      EquationEquiv base language right right' →
      EquationEquiv base language (.collection .hashBag [left, right] none)
        (.collection .hashBag [left', right'] none) := by
    intro left left' right right' first second
    exact equationEquiv_collection_of_forall₂ .hashBag none (.cons first (.cons second .nil))
  constructor
  · rintro ⟨_, _, _, left, remainder, leftTyped, _, outer, firstHolds, inner⟩
    obtain ⟨_, _, _, middle, right, middleTyped, rightTyped, innerEquation, secondHolds, thirdHolds⟩ := inner
    refine ⟨member, shape, checked, .collection .hashBag [left, middle] none, right,
      spatial_pair_typed member checked leftTyped middleTyped, rightTyped, ?_, ?_, thirdHolds⟩
    · exact laws.trans outer (laws.trans (congruent _ _ _ _ (laws.refl left) innerEquation)
        (spatial_pair_associative member checked leftTyped middleTyped rightTyped))
    · exact ⟨member, shape, checked, left, middle, leftTyped, middleTyped, laws.refl _,
        firstHolds, secondHolds⟩
  · rintro ⟨_, _, _, remainder, right, _, rightTyped, outer, inner, thirdHolds⟩
    obtain ⟨_, _, _, left, middle, leftTyped, middleTyped, innerEquation, firstHolds, secondHolds⟩ := inner
    refine ⟨member, shape, checked, left, .collection .hashBag [middle, right] none,
      leftTyped, spatial_pair_typed member checked middleTyped rightTyped, ?_, firstHolds, ?_⟩
    · exact laws.trans outer (laws.trans (congruent _ _ _ _ innerEquation (laws.refl right))
        (laws.symm (spatial_pair_associative member checked leftTyped middleTyped rightTyped)))
    · exact ⟨member, shape, checked, middle, right, middleTyped, rightTyped, laws.refl _,
        secondHolds, thirdHolds⟩

end Mettapedia.OSLF.NativeTypes.Structural
