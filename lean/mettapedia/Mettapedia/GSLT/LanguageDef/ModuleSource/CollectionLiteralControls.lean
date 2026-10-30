import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-! Shared collection literals retain kind, order, rests and typed rule contexts
through the module reader and printer. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionLiteralControls

open Mettapedia.OSLF.MeTTaIL Syntax Match
open ModuleSource.Commands
open scoped ModuleSource.Commands
open scoped Mettapedia.OSLF.MeTTaIL.LanguageDefDSL

Module CollectionLiterals {
  Theory Collections() {
    Types { Item; }
    Rewrites {
      Bag . x:Item, tail:HashBag(Item) |- {x, ...tail} ~> {x, ...tail};
      Vector . x:Item, tail:Vec(Item) |- [x, ...tail] ~> [x, ...tail];
      Set . x:Item, tail:HashSet(Item) |- #{x, ...tail} ~> #{x, ...tail};
      VectorRest . tail:Vec(Item) |- [...tail] ~> [];
      SetRest . tail:HashSet(Item) |- #{...tail} ~> #{};
      Guard . xs:Vec(Item), ys:HashSet(Item) | forAll(xs, x, x # #{...tail})
        |- xs ~> ys;
    }
    Equations {
      SetEquality . xs:HashSet(Item), ys:HashSet(Item) |- xs = ys;
    }
  }
  theory Collections()
}

#module_roundtrip CollectionLiterals

Module CollectionWrappers {
  Theory Data() {
    Types { Item; BoxData; BagData; }
    Terms {
      Box . items:Vec(Item) |- "box" items : BoxData ![wrapped];
      Bag . items:HashBag(Item) |- "bag" items : BagData;
      Fold . items:Vec(Item), seed:Item |- "fold" items seed : Item ![fold] ![wrapped];
    }
  }
  theory Data()
}

#module_roundtrip CollectionWrappers

def wrapperLanguage : LanguageDef := CollectionWrappers.language.toOption.get (by decide)

theorem wrapper_is_authored :
    wrapperLanguage.terms.map (fun row => (row.collectionRepresentation, row.evalPolicy?)) =
      [(.wrapped,none),(.bare,none),(.wrapped,some .fold)] := by decide +kernel

theorem wrapper_typing_separates :
    let free := fun identifier => if identifier == "a" then some (TypeExpr.base "Item") else none
    WellSorted.checkHasType wrapperLanguage free []
        (.apply "Box" [.collection .vec [.fvar "a"] none]) (.base "BoxData") = true ∧
      WellSorted.checkHasType wrapperLanguage free []
        (.collection .vec [.fvar "a"] none) (.base "BoxData") = false ∧
      WellSorted.checkHasType wrapperLanguage free []
        (.collection .hashBag [.fvar "a"] none) (.base "BagData") = true ∧
      WellSorted.checkHasType wrapperLanguage free []
        (.apply "Bag" [.collection .hashBag [.fvar "a"] none]) (.base "BagData") = false := by
  decide +kernel

def language : LanguageDef := CollectionLiterals.language.toOption.get (by decide)

theorem read_kinds : (language.rewrites.take 3).map (·.left) =
    [.collection .hashBag [.fvar "x"] (some "tail"),
     .collection .vec [.fvar "x"] (some "tail"),
     .collection .hashSet [.fvar "x"] (some "tail")] := by decide +kernel

theorem read_rests : ((language.rewrites.drop 3).take 2).map (·.left) =
    [.collection .vec [] (some "tail"), .collection .hashSet [] (some "tail")] := by
  decide +kernel

theorem vector_order_matters :
    matchPattern (.collection .vec [.apply "A" [], .apply "B" []] none)
      (.collection .vec [.apply "B" [], .apply "A" []] none) = [] := by decide +kernel

theorem set_is_not_bag :
    matchPattern (.collection .hashSet [.fvar "x"] (some "tail"))
      (.collection .hashBag [.apply "A" []] none) = [] := by decide +kernel

theorem printed_freshness_retains_set :
    Printer.premise (.freshness ⟨"x", .collection .hashSet [] (some "tail")⟩) =
      "x # #{...tail}" := by
  simp only [Printer.premise, Printer.pattern]
  rfl

open Lean Elab Command in
elab "#check_collection_pattern " pattern:langDefPattern : command => do
  discard <| liftMacroM (Mettapedia.OSLF.MeTTaIL.LanguageDefDSL.expandPattern pattern)

/-- error: collection rest `...rest` may only appear once at the end of a collection pattern -/
#guard_msgs (error) in
#check_collection_pattern [...tail, x]

/-- error: collection rest `...rest` may only appear once at the end of a collection pattern -/
#guard_msgs (error) in
#check_collection_pattern #{...first, ...second}

#print axioms read_kinds
#print axioms read_rests
#print axioms vector_order_matters
#print axioms set_is_not_bag
#print axioms printed_freshness_retains_set
#print axioms wrapper_is_authored
#print axioms wrapper_typing_separates

end Mettapedia.GSLT.LanguageDef.ModuleSource.CollectionLiteralControls
