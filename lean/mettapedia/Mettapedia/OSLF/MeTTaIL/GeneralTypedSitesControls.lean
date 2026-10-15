import Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesGenerator
import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceReplacement

/-!
# Typed site generation controls

The examples distinguish authored typing alternatives, exact nested binder
sorts, duplicate collection positions, operational permissions, and binding
representation constraints. They exercise the generic construction directly.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

private def typeA : TypeExpr := .base "A"
private def typeB : TypeExpr := .base "B"
private def typeC : TypeExpr := .base "C"
private def resultType : TypeExpr := .base "Result"

private def bodyRule : GrammarRule :=
  { label := "Body", category := "B", params := [], syntaxPattern := [] }
private def wrapA : GrammarRule :=
  { label := "Wrap", category := "Result",
    params := [.abstractionNamed none "body" (.arrow typeA typeB)], syntaxPattern := [] }
private def wrapC : GrammarRule :=
  { label := "Wrap", category := "Result",
    params := [.abstractionNamed none "body" (.arrow typeC typeB)], syntaxPattern := [] }
private def nestedRule : GrammarRule :=
  { label := "Nested", category := "Result",
    params := [.abstractionNamed none "body"
      (.arrow typeA (.arrow (.multiBinder typeC) typeB))], syntaxPattern := [] }

private def language : LanguageDef where
  name := "TypedSiteControls"
  types := []
  terms := [bodyRule, wrapA, wrapC, nestedRule]
  equations := []
  rewrites := []

private def body : Pattern := .apply "Body" []
private def source : Pattern := .apply "Wrap" [.lambda none body]

private theorem body_typed (bound : List TypeExpr) :
    HasType language FreeTypeContext.empty bound body typeB :=
  .constructor (rule := bodyRule) (by simp [language])
    (by simp [UsesBareCollection, bodyRule]) .nil

private def bodyA : SiteData :=
  (SiteData.here [typeA] typeB body).wrapLambda none typeA |>.wrapApplication 1 "Wrap" [.lambda none body] 0

private def bodyC : SiteData :=
  (SiteData.here [typeC] typeB body).wrapLambda none typeC |>.wrapApplication 2 "Wrap" [.lambda none body] 0

private theorem bodyA_generated :
    bodyA ∈ generate language FreeTypeContext.empty .all [] resultType source := by
  apply generate_complete
  exact .application (rule := wrapA) (by decide)
    (by simp [UsesBareCollection, wrapA])
    (.cons (by trivial) rfl (.lambda (body_typed [typeA])) .nil)
    rfl rfl rfl rfl (.inl rfl) (.lambda rfl (.here rfl rfl (body_typed [typeA])))

private theorem bodyC_generated :
    bodyC ∈ generate language FreeTypeContext.empty .all [] resultType source := by
  apply generate_complete
  exact .application (rule := wrapC) (by decide)
    (by simp [UsesBareCollection, wrapC])
    (.cons (by trivial) rfl (.lambda (body_typed [typeC])) .nil)
    rfl rfl rfl rfl (.inl rfl) (.lambda rfl (.here rfl rfl (body_typed [typeC])))

/-- The same source address and result sort retains both valid bound sorts. -/
theorem both_binder_alternatives :
    bodyA ∈ generate language FreeTypeContext.empty .all [] resultType source ∧
    bodyC ∈ generate language FreeTypeContext.empty .all [] resultType source ∧
    bodyA.address = bodyC.address ∧ bodyA.context = bodyC.context ∧
    bodyA.focusBound ≠ bodyC.focusBound ∧ bodyA.typingFrames ≠ bodyC.typingFrames := by
  exact ⟨bodyA_generated, bodyC_generated, rfl, rfl, by decide, by decide⟩

private def nestedSource : Pattern := .apply "Nested" [.lambda none (.multiLambda 2 [] body)]

private def nestedBody : SiteData :=
  (SiteData.here [typeC, typeC, typeA] typeB body).wrapMultiLambda 2 [] typeC |>.wrapLambda none typeA
    |>.wrapApplication 3 "Nested" [.lambda none (.multiLambda 2 [] body)] 0

theorem exact_nested_binder_sorts :
    nestedBody ∈ generate language FreeTypeContext.empty .all [] resultType nestedSource ∧
    nestedBody.focusBound = [typeC, typeC, typeA] ∧ nestedBody.address = [0, 0, 0] := by
  refine ⟨generate_complete ?_, rfl, rfl⟩
  exact .application (rule := nestedRule) (by decide)
    (by simp [UsesBareCollection, nestedRule])
    (.cons (by trivial) rfl (.lambda (.multiLambda (body_typed [typeC, typeC, typeA]))) .nil)
    rfl rfl rfl rfl (.inl rfl)
    (.lambda rfl (.multiLambda rfl (.here rfl rfl (body_typed [typeC, typeC, typeA]))))

private def collectionSource : Pattern := .collection .hashBag [body, body] none
private def firstElement : SiteData :=
  (SiteData.here [] typeB body).wrapCollection (.directCollection .hashBag) .hashBag [body, body] 0
private def secondElement : SiteData :=
  (SiteData.here [] typeB body).wrapCollection (.directCollection .hashBag) .hashBag [body, body] 1

theorem duplicate_collection_positions :
    firstElement ∈ generate language FreeTypeContext.empty .all [] (.collection .hashBag typeB) collectionSource ∧
    secondElement ∈ generate language FreeTypeContext.empty .all [] (.collection .hashBag typeB) collectionSource ∧
    firstElement.focus = secondElement.focus ∧ firstElement.address ≠ secondElement.address := by
  have typed : ElementsHaveType language FreeTypeContext.empty [] [body, body] typeB :=
    .cons (body_typed []) (.cons (body_typed []) (.nil [] typeB))
  have first := generate_complete
    (Licensed.directCollection (permissions := .all) (kind := .hashBag) (index := 0) (by decide) typed rfl rfl
      (.here rfl rfl (body_typed [])))
  have second := generate_complete
    (Licensed.directCollection (permissions := .all) (kind := .hashBag) (index := 1) (by decide) typed rfl rfl
      (.here rfl rfl (body_typed [])))
  exact ⟨first, second, rfl, by decide⟩

theorem permissions_affect_actual_generation :
    generate language FreeTypeContext.empty .rootOnly [] resultType source =
      [SiteData.here [] resultType source] ∧
    bodyA ∉ generate language FreeTypeContext.empty .rootOnly [] resultType source ∧
    bodyA ∈ generate language FreeTypeContext.empty .all [] resultType source ∧
    generate language FreeTypeContext.empty .stopped [] resultType source = [] := by
  have typed : HasType language FreeTypeContext.empty [] source resultType :=
    .constructor (rule := wrapA) (by simp [language])
      (by simp [UsesBareCollection, wrapA])
      (.cons (by trivial) rfl (.lambda (body_typed [typeA])) .nil)
  have sourceObject : isObjectPattern source = true := rfl
  have rootGenerated : generate language FreeTypeContext.empty .rootOnly [] resultType source =
      [SiteData.here [] resultType source] := by
    rw [generate_rootOnly, if_pos ⟨sourceObject, checkHasType_complete_of_object typed sourceObject⟩]
  exact ⟨rootGenerated, by rw [rootGenerated]; decide, bodyA_generated, generate_stopped _ _ _ _ _⟩

private def argumentA : SiteData :=
  (SiteData.here [] (.arrow typeA typeB) (.lambda none body)).wrapApplication 1 "Wrap" [.lambda none body] 0

private def arrowVariable : FreeTypeContext := fun name =>
  if name = "function" then some (.arrow typeA typeB) else none

/-- Equal type does not authorize dropping the required binding representation. -/
theorem abstraction_replacement_rejected :
    checkHasType language arrowVariable [] (.fvar "function") (.arrow typeA typeB) = true ∧
    argumentA.acceptsReplacementRepresentation language (.fvar "function") = false ∧
    argumentA.acceptsReplacementRepresentation language (.lambda none body) = true ∧
    bodyA.acceptsReplacementRepresentation language body = true := by
  decide

end Mettapedia.OSLF.MeTTaIL.GeneralTypedSitesControls
