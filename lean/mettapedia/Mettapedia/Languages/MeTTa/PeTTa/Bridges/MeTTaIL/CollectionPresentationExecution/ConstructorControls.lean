import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorRuntime

/-! Separating controls for constructor scopes, representation and membership. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorTyping.Controls

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL Syntax
open WellSorted
open BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView
open Eval

def valueType : TypeExpr := .base "Value"

def atomRow : GrammarRule :=
  {label := "Atom", category := "Value", params := [], syntaxPattern := []}

def constructorRow : GrammarRule :=
  {label := "Box", category := "Value", params := [.simple "value" valueType], syntaxPattern := []}

def bagRow (representation : CollectionRepresentation) : GrammarRule :=
  {label := "BagBox", category := "Value", params := [.simple "values" (.collection .hashBag valueType)],
    syntaxPattern := [], collectionRepresentation := representation}

def language : LanguageDef :=
  {name := "ConstructorControls", types := [⟨"Value",.ast⟩],
    terms := [atomRow,constructorRow,bagRow .wrapped], equations := [], rewrites := []}

def schemaContext : List (String × TypeExpr) :=
  [("x",valueType),("rest",.collection .hashBag valueType)]

def parameters : Retained.Parameters :=
  ⟨language,FreeTypeContext.ofList [],FreeTypeContext.ofList schemaContext,"Value","Zero"⟩

def focus (bound : List TypeExpr := []) : Focus :=
  .original bound valueType (.apply "Atom" []) .hole

theorem ordinary_constructor_ready :
    Retained.constructorReady parameters [] (focus []) "Box" [.fvar "x"] [.apply "Atom" []] constructorRow = true := by
  decide +kernel

theorem distinct_bound_contexts_ready :
    Retained.constructorReady parameters [valueType] (focus [valueType]) "Box" [.bvar 0] [.bvar 0] constructorRow = true := by
  decide +kernel

theorem same_depth_wrong_schema_type_refused :
    Retained.constructorReady parameters [.arrow valueType valueType] (focus [valueType])
      "Box" [.bvar 0] [.bvar 0] constructorRow = false := by
  decide +kernel

theorem same_depth_wrong_target_type_refused :
    Retained.constructorReady parameters [valueType] (focus [.arrow valueType valueType])
      "Box" [.bvar 0] [.bvar 0] constructorRow = false := by
  decide +kernel

theorem schema_environment_does_not_type_target :
    Retained.constructorReady parameters [] (focus []) "Box" [.fvar "x"] [.fvar "x"] constructorRow = false := by
  decide +kernel

theorem wrapped_and_bare_collections_differ :
    Retained.constructorReady parameters [] (focus []) "BagBox"
      [.collection .hashBag [] (some "rest")]
      [.collection .hashBag [.apply "Atom" [],.apply "Atom" []] none] (bagRow .wrapped) = true ∧
    Retained.constructorReady parameters [] (focus []) "BagBox"
      [.collection .hashBag [] (some "rest")]
      [.collection .hashBag [.apply "Atom" [],.apply "Atom" []] none] (bagRow .bare) = false := by
  decide +kernel

def undeclaredParameters : Retained.Parameters :=
  {parameters with language := {language with terms := [atomRow]}}

/-- A successful predicate cannot manufacture a declaration membership. -/
theorem readiness_does_not_grant_membership :
    Retained.constructorReady undeclaredParameters [] (focus []) "Box"
      [.fvar "x"] [.apply "Atom" []] constructorRow = true ∧
    constructorRow ∉ undeclaredParameters.language.terms := by
  decide +kernel

theorem undeclared_constructor_not_source_typed :
    ¬ WellSorted.HasType undeclaredParameters.language undeclaredParameters.free []
      (.apply "Box" [.apply "Atom" []]) valueType := by
  intro typed
  have checked := checkHasType_complete_of_object typed (by decide +kernel)
  change false = true at checked
  cases checked

theorem interpreted_success_has_both_source_typings (host : Effects.State)
    (completed : ∃ fuel, Eval.run interpretedRuntime fuel
      {state := host, control := .evaluate []
        (readyCall language [] schemaContext [] [] valueType "Box" [.fvar "x"] [.apply "Atom" []] constructorRow)} =
      .complete host [Effects.boolean true] [] []) :
    WellSorted.HasType language (FreeTypeContext.ofList []) [] (.apply "Box" [.apply "Atom" []]) valueType ∧
    RestAwareTyping.HasType language (FreeTypeContext.ofList schemaContext) [] (.apply "Box" [.fvar "x"]) valueType := by
  exact retained_true_source_typed interpretedRuntime interpreted_runtime_agreement host parameters
    [] schemaContext rfl rfl [] (focus []) "Box" [.fvar "x"] [.apply "Atom" []] constructorRow
    (by decide +kernel) completed

#print axioms wrapped_and_bare_collections_differ
#print axioms readiness_does_not_grant_membership
#print axioms undeclared_constructor_not_source_typed
#print axioms interpreted_success_has_both_source_typings

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorTyping.Controls
