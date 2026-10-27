import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorScan
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorControls

/-! Complete queued-state controls for one retained constructor inspection. -/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedConstructors.Controls

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts
open BagNormalForm.WithAuthoredEquations.AlgebraFocus.RecursiveView
open Retained RetainedWire
open InferenceCettaWire.AuthoredRule (typeTerm)

private abbrev valueType := ConstructorTyping.Controls.valueType
private abbrev atomRow := ConstructorTyping.Controls.atomRow
private abbrev boxRow := ConstructorTyping.Controls.constructorRow
private abbrev bagRow := ConstructorTyping.Controls.bagRow

def carrierRow : GrammarRule :=
  {label := "Parallel", category := "Value",
    params := [.simple "items" (.collection .hashBag valueType)],
    syntaxPattern := [.terminal "{",.nonTerminal "items",.terminal "}"],
    algebra? := some ⟨true,some "Zero"⟩}

def literalLabelRow : GrammarRule :=
  {boxRow with label := "if", evalPolicy? := some .rewrite}

def language : LanguageDef :=
  {name := "ConstructorScanControls", types := [⟨"Value",.ast⟩],
    terms := (List.range 9).map (fun index =>
      {label := "Unused" ++ toString index, category := "Value", params := [], syntaxPattern := []}) ++
      [boxRow,carrierRow,boxRow,atomRow,
        {label := "Zero", category := "Value", params := [], syntaxPattern := []},
        bagRow .wrapped,literalLabelRow],
    equations := [], rewrites := []}

def schemaContext := ConstructorTyping.Controls.schemaContext

def parameters : Parameters :=
  ⟨language,WellSorted.FreeTypeContext.ofList [],WellSorted.FreeTypeContext.ofList schemaContext,"Value","Zero"⟩

def atom : Pattern := .apply "Atom" []

def rootFocus : Focus := .original [] valueType (.apply "Box" [atom]) .hole

def boundFocus (bound : List TypeExpr) : Focus :=
  .original bound valueType (.apply "Box" [.bvar 0]) (.lambda (some "display") .hole)

def parent : Frame :=
  ⟨[4],[valueType],boundFocus [valueType],some 2,some ([[]],[])⟩

def continuation : Continuation .spelling :=
  .tail (.groups [valueType] [5] [valueType] 2 [.fvar "x"] [[]])
    (.application parent "Later" .done)

structure Control where
  name : String
  schemaBound : List TypeExpr := []
  focus : Focus := rootFocus
  label : String := "Box"
  schemas : List Pattern := [.fvar "x"]
  sources : List Pattern := [atom]
  outer : Option OneHoleContext := some .hole
  ordinal : Nat := 9
  remaining : List GrammarRule := [boxRow,carrierRow,boxRow]
  next : Continuation .spelling := .done
  children : Nat

def Control.task (control : Control) : Task :=
  .constructors control.schemaBound [3,1] control.focus control.label control.schemas control.sources
    control.outer control.ordinal control.remaining control.next

def Control.change (control : Control) : List Task × List Spelling := expand parameters control.task

def Control.callTerm (control : Control) : Term :=
  .application "gslt:collection-presentation:view-scan-constructors"
    [PremiseOperationsExecution.RestSchema.sortsTerm language,
      PremiseOperationsExecution.RestSchema.declarationsTerm language,
      PremiseOperationsExecution.RestSchema.freeTerm [],
      PremiseOperationsExecution.RestSchema.freeTerm schemaContext,
      .string parameters.category,taskTerm control.task]

def controls : List Control :=
  [{name := "ready-retains-rich-tail", children := 2},
   {name := "rejected-row-advances-to-duplicate", ordinal := 10,
     remaining := [carrierRow,boxRow], children := 1},
   {name := "duplicate-row-retains-original-index", ordinal := 11,
     remaining := language.terms.drop 11, children := 2},
   {name := "exhausted-scan", ordinal := language.terms.length, remaining := [], children := 0},
   {name := "distinct-bound-contexts", schemaBound := [valueType], focus := boundFocus [valueType],
     schemas := [.bvar 0], sources := [.bvar 0], outer := some (.lambda (some "display") .hole), children := 2},
   {name := "same-depth-wrong-schema-type", schemaBound := [.arrow valueType valueType], focus := boundFocus [valueType],
     schemas := [.bvar 0], sources := [.bvar 0], children := 1},
   {name := "same-depth-wrong-target-type", schemaBound := [valueType], focus := boundFocus [.arrow valueType valueType],
     schemas := [.bvar 0], sources := [.bvar 0], children := 1},
   {name := "missing-target-argument", sources := [], children := 1},
   {name := "excess-schema-arguments", schemas := [.fvar "x",.fvar "x"], children := 1},
   {name := "wrapped-bag-with-equal-occurrences", label := "BagBox", ordinal := 14,
     remaining := [bagRow .wrapped],
     schemas := [.collection .hashBag [] (some "rest")],
     sources := [.collection .hashBag [atom,atom] none], children := 2},
   {name := "bare-carrier-is-not-an-application", label := "Parallel", ordinal := 10,
     remaining := [carrierRow,boxRow],
     schemas := [.collection .hashBag [] (some "rest")],
     sources := [.collection .hashBag [atom,atom] none], children := 1},
   {name := "complete-dependent-continuation", next := continuation, children := 2},
   {name := "rejected-row-keeps-continuation", label := "Missing", next := continuation, children := 1},
   {name := "grouped-focus-keeps-physical-origin",
     focus := .grouped [] [⟨.apply "Box" [atom],[10],.collection .hashBag [] .hole [atom] none,.apply "Box" [atom]⟩],
     outer := some (.collection .hashBag [] .hole [atom] none), children := 2},
   {name := "literal-label-and-evaluation-metadata", label := "if", ordinal := 15,
     remaining := [literalLabelRow], children := 2},
   {name := "absent-outer-context-remains-absent", outer := none, children := 2}]

theorem declared_rows_retain_duplicate_indices :
    language.terms[9]? = some boxRow ∧ language.terms[10]? = some carrierRow ∧
      language.terms[11]? = some boxRow := by
  decide +kernel

theorem expected_children_and_no_publications :
    controls.all (fun control => control.change.1.length == control.children && control.change.2.isEmpty) = true := by
  decide +kernel

theorem successful_row_creates_original_ordinal_frame :
    (expand parameters (.constructors [] [3,1] rootFocus "Box" [.fvar "x"] [atom] (some .hole)
      9 [boxRow,carrierRow,boxRow] continuation)).1 =
    [.request (.arguments [] [3,1] rootFocus.bound "Box" (some .hole) [atom] 0 [.fvar "x"] [atom] boxRow.params)
      (.application ⟨[3,1],[],rootFocus,some 9,none⟩ "Box" continuation),
     .constructors [] [3,1] rootFocus "Box" [.fvar "x"] [atom] (some .hole)
       10 [carrierRow,boxRow] continuation] := by
  have ready : constructorReady parameters [] rootFocus "Box" [.fvar "x"] [atom] boxRow = true := by
    decide +kernel
  simp only [expand,ready,↓reduceIte]

#print axioms declared_rows_retain_duplicate_indices
#print axioms expected_children_and_no_publications
#print axioms successful_row_creates_original_ordinal_frame

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedConstructors.Controls
