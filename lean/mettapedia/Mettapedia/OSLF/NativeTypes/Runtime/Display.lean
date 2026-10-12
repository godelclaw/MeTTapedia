import Mettapedia.OSLF.NativeTypes.Executable
import Mettapedia.OSLF.NativeTypes.Semantics.Display

open Mettapedia.OSLF.Framework

/-!
# Readable generated native judgments and retained receipt views

All catalogue entries come from the supplied generated driver. Answers and
receipts come from the public retained formula machine. The work account is
shared by its branches, and duplicate receipts remain separate rows. Settling
a query does not assert that its operational frontier was exhausted.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Runtime.Display

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Runtime.Description
open Mettapedia.OSLF.NativeTypes.Runtime (Installed)
open Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax (Query)
open Mettapedia.OSLF.NativeTypes.Semantics.Display (renderPattern renderStructural renderModal renderCheck renderAdmission)

def queryText : Query → String
  | .constructor name => name ++ "(top inputs)"
  | .top => "top"
  | .bottom => "bottom"
  | .conj first second => "(" ++ queryText first ++ " and " ++ queryText second ++ ")"
  | .disj first second => "(" ++ queryText first ++ " or " ++ queryText second ++ ")"
  | .neg inner => "not(" ++ queryText inner ++ ")"
  | .imp first second => "(" ++ queryText first ++ " implies " ++ queryText second ++ ")"
  | .possibility inner => "exists-next(" ++ queryText inner ++ ")"
  | .outgoingUniversal inner => "all-next(" ++ queryText inner ++ ")"

def readoutText : Mettapedia.OSLF.NativeTypes.Runtime.Description.Readout → String
  | .sourceRefused .outsideProfile => "refused: source outside the admitted profile"
  | .sourceRefused .illScopedOrSorted => "refused: source fails scope or sorting"
  | .judgment result => renderCheck result

def catalogue (driver : Driver) : String :=
  let generated := driver.generated
  let ruleNames := generated.snapshot.language.rewrites.zipIdx.map fun (rule, index) =>
    "#" ++ toString index ++ " " ++ rule.name
  let structural := generated.structuralCatalogue.map renderStructural
  let modal := generated.modalCatalogue.zipIdx.map fun (schema, index) =>
    renderModal (Mettapedia.OSLF.NativeTypes.Semantics.Display.modalView generated index schema)
  String.intercalate "\n" <|
    ["Language: " ++ generated.snapshot.language.name,
     "Authored rules: " ++ String.intercalate ", " ruleNames,
     "Authored equations: " ++ toString generated.snapshot.language.equations.length,
     "Selected profile: " ++ reprStr driver.profileContract ++ "; " ++ renderAdmission driver.profileAdmission,
     "Uniform equation-formation diagnostic: " ++ renderAdmission generated.equationAdmission,
     "Generated structural types: " ++ toString structural.length] ++
    structural.map ("  " ++ ·) ++
    ["Generated modal schemas: " ++ toString modal.length] ++ modal.map ("  " ++ ·)

def report (installed : Installed) (formula : installed.native.Formula)
    (source : Pattern) (budget : Nat) : String :=
  let actual := Mettapedia.OSLF.NativeTypes.Executable.search installed formula source budget
  let receiptLines := actual.observations.zipIdx.map fun (observation, ordinal) =>
    "  receipt " ++ toString ordinal ++ "; formula position=" ++ reprStr observation.location ++
      "; " ++ renderPattern (installed.native.render observation.source) ++ " -> " ++
      renderPattern (installed.native.render
        (installed.runtime.cursor.target observation.source observation.receipt))
  String.intercalate "\n" <|
    ["  source: " ++ renderPattern source,
     "  result: " ++ readoutText actual.readout ++
       "; budget=" ++ toString budget ++ "; work=" ++ toString actual.spent ++
       "; query settled=" ++ toString actual.settled,
     "  retained receipts=" ++ toString actual.observations.length] ++ receiptLines

def query (installed : Installed) (title : String) (question : Query) (source : Pattern) (budget : Nat) : String :=
  title ++ ": " ++ queryText question ++ "\n" ++
    match Mettapedia.OSLF.NativeTypes.Runtime.QuerySyntax.elaborate installed.native question with
    | .error name => "  refused: no constructor at this carrier named " ++ name
    | .ok formula => report installed formula source budget

end Mettapedia.OSLF.NativeTypes.Runtime.Display
