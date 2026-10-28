import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourceReader

/-! Reading a finite certificate and independently printing its constructed
Core term recovers the input. Rejection remains rejection, without evaluating
the retained source proof to manufacture output text. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceReader

open Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate
open Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter (stringScalars)

def readPrintScalars? (input : List Nat) (sort : String) (certificate : Certificate) : Option (List Nat) := do
  let reading ← readCertificate? input sort 0 input.length certificate
  CorePrinter.printScalars? sort reading.core

def readPrintText? (input : String) (sort : String) (certificate : Certificate) : Option String := do
  let reading ← readCertificate? (stringScalars input) sort 0 (stringScalars input).length certificate
  CorePrinter.printText? sort reading.core

theorem readPrintScalars?_exact (input : List Nat) (sort : String) (certificate : Certificate) :
    readPrintScalars? input sort certificate =
      if (readCertificate? input sort 0 input.length certificate).isSome then some input else none := by
  cases read : readCertificate? input sort 0 input.length certificate with
  | none => simp [readPrintScalars?, read]
  | some reading => simpa [readPrintScalars?, read] using reading.full_source

theorem readPrintText?_exact (input sort : String) (certificate : Certificate) :
    readPrintText? input sort certificate =
      if (readCertificate? (stringScalars input) sort 0 (stringScalars input).length certificate).isSome
      then some input else none := by
  cases read : readCertificate? (stringScalars input) sort 0 (stringScalars input).length certificate with
  | none => simp [readPrintText?, read]
  | some reading =>
    simp only [readPrintText?, read]
    change (CorePrinter.printScalars? sort reading.core).map
      (fun points => String.ofList (points.map Char.ofNat)) = some input
    rw [reading.full_source]
    simp only [Option.map_some]
    congr 1
    simp [stringScalars, List.map_map, Function.comp_def]

#print axioms readPrintScalars?_exact
#print axioms readPrintText?_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceReader
