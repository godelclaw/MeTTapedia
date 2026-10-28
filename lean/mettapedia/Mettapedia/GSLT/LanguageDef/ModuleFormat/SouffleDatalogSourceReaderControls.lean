import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourceReadingPrinting
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterControls

/-! Raw scalar input and finite certificates reach closed Core terms, whose
independent printer preserves spelling. These controls do not constitute the
semantic ProgramData or complete native forest qualification. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceReader.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCertificate

def oneCertificate : Certificate := .structural 55 0 1
  (.nonterminal "DlDigits" 0 1
    (.structural 66 0 1 (.nonterminal "DlDigitScalar" 0 1
      (.lexical 3 (.class "Digit") 0 1) (.nil 1))) (.nil 1))

def leadingZeroCertificate : Certificate := .structural 55 0 2
  (.nonterminal "DlDigits" 0 2
    (.structural 67 0 2 (.nonterminal "DlDigitScalar" 0 1
      (.lexical 3 (.class "Digit") 0 1)
      (.nonterminal "DlDigits" 1 2
        (.structural 66 1 2 (.nonterminal "DlDigitScalar" 1 2
          (.lexical 3 (.class "Digit") 1 2) (.nil 2))) (.nil 2)))) (.nil 2))

def decimalCertificate : Certificate := .structural 64 0 3
  (.nonterminal "DlDigits" 0 1
    (.structural 66 0 1 (.nonterminal "DlDigitScalar" 0 1
      (.lexical 3 (.class "Digit") 0 1) (.nil 1)))
    (.terminal (.char 46) 1 2
      (.nonterminal "DlDigits" 2 3
        (.structural 66 2 3 (.nonterminal "DlDigitScalar" 2 3
          (.lexical 3 (.class "Digit") 2 3) (.nil 3))) (.nil 3))))

private def trivia (cursor : Nat) : Certificate := .structural 86 cursor cursor (.nil cursor)

private def children (row start stop : Nat)
    (items : List (String × Nat × Nat × Certificate)) : Certificate :=
  .structural row start stop (items.foldr (fun (sort, before, after, child) tail =>
    .nonterminal sort before after child tail) (.nil stop))

/-- An ordinary complete program is a source-syntax control. Static
declaration checking remains a separate operation. -/
def programCertificate : Certificate :=
  let identifier := children 51 0 1
    [("DlSingleIdentifierScalar", 0, 1, .lexical 0 (.class "IdentifierSingle") 0 1)]
  let relation := children 49 0 1 [("DlIdentifier", 0, 1, identifier)]
  let digits := children 66 2 3 [("DlDigitScalar", 2, 3, .lexical 3 (.class "Digit") 2 3)]
  let integer := children 55 2 3 [("DlDigits", 2, 3, digits)]
  let constant := children 46 2 3 [("DlInteger", 2, 3, integer)]
  let constants := children 40 2 3 [("DlConstant", 2, 3, constant), ("DlTrivia", 3, 3, trivia 3)]
  let ground := Certificate.structural 35 0 4
    (.nonterminal "DlQualifiedName" 0 1 relation
      (.nonterminal "DlTrivia" 1 1 (trivia 1)
        (.terminal (.char 40) 1 2
          (.nonterminal "DlTrivia" 2 2 (trivia 2)
            (.nonterminal "DlConstants" 2 3 constants
              (.terminal (.char 41) 3 4 (.nil 4)))))))
  let fact := Certificate.structural 21 0 5
    (.nonterminal "DlGroundAtom" 0 4 ground
      (.nonterminal "DlTrivia" 4 4 (trivia 4) (.terminal (.char 46) 4 5 (.nil 5))))
  let item := children 4 0 5 [("DlFact", 0, 5, fact)]
  let tail := children 1 5 5 []
  let items := children 2 0 5 [("DlItem", 0, 5, item), ("DlTrivia", 5, 5, trivia 5), ("DlItems", 5, 5, tail)]
  children 0 0 5 [("DlTrivia", 0, 0, trivia 0), ("DlItems", 0, 5, items)]

private def readAndPrint (input : List Nat) (sort : String) (certificate : Certificate) : Option String :=
  (readPrintScalars? input sort certificate).map fun points => String.ofList (points.map Char.ofNat)

theorem scalar_input_to_core_and_back :
    readAndPrint [49] "DlInteger" oneCertificate = some "1" ∧
      readAndPrint [48,49] "DlInteger" leadingZeroCertificate = some "01" ∧
      readAndPrint [49,46,48] "DlFloat" decimalCertificate = some "1.0" := by
  simp only [readAndPrint, readPrintScalars?_exact]
  decide +kernel

#guard readAndPrint [49] "DlInteger" oneCertificate == some "1"
#guard readAndPrint [48,49] "DlInteger" leadingZeroCertificate == some "01"
#guard readAndPrint [49,46,48] "DlFloat" decimalCertificate == some "1.0"

theorem whole_program_syntax_round_trip :
    readPrintText? "p(1)." "DlProgram" programCertificate = some "p(1)." ∧
      (readProgramCertificate? [112,40,49,41,46] programCertificate).isSome = true ∧
      (readProgramCertificate? [112,40,49,41,46,46] programCertificate).isSome = false := by
  rw [readPrintText?_exact]
  decide +kernel

#guard readPrintText? "p(1)." "DlProgram" programCertificate == some "p(1)."

theorem exact_input_and_sort_are_checked :
    (readCertificate? [48] "DlInteger" 0 1 oneCertificate).isSome = true ∧
      (readCertificate? [955] "DlInteger" 0 1 oneCertificate).isSome = false ∧
      (readCertificate? [49] "DlFloat" 0 1 oneCertificate).isSome = false ∧
      (readCertificate? [49,49] "DlInteger" 0 2 oneCertificate).isSome = false ∧
      (readCertificate? [] "DlInteger" 0 1 oneCertificate).isSome = false := by
  decide +kernel

theorem source_reification_retains_distinct_spellings :
    SourceToCore.reify PrinterControls.single ≠ SourceToCore.reify PrinterControls.leadingZero := by
  decide +kernel

theorem source_evidence_has_a_checked_reading :
    ∃ (certificate : Certificate) (reading : Reading [49] "DlInteger" 0 1),
      readCertificate? [49] "DlInteger" 0 1 certificate = some reading ∧
      reading.tree = PrinterControls.singleTree ∧
      reading.core = SourceToCore.reify PrinterControls.single :=
  source_has_reading PrinterControls.single

theorem malformed_core_constructors_are_refused :
    CorePrinter.printText? "DlInteger" (.apply "dl-src:integer-decimal" []) = none ∧
      CorePrinter.printText? "DlInteger" (.apply "Wrong" []) = none ∧
      CorePrinter.printText? "DlDigitScalar" (ScalarCore.wordLeaf ⟨3, by decide⟩ 955) = none := by
  decide_cbv

theorem raw_cst_reification_is_not_source_authority :
    CSTToCore.lower? "DlFloat"
      (.node "dl-src:float" 0 3
        [.node "dl-src:digits-one" 0 1 [PrinterControls.digitLeaf 49 0],
         .node "dl-src:digits-one" 2 3 [PrinterControls.digitLeaf 48 2]]) =
      some (SourceToCore.reify PrinterControls.decimal) ∧
      (readCertificate? [49,47,48] "DlFloat" 0 3 decimalCertificate).isSome = false := by
  constructor
  · exact CSTToCore.lower_source PrinterControls.decimal
  · decide +kernel

#print axioms scalar_input_to_core_and_back
#print axioms whole_program_syntax_round_trip
#print axioms exact_input_and_sort_are_checked
#print axioms source_evidence_has_a_checked_reading
#print axioms raw_cst_reification_is_not_source_authority

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceReader.Controls
