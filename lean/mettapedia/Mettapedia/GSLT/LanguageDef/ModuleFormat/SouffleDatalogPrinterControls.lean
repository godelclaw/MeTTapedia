import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourceViews
import Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter

/-! Retained source evidence for the actual authored Datalog grammar keeps
distinct numeric spellings. Semantic-program printing and native forest
certification are separate boundaries. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.PrinterControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing
open ParserProfileSemantics PresentationExprSemantics LanguageDefScalarSyntax LanguageDefScalarPrinter

open SourceViews

private instance (source : ParserProfileLayer) (className : String) (point : Nat) :
    Decidable (source.ClassEvidence className point) :=
  inferInstanceAs (Decidable (source.classAccepts? className point = some true))

theorem wrong_profile_not_source :
    lexicalPayload? ≠ some (Portable.lexicalData {profile with startSort := "Wrong"}) := by
  rw [profile_payload_exact]
  intro same
  have profiles := Portable.lexicalData_injective (Option.some.inj same)
  have wrong := congrArg ParserProfileLayer.startSort profiles
  have different : profile.startSort ≠ "Wrong" := by decide +kernel
  exact different wrong
def literalScalars? (text : String) : Option (List Nat) := some (stringScalars text)

def digitLeaf (point start : Nat) : CST :=
  .node "dl-lex:DlDigitScalar" start (start + 1) [.terminal [point] start (start + 1)]

def singleTree : CST :=
  .node "dl-src:integer-decimal" 0 1
    [.node "dl-src:digits-one" 0 1 [digitLeaf 49 0]]

def leadingZeroTree : CST :=
  .node "dl-src:integer-decimal" 0 2
    [.node "dl-src:digits-more" 0 2
      [digitLeaf 48 0, .node "dl-src:digits-one" 1 2 [digitLeaf 49 1]]]

def single : DerivesAt literalScalars? profile grammar [49] "DlInteger" 0 1 singleTree := by
  refine .structural ⟨55, by decide_cbv⟩ ?_
  refine .nonterminal (resultSort := "DlDigits") (middle := 1) (by decide_cbv) ?_ .nil
  refine .structural ⟨66, by decide_cbv⟩ ?_
  refine .nonterminal (resultSort := "DlDigitScalar") (middle := 1) (by decide_cbv) ?_ .nil
  exact .lexical ⟨3, by decide_cbv⟩ (by rfl) (by decide_cbv)

def leadingZero : DerivesAt literalScalars? profile grammar [48, 49] "DlInteger" 0 2 leadingZeroTree := by
  refine .structural ⟨55, by decide_cbv⟩ ?_
  refine .nonterminal (resultSort := "DlDigits") (middle := 2) (by decide_cbv) ?_ .nil
  refine .structural ⟨67, by decide_cbv⟩ ?_
  refine .nonterminal (resultSort := "DlDigitScalar") (middle := 1) (by decide_cbv) ?_ ?_
  · exact .lexical ⟨3, by decide_cbv⟩ (by rfl) (by decide_cbv)
  · refine .nonterminal (resultSort := "DlDigits") (middle := 2) (by decide_cbv) ?_ .nil
    refine .structural ⟨66, by decide_cbv⟩ ?_
    refine .nonterminal (resultSort := "DlDigitScalar") (middle := 2) (by decide_cbv) ?_ .nil
    exact .lexical ⟨3, by decide_cbv⟩ (by rfl) (by decide_cbv)

def decimalTree : CST :=
  .node "dl-src:float" 0 3
    [.node "dl-src:digits-one" 0 1 [digitLeaf 49 0],
     .node "dl-src:digits-one" 2 3 [digitLeaf 48 2]]

def decimal : DerivesAt literalScalars? profile grammar [49, 46, 48] "DlFloat" 0 3 decimalTree := by
  refine .structural ⟨64, by decide_cbv⟩ ?_
  refine .nonterminal (resultSort := "DlDigits") (middle := 1) (by decide_cbv) ?_ ?_
  · refine .structural ⟨66, by decide_cbv⟩ ?_
    refine .nonterminal (resultSort := "DlDigitScalar") (middle := 1) (by decide_cbv) ?_ .nil
    exact .lexical ⟨3, by decide_cbv⟩ (by rfl) (by decide_cbv)
  · refine .terminal (middle := 2) (codepoints := [46]) (by rfl) (.cons (by rfl) (.nil 2)) ?_
    refine .nonterminal (resultSort := "DlDigits") (middle := 3) (by decide_cbv) ?_ .nil
    refine .structural ⟨66, by decide_cbv⟩ ?_
    refine .nonterminal (resultSort := "DlDigitScalar") (middle := 3) (by decide_cbv) ?_ .nil
    exact .lexical ⟨3, by decide_cbv⟩ (by rfl) (by decide_cbv)

theorem actual_spelling_preserved :
    render single = [49] ∧ render leadingZero = [48, 49] ∧ render single ≠ render leadingZero := by
  decide +kernel

theorem actual_text_preserved :
    LanguageDefScalarPrinter.renderText (source := "1") single = "1" ∧
      LanguageDefScalarPrinter.renderText (source := "01") leadingZero = "01" := by
  exact ⟨full_text (source := "1") single, full_text (source := "01") leadingZero⟩

theorem declared_digit_class_refuses_letter : ¬ profile.ClassEvidence "Digit" 955 := by
  decide_cbv

theorem authored_punctuation_preserved :
    LanguageDefScalarPrinter.renderText (source := "1.0") decimal = "1.0" :=
  full_text (source := "1.0") decimal

theorem declared_string_class_keeps_unicode :
    profile.ClassEvidence "String" 955 ∧ profile.ClassEvidence "String" 128512 ∧
      ¬ profile.ClassEvidence "String" 34 := by
  decide +kernel

#print axioms actual_spelling_preserved
#print axioms actual_text_preserved
#print axioms declared_digit_class_refuses_letter
#print axioms grammar_exact
#print axioms profile_decode_exact
#print axioms authored_punctuation_preserved
#print axioms declared_string_class_keeps_unicode
#print axioms profile_source_exact
#print axioms wrong_profile_not_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.PrinterControls
