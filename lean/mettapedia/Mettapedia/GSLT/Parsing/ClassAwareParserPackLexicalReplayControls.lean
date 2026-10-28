import Mettapedia.GSLT.Parsing.ClassAwareParserPackLexicalReplay

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareParserPackLexicalReplay.Controls

open ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate

private def profile : ParserProfileLayer where
  name := "LexicalReplayControls"
  startSort := "Scalar"
  classes := [⟨"lambda", .points [955]⟩]
  states := [⟨"Scalar", "lambda", "leaf"⟩, ⟨"Scalar", "lambda", "leaf"⟩]

private def plan : CompiledParserPackPlan := ⟨compileLexicalPack profile, []⟩

theorem consuming_matchers_and_eof :
    (replayTerminal? profile [955] .any 0 1).isSome = true ∧
      (replayTerminal? profile [955] (.char 955) 0 1).isSome = true ∧
      (replayTerminal? profile [955] (.class "lambda") 0 1).isSome = true ∧
      (replayTerminal? profile [955] .eof 1 1).isSome = true ∧
      (replayTerminal? profile [] .eof 0 0).isSome = true := by
  decide +kernel

theorem wrong_payload_span_and_class_refused :
    (replayTerminal? profile [955] (.char 65) 0 1).isSome = false ∧
      (replayTerminal? profile [955] (.class "missing") 0 1).isSome = false ∧
      (replayTerminal? profile [65] (.class "lambda") 0 1).isSome = false ∧
      (replayTerminal? profile [955] .any 0 0).isSome = false ∧
      (replayTerminal? profile [955] .any 0 2).isSome = false ∧
      (replayTerminal? profile [955] .any 1 2).isSome = false ∧
      (replayTerminal? profile [955] .eof 0 0).isSome = false ∧
      (replayTerminal? profile [955] .eof 1 2).isSome = false := by
  decide +kernel

theorem physical_production_occurrences_survive :
    (replayLexical? profile plan [955] 0 (.class "lambda") 0 1).isSome = true ∧
      (replayLexical? profile plan [955] 1 (.class "lambda") 0 1).isSome = true ∧
      Certificate.lexical 0 (.class "lambda") 0 1 ≠ Certificate.lexical 1 (.class "lambda") 0 1 := by
  decide +kernel

theorem corrupted_production_identity_refused :
    (replayLexical? profile plan [955] 2 (.class "lambda") 0 1).isSome = false ∧
      (replayLexical? profile plan [955] 0 .any 0 1).isSome = false ∧
      (replayLexical? profile plan [955] 0 (.char 955) 0 1).isSome = false := by
  decide +kernel

#print axioms consuming_matchers_and_eof
#print axioms wrong_payload_span_and_class_refused
#print axioms physical_production_occurrences_survive
#print axioms corrupted_production_identity_refused

end Mettapedia.GSLT.Parsing.ClassAwareParserPackLexicalReplay.Controls
