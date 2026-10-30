import Mettapedia.GSLT.Parsing.ClassAwareParserPackReplay

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareParserPackReplay.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate

private def profile : ParserProfileLayer where
  name := "StructuralReplayControls"
  startSort := "Expression"
  classes := [⟨"lambda", .points [955]⟩]
  states := [⟨"Scalar", "lambda", "leaf"⟩]

private def sourceRow : GrammarRule where
  label := "Wrapped"
  category := "Expression"
  params := [.simple "body" (.base "Scalar")]
  syntaxPattern := [.terminal "(", .nonTerminal "body", .terminal ")"]

private def plan : CompiledParserPackPlan where
  lexical := compileLexicalPack profile
  structural := [
    ⟨"Wrapped", "Expression", [.terminal (.char 40), .nonterminal "Scalar",
      .terminal (.char 41), .terminal .eof], [1], sourceRow⟩]

private def certificate : Certificate := .structural 0 0 3
  (.terminal (.char 40) 0 1
    (.nonterminal "Scalar" 1 2 (.lexical 0 (.class "lambda") 1 2)
      (.terminal (.char 41) 2 3 (.terminal .eof 3 3 (.nil 3)))))

private def input : List Nat := [40, 955, 41]

theorem complete_certificate_replays :
    (replay profile plan input "Expression" 0 3 certificate).isSome = true ∧
      ((replay profile plan input "Expression" 0 3 certificate).map Sigma.fst) =
        some (.node "Wrapped" 0 3 [.node "leaf" 1 2 [.terminal [955] 1 2]]) := by
  decide +kernel

theorem corrupted_sorts_spans_and_payloads_refused :
    (replay profile plan input "Scalar" 0 3 certificate).isSome = false ∧
      (replay profile plan input "Expression" 0 2 certificate).isSome = false ∧
      (replay profile plan [40, 65, 41] "Expression" 0 3 certificate).isSome = false ∧
      (replay profile plan [40, 955, 41, 41] "Expression" 0 3 certificate).isSome = false := by
  decide +kernel

theorem corrupted_internal_seam_refused :
    (replay profile plan input "Expression" 0 3
      (.structural 0 0 3 (.terminal (.char 40) 0 1
        (.nonterminal "Scalar" 2 2 (.lexical 0 (.class "lambda") 1 2)
          (.terminal (.char 41) 2 3 (.terminal .eof 3 3 (.nil 3))))))).isSome = false ∧
      (replay profile plan input "Expression" 0 3
        (.structural 0 0 3 (.terminal (.char 40) 0 1
          (.nonterminal "Wrong" 1 2 (.lexical 0 (.class "lambda") 1 2)
            (.terminal (.char 41) 2 3 (.terminal .eof 3 3 (.nil 3))))))).isSome = false := by
  decide +kernel

theorem missing_and_extra_items_refused :
    (replay profile plan input "Expression" 0 3 (.structural 0 0 3 (.nil 3))).isSome = false ∧
      (replayItems profile plan input [] 3 3 (.terminal .eof 3 3 (.nil 3))).isSome = false ∧
      (replay profile plan input "Expression" 0 3 (.structural 1 0 3 (.nil 3))).isSome = false := by
  decide +kernel

#print axioms complete_certificate_replays
#print axioms corrupted_sorts_spans_and_payloads_refused
#print axioms corrupted_internal_seam_refused
#print axioms missing_and_extra_items_refused

end Mettapedia.GSLT.Parsing.ClassAwareParserPackReplay.Controls
