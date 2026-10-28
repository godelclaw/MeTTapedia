import Mettapedia.GSLT.Parsing.ClassAwareParserPackReplay

/-! A finite certificate determines its CST, not only the replay proof at an
already fixed CST. This links executable replay output to independently
constructed source derivations without choosing another parse. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareParserPackOutput

open ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate

private theorem terminal_output {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {start stop : Nat} {first second : List CST}
    (left : CSTTerminalMatchesAt profile input matcher start stop first)
    (right : CSTTerminalMatchesAt profile input matcher start stop second) : first = second :=
  left.property.symm.trans ((ClassAwareParserPackLexicalReplay.terminalOutput_exact left.val).trans
    ((ClassAwareParserPackLexicalReplay.terminalOutput_exact right.val).symm.trans right.property))

mutual
  theorem output_unique {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : Certificate} {sort : String} {start stop : Nat}
      {first second : CST}
      (left : Replays profile plan input certificate sort start stop first)
      (right : Replays profile plan input certificate sort start stop second) : first = second := by
    cases left with
    | lexical _ _ _ _ leftLabel leftMatched =>
      cases right with
      | lexical _ _ _ _ rightLabel rightMatched =>
        have labels := leftLabel.symm.trans rightLabel
        have children := terminal_output leftMatched rightMatched
        cases labels
        cases children
        rfl
    | structural _ _ _ leftLabel leftBody =>
      cases right with
      | structural _ _ _ rightLabel rightBody =>
        have labels := leftLabel.symm.trans rightLabel
        have children := items_output_unique leftBody rightBody
        cases labels
        cases children
        rfl

  theorem items_output_unique {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      {input : List Nat} {certificate : ItemsCertificate} {items : List PackItem}
      {start stop : Nat} {first second : List CST}
      (left : ItemsReplays profile plan input certificate items start stop first)
      (right : ItemsReplays profile plan input certificate items start stop second) : first = second := by
    cases left with
    | nil => cases right; rfl
    | terminal _ leftRest =>
      cases right with
      | terminal _ rightRest => exact items_output_unique leftRest rightRest
    | nonterminal leftHead leftRest =>
      cases right with
      | nonterminal rightHead rightRest =>
        rw [output_unique leftHead rightHead, items_output_unique leftRest rightRest]
end

theorem replay_output {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {certificate : Certificate} {sort : String} {start stop : Nat} {tree : CST}
    (source : Replays profile plan input certificate sort start stop tree) :
    (ClassAwareParserPackReplay.replay profile plan input sort start stop certificate).map Sigma.fst = some tree := by
  obtain ⟨result, found⟩ := Option.isSome_iff_exists.mp (ClassAwareParserPackReplay.replay_complete source)
  rw [found]
  exact congrArg some (output_unique result.2 source)

#print axioms output_unique
#print axioms items_output_unique
#print axioms replay_output

end Mettapedia.GSLT.Parsing.ClassAwareParserPackOutput
