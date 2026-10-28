import Mettapedia.GSLT.Parsing.ClassAwareParserPackCertificate
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestTerminalValidation

/-! Executable replay for the lexical part of existing ParserPack
certificates. Checks consume the declared physical production, matcher,
immutable input occurrence and exact span. Success constructs the existing
replay evidence; it introduces no new certificate format. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareParserPackLexicalReplay

open ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ClassAwareNativeForestContract ClassAwareNativeForestTerminalValidation

def terminalValue? (input : List Nat) (matcher : TerminalMatcher) (start : Nat) : Option TerminalValue :=
  match matcher with
  | .eof => some .eof
  | _ => input[start]?.map TerminalValue.scalar

def replayTerminal? (profile : ParserProfileLayer) (input : List Nat)
    (matcher : TerminalMatcher) (start stop : Nat) :
    Option (TerminalMatchesAt profile input matcher start stop) := do
  let value ← terminalValue? input matcher start
  if accepted : terminalSemanticValid profile input matcher value start stop = true then
    some (terminalSemanticValid_sound accepted).2
  else none

def terminalOutput (input : List Nat) (matcher : TerminalMatcher) (start stop : Nat) : List CST :=
  match matcher with
  | .eof => []
  | _ => match input[start]? with
      | none => []
      | some point => [.terminal [point] start stop]

theorem terminalOutput_exact {profile : ParserProfileLayer} {input : List Nat}
    {matcher : TerminalMatcher} {start stop : Nat}
    (matched : TerminalMatchesAt profile input matcher start stop) :
    matched.cst = terminalOutput input matcher start stop := by
  cases matched <;> simp_all [TerminalMatchesAt.cst, terminalOutput]

theorem replayTerminal?_complete (profile : ParserProfileLayer) (input : List Nat)
    (matcher : TerminalMatcher) (start stop : Nat)
    (matched : TerminalMatchesAt profile input matcher start stop) :
    (replayTerminal? profile input matcher start stop).isSome = true := by
  cases matched with
  | any lookup => simp [replayTerminal?, terminalValue?, terminalSemanticValid, lookup]
  | eof atEnd => simp [replayTerminal?, terminalValue?, terminalSemanticValid, atEnd]
  | char lookup => simp [replayTerminal?, terminalValue?, terminalSemanticValid, lookup]
  | classMember lookup evidence =>
    simp [replayTerminal?, terminalValue?, terminalSemanticValid, lookup,
      ParserProfileLayer.ClassEvidence] at *
    exact evidence

theorem replayTerminal?_isSome_iff (profile : ParserProfileLayer) (input : List Nat)
    (matcher : TerminalMatcher) (start stop : Nat) :
    (replayTerminal? profile input matcher start stop).isSome = true ↔
      Nonempty (TerminalMatchesAt profile input matcher start stop) := by
  constructor
  · intro accepted
    obtain ⟨matched, _⟩ := Option.isSome_iff_exists.mp accepted
    exact ⟨matched⟩
  · rintro ⟨matched⟩
    exact replayTerminal?_complete profile input matcher start stop matched

structure Result (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (certificate : Certificate) (start stop : Nat) where
  sort : String
  tree : CST
  evidence : Replays profile plan input certificate sort start stop tree

def replayLexical? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (position : Nat) (matcher : TerminalMatcher) (start stop : Nat) :
    Option (Result profile plan input (.lexical position matcher start stop) start stop) := do
  if valid : position < plan.lexical.productions.length then
    let row := plan.lexical.productions.get ⟨position, valid⟩
    if same : row.matcher = matcher then
      let matched ← replayTerminal? profile input matcher start stop
      some ⟨row.resultSort, .node row.label start stop (terminalOutput input matcher start stop),
        .lexical position valid same rfl rfl ⟨matched, terminalOutput_exact matched⟩⟩
    else none
  else none

theorem replayLexical?_complete (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (position : Nat) (matcher : TerminalMatcher) (start stop : Nat)
    {sort : String} {tree : CST}
    (replayed : Replays profile plan input (.lexical position matcher start stop) sort start stop tree) :
    (replayLexical? profile plan input position matcher start stop).isSome = true := by
  cases replayed with
  | lexical _ valid same _ _ matched =>
    obtain ⟨terminal, found⟩ := Option.isSome_iff_exists.mp
      (replayTerminal?_complete profile input matcher start stop matched.val)
    change plan.lexical.productions[position].matcher = matcher at same
    simp [replayLexical?, valid, same, found]

theorem replayLexical?_isSome_iff (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (position : Nat) (matcher : TerminalMatcher) (start stop : Nat) :
    (replayLexical? profile plan input position matcher start stop).isSome = true ↔
      ∃ sort tree, Nonempty
        (Replays profile plan input (.lexical position matcher start stop) sort start stop tree) := by
  constructor
  · intro accepted
    obtain ⟨result, _⟩ := Option.isSome_iff_exists.mp accepted
    exact ⟨result.sort, result.tree, ⟨result.evidence⟩⟩
  · rintro ⟨sort, tree, ⟨replayed⟩⟩
    exact replayLexical?_complete profile plan input position matcher start stop replayed

#print axioms replayTerminal?_isSome_iff
#print axioms replayLexical?_isSome_iff

end Mettapedia.GSLT.Parsing.ClassAwareParserPackLexicalReplay
