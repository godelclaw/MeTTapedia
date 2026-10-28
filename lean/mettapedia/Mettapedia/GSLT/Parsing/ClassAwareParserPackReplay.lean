import Mettapedia.GSLT.Parsing.ClassAwareParserPackLexicalReplay

/-! Proof-producing replay of the existing finite ParserPack certificates.
The recursion follows certificate data, so rejection has no fuel ambiguity.
Production positions, sorts, matchers, all redundant cursors and ordered
children are checked against the supplied plan and immutable scalar input. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.GSLT.Parsing.ClassAwareParserPackReplay

open ParserProfileSemantics PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ClassAwareParserPackLexicalReplay (replayTerminal? replayLexical?)

abbrev Checked (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (certificate : Certificate) (sort : String) (start stop : Nat) :=
  Sigma fun tree => Replays profile plan input certificate sort start stop tree

abbrev CheckedItems (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (certificate : ItemsCertificate) (items : List PackItem) (start stop : Nat) :=
  Sigma fun children => ItemsReplays profile plan input certificate items start stop children

mutual
  def replay (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
      (sort : String) (start stop : Nat) (certificate : Certificate) :
      Option (Checked profile plan input certificate sort start stop) :=
    match certificate with
    | .lexical position matcher before after =>
      if beforeSame : before = start then
       if afterSame : after = stop then by
        subst before after
        exact do
          let result ← replayLexical? profile plan input position matcher start stop
          if same : result.sort = sort then
            some ⟨result.tree, same ▸ result.evidence⟩
          else none
       else none
      else none
    | .structural position before after bodyCertificate =>
      if beforeSame : before = start then
       if afterSame : after = stop then by
        subst before after
        exact do
          if valid : position < plan.structural.length then
            let row := plan.structural.get ⟨position, valid⟩
            if same : row.resultSort = sort then
              let body ← replayItems profile plan input row.items start stop bodyCertificate
              some ⟨.node row.label start stop body.1,
                .structural position valid same rfl body.2⟩
            else none
          else none
       else none
      else none
    termination_by structural certificate

  def replayItems (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
      (items : List PackItem) (start stop : Nat) (certificate : ItemsCertificate) :
      Option (CheckedItems profile plan input certificate items start stop) :=
    match certificate, items with
    | .nil cursor, [] =>
      if cursorSame : cursor = start then
       if stopSame : stop = start then by
        subst cursor stop
        exact some ⟨[], .nil⟩
       else none
      else none
    | .terminal matcher before middle restCertificate, .terminal expected :: items =>
      if matcherSame : matcher = expected then
       if beforeSame : before = start then by
        subst matcher before
        exact do
          let matched ← replayTerminal? profile input expected start middle
          let rest ← replayItems profile plan input items middle stop restCertificate
          some ⟨rest.1, .terminal matched rest.2⟩
       else none
      else none
    | .nonterminal resultSort before middle headCertificate restCertificate, .nonterminal expected :: items =>
      if sortSame : resultSort = expected then
       if beforeSame : before = start then by
        subst resultSort before
        exact do
          let head ← replay profile plan input expected start middle headCertificate
          let rest ← replayItems profile plan input items middle stop restCertificate
          some ⟨head.1 :: rest.1, .nonterminal head.2 rest.2⟩
       else none
      else none
    | _, _ => none
    termination_by structural certificate
end

private theorem lexical_sort_agrees {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {position : Nat} {matcher : TerminalMatcher} {start stop : Nat}
    {firstSort secondSort : String} {firstTree secondTree : CST}
    (first : Replays profile plan input (.lexical position matcher start stop) firstSort start stop firstTree)
    (second : Replays profile plan input (.lexical position matcher start stop) secondSort start stop secondTree) :
    firstSort = secondSort := by
  cases first with
  | lexical _ _ _ firstSortExact _ _ =>
    cases second with
    | lexical _ _ _ secondSortExact _ _ => exact firstSortExact.symm.trans secondSortExact

mutual
  theorem replay_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan} {input : List Nat}
      {sort : String} {start stop : Nat} {certificate : Certificate} {tree : CST}
      (replayed : Replays profile plan input certificate sort start stop tree) :
      (replay profile plan input sort start stop certificate).isSome = true :=
    match replayed with
    | .lexical position valid same sortExact labelExact matched => by
      have original := Replays.lexical position valid same sortExact labelExact matched
      obtain ⟨result, found⟩ := Option.isSome_iff_exists.mp
        (ClassAwareParserPackLexicalReplay.replayLexical?_complete
          profile plan input position _ start stop original)
      have sameSort : result.sort = sort := lexical_sort_agrees result.evidence original
      simp [replay, found, sameSort]
    | .structural position valid sortExact labelExact body => by
      obtain ⟨result, found⟩ := Option.isSome_iff_exists.mp (replayItems_complete body)
      change plan.structural[position].resultSort = sort at sortExact
      change replayItems profile plan input plan.structural[position].items start stop _ = some result at found
      simp [replay, valid, sortExact, found]
    termination_by structural replayed

  theorem replayItems_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan} {input : List Nat}
      {items : List PackItem} {start stop : Nat} {certificate : ItemsCertificate} {children : List CST}
      (replayed : ItemsReplays profile plan input certificate items start stop children) :
      (replayItems profile plan input items start stop certificate).isSome = true :=
    match replayed with
    | .nil => by simp [replayItems]
    | .terminal matched rest => by
      obtain ⟨terminal, terminalFound⟩ := Option.isSome_iff_exists.mp
        (ClassAwareParserPackLexicalReplay.replayTerminal?_complete _ _ _ _ _ matched)
      obtain ⟨tail, tailFound⟩ := Option.isSome_iff_exists.mp (replayItems_complete rest)
      simp [replayItems, terminalFound, tailFound]
    | .nonterminal head rest => by
      obtain ⟨first, firstFound⟩ := Option.isSome_iff_exists.mp (replay_complete head)
      obtain ⟨tail, tailFound⟩ := Option.isSome_iff_exists.mp (replayItems_complete rest)
      simp [replayItems, firstFound, tailFound]
    termination_by structural replayed
end

theorem replay_sound {profile : ParserProfileLayer} {plan : CompiledParserPackPlan} {input : List Nat}
    {sort : String} {start stop : Nat} {certificate : Certificate}
    (accepted : (replay profile plan input sort start stop certificate).isSome = true) :
    ∃ tree, Nonempty (Replays profile plan input certificate sort start stop tree) := by
  obtain ⟨result, _⟩ := Option.isSome_iff_exists.mp accepted
  exact ⟨result.1, ⟨result.2⟩⟩

theorem replayItems_sound {profile : ParserProfileLayer} {plan : CompiledParserPackPlan} {input : List Nat}
    {items : List PackItem} {start stop : Nat} {certificate : ItemsCertificate}
    (accepted : (replayItems profile plan input items start stop certificate).isSome = true) :
    ∃ children, Nonempty (ItemsReplays profile plan input certificate items start stop children) := by
  obtain ⟨result, _⟩ := Option.isSome_iff_exists.mp accepted
  exact ⟨result.1, ⟨result.2⟩⟩

theorem replay_isSome_iff (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (sort : String) (start stop : Nat) (certificate : Certificate) :
    (replay profile plan input sort start stop certificate).isSome = true ↔
      ∃ tree, Nonempty (Replays profile plan input certificate sort start stop tree) :=
  ⟨replay_sound, fun ⟨_, ⟨replayed⟩⟩ => replay_complete replayed⟩

#print axioms replay_sound
#print axioms replayItems_sound
#print axioms replay_complete
#print axioms replayItems_complete
#print axioms replay_isSome_iff

end Mettapedia.GSLT.Parsing.ClassAwareParserPackReplay
