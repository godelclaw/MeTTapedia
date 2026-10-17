import Mettapedia.GSLT.LanguageDef.RegexScalarSyntax

/-!
# Ambiguity and corruption controls at the regex lexical boundary

An authored profile extension deliberately contributes a second lexical
occurrence for the same scalar and source category. The original structural
regex language is unchanged. Both admitted trees survive packing; deleting
the second physical alternative fails coverage. A fabricated out-of-table
production can be stored as forest data but cannot pass semantic replay.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.GSLT.LanguageDef.RegexScalarSyntaxControls

open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate
open ClassAwarePackedForest ClassAwareGroundedChart
open ParserProfileSemantics PresentationExprSemantics
open ModuleFormat.RegexSyntaxAuthoring

def extendedProfile : ParserProfileLayer := {
  profile with
  startSort := "RxScalar"
  states := profile.states ++ [⟨"RxScalar", "RxLiteralClass", "re-src:lex-alternate"⟩]
}

def extendedPlan : CompiledParserPackPlan := {
  lexical := compileLexicalPack extendedProfile
  structural := RegexScalarSyntax.plan.structural
}

/-- The lexical extension does not pretend to alter the compiled structural
rules. Their actual compilation agrees independently of the entry sort. -/
theorem extended_agreement :
    ParserPackPlanAgreement RegexScalarSyntax.literalScalars extendedProfile compiledRules
      extendedPlan :=
  ⟨rfl, RegexScalarSyntax.agreement.structural_exact⟩

def firstTree : CST := .node "re-src:lex-scalar" 0 1 [.terminal [955] 0 1]
def secondTree : CST := .node "re-src:lex-alternate" 0 1 [.terminal [955] 0 1]
def first : Certificate := .lexical 0 (.class "RxLiteralClass") 0 1
def second : Certificate := .lexical 8 (.class "RxLiteralClass") 0 1

def firstReplay : Replays extendedProfile extendedPlan [955] first "RxScalar" 0 1 firstTree := by
  apply Replays.lexical 0 (by decide) rfl rfl rfl
  exact ⟨.classMember rfl (by
    change extendedProfile.classAccepts? "RxLiteralClass" 955 = some true
    decide), rfl⟩

def secondReplay : Replays extendedProfile extendedPlan [955] second "RxScalar" 0 1 secondTree := by
  apply Replays.lexical 8 (by decide) rfl rfl rfl
  exact ⟨.classMember rfl (by
    change extendedProfile.classAccepts? "RxLiteralClass" 955 = some true
    decide), rfl⟩

def both : Forest := pack [("RxScalar", first), ("RxScalar", second)]
def onlyFirst : Forest := pack [("RxScalar", first)]

def Admitted (target : Forest) (tree : CST) : Prop :=
  ∃ certificate, Nonempty (PackedReplays target extendedProfile extendedPlan [955]
    certificate "RxScalar" 0 1 tree)

theorem first_alternative_is_admitted : Admitted both firstTree :=
  ⟨first, ⟨⟨⟨member_pack_rootUnfolds (by simp)⟩, firstReplay⟩⟩⟩

theorem second_alternative_is_admitted : Admitted both secondTree :=
  ⟨second, ⟨⟨⟨member_pack_rootUnfolds (by simp)⟩, secondReplay⟩⟩⟩

theorem authored_lexical_ambiguity_is_retained : RegexScalarSyntax.Ambiguous (Admitted both) :=
  ⟨firstTree, secondTree, by decide,
    first_alternative_is_admitted, second_alternative_is_admitted⟩

theorem alternatives_share_one_root_but_keep_both_rows :
    both.roots.length = 1 ∧ both.families.length = 2 := by decide

theorem dropping_one_physical_alternative_fails_coverage :
    validateForestCovers both onlyFirst = false := by decide

theorem dropped_alternative_cannot_unfold :
    ¬ RootUnfolds onlyFirst "RxScalar" second := by
  intro stored
  have absent : certificateFamily "RxScalar" second ∉ onlyFirst.families := by decide
  apply absent
  apply stored.2
  exact List.mem_singleton_self _

theorem lexical_replay_has_a_real_production
    {lexicalProfile : ParserProfileLayer} {compiledPlan : CompiledParserPackPlan}
    {input : List Nat} {position start stop : Nat} {matcher : TerminalMatcher}
    {sort : String} {tree : CST}
    (replayed : Replays lexicalProfile compiledPlan input
      (.lexical position matcher start stop) sort start stop tree) :
    position < compiledPlan.lexical.productions.length := by
  cases replayed with
  | lexical _ valid _ _ _ _ => exact valid

def spurious : Certificate := .lexical 999 (.class "RxLiteralClass") 0 1
def spuriousForest : Forest := pack [("RxScalar", spurious)]

/-- Storage is not evidence: arbitrary certificate data can be packed. -/
theorem spurious_data_can_be_stored : RootUnfolds spuriousForest "RxScalar" spurious :=
  member_pack_rootUnfolds (by simp)

/-- Semantic replay rejects the fabricated ordinal independently of packing. -/
theorem spurious_production_cannot_be_admitted (tree : CST) :
    IsEmpty (Replays extendedProfile extendedPlan [955] spurious "RxScalar" 0 1 tree) := by
  constructor
  intro replayed
  have valid := lexical_replay_has_a_real_production replayed
  have tooLarge : ¬ 999 < extendedPlan.lexical.productions.length := by decide
  exact tooLarge valid

#print axioms authored_lexical_ambiguity_is_retained
#print axioms spurious_production_cannot_be_admitted

end Mettapedia.GSLT.LanguageDef.RegexScalarSyntaxControls
