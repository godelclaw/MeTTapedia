import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

/-! Source-certified closed views of the authored Datalog grammar and lexical
profile. Quotation proposes data; kernel equalities link the source packet,
its existing decoder and the original reply interface. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceViews

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

private instance : DecidableEq LanguageDef := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (LanguageDef.mk.injEq _ _ _ _ _ _ _ _ _ _))

def grammar : LanguageDef := module_language_view% grammar?
def profile : ParserProfileLayer := module_profile_view% (lexicalReply?.map (·.2))

theorem grammar_exact : grammar? = some grammar := by decide +kernel

def lexicalPayload? : Option Pattern := do
  let (_, fragment) ← lexicalFragment.toOption
  match fragment.entries.filter (fun entry => entry.label == (.rewrite,"ReturnLexicalProfile")) with
  | [entry] => match entry.body with
      | .rewrite rule =>
          if rule.left == profileRequest && rule.premises.isEmpty && rule.bindings.isNone
          then some rule.right else none
      | _ => none
  | _ => none

theorem profile_payload_exact : lexicalPayload? = some (Portable.lexicalData profile) := by decide +kernel

theorem profile_decode_exact : lexicalPayload?.bind Portable.readLexicalData? = some profile := by
  rw [profile_payload_exact]
  exact Portable.lexicalData_roundtrip profile

private theorem reply_payload_bridge :
    lexicalReply?.map Prod.snd = lexicalPayload?.bind Portable.readLexicalData? := by
  unfold lexicalReply? lexicalReplyAt? lexicalPayload?
  cases found : lexicalFragment.toOption with
  | none => rfl
  | some pair =>
    rcases pair with ⟨name, fragment⟩
    cases selected : fragment.entries.filter
        (fun entry => entry.label == (.rewrite,"ReturnLexicalProfile")) with
    | nil => simp [selected]
    | cons entry rest =>
      cases rest with
      | cons _ _ => simp [selected]
      | nil =>
        cases body : entry.body with
        | sort _ => simp [selected, body]
        | term _ => simp [selected, body]
        | equation _ => simp [selected, body]
        | rewrite rule =>
          by_cases permitted : (rule.left = profileRequest ∧ rule.premises = []) ∧ rule.bindings = none
          · simp [selected, body, permitted]
          · simp [selected, body, permitted]

theorem profile_source_exact : lexicalReply?.map Prod.snd = some profile := by
  rw [reply_payload_bridge, profile_decode_exact]

#print axioms grammar_exact
#print axioms profile_source_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceViews
