import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionRules
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionReference

/-! The four authored constant projections preserve the literal payload
exactly. Every reference step from such a call has the declared result;
matching another constructor or returning another value is impossible. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection

open Mettapedia.OSLF.MeTTaIL Syntax Match

namespace Constants

inductive Kind where
  | symbol | integer | unsigned | floating
  deriving DecidableEq, Repr

def index : Kind → Nat
  | .symbol => 37
  | .integer => 38
  | .unsigned => 39
  | .floating => 40

def sourceHead : Kind → String
  | .symbol => "dl-src:constant-symbol"
  | .integer => "dl-src:constant-integer"
  | .unsigned => "dl-src:constant-unsigned"
  | .floating => "dl-src:constant-float"

def targetHead : Kind → String
  | .symbol => "SymbolValue"
  | .integer => "IntegerValue"
  | .unsigned => "UnsignedValue"
  | .floating => "FloatValue"

def rule (kind : Kind) : RewriteRule :=
  language.rewrites[index kind]'(by cases kind <;> rw [authored_rule_count] <;> decide)

def call (kind : Kind) (payload : Pattern) : Pattern :=
  .apply "ProjectConstant" [.apply (sourceHead kind) [payload]]

def result (kind : Kind) (payload : Pattern) : Pattern := .apply (targetHead kind) [payload]

def bindings (payload : Pattern) : Bindings := [("source", payload)]

theorem rule_at (kind : Kind) : language.rewrites[index kind]? = some (rule kind) := by
  simp [rule]

theorem rule_left (kind : Kind) :
    (rule kind).left = .apply "ProjectConstant" [.apply (sourceHead kind) [.fvar "source"]] := by
  cases kind <;> decide +kernel

theorem rule_right (kind : Kind) :
    (rule kind).right = .apply (targetHead kind) [.fvar "source"] := by
  cases kind <;> decide +kernel

theorem rule_premises (kind : Kind) : (rule kind).premises = [] := by
  cases kind <;> decide +kernel

theorem cross_match (selected actual : Kind) (payload : Pattern) :
    matchPattern (rule selected).left (call actual payload) =
      if selected = actual then [bindings payload] else [] := by
  rw [rule_left]
  cases selected <;> cases actual <;>
    simp [call, sourceHead, bindings, matchPattern, matchArgs, mergeBindings]

theorem result_instantiated (sites : Pattern) (kind : Kind) (payload : Pattern) :
    applyBindingsScoped sites (bindings payload) 0 (rule kind).right = result kind payload := by
  rw [rule_right]
  simp [applyBindingsScoped_apply, applyBindingsScoped_fvar_zero, bindings, applyBindings, result]

theorem step (environment : Engine.RelationEnv) (kind : Kind) (payload : Pattern) :
    ReferenceStep.Step environment language (call kind payload) (result kind payload) := by
  have premises : ReferenceStep.PremisesValid environment language
      (ReferenceStep.captureSites (rule kind)) (bindings payload) (rule kind).premises []
      (bindings payload) := by
    rw [rule_premises]
    exact .nil _
  have matched : bindings payload ∈
      ReflectiveCanonical.matchPatternForRule language (rule kind) (call kind payload) := by
    simp only [ReflectiveCanonical.matchPatternForRule_eq_syntactic, cross_match, ↓reduceIte]
    exact List.mem_singleton_self _
  have valid := ReferenceStep.StepValid.rule (rule_at kind) matched premises
  rw [result_instantiated] at valid
  exact ⟨_, valid⟩

theorem step_only_result (environment : Engine.RelationEnv) (kind : Kind) (payload : Pattern)
    {target : Pattern} (stepped : ReferenceStep.Step environment language (call kind payload) target) :
    target = result kind payload := by
  obtain ⟨witness, valid⟩ := stepped
  cases valid with
  | @rule _ ruleIndex selected initial final witnesses found matched premises =>
    have candidate := candidate_of_match found
      (by simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic, call] using matched)
    rw [constant_candidates] at candidate
    have selectedKind : ∃ selectedKind : Kind, ruleIndex = index selectedKind := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at candidate
      rcases candidate with same | same | same | same
      · exact ⟨.symbol, same⟩
      · exact ⟨.integer, same⟩
      · exact ⟨.unsigned, same⟩
      · exact ⟨.floating, same⟩
    obtain ⟨selectedKind, rfl⟩ := selectedKind
    rw [rule_at] at found
    cases Option.some.inj found
    simp only [ReflectiveCanonical.matchPatternForRule_eq_syntactic, cross_match] at matched
    by_cases same : selectedKind = kind
    · subst selectedKind
      simp only [↓reduceIte, List.mem_singleton] at matched
      subst initial
      rw [rule_premises] at premises
      cases premises
      exact result_instantiated _ _ _
    · simp [same] at matched

theorem step_exact (environment : Engine.RelationEnv) (kind : Kind) (payload target : Pattern) :
    ReferenceStep.Step environment language (call kind payload) target ↔ target = result kind payload := by
  constructor
  · exact step_only_result environment kind payload
  · rintro rfl
    exact step environment kind payload

theorem reference_agreement (kind : Kind) (payload : Pattern) :
    Reference.constant? (.apply (sourceHead kind) [payload]) = some (result kind payload) := by
  cases kind <;> rfl

theorem match_payload (kind : Kind) {source : Pattern} {initial : Bindings}
    (matched : initial ∈ matchPattern (rule kind).left (.apply "ProjectConstant" [source])) :
    ∃ payload, source = .apply (sourceHead kind) [payload] ∧ initial = bindings payload := by
  rw [rule_left] at matched
  have related := MatchSpec.matchPattern_sound matched
  cases related with
  | apply arguments _ =>
    cases arguments with
    | cons inside tail outerMerge =>
      cases tail
      cases inside with
      | apply payloads _ =>
        cases payloads with
        | cons payloadMatch rest payloadMerge =>
          cases rest
          cases payloadMatch with
          | fvar =>
            refine ⟨_, rfl, ?_⟩
            simp [mergeBindings] at payloadMerge outerMerge
            cases payloadMerge
            cases outerMerge
            rfl

theorem source_readback (environment : Engine.RelationEnv) {source target : Pattern}
    (stepped : ReferenceStep.Step environment language (.apply "ProjectConstant" [source]) target) :
    ∃ kind payload, source = .apply (sourceHead kind) [payload] := by
  obtain ⟨witness, valid⟩ := stepped
  cases valid with
  | @rule _ ruleIndex selected initial final witnesses found matched premises =>
    have ordinary : initial ∈ matchPattern selected.left (.apply "ProjectConstant" [source]) := by
      simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic] using matched
    have candidate := candidate_of_match found ordinary
    rw [constant_candidates] at candidate
    have selectedKind : ∃ selectedKind : Kind, ruleIndex = index selectedKind := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at candidate
      rcases candidate with same | same | same | same
      · exact ⟨.symbol, same⟩
      · exact ⟨.integer, same⟩
      · exact ⟨.unsigned, same⟩
      · exact ⟨.floating, same⟩
    obtain ⟨selectedKind, rfl⟩ := selectedKind
    rw [rule_at] at found
    cases Option.some.inj found
    obtain ⟨payload, sourceEqual, _⟩ := match_payload selectedKind ordinary
    exact ⟨selectedKind, payload, sourceEqual⟩

private theorem reference_source {source target : Pattern}
    (projected : Reference.constant? source = some target) :
    ∃ kind payload, source = .apply (sourceHead kind) [payload] ∧ target = result kind payload := by
  unfold Reference.constant? at projected
  split at projected
  · cases Option.some.inj projected
    exact ⟨.symbol, _, rfl, rfl⟩
  · cases Option.some.inj projected
    exact ⟨.integer, _, rfl, rfl⟩
  · cases Option.some.inj projected
    exact ⟨.unsigned, _, rfl, rfl⟩
  · cases Option.some.inj projected
    exact ⟨.floating, _, rfl, rfl⟩
  · cases projected

theorem reference_exact (environment : Engine.RelationEnv) (source target : Pattern) :
    ReferenceStep.Step environment language (.apply "ProjectConstant" [source]) target ↔
      Reference.constant? source = some target := by
  constructor
  · intro stepped
    obtain ⟨kind, payload, rfl⟩ := source_readback environment stepped
    have same : target = result kind payload := step_only_result environment kind payload stepped
    rw [same]
    exact reference_agreement kind payload
  · intro projected
    obtain ⟨kind, payload, rfl, rfl⟩ := reference_source projected
    exact step environment kind payload

#print axioms cross_match
#print axioms result_instantiated
#print axioms step
#print axioms step_only_result
#print axioms step_exact
#print axioms reference_agreement
#print axioms match_payload
#print axioms source_readback
#print axioms reference_exact

end Constants
end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection
