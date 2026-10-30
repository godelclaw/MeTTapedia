import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProgramProjection
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.MeTTaIL.ReferenceStepRuleViews

/-! Rule selection for the actual authored program projector. Constructor-head
certificates narrow the original rule indices; they do not replace matching,
premise evidence or the reference step relation. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection

open Mettapedia.OSLF.MeTTaIL Syntax Match

def applicationHead? : Pattern → Option String
  | .apply head _ => some head
  | _ => none

theorem all_rule_heads :
    language.rewrites.all (fun rule => (applicationHead? rule.left).isSome) = true := by
  decide +kernel

def candidates (head : String) : List Nat :=
  (List.range language.rewrites.length).filter fun index =>
    ((language.rewrites[index]?).map fun rule => applicationHead? rule.left) == some (some head)

private theorem match_same_head (schemaHead sourceHead : String)
    (schemaArgs sourceArgs : List Pattern) {bindings : Bindings}
    (matched : bindings ∈ matchPattern (.apply schemaHead schemaArgs) (.apply sourceHead sourceArgs)) :
    schemaHead = sourceHead := by
  by_contra different
  simp [matchPattern, different] at matched

theorem candidate_of_match {head : String} {arguments : List Pattern}
    {index : Nat} {rule : RewriteRule} {bindings : Bindings}
    (found : language.rewrites[index]? = some rule)
    (matched : bindings ∈ matchPattern rule.left (.apply head arguments)) :
    index ∈ candidates head := by
  have inside : index < language.rewrites.length := by
    by_contra outside
    rw [List.getElem?_eq_none (by omega)] at found
    cases found
  have member : rule ∈ language.rewrites := List.mem_of_getElem? found
  have headed := List.all_eq_true.mp all_rule_heads rule member
  have same : applicationHead? rule.left = some head := by
    cases shape : rule.left with
    | apply name args =>
      have equal := match_same_head name head args arguments (by simpa only [shape] using matched)
      simp only [applicationHead?, equal]
    | _ => simp [shape, applicationHead?] at headed
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr inside, by simp [found, same]⟩

theorem constant_candidates : candidates "ProjectConstant" = [37,38,39,40] := by
  decide +kernel

theorem attribute_type_candidates : candidates "ProjectAttributeType" = [16,17,18,19] := by
  decide +kernel

theorem comparison_operator_candidates : candidates "ProjectComparisonOperator" = [42,43,44,45,46,47] := by
  decide +kernel

theorem term_candidates : candidates "ProjectTerm" = [34,35,36] := by
  decide +kernel

theorem constants_candidates : candidates "ProjectConstants" = [31,32,33] := by
  decide +kernel

theorem terms_candidates : candidates "ProjectTerms" = [28,29,30] := by
  decide +kernel

theorem atom_candidates : candidates "ProjectAtom" = [26] := by
  decide +kernel

theorem ground_atom_candidates : candidates "ProjectGroundAtom" = [27] := by
  decide +kernel

theorem fact_candidates : candidates "ProjectFact" = [20] := by
  decide +kernel

theorem comparison_candidates : candidates "ProjectComparison" = [41] := by
  decide +kernel

theorem positive_literal_candidates : candidates "ProjectPositiveLiteral" = [24,25] := by
  decide +kernel

theorem body_candidates : candidates "ProjectBody" = [22,23] := by
  decide +kernel

theorem rule_candidates : candidates "ProjectRule" = [21] := by
  decide +kernel

theorem attributes_candidates : candidates "ProjectAttributes" = [12,13,14] := by
  decide +kernel

theorem attribute_candidates : candidates "ProjectAttribute" = [15] := by
  decide +kernel

theorem program_candidates : candidates "ProjectProgram" = [2] := by
  decide +kernel

theorem items_candidates : candidates "ProjectItemsInto" = [3,4] := by
  decide +kernel

theorem item_candidates : candidates "ProjectItemInto" = [5,6,7,8,9] := by
  decide +kernel

theorem relations_candidates : candidates "ProjectRelationsInto" = [10,11] := by
  decide +kernel

theorem step_candidates_iff (environment : Engine.RelationEnv) (head : String)
    (arguments : List Pattern) (target : Pattern) :
    ReferenceStep.Step environment language (.apply head arguments) target ↔
      ∃ index ∈ candidates head, ∃ rule, language.rewrites[index]? = some rule ∧
        ∃ initial, initial ∈ matchPattern rule.left (.apply head arguments) ∧
          ∃ final, (∃ witnesses, ReferenceStep.PremisesValid environment language
            (ReferenceStep.captureSites rule) initial rule.premises witnesses final) ∧
            applyBindingsScoped (ReferenceStep.captureSites rule) final 0 rule.right = target := by
  rw [ReferenceStep.step_rule_iff]
  constructor
  · rintro ⟨index, rule, found, initial, matched, rest⟩
    exact ⟨index, candidate_of_match found matched, rule, found, initial, matched, rest⟩
  · rintro ⟨index, _, rule, found, initial, matched, rest⟩
    exact ⟨index, rule, found, initial, matched, rest⟩

/-- A matched unary request retains the inner constructor and exact arity. -/
theorem source_constructor_of_match (operation tag : String) (schemaArguments : List Pattern)
    {source : Pattern} {initial : Bindings}
    (matched : initial ∈ matchPattern (.apply operation [.apply tag schemaArguments])
      (.apply operation [source])) :
    ∃ arguments, source = .apply tag arguments ∧ arguments.length = schemaArguments.length := by
  have related := MatchSpec.matchPattern_sound matched
  cases related with
  | apply arguments _ =>
    cases arguments with
    | cons first _ _ =>
      cases first with
      | apply _ length => exact ⟨_,rfl,length.symm⟩

/-- The first request argument retains its constructor, independently of
additional arguments passed to the same operation. -/
theorem first_argument_constructor_of_match (operation tag : String)
    (schemaArguments schemaTail : List Pattern) {source : Pattern} {arguments : List Pattern}
    {initial : Bindings}
    (matched : initial ∈ matchPattern (.apply operation (.apply tag schemaArguments :: schemaTail))
      (.apply operation (source :: arguments))) :
    ∃ children, source = .apply tag children ∧ children.length = schemaArguments.length := by
  have related := MatchSpec.matchPattern_sound matched
  cases related with
  | apply arguments _ =>
    cases arguments with
    | cons first _ _ =>
      cases first with
      | apply _ length => exact ⟨_,rfl,length.symm⟩

/-- Two nested constructors at the first argument retain the inner arity. -/
theorem nested_first_argument_constructor_of_match (operation outer inner : String)
    (schemaArguments schemaTail : List Pattern) {source : Pattern} {arguments : List Pattern}
    {initial : Bindings}
    (matched : initial ∈ matchPattern
      (.apply operation (.apply outer [.apply inner schemaArguments] :: schemaTail))
      (.apply operation (source :: arguments))) :
    ∃ children, source = .apply outer [.apply inner children] ∧ children.length = schemaArguments.length := by
  have related := MatchSpec.matchPattern_sound matched
  cases related with
  | apply arguments _ =>
    cases arguments with
    | cons outerMatch _ _ =>
      cases outerMatch with
      | apply outerArguments _ =>
        cases outerArguments with
        | cons innerMatch remaining _ =>
          cases remaining
          cases innerMatch with
          | apply _ length => exact ⟨_,rfl,length.symm⟩

#print axioms all_rule_heads
#print axioms candidate_of_match
#print axioms constant_candidates
#print axioms attribute_type_candidates
#print axioms comparison_operator_candidates
#print axioms term_candidates
#print axioms step_candidates_iff
#print axioms source_constructor_of_match

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection
