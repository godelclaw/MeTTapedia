import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogProjectionRules
import Mettapedia.OSLF.MeTTaIL.ReferenceStepRuleTranslation

/-! Native specialization of the authored projector. The inherited inference
rows remain in the source module. On projector calls, selecting the compiler
rows preserves and reflects reference steps with explicit witness-index
transport. The general execution-admission policy is unchanged. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.NativeSlice

open Mettapedia.OSLF.MeTTaIL Syntax Match

abbrev sourceLanguage := ProgramProjection.language

def language : LanguageDef :=
  {sourceLanguage with rewrites := sourceLanguage.rewrites.drop 2}

def heads : List String :=
  ["ProjectProgram", "ProjectItemsInto", "ProjectItemInto", "ProjectRelationsInto",
    "ProjectAttributes", "ProjectAttribute", "ProjectAttributeType", "ProjectFact", "ProjectRule",
    "ProjectBody", "ProjectPositiveLiteral", "ProjectAtom", "ProjectGroundAtom", "ProjectTerms",
    "ProjectTerm", "ProjectConstants", "ProjectConstant", "ProjectComparison", "ProjectComparisonOperator"]

def Calls (term : Pattern) : Prop := ∃ head arguments, term = .apply head arguments ∧ head ∈ heads

private def childChecked : Premise → Bool
  | .congruence (.apply head _) _ => decide (head ∈ heads)
  | _ => false

private theorem children_checked : ∀ rule ∈ language.rewrites,
    rule.premises.all childChecked = true := by decide +kernel

private theorem candidates_from_two : ∀ head ∈ heads, ∀ index ∈ candidates head, 2 ≤ index := by
  decide +kernel

private theorem index_from_two {redex : Pattern} (inside : Calls redex)
    {index : Nat} {rule : RewriteRule} {initial : Bindings}
    (found : sourceLanguage.rewrites[index]? = some rule)
    (matched : initial ∈ matchPattern rule.left redex) : 2 ≤ index := by
  obtain ⟨head,arguments,rfl,member⟩ := inside
  exact candidates_from_two head member index (candidate_of_match found matched)

private theorem child_closed (sites : Pattern) (premise : Premise) (checked : childChecked premise = true) :
    ReferenceStep.CongruenceClosed Calls sites premise := by
  cases premise with
  | congruence source target =>
    cases source with
    | apply head arguments =>
      have member : head ∈ heads := of_decide_eq_true checked
      refine ⟨.apply head arguments,target,rfl,?_⟩
      intro bindings
      rw [applyBindingsScoped_apply]
      exact ⟨head,_,rfl,member⟩
    | _ => cases checked
  | _ => cases checked

private theorem row_children {rule : RewriteRule} (member : rule ∈ language.rewrites) :
    ∀ premise ∈ rule.premises, ReferenceStep.CongruenceClosed Calls (ReferenceStep.captureSites rule) premise := by
  intro premise present
  apply child_closed
  exact List.all_eq_true.mp (children_checked rule member) premise present

def intoSource : ReferenceStep.RuleTranslation language sourceLanguage Calls where
  indices := (· + 2)
  selected := by
    intro redex inside index rule found initial matched
    simpa only [language, List.getElem?_drop, Nat.add_comm] using found
  children := by
    intro redex inside index rule found initial matched
    exact row_children (List.mem_of_getElem? found)

def fromSource : ReferenceStep.RuleTranslation sourceLanguage language Calls where
  indices := (· - 2)
  selected := by
    intro redex inside index rule found initial matched
    have bound := index_from_two inside found matched
    simpa only [language, List.getElem?_drop, Nat.add_sub_of_le bound] using found
  children := by
    intro redex inside index rule found initial matched
    have bound := index_from_two inside found matched
    have selected : language.rewrites[index - 2]? = some rule := by
      simpa only [language, List.getElem?_drop, Nat.add_sub_of_le bound] using found
    exact row_children (List.mem_of_getElem? selected)

theorem reference_exact (environment : Engine.RelationEnv) {source target : Pattern} (inside : Calls source) :
    ReferenceStep.Step environment language source target ↔
      ReferenceStep.Step environment sourceLanguage source target :=
  ⟨ReferenceStep.step_mapRules intoSource environment inside,
    ReferenceStep.step_mapRules fromSource environment inside⟩

theorem source_witness (environment : Engine.RelationEnv) {source target : Pattern} (inside : Calls source)
    {witness : ReferenceStep.Witness} (valid : ReferenceStep.StepValid environment language source witness target) :
    ReferenceStep.StepValid environment sourceLanguage source (witness.mapRules (· + 2)) target :=
  ReferenceStep.stepValid_mapRules intoSource environment source inside valid

theorem source_witness_injective : Function.Injective (ReferenceStep.Witness.mapRules (· + 2)) :=
  ReferenceStep.Witness.mapRules_add_injective 2

#print axioms reference_exact
#print axioms source_witness
#print axioms source_witness_injective

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ProgramProjection.NativeSlice
