import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogKernel
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-! Source membership is implemented by the actual authored set-pattern rule.
The result is uniform in the fact store, rather than a finite fixture claim. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.Kernel

open Mettapedia.OSLF.MeTTaIL Syntax Match MatchSpec

def membershipRule : RewriteRule := language.rewrites[0]'(by decide +kernel)

theorem membership_rule_left : membershipRule.left =
    .apply "HasFact" [.apply "FactStore" [.collection .hashSet [.fvar "fact"] (some "rest")],
      .fvar "fact"] := by decide +kernel

theorem membership_rule_right : membershipRule.right = .apply "FactPresent" [] := by decide +kernel

theorem membership_rule_premises : membershipRule.premises = [] := by decide +kernel

def selectedBindings (selected : Pattern) (remaining : List Pattern) : Bindings :=
  [("rest", .collection .hashSet remaining none), ("fact", selected)]

private theorem merge_selected (selected : Pattern) (remaining : List Pattern) :
    mergeBindings (selectedBindings selected remaining) [("fact", selected)] =
      some (selectedBindings selected remaining) := by
  simp [mergeBindings, selectedBindings, BEq.beq]

theorem membership_match_at (facts : List Pattern) (index : Nat) (inside : index < facts.length) :
    selectedBindings facts[index] (facts.eraseIdx index) ∈
      matchPattern membershipRule.left (.apply "HasFact" [factStore facts, facts[index]]) := by
  rw [membership_rule_left]
  apply matchRel_complete
  have bag : MatchBagRel [.fvar "fact"] (some "rest") .hashSet facts
      (selectedBindings facts[index] (facts.eraseIdx index)) :=
    .cons index inside .fvar .nilRest rfl
  have store : MatchRel
      (.apply "FactStore" [.collection .hashSet [.fvar "fact"] (some "rest")])
      (factStore facts) (selectedBindings facts[index] (facts.eraseIdx index)) :=
    .apply (.cons (.collection (by decide) bag) .nil rfl) rfl
  exact .apply (.cons store (.cons .fvar .nil rfl) (merge_selected _ _)) rfl

theorem membership_match_of_mem {facts : List Pattern} {selected : Pattern} (member : selected ∈ facts) :
    ∃ bindings, bindings ∈ matchPattern membershipRule.left (.apply "HasFact" [factStore facts, selected]) := by
  obtain ⟨index, inside, same⟩ := List.mem_iff_getElem.mp member
  subst selected
  exact ⟨_, membership_match_at facts index inside⟩

private theorem store_match_selects {facts : List Pattern} {bindings : Bindings}
    (matched : MatchRel
      (.apply "FactStore" [.collection .hashSet [.fvar "fact"] (some "rest")])
      (factStore facts) bindings) :
    ∃ index, ∃ inside : index < facts.length,
      bindings.find? (·.1 == "fact") = some ("fact", facts[index]) := by
  cases matched with
  | apply arguments _ =>
    cases arguments with
    | cons collection tail storeMerge =>
      cases collection with
      | collection _ bag =>
        cases bag with
        | cons index inside selected rest bagMerge =>
          cases selected with
          | fvar =>
            exact ⟨index, inside, mergeBindings_subsumed_left storeMerge
              (mergeBindings_subsumed_left bagMerge (by rfl))⟩

theorem membership_match_only_mem {facts : List Pattern} {selected : Pattern} {bindings : Bindings}
    (member : bindings ∈
      matchPattern membershipRule.left (.apply "HasFact" [factStore facts, selected])) :
    selected ∈ facts := by
  rw [membership_rule_left] at member
  have matched := matchPattern_sound member
  cases matched with
  | apply arguments _ =>
    cases arguments with
    | cons store tail outerMerge =>
      obtain ⟨index, inside, found⟩ := store_match_selects store
      have first := mergeBindings_subsumed_left outerMerge found
      cases tail with
      | cons repeated rest tailMerge =>
        cases repeated with
        | fvar =>
          have other := mergeBindings_subsumed_left tailMerge (x := "fact") (v := selected) (by rfl)
          have second := mergeBindings_subsumed_right outerMerge other
          have same : facts[index] = selected := by
            have := Option.some.inj (first.symm.trans second)
            exact congrArg Prod.snd this
          exact same ▸ List.getElem_mem inside

theorem membership_match_iff (facts : List Pattern) (selected : Pattern) :
    (∃ bindings, bindings ∈
      matchPattern membershipRule.left (.apply "HasFact" [factStore facts, selected])) ↔
      selected ∈ facts :=
  ⟨fun ⟨_, member⟩ => membership_match_only_mem member, membership_match_of_mem⟩

theorem membership_rule_at : language.rewrites[0]? = some membershipRule := by
  simp [membershipRule]

theorem membership_step_of_mem (environment : Engine.RelationEnv)
    {facts : List Pattern} {selected : Pattern} (member : selected ∈ facts) :
    ReferenceStep.Step environment language (.apply "HasFact" [factStore facts, selected])
      (.apply "FactPresent" []) := by
  obtain ⟨bindings, matched⟩ := membership_match_of_mem member
  have premises : ReferenceStep.PremisesValid environment language
      (ReferenceStep.captureSites membershipRule) bindings membershipRule.premises [] bindings := by
    rw [membership_rule_premises]
    exact .nil bindings
  have valid := ReferenceStep.StepValid.rule membership_rule_at
    (by simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic] using matched) premises
  rw [membership_rule_right] at valid
  exact ⟨.rule 0 bindings [], valid⟩

private theorem other_rule_left : (language.rewrites[1]'(by decide +kernel)).left =
    .apply "ApplyGround"
      [.apply "GroundRule" [.fvar "identifier", .fvar "grounding", .fvar "conclusion",
        .apply "GroundBody" [.fvar "B"]], .apply "FactStore" [.fvar "known"]] := by
  decide +kernel

private theorem other_rule_has_no_membership_match (facts : List Pattern) (selected : Pattern) :
    matchPattern (language.rewrites[1]'(by decide +kernel)).left
      (.apply "HasFact" [factStore facts, selected]) = [] := by
  rw [other_rule_left]
  simp only [matchPattern]
  rfl

theorem membership_step_only_mem (environment : Engine.RelationEnv)
    {facts : List Pattern} {selected target : Pattern}
    (step : ReferenceStep.Step environment language
      (.apply "HasFact" [factStore facts, selected]) target) : selected ∈ facts := by
  obtain ⟨witness, valid⟩ := step
  cases valid with
  | @rule _ index rule initial final witnesses found matched premises =>
    have bound : index < language.rewrites.length := by
      by_contra outside
      rw [List.getElem?_eq_none (by omega)] at found
      cases found
    have length : language.rewrites.length = 2 := authored_kernel_nonempty
    have possibilities : index = 0 ∨ index = 1 := by omega
    rcases possibilities with rfl | rfl
    · rw [membership_rule_at] at found
      cases Option.some.inj found
      exact membership_match_only_mem
        (by simpa only [ReflectiveCanonical.matchPatternForRule_eq_syntactic] using matched)
    · have ruleAt : language.rewrites[1]? =
          some (language.rewrites[1]'(by decide +kernel)) := by simp
      rw [ruleAt] at found
      cases Option.some.inj found
      simp only [ReflectiveCanonical.matchPatternForRule_eq_syntactic,
        other_rule_has_no_membership_match] at matched
      cases matched

theorem membership_step_iff (environment : Engine.RelationEnv) (facts : List Pattern) (selected : Pattern) :
    ReferenceStep.Step environment language (.apply "HasFact" [factStore facts, selected])
      (.apply "FactPresent" []) ↔ selected ∈ facts :=
  ⟨membership_step_only_mem environment, membership_step_of_mem environment⟩

#print axioms membership_match_at
#print axioms membership_match_of_mem
#print axioms membership_match_only_mem
#print axioms membership_match_iff
#print axioms membership_step_of_mem
#print axioms membership_step_only_mem
#print axioms membership_step_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.Kernel
