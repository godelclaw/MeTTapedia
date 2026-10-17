import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipe
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceReceiptKeys

/-!
# Compact rewrite instructions and their expanded evidence

A recipe retains the selected rule, typed occurrence path, scoped
matching choices and premise choices. Assignments, the zipper and the result
are reconstructed by replay. Expanded evidence can therefore be stored or
recomputed without changing the independently declared rewrite judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipe

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open GeneralExecutionAdmission GeneralTypedSites GeneralRuleJobs ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Choices needed for one primitive rule application. The recipe is data;
neither a source derivation nor a claimed final assignment is an input. -/
structure Recipe where
  rulePosition : Nat
  address : List Nat
  typingFrames : List TypingFrame
  matching : List GeneralScopedMatchMachine.BagChoice
  premises : List GeneralPremise.Event
  deriving Repr

def Recipe.ofFiring (value : GeneralRuleJobs.Receipt) : Recipe :=
  ⟨value.job.ordinal, value.job.site.address, value.job.site.typingFrames,
    value.matcherTrace, value.premiseHistory⟩

/-- Execute the fully selected recipe, expanding its reconstructible
fields. It follows the recipe rather than searching for a rule or a match. -/
def expand (plan : Plan) (bound : List TypeExpr) (type : TypeExpr)
    (source : Pattern) (invocation : Recipe) : Option GeneralRuleJobs.Receipt := do
  let declaration ← plan.rules[invocation.rulePosition]?
  let site ← Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceChecking.replay
    (GeneralPlanEnvironment.environment plan).language plan.snapshot.free plan.permissions.sites
    bound type source invocation.address invocation.typingFrames
  let job : GeneralRuleJobs.Job := ⟨invocation.rulePosition, declaration, site⟩
  let captured ← GeneralScopedMatchReplay.replay
    ⟨declaration.rule, declaration.binding.spec, site.focusBound.length,
      .left, [], 0, [], declaration.rule.left, site.focus⟩ invocation.matching
  let completed ← GeneralPremise.RecipeChecking.replayPremises
    (GeneralPlanEnvironment.environment plan) job.context declaration.rule.premises
    captured invocation.premises
  GeneralRuleJobs.finish? plan bound type job invocation.matching captured completed invocation.premises

theorem expand_sound {plan : Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {invocation : Recipe} {value : GeneralRuleJobs.Receipt}
    (expanded : expand plan bound type source invocation = some value) :
    value.Valid plan bound type source := by
  simp only [expand, Option.bind_eq_bind, Option.bind_eq_some_iff] at expanded
  obtain ⟨declaration, selected, site, located, captured, matched, completed, premises, finished⟩ := expanded
  apply GeneralRuleJobs.finish_sound (job := ⟨invocation.rulePosition, declaration, site⟩)
  · exact ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected,
      Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceChecking.replay_sound located⟩
  · exact (GeneralScopedMatchReplay.replay_exact _ _ _).mp matched
  · exact (GeneralPremise.RecipeChecking.replayPremises_exact _ _ _ _ _ _).mp premises
  · exact finished

private theorem firing_choices {plan : Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {value : GeneralRuleJobs.Receipt}
    (valid : value.Valid plan bound type source) :
    GeneralScopedMatchMachine.TracedMatches value.job.declaration.rule value.job.declaration.binding.spec
      value.job.site.focusBound.length .left [] 0 [] value.job.declaration.rule.left
      value.job.site.focus value.matcherTrace value.captured ∧
    GeneralPremise.PremisesHold (GeneralPlanEnvironment.environment plan) value.job.context
      value.job.declaration.rule.premises value.captured value.completed value.premiseHistory := by
  have declared := GeneralRuleJobs.Job.selected_rule valid.1
  have specified := GeneralRuleJobs.Job.selected_specification valid.1
  have firing := valid.2.1
  cases firing with
  | @fire _ _ _ _ _ rule spec _ _ _ _ selected specification _ _ matching _ premises _ _ =>
    have sameRule : rule = value.job.declaration.rule := Option.some.inj (selected.symm.trans declared)
    have sameSpec : spec = value.job.declaration.binding.spec := Option.some.inj (specification.symm.trans specified)
    cases sameRule
    cases sameSpec
    exact ⟨matching, premises⟩

/-- Every original valid firing is reconstructed exactly from its choices.
The equality preserves every original occurrence and history field. -/
theorem expand_complete {plan : Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {value : GeneralRuleJobs.Receipt}
    (valid : value.Valid plan bound type source) :
    expand plan bound type source (Recipe.ofFiring value) = some value := by
  have selected := List.mk_mem_zipIdx_iff_getElem?.mp valid.1.1
  have located := Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceChecking.replay_complete valid.1.2
  have choices := firing_choices valid
  have matched := (GeneralScopedMatchReplay.replay_exact
    ⟨value.job.declaration.rule, value.job.declaration.binding.spec, value.job.site.focusBound.length,
      .left, [], 0, [], value.job.declaration.rule.left, value.job.site.focus⟩
    value.matcherTrace value.captured).mpr choices.1
  have premises := (GeneralPremise.RecipeChecking.replayPremises_exact
    (GeneralPlanEnvironment.environment plan) value.job.context value.job.declaration.rule.premises
    value.captured value.completed value.premiseHistory).mpr choices.2
  simpa only [expand, Recipe.ofFiring, selected, located, matched, premises,
    Option.bind_eq_bind, Option.bind_some] using GeneralRuleJobs.finish_complete valid

/-- On valid evidence for a fixed source, forgetting reconstructed fields
loses no information. This is not a claim about arbitrary malformed data. -/
theorem choices_injective_on_valid {plan : Plan} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {first second : GeneralRuleJobs.Receipt}
    (firstValid : first.Valid plan bound type source)
    (secondValid : second.Valid plan bound type source)
    (sameChoices : Recipe.ofFiring first = Recipe.ofFiring second) : first = second := by
  have left := expand_complete firstValid
  have right := expand_complete secondValid
  rw [sameChoices] at left
  exact Option.some.inj (left.symm.trans right)


end Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipe
