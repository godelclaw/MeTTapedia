import Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier
import Mettapedia.OSLF.MeTTaIL.ReferenceStep
import Mettapedia.OSLF.Syntax.LambdaAuthoredFullRuleProfile
import Mettapedia.OSLF.Syntax.LambdaPatternRendering

/-!
# The λ-calculus's selected steps are its reference steps

The intrinsically scoped λ semantics (`Frontier.SelectedStep`) steps by β, under a binder, and on either side of an
application, as a selection allows. The authored four-rule λ language, restricted to the selected rules
(`selectedLanguage`), steps by the reference relation. On the encodings of terms in every context the two agree:

- **sound** (`sound`): every reference step of an encoding is the encoding of a selected step;
- **complete** (`complete`): every selected step is a reference step of the encodings.

Under a binder the reference relation steps the body in place, as an open term one binder deeper, and the selected
semantics steps it in the extended context; β's contractum is the binder elimination of the encoded body by the
encoded argument (`LambdaPatternRendering.encode_inst`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Lambda.ReferenceAgreement

open Mettapedia.OSLF.Binding LambdaContextualRung LambdaScopedAuthoringComparison LambdaPatternRendering
open LambdaAuthoredFullRuleProfile
open Mettapedia.OSLF.MeTTaIL Syntax Match ReferenceStep ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.GSLT.Examples.ScopedLamCongExecution (betaRule lamCongRule)
open Mettapedia.OSLF.NativeTypes.Instances.Lambda.Frontier (Selection SelectedStep)

/-! ## The selected language -/

/-- The authored rules a selection keeps. -/
def selectedRules (selection : Selection) : List RewriteRule :=
  [(selection.beta, betaRule), (selection.lamCong, lamCongRule), (selection.appCongL, appCongLRule),
    (selection.appCongR, appCongRRule)].filterMap fun entry => if entry.1 then some entry.2 else none

/-- **The authored λ language, restricted to the selected rules.** -/
def selectedLanguage (selection : Selection) : LanguageDef := {language with rewrites := selectedRules selection}

theorem mem_selectedRules {selection : Selection} {rule : RewriteRule} :
    rule ∈ (selectedLanguage selection).rewrites ↔
      (selection.beta = true ∧ rule = betaRule) ∨ (selection.lamCong = true ∧ rule = lamCongRule) ∨
        (selection.appCongL = true ∧ rule = appCongLRule) ∨ (selection.appCongR = true ∧ rule = appCongRRule) := by
  simp only [selectedLanguage, selectedRules, List.mem_filterMap, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨entry, member, kept⟩
    rcases member with rfl | rfl | rfl | rfl <;> split_ifs at kept with enabled <;> cases kept <;>
      first
      | exact Or.inl ⟨enabled, rfl⟩
      | exact Or.inr (Or.inl ⟨enabled, rfl⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨enabled, rfl⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨enabled, rfl⟩))
  · rintro (⟨enabled, rfl⟩ | ⟨enabled, rfl⟩ | ⟨enabled, rfl⟩ | ⟨enabled, rfl⟩)
    · exact ⟨_, Or.inl rfl, by simp [enabled]⟩
    · exact ⟨_, Or.inr (Or.inl rfl), by simp [enabled]⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), by simp [enabled]⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), by simp [enabled]⟩

/-! ## Matching the rules at encodings -/

theorem beta_match (L : LanguageDef) {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) (argument : Term sig Γ .term) :
    matchPatternForRule L betaRule (encodeTerm (appT (lamT body) argument)) =
      [[("A", encodeTerm argument), ("B", encodeTerm body)]] := by
  simp [matchPatternForRule, matchPatternForRuleUsing, betaRule, matchPattern, matchArgs, mergeBindings,
    ReflectiveSubstitution.matchingPresentationForRule?, ReflectiveSubstitution.reflectiveRuleForRule?,
    appT, lamT, encodeTerm, encodeArgs, wrapBinders]

theorem lamCong_match (L : LanguageDef) {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) :
    matchPatternForRule L lamCongRule (encodeTerm (lamT body)) = [[("B", encodeTerm body)]] := by
  simp [matchPatternForRule, matchPatternForRuleUsing, lamCongRule, matchPattern, matchArgs, mergeBindings,
    ReflectiveSubstitution.matchingPresentationForRule?, ReflectiveSubstitution.reflectiveRuleForRule?,
    lamT, encodeTerm, encodeArgs, wrapBinders]

theorem appCongL_match (L : LanguageDef) {Γ : Ctx sig} (function argument : Term sig Γ .term) :
    matchPatternForRule L appCongLRule (encodeTerm (appT function argument)) =
      [[("A", encodeTerm argument), ("F", encodeTerm function)]] := by
  simp [matchPatternForRule, matchPatternForRuleUsing, appCongLRule, matchPattern, matchArgs, mergeBindings,
    ReflectiveSubstitution.matchingPresentationForRule?, ReflectiveSubstitution.reflectiveRuleForRule?,
    appT, encodeTerm, encodeArgs, wrapBinders]

theorem appCongR_match (L : LanguageDef) {Γ : Ctx sig} (function argument : Term sig Γ .term) :
    matchPatternForRule L appCongRRule (encodeTerm (appT function argument)) =
      [[("A", encodeTerm argument), ("F", encodeTerm function)]] := by
  simp [matchPatternForRule, matchPatternForRuleUsing, appCongRRule, matchPattern, matchArgs, mergeBindings,
    ReflectiveSubstitution.matchingPresentationForRule?, ReflectiveSubstitution.reflectiveRuleForRule?,
    appT, encodeTerm, encodeArgs, wrapBinders]

/-! ## Instantiating the rules' sides -/

theorem beta_target {Γ : Ctx sig} (body : Term sig (.term :: Γ) .term) (argument : Term sig Γ .term) :
    applyBindingsScoped (captureSites betaRule) [("A", encodeTerm argument), ("B", encodeTerm body)] 0 betaRule.right =
      encodeTerm (inst body argument) := by
  rw [encode_inst]
  simp [captureSites, captureSitesOf, betaRule, applyBindingsScoped, captureDepth, captureDepthList,
    Substitution.liftBVars_zero]

theorem lamCong_source (sites : Pattern) (depth : ℕ) (value : Pattern) (found : captureDepth "B" 0 sites = some depth) :
    applyBindingsScoped sites [("B", value)] depth (.fvar "B") = value := by
  simp [applyBindingsScoped, found, Substitution.liftBVars_zero]

/-! ## Sound -/

variable {relEnv : RelationEnv}

/-- A step premise's evidence: the step of its instantiated source, and its target matched against the result. -/
theorem scopedStep_inv {L : LanguageDef} {sites : Pattern} {bindings result : Bindings} {premise : ScopedStepPremise}
    {witness : Witness} (valid : PremiseValid relEnv L sites bindings (.scopedStep premise) witness result) :
    ∃ inner candidate matched, witness = .premiseStep inner candidate matched result ∧
      StepValid relEnv L
        (applyBindingsScoped sites bindings (stepDepth sites (.scopedStep premise)) premise.source) inner candidate ∧
      matched ∈ matchPattern premise.target candidate ∧ mergeBindings bindings matched = some result := by
  cases valid with
  | base base _ => simp [isBase] at base
  | step endpoints stepped matched merged =>
    simp only [stepEndpoints, Option.some.injEq, Prod.mk.injEq] at endpoints
    obtain ⟨rfl, rfl⟩ := endpoints
    exact ⟨_, _, _, rfl, stepped, matched, merged⟩

/-- What the reference relation reads off a rule's sides and premises. -/
syntax "rule_sites" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| rule_sites $[$location]?) => `(tactic| simp [captureSites, captureSitesOf, betaRule, lamCongRule,
      appCongLRule, appCongRRule, appCongLStep, appCongRStep, premiseSites, stepDepth, inPlaceDepth, captureDepth,
      captureDepthList, applyBindingsScoped, applyBindingsScopedList, Substitution.liftBVars_zero, matchPattern,
      mergeBindings, applyBindings] $[$location]?)

/-- How a rule matches an encoding. -/
syntax "rule_match" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| rule_match $[$location]?) => `(tactic| simp [matchPatternForRule, matchPatternForRuleUsing,
      ReflectiveSubstitution.matchingPresentationForRule?, ReflectiveSubstitution.reflectiveRuleForRule?,
      betaRule, lamCongRule, appCongLRule, appCongRRule, matchPattern, matchArgs, mergeBindings, encodeTerm,
      encodeArgs, wrapBinders, appT, lamT] $[$location]?)

theorem sound (selection : Selection) : ∀ {Γ : Ctx sig} (s : Term sig Γ .term) {witness : Witness} {target : Pattern},
    StepValid relEnv (selectedLanguage selection) (encodeTerm s) witness target →
      ∃ t, target = encodeTerm t ∧ SelectedStep selection Γ s t
  | _, .var _, _, _, valid => by
    cases valid with
    | rule found matched _ =>
      rcases mem_selectedRules.mp (List.mem_of_getElem? found) with
        ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
      rule_match at matched
  | _, .op .lam (.cons body .nil), _, _, valid => by
    cases valid with
    | rule found matched premises =>
      rcases mem_selectedRules.mp (List.mem_of_getElem? found) with
        ⟨_, rfl⟩ | ⟨enabled, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · rule_match at matched
      · change _ ∈ matchPatternForRule _ lamCongRule (encodeTerm (lamT body)) at matched
        rw [lamCong_match, List.mem_singleton] at matched
        subst matched
        cases premises with
        | cons first rest =>
          cases rest with
          | nil =>
            obtain ⟨inner, candidate, matchedTarget, rfl, stepped, matchedC, merged⟩ := scopedStep_inv first
            have source : applyBindingsScoped (captureSites lamCongRule) [("B", encodeTerm body)]
                (stepDepth (captureSites lamCongRule) (lamCongRule.premises.head (by simp [lamCongRule])))
                (match lamCongRule.premises.head (by simp [lamCongRule]) with
                  | .scopedStep premise => premise.source | _ => .bvar 0) = encodeTerm body := by
              rule_sites
            obtain ⟨result, rfl, child⟩ := sound selection body (source ▸ stepped)
            rule_sites at matchedC
            subst matchedC
            rule_sites at merged
            subst merged
            refine ⟨lamT result, ?_, .lamCong enabled child⟩
            rule_sites
            rfl
      · rule_match at matched
      · rule_match at matched
  | _, .op .app (.cons function (.cons argument .nil)), _, _, valid => by
    cases valid with
    | rule found matched premises =>
      rcases mem_selectedRules.mp (List.mem_of_getElem? found) with
        ⟨enabled, rfl⟩ | ⟨_, rfl⟩ | ⟨enabled, rfl⟩ | ⟨enabled, rfl⟩
      · match function with
        | .var _ => rule_match at matched
        | .op .app (.cons _ (.cons _ .nil)) => rule_match at matched
        | .op .lam (.cons body .nil) =>
          change _ ∈ matchPatternForRule _ betaRule (encodeTerm (appT (lamT body) argument)) at matched
          rw [beta_match, List.mem_singleton] at matched
          subst matched
          cases premises with
          | nil => exact ⟨inst body argument, beta_target body argument, .beta enabled body argument⟩
      · rule_match at matched
      · change _ ∈ matchPatternForRule _ appCongLRule (encodeTerm (appT function argument)) at matched
        rw [appCongL_match, List.mem_singleton] at matched
        subst matched
        cases premises with
        | cons first rest =>
          cases rest with
          | nil =>
            obtain ⟨inner, candidate, matchedTarget, rfl, stepped, matchedG, merged⟩ := scopedStep_inv first
            rule_sites at stepped
            obtain ⟨result, rfl, child⟩ := sound selection function stepped
            rule_sites at matchedG
            subst matchedG
            rule_sites at merged
            subst merged
            refine ⟨appT result argument, ?_, .appCongL enabled argument child⟩
            rule_sites
            rfl
      · change _ ∈ matchPatternForRule _ appCongRRule (encodeTerm (appT function argument)) at matched
        rw [appCongR_match, List.mem_singleton] at matched
        subst matched
        cases premises with
        | cons first rest =>
          cases rest with
          | nil =>
            obtain ⟨inner, candidate, matchedTarget, rfl, stepped, matchedB, merged⟩ := scopedStep_inv first
            rule_sites at stepped
            obtain ⟨result, rfl, child⟩ := sound selection argument stepped
            rule_sites at matchedB
            subst matchedB
            rule_sites at merged
            subst merged
            refine ⟨appT function result, ?_, .appCongR enabled function child⟩
            rule_sites
            rfl

/-! ## Complete -/

/-- A step by a rule with one step premise. -/
theorem step_of_one_premise {L : LanguageDef} {index : ℕ} {rule : RewriteRule} {source : Pattern} {initial : Bindings}
    (found : L.rewrites[index]? = some rule) (matched : initial ∈ matchPatternForRule L rule source)
    {premise : Premise} (single : rule.premises = [premise]) {premiseSource premiseTarget : Pattern}
    (endpoints : stepEndpoints premise = some (premiseSource, premiseTarget)) {witness : Witness} {candidate : Pattern}
    (stepped : StepValid relEnv L
      (applyBindingsScoped (captureSites rule) initial (stepDepth (captureSites rule) premise) premiseSource) witness
        candidate)
    {matchedTarget final : Bindings} (matchedCandidate : matchedTarget ∈ matchPattern premiseTarget candidate)
    (merged : mergeBindings initial matchedTarget = some final) :
    Step relEnv L source (applyBindingsScoped (captureSites rule) final 0 rule.right) := by
  have premises : PremisesValid relEnv L (captureSites rule) initial rule.premises
      [.premiseStep witness candidate matchedTarget final] final := by
    rw [single]
    exact .cons (.step endpoints stepped matchedCandidate merged) (.nil _)
  exact ⟨_, .rule found matched premises⟩

theorem complete (selection : Selection) {Γ : Ctx sig} {source target : Term sig Γ .term}
    (step : SelectedStep selection Γ source target) :
    Step relEnv (selectedLanguage selection) (encodeTerm source) (encodeTerm target) := by
  induction step with
  | beta enabled body argument =>
    obtain ⟨index, found⟩ := List.getElem?_of_mem (mem_selectedRules.mpr (Or.inl ⟨enabled, rfl⟩))
    have valid := StepValid.rule (relEnv := relEnv) found
      (by rw [beta_match _ body argument]; exact List.mem_singleton_self _) (PremisesValid.nil _)
    rw [beta_target body argument] at valid
    exact ⟨_, valid⟩
  | @lamCong Γ enabled source target child stepped =>
    obtain ⟨witness, valid⟩ := stepped
    obtain ⟨index, found⟩ := List.getElem?_of_mem (mem_selectedRules.mpr (Or.inr (Or.inl ⟨enabled, rfl⟩)))
    have result := step_of_one_premise found (by rw [lamCong_match _ source]; exact List.mem_singleton_self _) rfl rfl
      (by rule_sites; exact valid) (matchedTarget := [("C", encodeTerm target)])
      (final := [("C", encodeTerm target), ("B", encodeTerm source)]) (by rule_sites) (by rule_sites)
    have rendered : applyBindingsScoped (captureSites lamCongRule) [("C", encodeTerm target), ("B", encodeTerm source)] 0
        lamCongRule.right = encodeTerm (lamT target) := by
      rule_sites
      rfl
    rw [rendered] at result
    exact result
  | @appCongL Γ enabled source target argument child stepped =>
    obtain ⟨witness, valid⟩ := stepped
    obtain ⟨index, found⟩ :=
      List.getElem?_of_mem (mem_selectedRules.mpr (Or.inr (Or.inr (Or.inl ⟨enabled, rfl⟩))))
    have result := step_of_one_premise found (by rw [appCongL_match _ source argument]; exact List.mem_singleton_self _) rfl rfl
      (by rule_sites; exact valid) (matchedTarget := [("G", encodeTerm target)])
      (final := [("G", encodeTerm target), ("A", encodeTerm argument), ("F", encodeTerm source)]) (by rule_sites)
      (by rule_sites)
    have rendered : applyBindingsScoped (captureSites appCongLRule)
        [("G", encodeTerm target), ("A", encodeTerm argument), ("F", encodeTerm source)] 0 appCongLRule.right =
          encodeTerm (appT target argument) := by
      rule_sites
      rfl
    rw [rendered] at result
    exact result
  | @appCongR Γ enabled source target function child stepped =>
    obtain ⟨witness, valid⟩ := stepped
    obtain ⟨index, found⟩ :=
      List.getElem?_of_mem (mem_selectedRules.mpr (Or.inr (Or.inr (Or.inr ⟨enabled, rfl⟩))))
    have result := step_of_one_premise found (by rw [appCongR_match _ function source]; exact List.mem_singleton_self _) rfl rfl
      (by rule_sites; exact valid) (matchedTarget := [("B", encodeTerm target)])
      (final := [("B", encodeTerm target), ("A", encodeTerm source), ("F", encodeTerm function)]) (by rule_sites)
      (by rule_sites)
    have rendered : applyBindingsScoped (captureSites appCongRRule)
        [("B", encodeTerm target), ("A", encodeTerm source), ("F", encodeTerm function)] 0 appCongRRule.right =
          encodeTerm (appT function target) := by
      rule_sites
      rfl
    rw [rendered] at result
    exact result

/-- **The selected steps are the reference steps of the encodings**, in every context. -/
theorem step_iff (selection : Selection) {Γ : Ctx sig} (source : Term sig Γ .term) (target : Pattern) :
    Step relEnv (selectedLanguage selection) (encodeTerm source) target ↔
      ∃ result, target = encodeTerm result ∧ SelectedStep selection Γ source result := by
  constructor
  · rintro ⟨witness, valid⟩
    exact sound selection source valid
  · rintro ⟨result, rfl, step⟩
    exact complete selection step

end Mettapedia.OSLF.NativeTypes.Instances.Lambda.ReferenceAgreement
