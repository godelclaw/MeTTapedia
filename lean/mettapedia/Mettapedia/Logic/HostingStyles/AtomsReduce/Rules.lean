import Mettapedia.Logic.HostingStyles.AtomsReduce.Language

/-!
# The sixteen rewrites of the candidate, read on patterns

For each rewrite of the candidate this module says, on patterns and for every
language that has the rewrite, what a step by it is:

* **introduction**: the step that the rewrite gives, from a step of the part
  it is about (`step_appFunction`, …, `step_runLamBody`), from nothing
  (`step_beta`, `step_release`), or from an answer of the matching evaluator
  (`step_runRoot`);
* **inversion**: what a match of the left side and a derivation of the
  premises are (`appFunction_inv`, …, `runLamBody_inv`, `beta_inv`,
  `release_inv`, `runRoot_inv`).

The six congruences beneath a run have a premise between two runs: the step
of the part is taken in the space of the whole (`premisesAt_runs_inv`).

`left_heads` lists the heads of the sixteen left sides: nine are a run, and
the others are an application, a product, an abstraction or a dropping.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti.Language
  (betaRule betaLeft appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule
    lamBodyRule appLeft piLeft lamLeft fixedRules premisesAt_congruence_inv premisesAt_congruence
    stepAt_of_congruence stepAt_of_premiseFree apply_appFunctionRule apply_appArgumentRule
    apply_piDomainRule apply_piBodyRule apply_lamDomainRule apply_lamBodyRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVars_zero instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical (matchPatternForRule_eq_syntactic)
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution (applyBindingsForRule_eq_syntactic)
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate

variable {base : BasePremiseEvaluator} {lang : LanguageDef}

/-! ## Matching, one node at a time -/

/-- A variable matches every pattern, with one binding. -/
theorem mem_matchPattern_fvar {name : String} {pattern : Pattern} {bindings : Bindings} :
    bindings ∈ matchPattern (.fvar name) pattern ↔ bindings = [(name, pattern)] := by
  simp [matchPattern]

/-- What matches an application to one parameter. -/
theorem matched_apply_one {label : String} {parameter subject : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (.apply label [parameter]) subject) :
    ∃ argument, subject = .apply label [argument] ∧ bindings ∈ matchPattern parameter argument := by
  cases matchPattern_sound matched with
  | apply argsRel _ =>
      cases argsRel with
      | cons headRel tailRel merged =>
          cases tailRel
          have same : mergeBindings _ [] = some bindings := merged
          simp only [mergeBindings, List.foldlM_nil, Option.pure_def, Option.some.injEq] at same
          subst same
          exact ⟨_, rfl, matchRel_complete headRel⟩

/-- What matches an application to two parameters. -/
theorem matched_apply_two {label : String} {first second subject : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (.apply label [first, second]) subject) :
    ∃ left right leftBindings rightBindings, subject = .apply label [left, right] ∧
      leftBindings ∈ matchPattern first left ∧ rightBindings ∈ matchPattern second right ∧
        mergeBindings leftBindings rightBindings = some bindings := by
  cases matchPattern_sound matched with
  | apply argsRel _ =>
      cases argsRel with
      | cons headRel tailRel merged =>
          cases tailRel with
          | cons secondRel restRel mergedTail =>
              cases restRel
              have same : mergeBindings _ [] = some _ := mergedTail
              simp only [mergeBindings, List.foldlM_nil, Option.pure_def,
                Option.some.injEq] at same
              subst same
              exact ⟨_, _, _, _, rfl, matchRel_complete headRel, matchRel_complete secondRel,
                merged⟩

/-- What matches an abstraction. -/
theorem matched_lambda {binder : Option String} {body subject : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (.lambda binder body) subject) :
    ∃ name inner, subject = .lambda name inner ∧ bindings ∈ matchPattern body inner := by
  cases matchPattern_sound matched with
  | lambda bodyRel => exact ⟨_, _, rfl, matchRel_complete bodyRel⟩

/-! ## The left sides -/

/-- What matches `App(F, X)`. -/
theorem mem_matchPattern_appLeft {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern appLeft pattern) :
    ∃ function argument, pattern = .apply "App" [function, argument] ∧
      bindings = [("X", argument), ("F", function)] := by
  obtain ⟨function, argument, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "App") matched
  rw [mem_matchPattern_fvar] at inFirst inSecond
  subst inFirst
  subst inSecond
  exact ⟨function, argument, rfl, by simpa [mergeBindings] using merged.symm⟩

theorem matchPattern_appLeft_apply (function argument : Pattern) :
    matchPattern appLeft (.apply "App" [function, argument]) =
      [[("X", argument), ("F", function)]] := by
  simp [appLeft, matchPattern, matchArgs, mergeBindings]

/-- What matches `Lam(A, x. B)`. -/
theorem mem_matchPattern_lamLeft {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern lamLeft pattern) :
    ∃ domain binder body, pattern = .apply "Lam" [domain, .lambda binder body] ∧
      bindings = [("B", body), ("A", domain)] := by
  obtain ⟨domain, abstraction, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "Lam") matched
  obtain ⟨binder, body, rfl, inBody⟩ := matched_lambda inSecond
  rw [mem_matchPattern_fvar] at inFirst inBody
  subst inFirst
  subst inBody
  exact ⟨domain, binder, body, rfl, by simpa [mergeBindings] using merged.symm⟩

theorem matchPattern_lamLeft_apply (domain body : Pattern) (binder : Option String) :
    matchPattern lamLeft (.apply "Lam" [domain, .lambda binder body]) =
      [[("B", body), ("A", domain)]] := by
  simp [lamLeft, matchPattern, matchArgs, mergeBindings]

/-- What matches `Pi(A, x. B)`. -/
theorem mem_matchPattern_piLeft {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern piLeft pattern) :
    ∃ domain binder body, pattern = .apply "Pi" [domain, .lambda binder body] ∧
      bindings = [("B", body), ("A", domain)] := by
  obtain ⟨domain, abstraction, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "Pi") matched
  obtain ⟨binder, body, rfl, inBody⟩ := matched_lambda inSecond
  rw [mem_matchPattern_fvar] at inFirst inBody
  subst inFirst
  subst inBody
  exact ⟨domain, binder, body, rfl, by simpa [mergeBindings] using merged.symm⟩

theorem matchPattern_piLeft_apply (domain body : Pattern) (binder : Option String) :
    matchPattern piLeft (.apply "Pi" [domain, .lambda binder body]) =
      [[("B", body), ("A", domain)]] := by
  simp [piLeft, matchPattern, matchArgs, mergeBindings]

/-- What matches `App(Lam(A, x. B), X)`. -/
theorem mem_matchPattern_betaLeft {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern betaLeft pattern) :
    ∃ domain binder body argument,
      pattern = .apply "App" [.apply "Lam" [domain, .lambda binder body], argument] ∧
        bindings = [("X", argument), ("B", body), ("A", domain)] := by
  obtain ⟨function, argument, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "App") matched
  obtain ⟨domain, binder, body, rfl, rfl⟩ := mem_matchPattern_lamLeft inFirst
  rw [mem_matchPattern_fvar] at inSecond
  subst inSecond
  exact ⟨domain, binder, body, argument, rfl, by simpa [mergeBindings] using merged.symm⟩

theorem matchPattern_betaLeft_apply (domain body argument : Pattern) (binder : Option String) :
    matchPattern betaLeft (.apply "App" [.apply "Lam" [domain, .lambda binder body], argument]) =
      [[("X", argument), ("B", body), ("A", domain)]] := by
  simp [betaLeft, matchPattern, matchArgs, mergeBindings]

/-- What matches the dropping of a quotation. -/
theorem mem_matchPattern_releaseLeft {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern releaseRule.left pattern) :
    ∃ atom, pattern = dropped (quoted atom) ∧ bindings = [("atom", atom)] := by
  obtain ⟨name, rfl, inName⟩ := matched_apply_one (label := "prime-drop") matched
  obtain ⟨atom, rfl, inAtom⟩ := matched_apply_one (label := "prime-quote") inName
  rw [mem_matchPattern_fvar] at inAtom
  exact ⟨atom, rfl, inAtom⟩

/-- What matches a run of two variables. -/
theorem mem_matchPattern_run {spaceName subjectName : String} {pattern : Pattern}
    {bindings : Bindings} (distinct : spaceName ≠ subjectName)
    (matched : bindings ∈ matchPattern (runPattern (.fvar spaceName) (.fvar subjectName)) pattern) :
    ∃ space subject, pattern = runPattern space subject ∧
      bindings = [(subjectName, subject), (spaceName, space)] := by
  obtain ⟨space, subject, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "prime-run") matched
  rw [mem_matchPattern_fvar] at inFirst inSecond
  subst inFirst
  subst inSecond
  exact ⟨space, subject, rfl, by simpa [mergeBindings, distinct] using merged.symm⟩

/-- What matches the run of an application. -/
theorem mem_matchPattern_runApp {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (runPattern (.fvar "space") appLeft) pattern) :
    ∃ space function argument, pattern = runPattern space (.apply "App" [function, argument]) ∧
      bindings = [("F", function), ("X", argument), ("space", space)] := by
  obtain ⟨space, subject, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "prime-run") matched
  obtain ⟨function, argument, rfl, rfl⟩ := mem_matchPattern_appLeft inSecond
  rw [mem_matchPattern_fvar] at inFirst
  subst inFirst
  exact ⟨space, function, argument, rfl, by simpa [mergeBindings] using merged.symm⟩

/-- What matches the run of an abstraction. -/
theorem mem_matchPattern_runLam {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (runPattern (.fvar "space") lamLeft) pattern) :
    ∃ space domain binder body,
      pattern = runPattern space (.apply "Lam" [domain, .lambda binder body]) ∧
        bindings = [("A", domain), ("B", body), ("space", space)] := by
  obtain ⟨space, subject, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "prime-run") matched
  obtain ⟨domain, binder, body, rfl, rfl⟩ := mem_matchPattern_lamLeft inSecond
  rw [mem_matchPattern_fvar] at inFirst
  subst inFirst
  exact ⟨space, domain, binder, body, rfl, by simpa [mergeBindings] using merged.symm⟩

/-- What matches the run of a product. -/
theorem mem_matchPattern_runPi {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (runPattern (.fvar "space") piLeft) pattern) :
    ∃ space domain binder body,
      pattern = runPattern space (.apply "Pi" [domain, .lambda binder body]) ∧
        bindings = [("A", domain), ("B", body), ("space", space)] := by
  obtain ⟨space, subject, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "prime-run") matched
  obtain ⟨domain, binder, body, rfl, rfl⟩ := mem_matchPattern_piLeft inSecond
  rw [mem_matchPattern_fvar] at inFirst
  subst inFirst
  exact ⟨space, domain, binder, body, rfl, by simpa [mergeBindings] using merged.symm⟩

/-! ## Premises -/

/-- What one congruence premise gives, whatever its two patterns. -/
theorem premisesAt_single_inv {fuel : Nat} {initial final : Bindings} {source target : Pattern}
    (premises : PremisesAt base lang fuel initial [.congruence source target] final) :
    ∃ candidate found, StepAt base lang fuel (applyBindings initial source) candidate ∧
      found ∈ matchPattern target candidate ∧ mergeBindings initial found = some final := by
  cases premises with
  | cons premise rest =>
      cases rest with
      | nil =>
          cases premise with
          | congruence step matched merged => exact ⟨_, _, step, matched, merged⟩

/-- One congruence premise, from a step. -/
theorem premisesAt_single {fuel : Nat} {initial final found : Bindings} {source target : Pattern}
    {candidate : Pattern} (step : StepAt base lang fuel (applyBindings initial source) candidate)
    (matched : found ∈ matchPattern target candidate)
    (merged : mergeBindings initial found = some final) :
    PremisesAt base lang fuel initial [.congruence source target] final :=
  .cons (.congruence step matched merged) (.nil final)

/-- **The premise of a congruence beneath a run**: a step from the run of the
part, in the space of the whole, to a run in the same space. -/
theorem premisesAt_runs_inv {fuel : Nat} {initial final : Bindings} {partName nextName : String}
    {space part : Pattern} (fresh : applyBindings initial (.fvar "space") = space)
    (bound : initial.find? (·.1 == "space") = some ("space", space))
    (partValue : applyBindings initial (.fvar partName) = part)
    (unbound : initial.find? (·.1 == nextName) = none) (distinct : "space" ≠ nextName)
    (premises : PremisesAt base lang fuel initial
      [.congruence (runPattern (.fvar "space") (.fvar partName))
        (runPattern (.fvar "space") (.fvar nextName))] final) :
    ∃ next, StepAt base lang fuel (runPattern space part) (runPattern space next) ∧
      final = (nextName, next) :: initial := by
  obtain ⟨candidate, found, step, matched, merged⟩ := premisesAt_single_inv premises
  have source : applyBindings initial (runPattern (.fvar "space") (.fvar partName)) =
      runPattern space part := by
    rw [← fresh, ← partValue]
    simp [runPattern, applyBindings]
  rw [source] at step
  obtain ⟨otherSpace, next, rfl, rfl⟩ := mem_matchPattern_run distinct matched
  have merging : mergeBindings initial [(nextName, next), ("space", otherSpace)] = some final :=
    merged
  simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil, unbound, Option.pure_def,
    Option.bind_eq_bind, Option.bind_some] at merging
  have still : (((nextName, next) :: initial).find? (·.1 == "space")) = some ("space", space) := by
    have other : (nextName == "space") = false := by
      simpa using fun same : nextName = "space" => distinct same.symm
    simp [other, bound]
  rw [still] at merging
  by_cases same : space = otherSpace
  · subst same
    have result : (nextName, next) :: initial = final := by simpa using merging
    exact ⟨next, step, result.symm⟩
  · have differs : (space == otherSpace) = false := by simpa using same
    simp [differs] at merging

/-- The premise of a congruence beneath a run, from a step between two runs
in one space. -/
theorem premisesAt_runs {fuel : Nat} {initial : Bindings} {partName nextName : String}
    {space part next : Pattern} (fresh : applyBindings initial (.fvar "space") = space)
    (bound : initial.find? (·.1 == "space") = some ("space", space))
    (partValue : applyBindings initial (.fvar partName) = part)
    (unbound : initial.find? (·.1 == nextName) = none) (distinct : "space" ≠ nextName)
    (step : StepAt base lang fuel (runPattern space part) (runPattern space next)) :
    PremisesAt base lang fuel initial
      [.congruence (runPattern (.fvar "space") (.fvar partName))
        (runPattern (.fvar "space") (.fvar nextName))] ((nextName, next) :: initial) := by
  have source : applyBindings initial (runPattern (.fvar "space") (.fvar partName)) =
      runPattern space part := by
    rw [← fresh, ← partValue]
    simp [runPattern, applyBindings]
  refine premisesAt_single (found := [(nextName, next), ("space", space)]) (source ▸ step) ?_ ?_
  · simp [runPattern, matchPattern, matchArgs, mergeBindings, distinct]
  · have other : (nextName == "space") = false := by
      simpa using fun same : nextName = "space" => distinct same.symm
    simp [mergeBindings, unbound, other, bound]

/-! ## Rule by rule: a step by a rule, from its match and its premises -/

/-- A step by a rule of the language. -/
theorem stepAt_of_rule {rule : RewriteRule} (member : rule ∈ lang.rewrites) {fuel : Nat}
    {source target : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern rule.left source)
    (premises : PremisesAt base lang fuel initial rule.premises final)
    (applied : applyRuleBindings rule final = target) :
    StepAt base lang (fuel + 1) source target := by
  refine StepAt.rule (initialBindings := initial) (finalBindings := final) member ?_ premises ?_
  · rw [matchPatternForRule_eq_syntactic]
    exact matched
  · rw [applyBindingsForRule_eq_syntactic]
    exact applied

/-- What a bounded step is: a rule, a match of its left side, a derivation of
its premises, and the instance of its right side. -/
theorem exists_rule_of_stepAt {fuel : Nat} {source target : Pattern}
    (step : StepAt base lang (fuel + 1) source target) :
    ∃ rule ∈ lang.rewrites, ∃ initial final : Bindings,
      initial ∈ matchPattern rule.left source ∧
        PremisesAt base lang fuel initial rule.premises final ∧
          applyRuleBindings rule final = target := by
  cases step with
  | rule member matched premises applied =>
      rw [matchPatternForRule_eq_syntactic] at matched
      rw [applyBindingsForRule_eq_syntactic] at applied
      exact ⟨_, member, _, _, matched, premises, applied⟩

/-! ### Beta and release -/

/-- **Beta**, on patterns. -/
theorem step_beta (member : betaRule ∈ lang.rewrites) (domain body argument : Pattern)
    (binder : Option String) :
    StepAt base lang 1 (.apply "App" [.apply "Lam" [domain, .lambda binder body], argument])
      (instantiateBVar argument body) :=
  stepAt_of_rule member (initial := [("X", argument), ("B", body), ("A", domain)])
    (by rw [show betaRule.left = betaLeft from rfl, matchPattern_betaLeft_apply]
        exact List.mem_singleton.mpr rfl)
    (.nil _)
    (by simp [applyRuleBindings, betaRule, betaLeft, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero])

/-- What a step by beta is. -/
theorem beta_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern betaRule.left source)
    (premises : PremisesAt base lang fuel initial betaRule.premises final) :
    ∃ domain binder body argument,
      source = .apply "App" [.apply "Lam" [domain, .lambda binder body], argument] ∧
        applyRuleBindings betaRule final = instantiateBVar argument body := by
  obtain ⟨domain, binder, body, argument, rfl, rfl⟩ :=
    mem_matchPattern_betaLeft (show initial ∈ matchPattern betaLeft source from matched)
  cases premises
  exact ⟨domain, binder, body, argument, rfl, by
    simp [applyRuleBindings, betaRule, betaLeft, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero]⟩

/-- **Release**, on patterns. -/
theorem step_release (member : releaseRule ∈ lang.rewrites) (atom : Pattern) :
    StepAt base lang 1 (dropped (quoted atom)) atom :=
  stepAt_of_rule member (initial := [("atom", atom)])
    (by simp [releaseRule, dropped, quoted, matchPattern, matchArgs, mergeBindings])
    (.nil _)
    (by simp [applyRuleBindings, releaseRule, applyBindings])

/-- What a step by release is. -/
theorem release_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern releaseRule.left source)
    (premises : PremisesAt base lang fuel initial releaseRule.premises final) :
    ∃ atom, source = dropped (quoted atom) ∧ applyRuleBindings releaseRule final = atom := by
  obtain ⟨atom, rfl, rfl⟩ := mem_matchPattern_releaseLeft matched
  cases premises
  exact ⟨atom, rfl, by simp [applyRuleBindings, releaseRule, applyBindings]⟩

/-! ### The six congruences of an atom -/

theorem step_appFunction (member : appFunctionRule ∈ lang.rewrites) {fuel : Nat}
    {function next : Pattern} (argument : Pattern) (inner : StepAt base lang fuel function next) :
    StepAt base lang (fuel + 1) (.apply "App" [function, argument])
      (.apply "App" [next, argument]) :=
  stepAt_of_congruence (rule := appFunctionRule) member rfl
    (initial := [("X", argument), ("F", function)]) (candidate := next)
    (final := [("G", next), ("X", argument), ("F", function)])
    (by rw [show appFunctionRule.left = appLeft from rfl, matchPattern_appLeft_apply]
        exact List.mem_singleton.mpr rfl)
    (by simpa [applyBindings] using inner) (by simp [mergeBindings])
    (apply_appFunctionRule _ _ _)

theorem appFunction_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern appFunctionRule.left source)
    (premises : PremisesAt base lang fuel initial appFunctionRule.premises final) :
    ∃ function argument next, source = .apply "App" [function, argument] ∧
      StepAt base lang fuel function next ∧
        applyRuleBindings appFunctionRule final = .apply "App" [next, argument] := by
  obtain ⟨function, argument, rfl, rfl⟩ :=
    mem_matchPattern_appLeft (show initial ∈ matchPattern appLeft source from matched)
  obtain ⟨next, inner, merged⟩ := premisesAt_congruence_inv
    (show PremisesAt base lang fuel _ [.congruence (.fvar "F") (.fvar "G")] final from premises)
  simp [applyBindings] at inner
  simp [mergeBindings] at merged
  subst merged
  exact ⟨function, argument, next, rfl, inner, apply_appFunctionRule _ _ _⟩

theorem step_appArgument (member : appArgumentRule ∈ lang.rewrites) {fuel : Nat}
    {argument next : Pattern} (function : Pattern) (inner : StepAt base lang fuel argument next) :
    StepAt base lang (fuel + 1) (.apply "App" [function, argument])
      (.apply "App" [function, next]) :=
  stepAt_of_congruence (rule := appArgumentRule) member rfl
    (initial := [("X", argument), ("F", function)]) (candidate := next)
    (final := [("Y", next), ("X", argument), ("F", function)])
    (by rw [show appArgumentRule.left = appLeft from rfl, matchPattern_appLeft_apply]
        exact List.mem_singleton.mpr rfl)
    (by simpa [applyBindings] using inner) (by simp [mergeBindings])
    (apply_appArgumentRule _ _ _)

theorem appArgument_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern appArgumentRule.left source)
    (premises : PremisesAt base lang fuel initial appArgumentRule.premises final) :
    ∃ function argument next, source = .apply "App" [function, argument] ∧
      StepAt base lang fuel argument next ∧
        applyRuleBindings appArgumentRule final = .apply "App" [function, next] := by
  obtain ⟨function, argument, rfl, rfl⟩ :=
    mem_matchPattern_appLeft (show initial ∈ matchPattern appLeft source from matched)
  obtain ⟨next, inner, merged⟩ := premisesAt_congruence_inv
    (show PremisesAt base lang fuel _ [.congruence (.fvar "X") (.fvar "Y")] final from premises)
  simp [applyBindings] at inner
  simp [mergeBindings] at merged
  subst merged
  exact ⟨function, argument, next, rfl, inner, apply_appArgumentRule _ _ _⟩

theorem step_piDomain (member : piDomainRule ∈ lang.rewrites) {fuel : Nat}
    {domain next : Pattern} (body : Pattern) (binder : Option String)
    (inner : StepAt base lang fuel domain next) :
    StepAt base lang (fuel + 1) (.apply "Pi" [domain, .lambda binder body])
      (.apply "Pi" [next, .lambda none body]) :=
  stepAt_of_congruence (rule := piDomainRule) member rfl
    (initial := [("B", body), ("A", domain)]) (candidate := next)
    (final := [("C", next), ("B", body), ("A", domain)])
    (by rw [show piDomainRule.left = piLeft from rfl, matchPattern_piLeft_apply]
        exact List.mem_singleton.mpr rfl)
    (by simpa [applyBindings] using inner) (by simp [mergeBindings])
    (apply_piDomainRule _ _ _)

theorem piDomain_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern piDomainRule.left source)
    (premises : PremisesAt base lang fuel initial piDomainRule.premises final) :
    ∃ domain binder body next, source = .apply "Pi" [domain, .lambda binder body] ∧
      StepAt base lang fuel domain next ∧
        applyRuleBindings piDomainRule final = .apply "Pi" [next, .lambda none body] := by
  obtain ⟨domain, binder, body, rfl, rfl⟩ :=
    mem_matchPattern_piLeft (show initial ∈ matchPattern piLeft source from matched)
  obtain ⟨next, inner, merged⟩ := premisesAt_congruence_inv
    (show PremisesAt base lang fuel _ [.congruence (.fvar "A") (.fvar "C")] final from premises)
  simp [applyBindings] at inner
  simp [mergeBindings] at merged
  subst merged
  exact ⟨domain, binder, body, next, rfl, inner, apply_piDomainRule _ _ _⟩

theorem step_piBody (member : piBodyRule ∈ lang.rewrites) {fuel : Nat}
    {body next : Pattern} (domain : Pattern) (binder : Option String)
    (inner : StepAt base lang fuel body next) :
    StepAt base lang (fuel + 1) (.apply "Pi" [domain, .lambda binder body])
      (.apply "Pi" [domain, .lambda none next]) :=
  stepAt_of_congruence (rule := piBodyRule) member rfl
    (initial := [("B", body), ("A", domain)]) (candidate := next)
    (final := [("D", next), ("B", body), ("A", domain)])
    (by rw [show piBodyRule.left = piLeft from rfl, matchPattern_piLeft_apply]
        exact List.mem_singleton.mpr rfl)
    (by simpa [applyBindings] using inner) (by simp [mergeBindings])
    (apply_piBodyRule _ _ _)

theorem piBody_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern piBodyRule.left source)
    (premises : PremisesAt base lang fuel initial piBodyRule.premises final) :
    ∃ domain binder body next, source = .apply "Pi" [domain, .lambda binder body] ∧
      StepAt base lang fuel body next ∧
        applyRuleBindings piBodyRule final = .apply "Pi" [domain, .lambda none next] := by
  obtain ⟨domain, binder, body, rfl, rfl⟩ :=
    mem_matchPattern_piLeft (show initial ∈ matchPattern piLeft source from matched)
  obtain ⟨next, inner, merged⟩ := premisesAt_congruence_inv
    (show PremisesAt base lang fuel _ [.congruence (.fvar "B") (.fvar "D")] final from premises)
  simp [applyBindings] at inner
  simp [mergeBindings] at merged
  subst merged
  exact ⟨domain, binder, body, next, rfl, inner, apply_piBodyRule _ _ _⟩

theorem step_lamDomain (member : lamDomainRule ∈ lang.rewrites) {fuel : Nat}
    {domain next : Pattern} (body : Pattern) (binder : Option String)
    (inner : StepAt base lang fuel domain next) :
    StepAt base lang (fuel + 1) (.apply "Lam" [domain, .lambda binder body])
      (.apply "Lam" [next, .lambda none body]) :=
  stepAt_of_congruence (rule := lamDomainRule) member rfl
    (initial := [("B", body), ("A", domain)]) (candidate := next)
    (final := [("C", next), ("B", body), ("A", domain)])
    (by rw [show lamDomainRule.left = lamLeft from rfl, matchPattern_lamLeft_apply]
        exact List.mem_singleton.mpr rfl)
    (by simpa [applyBindings] using inner) (by simp [mergeBindings])
    (apply_lamDomainRule _ _ _)

theorem lamDomain_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern lamDomainRule.left source)
    (premises : PremisesAt base lang fuel initial lamDomainRule.premises final) :
    ∃ domain binder body next, source = .apply "Lam" [domain, .lambda binder body] ∧
      StepAt base lang fuel domain next ∧
        applyRuleBindings lamDomainRule final = .apply "Lam" [next, .lambda none body] := by
  obtain ⟨domain, binder, body, rfl, rfl⟩ :=
    mem_matchPattern_lamLeft (show initial ∈ matchPattern lamLeft source from matched)
  obtain ⟨next, inner, merged⟩ := premisesAt_congruence_inv
    (show PremisesAt base lang fuel _ [.congruence (.fvar "A") (.fvar "C")] final from premises)
  simp [applyBindings] at inner
  simp [mergeBindings] at merged
  subst merged
  exact ⟨domain, binder, body, next, rfl, inner, apply_lamDomainRule _ _ _⟩

theorem step_lamBody (member : lamBodyRule ∈ lang.rewrites) {fuel : Nat}
    {body next : Pattern} (domain : Pattern) (binder : Option String)
    (inner : StepAt base lang fuel body next) :
    StepAt base lang (fuel + 1) (.apply "Lam" [domain, .lambda binder body])
      (.apply "Lam" [domain, .lambda none next]) :=
  stepAt_of_congruence (rule := lamBodyRule) member rfl
    (initial := [("B", body), ("A", domain)]) (candidate := next)
    (final := [("D", next), ("B", body), ("A", domain)])
    (by rw [show lamBodyRule.left = lamLeft from rfl, matchPattern_lamLeft_apply]
        exact List.mem_singleton.mpr rfl)
    (by simpa [applyBindings] using inner) (by simp [mergeBindings])
    (apply_lamBodyRule _ _ _)

theorem lamBody_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern lamBodyRule.left source)
    (premises : PremisesAt base lang fuel initial lamBodyRule.premises final) :
    ∃ domain binder body next, source = .apply "Lam" [domain, .lambda binder body] ∧
      StepAt base lang fuel body next ∧
        applyRuleBindings lamBodyRule final = .apply "Lam" [domain, .lambda none next] := by
  obtain ⟨domain, binder, body, rfl, rfl⟩ :=
    mem_matchPattern_lamLeft (show initial ∈ matchPattern lamLeft source from matched)
  obtain ⟨next, inner, merged⟩ := premisesAt_congruence_inv
    (show PremisesAt base lang fuel _ [.congruence (.fvar "B") (.fvar "D")] final from premises)
  simp [applyBindings] at inner
  simp [mergeBindings] at merged
  subst merged
  exact ⟨domain, binder, body, next, rfl, inner, apply_lamBodyRule _ _ _⟩

/-! ### Beneath a run -/

/-- **A step of the subject of a run is a step of the run.** -/
theorem step_runSubject (member : runSubjectRule ∈ lang.rewrites) {fuel : Nat}
    {subject next : Pattern} (space : Pattern) (inner : StepAt base lang fuel subject next) :
    StepAt base lang (fuel + 1) (runPattern space subject) (runPattern space next) :=
  stepAt_of_rule (rule := runSubjectRule) member
    (initial := [("X", subject), ("space", space)])
    (final := [("Y", next), ("X", subject), ("space", space)])
    (by simp [runSubjectRule, runPattern, matchPattern, matchArgs, mergeBindings])
    (premisesAt_congruence (by simpa [applyBindings] using inner) (by simp [mergeBindings]))
    (by simp [applyRuleBindings, runSubjectRule, runPattern, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero])

theorem runSubject_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runSubjectRule.left source)
    (premises : PremisesAt base lang fuel initial runSubjectRule.premises final) :
    ∃ space subject next, source = runPattern space subject ∧
      StepAt base lang fuel subject next ∧
        applyRuleBindings runSubjectRule final = runPattern space next := by
  obtain ⟨space, subject, rfl, rfl⟩ := mem_matchPattern_run (by decide)
    (show initial ∈ matchPattern (runPattern (.fvar "space") (.fvar "X")) source from matched)
  obtain ⟨next, inner, merged⟩ := premisesAt_congruence_inv
    (show PremisesAt base lang fuel _ [.congruence (.fvar "X") (.fvar "Y")] final from premises)
  simp [applyBindings] at inner
  simp [mergeBindings] at merged
  subst merged
  exact ⟨space, subject, next, rfl, inner, by
    simp [applyRuleBindings, runSubjectRule, runPattern, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero]⟩

theorem step_runAppFunction (member : runAppFunctionRule ∈ lang.rewrites) {fuel : Nat}
    {space function next : Pattern} (argument : Pattern)
    (inner : StepAt base lang fuel (runPattern space function) (runPattern space next)) :
    StepAt base lang (fuel + 1) (runPattern space (.apply "App" [function, argument]))
      (runPattern space (.apply "App" [next, argument])) :=
  stepAt_of_rule (rule := runAppFunctionRule) member
    (initial := [("F", function), ("X", argument), ("space", space)])
    (by simp [runAppFunctionRule, runPattern, appLeft, matchPattern, matchArgs, mergeBindings])
    (premisesAt_runs (partName := "F") (nextName := "G") (by simp [applyBindings]) (by simp)
      (by simp [applyBindings]) (by simp) (by decide) inner)
    (by simp [applyRuleBindings, runAppFunctionRule, runPattern, appLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero])

theorem runAppFunction_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runAppFunctionRule.left source)
    (premises : PremisesAt base lang fuel initial runAppFunctionRule.premises final) :
    ∃ space function argument next,
      source = runPattern space (.apply "App" [function, argument]) ∧
        StepAt base lang fuel (runPattern space function) (runPattern space next) ∧
          applyRuleBindings runAppFunctionRule final =
            runPattern space (.apply "App" [next, argument]) := by
  obtain ⟨space, function, argument, rfl, rfl⟩ := mem_matchPattern_runApp matched
  obtain ⟨next, inner, rfl⟩ := premisesAt_runs_inv (partName := "F") (nextName := "G")
    (space := space) (part := function) (by simp [applyBindings]) (by simp)
    (by simp [applyBindings]) (by simp) (by decide) premises
  exact ⟨space, function, argument, next, rfl, inner, by
    simp [applyRuleBindings, runAppFunctionRule, runPattern, appLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero]⟩

theorem step_runAppArgument (member : runAppArgumentRule ∈ lang.rewrites) {fuel : Nat}
    {space argument next : Pattern} (function : Pattern)
    (inner : StepAt base lang fuel (runPattern space argument) (runPattern space next)) :
    StepAt base lang (fuel + 1) (runPattern space (.apply "App" [function, argument]))
      (runPattern space (.apply "App" [function, next])) :=
  stepAt_of_rule (rule := runAppArgumentRule) member
    (initial := [("F", function), ("X", argument), ("space", space)])
    (by simp [runAppArgumentRule, runPattern, appLeft, matchPattern, matchArgs, mergeBindings])
    (premisesAt_runs (partName := "X") (nextName := "Y") (by simp [applyBindings]) (by simp)
      (by simp [applyBindings]) (by simp) (by decide) inner)
    (by simp [applyRuleBindings, runAppArgumentRule, runPattern, appLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero])

theorem runAppArgument_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runAppArgumentRule.left source)
    (premises : PremisesAt base lang fuel initial runAppArgumentRule.premises final) :
    ∃ space function argument next,
      source = runPattern space (.apply "App" [function, argument]) ∧
        StepAt base lang fuel (runPattern space argument) (runPattern space next) ∧
          applyRuleBindings runAppArgumentRule final =
            runPattern space (.apply "App" [function, next]) := by
  obtain ⟨space, function, argument, rfl, rfl⟩ := mem_matchPattern_runApp matched
  obtain ⟨next, inner, rfl⟩ := premisesAt_runs_inv (partName := "X") (nextName := "Y")
    (space := space) (part := argument) (by simp [applyBindings]) (by simp)
    (by simp [applyBindings]) (by simp) (by decide) premises
  exact ⟨space, function, argument, next, rfl, inner, by
    simp [applyRuleBindings, runAppArgumentRule, runPattern, appLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero]⟩

theorem step_runPiDomain (member : runPiDomainRule ∈ lang.rewrites) {fuel : Nat}
    {space domain next : Pattern} (body : Pattern) (binder : Option String)
    (inner : StepAt base lang fuel (runPattern space domain) (runPattern space next)) :
    StepAt base lang (fuel + 1) (runPattern space (.apply "Pi" [domain, .lambda binder body]))
      (runPattern space (.apply "Pi" [next, .lambda none body])) :=
  stepAt_of_rule (rule := runPiDomainRule) member
    (initial := [("A", domain), ("B", body), ("space", space)])
    (by simp [runPiDomainRule, runPattern, piLeft, matchPattern, matchArgs, mergeBindings])
    (premisesAt_runs (partName := "A") (nextName := "C") (by simp [applyBindings]) (by simp)
      (by simp [applyBindings]) (by simp) (by decide) inner)
    (by simp [applyRuleBindings, runPiDomainRule, runPattern, piLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero])

theorem runPiDomain_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runPiDomainRule.left source)
    (premises : PremisesAt base lang fuel initial runPiDomainRule.premises final) :
    ∃ space domain binder body next,
      source = runPattern space (.apply "Pi" [domain, .lambda binder body]) ∧
        StepAt base lang fuel (runPattern space domain) (runPattern space next) ∧
          applyRuleBindings runPiDomainRule final =
            runPattern space (.apply "Pi" [next, .lambda none body]) := by
  obtain ⟨space, domain, binder, body, rfl, rfl⟩ := mem_matchPattern_runPi matched
  obtain ⟨next, inner, rfl⟩ := premisesAt_runs_inv (partName := "A") (nextName := "C")
    (space := space) (part := domain) (by simp [applyBindings]) (by simp)
    (by simp [applyBindings]) (by simp) (by decide) premises
  exact ⟨space, domain, binder, body, next, rfl, inner, by
    simp [applyRuleBindings, runPiDomainRule, runPattern, piLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero]⟩

theorem step_runPiBody (member : runPiBodyRule ∈ lang.rewrites) {fuel : Nat}
    {space body next : Pattern} (domain : Pattern) (binder : Option String)
    (inner : StepAt base lang fuel (runPattern space body) (runPattern space next)) :
    StepAt base lang (fuel + 1) (runPattern space (.apply "Pi" [domain, .lambda binder body]))
      (runPattern space (.apply "Pi" [domain, .lambda none next])) :=
  stepAt_of_rule (rule := runPiBodyRule) member
    (initial := [("A", domain), ("B", body), ("space", space)])
    (by simp [runPiBodyRule, runPattern, piLeft, matchPattern, matchArgs, mergeBindings])
    (premisesAt_runs (partName := "B") (nextName := "D") (by simp [applyBindings]) (by simp)
      (by simp [applyBindings]) (by simp) (by decide) inner)
    (by simp [applyRuleBindings, runPiBodyRule, runPattern, piLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero])

theorem runPiBody_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runPiBodyRule.left source)
    (premises : PremisesAt base lang fuel initial runPiBodyRule.premises final) :
    ∃ space domain binder body next,
      source = runPattern space (.apply "Pi" [domain, .lambda binder body]) ∧
        StepAt base lang fuel (runPattern space body) (runPattern space next) ∧
          applyRuleBindings runPiBodyRule final =
            runPattern space (.apply "Pi" [domain, .lambda none next]) := by
  obtain ⟨space, domain, binder, body, rfl, rfl⟩ := mem_matchPattern_runPi matched
  obtain ⟨next, inner, rfl⟩ := premisesAt_runs_inv (partName := "B") (nextName := "D")
    (space := space) (part := body) (by simp [applyBindings]) (by simp)
    (by simp [applyBindings]) (by simp) (by decide) premises
  exact ⟨space, domain, binder, body, next, rfl, inner, by
    simp [applyRuleBindings, runPiBodyRule, runPattern, piLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero]⟩

theorem step_runLamDomain (member : runLamDomainRule ∈ lang.rewrites) {fuel : Nat}
    {space domain next : Pattern} (body : Pattern) (binder : Option String)
    (inner : StepAt base lang fuel (runPattern space domain) (runPattern space next)) :
    StepAt base lang (fuel + 1) (runPattern space (.apply "Lam" [domain, .lambda binder body]))
      (runPattern space (.apply "Lam" [next, .lambda none body])) :=
  stepAt_of_rule (rule := runLamDomainRule) member
    (initial := [("A", domain), ("B", body), ("space", space)])
    (by simp [runLamDomainRule, runPattern, lamLeft, matchPattern, matchArgs, mergeBindings])
    (premisesAt_runs (partName := "A") (nextName := "C") (by simp [applyBindings]) (by simp)
      (by simp [applyBindings]) (by simp) (by decide) inner)
    (by simp [applyRuleBindings, runLamDomainRule, runPattern, lamLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero])

theorem runLamDomain_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runLamDomainRule.left source)
    (premises : PremisesAt base lang fuel initial runLamDomainRule.premises final) :
    ∃ space domain binder body next,
      source = runPattern space (.apply "Lam" [domain, .lambda binder body]) ∧
        StepAt base lang fuel (runPattern space domain) (runPattern space next) ∧
          applyRuleBindings runLamDomainRule final =
            runPattern space (.apply "Lam" [next, .lambda none body]) := by
  obtain ⟨space, domain, binder, body, rfl, rfl⟩ := mem_matchPattern_runLam matched
  obtain ⟨next, inner, rfl⟩ := premisesAt_runs_inv (partName := "A") (nextName := "C")
    (space := space) (part := domain) (by simp [applyBindings]) (by simp)
    (by simp [applyBindings]) (by simp) (by decide) premises
  exact ⟨space, domain, binder, body, next, rfl, inner, by
    simp [applyRuleBindings, runLamDomainRule, runPattern, lamLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero]⟩

theorem step_runLamBody (member : runLamBodyRule ∈ lang.rewrites) {fuel : Nat}
    {space body next : Pattern} (domain : Pattern) (binder : Option String)
    (inner : StepAt base lang fuel (runPattern space body) (runPattern space next)) :
    StepAt base lang (fuel + 1) (runPattern space (.apply "Lam" [domain, .lambda binder body]))
      (runPattern space (.apply "Lam" [domain, .lambda none next])) :=
  stepAt_of_rule (rule := runLamBodyRule) member
    (initial := [("A", domain), ("B", body), ("space", space)])
    (by simp [runLamBodyRule, runPattern, lamLeft, matchPattern, matchArgs, mergeBindings])
    (premisesAt_runs (partName := "B") (nextName := "D") (by simp [applyBindings]) (by simp)
      (by simp [applyBindings]) (by simp) (by decide) inner)
    (by simp [applyRuleBindings, runLamBodyRule, runPattern, lamLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero])

theorem runLamBody_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runLamBodyRule.left source)
    (premises : PremisesAt base lang fuel initial runLamBodyRule.premises final) :
    ∃ space domain binder body next,
      source = runPattern space (.apply "Lam" [domain, .lambda binder body]) ∧
        StepAt base lang fuel (runPattern space body) (runPattern space next) ∧
          applyRuleBindings runLamBodyRule final =
            runPattern space (.apply "Lam" [domain, .lambda none next]) := by
  obtain ⟨space, domain, binder, body, rfl, rfl⟩ := mem_matchPattern_runLam matched
  obtain ⟨next, inner, rfl⟩ := premisesAt_runs_inv (partName := "B") (nextName := "D")
    (space := space) (part := body) (by simp [applyBindings]) (by simp)
    (by simp [applyBindings]) (by simp) (by decide) premises
  exact ⟨space, domain, binder, body, next, rfl, inner, by
    simp [applyRuleBindings, runLamBodyRule, runPattern, lamLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero]⟩

/-! ### The root step of a run -/

/-- **The root step of a run**, under the matching evaluator: to the run of
an answer of the space for the subject, both read up to the static
equivalence. -/
theorem step_runRoot (member : runRewrite ∈ lang.rewrites) {space subject answer : Pattern}
    (found : answer ∈ matchResults (contract space) (contract subject)) :
    StepAt matchingEvaluator lang 1 (runPattern space subject) (runPattern space answer) := by
  refine stepAt_of_rule (rule := runRewrite) member
    (initial := [("subject", subject), ("space", space)])
    (final := [("answer", answer), ("subject", subject), ("space", space)]) ?_ ?_ ?_
  · simp [runRewrite, runPattern, matchPattern, matchArgs, mergeBindings]
  · refine .cons (.relationQuery ?_) (.nil _)
    show _ ∈ (matchResults
      (contract (applyBindings [("subject", subject), ("space", space)] (.fvar "space")))
      (contract (applyBindings [("subject", subject), ("space", space)] (.fvar "subject")))).map
        fun result => ("answer", result) :: [("subject", subject), ("space", space)]
    have spaceValue : applyBindings [("subject", subject), ("space", space)] (.fvar "space") =
        space := by simp [applyBindings]
    have subjectValue : applyBindings [("subject", subject), ("space", space)] (.fvar "subject") =
        subject := by simp [applyBindings]
    rw [spaceValue, subjectValue]
    exact List.mem_map.mpr ⟨answer, found, rfl⟩
  · simp [applyRuleBindings, runRewrite, runPattern, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero]

/-- What a root step of a run is, under the matching evaluator. -/
theorem runRoot_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runRewrite.left source)
    (premises : PremisesAt matchingEvaluator lang fuel initial runRewrite.premises final) :
    ∃ space subject answer, source = runPattern space subject ∧
      answer ∈ matchResults (contract space) (contract subject) ∧
        applyRuleBindings runRewrite final = runPattern space answer := by
  obtain ⟨space, subject, rfl, rfl⟩ := mem_matchPattern_run (by decide)
    (show initial ∈ matchPattern (runPattern (.fvar "space") (.fvar "subject")) source from matched)
  have premises' : PremisesAt matchingEvaluator lang fuel [("subject", subject), ("space", space)]
      [runPremise] final := premises
  cases premises' with
  | cons first rest =>
      cases rest
      cases first with
      | relationQuery answered =>
          have answers : final ∈ (matchResults
              (contract (applyBindings [("subject", subject), ("space", space)] (.fvar "space")))
              (contract (applyBindings [("subject", subject), ("space", space)]
                (.fvar "subject")))).map
                fun result => ("answer", result) :: [("subject", subject), ("space", space)] :=
            answered
          have spaceValue : applyBindings [("subject", subject), ("space", space)]
              (.fvar "space") = space := by simp [applyBindings]
          have subjectValue : applyBindings [("subject", subject), ("space", space)]
              (.fvar "subject") = subject := by simp [applyBindings]
          rw [spaceValue, subjectValue] at answers
          obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
          exact ⟨space, subject, answer, rfl, found, by
            simp [applyRuleBindings, runRewrite, runPattern, applyBindingsScoped, captureDepth,
              captureDepthList, liftBVars_zero]⟩

/-! ## The heads of the left sides -/

/-- **The heads of the sixteen left sides.**  Nine rewrites are about a run;
the seven others are about an application, a product, an abstraction or a
dropping.  No left side is headed by a quotation, a symbol, a variable, an
equation or a space: there is no congruence beneath those. -/
theorem left_heads :
    atomsReduce.rewrites.map (fun rule => head? rule.left) =
      [some "App", some "App", some "App", some "Pi", some "Pi", some "Lam", some "Lam",
        some "prime-drop", some "prime-run", some "prime-run", some "prime-run", some "prime-run",
        some "prime-run", some "prime-run", some "prime-run", some "prime-run"] := by
  rfl

#print axioms mem_matchPattern_betaLeft
#print axioms premisesAt_runs_inv
#print axioms premisesAt_runs
#print axioms step_beta
#print axioms beta_inv
#print axioms step_release
#print axioms release_inv
#print axioms step_appFunction
#print axioms appFunction_inv
#print axioms step_lamBody
#print axioms lamBody_inv
#print axioms step_runSubject
#print axioms runSubject_inv
#print axioms step_runAppFunction
#print axioms runAppFunction_inv
#print axioms step_runLamBody
#print axioms runLamBody_inv
#print axioms step_runRoot
#print axioms runRoot_inv
#print axioms left_heads

end Mettapedia.Logic.HostingStyles.AtomsReduce
