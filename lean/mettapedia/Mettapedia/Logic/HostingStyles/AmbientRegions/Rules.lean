import Mettapedia.Logic.HostingStyles.AmbientRegions.Language

/-!
# The rewrites of the two presentations, read on patterns

For the rewrites that the two presentations add to those whose steps are read
already (`AtomsReduce.Rules`), this module says what a step by each is, on
patterns and for every language that has the rewrite:

* the ambient root step and the root step of a run **under the evaluator of a
  region** (`step_ambientRoot`, `ambientRoot_inv`, `step_regionRunRoot`,
  `regionRunRoot_inv`): a step to an answer that the guard admitted, of the
  ambient space in the first case and of the space of the run in the second;
* beta, release and the step of a run, each beneath a run (`step_runBeta`,
  `runBeta_inv`, `step_runRelease`, `runRelease_inv`, `step_runBeneathRun`,
  `runBeneathRun_inv`).

The statements `step_root`, `root_inv`, `step_runRoot` and `runRoot_inv` of
the earlier modules are the same facts for the evaluator of the ambient
family and for the matching evaluator; they are stated again here because the
evaluator is another one.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti.Language
  (betaRule betaLeft appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule
    lamBodyRule appLeft piLeft lamLeft fixedRules)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVars_zero instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace

variable {base : BasePremiseEvaluator} {lang : LanguageDef} {admits : Pattern → Bool}
  {ambientSpace : Pattern}

/-! ## What matches a left side headed by a constructor -/

/-- What matches a run is a run. -/
theorem eq_run_of_matched {left right source : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (runPattern left right) source) :
    ∃ space subject, source = runPattern space subject := by
  obtain ⟨arguments, rfl, length⟩ := eq_apply_of_matched matched
  obtain ⟨space, subject, rfl⟩ := List.length_eq_two.mp length
  exact ⟨space, subject, rfl⟩

/-- An application of one constructor matches no application of another. -/
theorem apply_not_matched {label other : String} (differ : label ≠ other)
    {parameters arguments : List Pattern} {bindings : Bindings} :
    bindings ∉ matchPattern (.apply label parameters) (.apply other arguments) := by
  intro matched
  obtain ⟨found, shape, -⟩ := eq_apply_of_matched matched
  simp only [Pattern.apply.injEq] at shape
  exact differ shape.1.symm

/-- **Negative**: a bound variable matches no application. -/
theorem bvar_not_matched {label : String} {parameters : List Pattern} {index : Nat}
    {bindings : Bindings} : bindings ∉ matchPattern (.apply label parameters) (.bvar index) := by
  intro matched
  obtain ⟨found, shape, -⟩ := eq_apply_of_matched matched
  cases shape

/-! ## The ambient root step, under the evaluator of a region -/

/-- **The ambient root step**: from a pattern to an answer of the ambient
space for it that the guard admitted. -/
theorem step_ambientRoot (member : rootRule ∈ lang.rewrites) {subject answer : Pattern}
    (found : answer ∈ admittedAnswers admits ambientSpace subject) :
    StepAt (regionEvaluator admits ambientSpace) lang 1 subject answer := by
  refine stepAt_of_rule (rule := rootRule) member (initial := [("subject", subject)])
    (final := [("answer", answer), ("subject", subject)]) ?_ ?_ ?_
  · simp [rootRule, matchPattern]
  · refine .cons (.relationQuery ?_) (.nil _)
    show _ ∈ (admittedAnswers admits ambientSpace
      (applyBindings [("subject", subject)] (.fvar "subject"))).map
        fun result => ("answer", result) :: [("subject", subject)]
    have subjectValue : applyBindings [("subject", subject)] (.fvar "subject") = subject := by
      simp [applyBindings]
    rw [subjectValue]
    exact List.mem_map.mpr ⟨answer, found, rfl⟩
  · simp [applyRuleBindings, rootRule, applyBindings]

/-- What an ambient root step is. -/
theorem ambientRoot_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern rootRule.left source)
    (premises : PremisesAt (regionEvaluator admits ambientSpace) lang fuel initial
      rootRule.premises final) :
    ∃ answer, answer ∈ admittedAnswers admits ambientSpace source ∧
      applyRuleBindings rootRule final = answer := by
  have bound : initial = [("subject", source)] :=
    mem_matchPattern_fvar.mp (show initial ∈ matchPattern (.fvar "subject") source from matched)
  subst bound
  have premises' : PremisesAt (regionEvaluator admits ambientSpace) lang fuel
      [("subject", source)] [rootPremise] final := premises
  cases premises' with
  | cons first rest =>
      cases rest
      cases first with
      | relationQuery answered =>
          have answers : final ∈ (admittedAnswers admits ambientSpace
              (applyBindings [("subject", source)] (.fvar "subject"))).map
                fun result => ("answer", result) :: [("subject", source)] := answered
          have subjectValue : applyBindings [("subject", source)] (.fvar "subject") = source := by
            simp [applyBindings]
          rw [subjectValue] at answers
          obtain ⟨answer, found, rfl⟩ := List.mem_map.mp answers
          exact ⟨answer, found, by simp [applyRuleBindings, rootRule, applyBindings]⟩

/-- **Negative**: a subject that the guard refuses has no ambient root
step. -/
theorem ambientRoot_refused {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (refused : admits (contract source) = false)
    (matched : initial ∈ matchPattern rootRule.left source) :
    ¬ PremisesAt (regionEvaluator admits ambientSpace) lang fuel initial rootRule.premises
      final := by
  intro premises
  obtain ⟨answer, found, -⟩ := ambientRoot_inv matched premises
  rw [admittedAnswers_of_not_admitted refused] at found
  cases found

/-! ## The root step of a run, under the evaluator of a region -/

/-- **The root step of a run**: to the run of an answer of the space of the
run for the subject that the guard admitted.  The ambient space is not
asked. -/
theorem step_regionRunRoot (member : runRewrite ∈ lang.rewrites) {space subject answer : Pattern}
    (found : answer ∈ admittedAnswers admits space subject) :
    StepAt (regionEvaluator admits ambientSpace) lang 1 (runPattern space subject)
      (runPattern space answer) := by
  refine stepAt_of_rule (rule := runRewrite) member
    (initial := [("subject", subject), ("space", space)])
    (final := [("answer", answer), ("subject", subject), ("space", space)]) ?_ ?_ ?_
  · simp [runRewrite, runPattern, matchPattern, matchArgs, mergeBindings]
  · refine .cons (.relationQuery ?_) (.nil _)
    show _ ∈ (admittedAnswers admits
      (applyBindings [("subject", subject), ("space", space)] (.fvar "space"))
      (applyBindings [("subject", subject), ("space", space)] (.fvar "subject"))).map
        fun result => ("answer", result) :: [("subject", subject), ("space", space)]
    have spaceValue : applyBindings [("subject", subject), ("space", space)] (.fvar "space") =
        space := by simp [applyBindings]
    have subjectValue : applyBindings [("subject", subject), ("space", space)] (.fvar "subject") =
        subject := by simp [applyBindings]
    rw [spaceValue, subjectValue]
    exact List.mem_map.mpr ⟨answer, found, rfl⟩
  · simp [applyRuleBindings, runRewrite, runPattern, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero]

/-- What a root step of a run is. -/
theorem regionRunRoot_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runRewrite.left source)
    (premises : PremisesAt (regionEvaluator admits ambientSpace) lang fuel initial
      runRewrite.premises final) :
    ∃ space subject answer, source = runPattern space subject ∧
      answer ∈ admittedAnswers admits space subject ∧
        applyRuleBindings runRewrite final = runPattern space answer := by
  obtain ⟨space, subject, rfl, rfl⟩ := mem_matchPattern_run (by decide)
    (show initial ∈ matchPattern (runPattern (.fvar "space") (.fvar "subject")) source from matched)
  have premises' : PremisesAt (regionEvaluator admits ambientSpace) lang fuel
      [("subject", subject), ("space", space)] [runPremise] final := premises
  cases premises' with
  | cons first rest =>
      cases rest
      cases first with
      | relationQuery answered =>
          have answers : final ∈ (admittedAnswers admits
              (applyBindings [("subject", subject), ("space", space)] (.fvar "space"))
              (applyBindings [("subject", subject), ("space", space)] (.fvar "subject"))).map
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

/-! ## Beta beneath a run -/

/-- What matches the run of a beta redex. -/
theorem mem_matchPattern_runBeta {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern (runPattern (.fvar "space") betaLeft) pattern) :
    ∃ space domain binder body argument,
      pattern = runPattern space
        (.apply "App" [.apply "Lam" [domain, .lambda binder body], argument]) ∧
        bindings = [("A", domain), ("B", body), ("X", argument), ("space", space)] := by
  obtain ⟨space, subject, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "prime-run") matched
  obtain ⟨domain, binder, body, argument, rfl, rfl⟩ := mem_matchPattern_betaLeft inSecond
  rw [mem_matchPattern_fvar] at inFirst
  subst inFirst
  exact ⟨space, domain, binder, body, argument, rfl, by simpa [mergeBindings] using merged.symm⟩

/-- **Beta beneath a run**, on patterns: no premise is asked. -/
theorem step_runBeta (member : runBetaRule ∈ lang.rewrites) (space domain body argument : Pattern)
    (binder : Option String) :
    StepAt base lang 1
      (runPattern space (.apply "App" [.apply "Lam" [domain, .lambda binder body], argument]))
      (runPattern space (instantiateBVar argument body)) :=
  stepAt_of_rule member (initial := [("A", domain), ("B", body), ("X", argument), ("space", space)])
    (by simp [runBetaRule, runPattern, betaLeft, matchPattern, matchArgs, mergeBindings])
    (.nil _)
    (by simp [applyRuleBindings, runBetaRule, runPattern, betaLeft, applyBindingsScoped,
      captureDepth, captureDepthList, liftBVars_zero])

/-- What a step by beta beneath a run is. -/
theorem runBeta_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runBetaRule.left source)
    (premises : PremisesAt base lang fuel initial runBetaRule.premises final) :
    ∃ space domain binder body argument,
      source = runPattern space
        (.apply "App" [.apply "Lam" [domain, .lambda binder body], argument]) ∧
        applyRuleBindings runBetaRule final = runPattern space (instantiateBVar argument body) := by
  obtain ⟨space, domain, binder, body, argument, rfl, rfl⟩ := mem_matchPattern_runBeta matched
  cases premises
  exact ⟨space, domain, binder, body, argument, rfl, by
    simp [applyRuleBindings, runBetaRule, runPattern, betaLeft, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero]⟩

/-- **Negative**: the run of a symbol is no beta redex beneath a run. -/
theorem runBeta_not_matched_symbol {space : Pattern} {code : Nat} {bindings : Bindings} :
    bindings ∉ matchPattern runBetaRule.left (runPattern space (symbolAtom code)) := by
  intro matched
  obtain ⟨other, domain, binder, body, argument, shape, -⟩ := mem_matchPattern_runBeta matched
  simp [runPattern, symbolAtom] at shape

/-! ## Release beneath a run -/

/-- What matches the run of a dropped quotation. -/
theorem mem_matchPattern_runRelease {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern runReleaseRule.left pattern) :
    ∃ space atom, pattern = runPattern space (dropped (quoted atom)) ∧
      bindings = [("atom", atom), ("space", space)] := by
  obtain ⟨space, subject, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "prime-run") matched
  obtain ⟨atom, rfl, rfl⟩ := mem_matchPattern_releaseLeft inSecond
  rw [mem_matchPattern_fvar] at inFirst
  subst inFirst
  exact ⟨space, atom, rfl, by simpa [mergeBindings] using merged.symm⟩

/-- **Release beneath a run**, on patterns. -/
theorem step_runRelease (member : runReleaseRule ∈ lang.rewrites) (space atom : Pattern) :
    StepAt base lang 1 (runPattern space (dropped (quoted atom))) (runPattern space atom) :=
  stepAt_of_rule member (initial := [("atom", atom), ("space", space)])
    (by simp [runReleaseRule, runPattern, dropped, quoted, matchPattern, matchArgs, mergeBindings])
    (.nil _)
    (by simp [applyRuleBindings, runReleaseRule, runPattern, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero])

/-- What a step by release beneath a run is. -/
theorem runRelease_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runReleaseRule.left source)
    (premises : PremisesAt base lang fuel initial runReleaseRule.premises final) :
    ∃ space atom, source = runPattern space (dropped (quoted atom)) ∧
      applyRuleBindings runReleaseRule final = runPattern space atom := by
  obtain ⟨space, atom, rfl, rfl⟩ := mem_matchPattern_runRelease matched
  cases premises
  exact ⟨space, atom, rfl, by
    simp [applyRuleBindings, runReleaseRule, runPattern, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero]⟩

/-- **Negative**: the run of a symbol is no dropped quotation beneath a
run. -/
theorem runRelease_not_matched_symbol {space : Pattern} {code : Nat} {bindings : Bindings} :
    bindings ∉ matchPattern runReleaseRule.left (runPattern space (symbolAtom code)) := by
  intro matched
  obtain ⟨other, atom, shape, -⟩ := mem_matchPattern_runRelease matched
  simp [runPattern, symbolAtom, dropped] at shape

/-! ## The step of a run beneath a run -/

/-- What matches a run of a run. -/
theorem mem_matchPattern_runBeneathRun {pattern : Pattern} {bindings : Bindings}
    (matched : bindings ∈ matchPattern runRunRule.left pattern) :
    ∃ outer space subject, pattern = runPattern outer (runPattern space subject) ∧
      bindings = [("space", space), ("X", subject), ("outer", outer)] := by
  obtain ⟨outer, inner, first, second, rfl, inFirst, inSecond, merged⟩ :=
    matched_apply_two (label := "prime-run") matched
  obtain ⟨space, subject, rfl, rfl⟩ := mem_matchPattern_run (by decide) inSecond
  rw [mem_matchPattern_fvar] at inFirst
  subst inFirst
  exact ⟨outer, space, subject, rfl, by simpa [mergeBindings] using merged.symm⟩

/-- **A step of a run, from a run to a run in its space, is a step of the run
around it.**  The space of the outer run is not handed down. -/
theorem step_runBeneathRun (member : runRunRule ∈ lang.rewrites) {fuel : Nat}
    {space subject next : Pattern} (outer : Pattern)
    (inner : StepAt base lang fuel (runPattern space subject) (runPattern space next)) :
    StepAt base lang (fuel + 1) (runPattern outer (runPattern space subject))
      (runPattern outer (runPattern space next)) :=
  stepAt_of_rule (rule := runRunRule) member
    (initial := [("space", space), ("X", subject), ("outer", outer)])
    (by simp [runRunRule, runPattern, matchPattern, matchArgs, mergeBindings])
    (premisesAt_runs (partName := "X") (nextName := "Y") (by simp [applyBindings]) (by simp)
      (by simp [applyBindings]) (by simp) (by decide) inner)
    (by simp [applyRuleBindings, runRunRule, runPattern, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero])

/-- What a step of a run beneath a run is. -/
theorem runBeneathRun_inv {fuel : Nat} {source : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPattern runRunRule.left source)
    (premises : PremisesAt base lang fuel initial runRunRule.premises final) :
    ∃ outer space subject next, source = runPattern outer (runPattern space subject) ∧
      StepAt base lang fuel (runPattern space subject) (runPattern space next) ∧
        applyRuleBindings runRunRule final = runPattern outer (runPattern space next) := by
  obtain ⟨outer, space, subject, rfl, rfl⟩ := mem_matchPattern_runBeneathRun matched
  obtain ⟨next, inner, rfl⟩ := premisesAt_runs_inv (partName := "X") (nextName := "Y")
    (space := space) (part := subject) (by simp [applyBindings]) (by simp)
    (by simp [applyBindings]) (by simp) (by decide) premises
  exact ⟨outer, space, subject, next, rfl, inner, by
    simp [applyRuleBindings, runRunRule, runPattern, applyBindingsScoped, captureDepth,
      captureDepthList, liftBVars_zero]⟩

/-- **Negative**: the run of a symbol is no run of a run. -/
theorem runBeneathRun_not_matched_symbol {space : Pattern} {code : Nat} {bindings : Bindings} :
    bindings ∉ matchPattern runRunRule.left (runPattern space (symbolAtom code)) := by
  intro matched
  obtain ⟨outer, inner, subject, shape, -⟩ := mem_matchPattern_runBeneathRun matched
  simp [runPattern, symbolAtom] at shape

/-! ## The heads of the left sides -/

/-- **The heads of the nineteen left sides of the contained presentation.**
Ten are a run; the left side of the ambient root step has no head. -/
theorem contained_left_heads :
    containedRun.rewrites.map (fun rule => head? rule.left) =
      [some "App", some "App", some "App", some "Pi", some "Pi", some "Lam", some "Lam",
        some "prime-drop", none, some "prime-run", some "prime-run", some "prime-run",
        some "prime-run", some "prime-run", some "prime-run", some "prime-run", some "prime-run",
        some "prime-run", some "prime-run"] := by
  rfl

/-- **The heads of the seventeen left sides of the scoped presentation.** -/
theorem scoped_left_heads :
    scopedRun.rewrites.map (fun rule => head? rule.left) =
      [some "App", some "App", some "App", some "Pi", some "Pi", some "Lam", some "Lam",
        some "prime-drop", none, some "prime-run", some "prime-run", some "prime-run",
        some "prime-run", some "prime-run", some "prime-run", some "prime-run",
        some "prime-run"] := by
  rfl

#print axioms eq_run_of_matched
#print axioms step_ambientRoot
#print axioms ambientRoot_inv
#print axioms ambientRoot_refused
#print axioms step_regionRunRoot
#print axioms regionRunRoot_inv
#print axioms step_runBeta
#print axioms runBeta_inv
#print axioms step_runRelease
#print axioms runRelease_inv
#print axioms step_runBeneathRun
#print axioms runBeneathRun_inv
#print axioms contained_left_heads
#print axioms scoped_left_heads
#print axioms apply_not_matched
#print axioms bvar_not_matched
#print axioms mem_matchPattern_runBeta
#print axioms runBeta_not_matched_symbol
#print axioms mem_matchPattern_runRelease
#print axioms runRelease_not_matched_symbol
#print axioms mem_matchPattern_runBeneathRun
#print axioms runBeneathRun_not_matched_symbol

end Mettapedia.Logic.HostingStyles.AmbientRegions
