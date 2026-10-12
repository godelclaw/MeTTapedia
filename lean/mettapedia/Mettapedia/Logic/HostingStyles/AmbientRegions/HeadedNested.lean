import Mettapedia.Logic.HostingStyles.AmbientRegions.HeadedContainment

/-!
# With headed root steps: a run in a run

In `headedContained` the root step of a run keeps a variable as its subject
(`headed_runRoot_unheaded`).  A run is an atom, so the space of a run is
asked for a run inside it, as a whole.

* **The steps of `run(outer, run(inner, subject))`** (`headed_nested_step_iff`),
  under every guard and at every ambient space: the runs of the answers of
  `outer` for `run(inner, subject)`, and the runs of the steps of
  `run(inner, subject)`.  The ambient space is in neither part
  (`headed_run_step_ambient_irrelevant`).
* **The outer space rewrites the inner run as a whole**
  (`headed_nested_outer_rewrites`): in the space of the rule `x ⟶ u` the run
  of `choose heads tails` in the empty space steps to `u`, at every ambient
  space and without a guard.
* **It does not reach inside the inner run** (`headed_nested_outer_silent`):
  where the outer space answers nothing for a run, the steps are the runs of
  the steps of the inner run alone.

With the root step of a run headed too the first part is empty for every
outer space (`allHeaded_nested_step_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Dedukti (chooseLeft chooseRight)
open Mettapedia.GSLT.Dedukti.Language
  (betaRule appFunctionRule appArgumentRule piDomainRule piBodyRule lamDomainRule lamBodyRule
    metaName)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.LocatedAtoms (takeAll takeAll_admitted)

variable {admits : Pattern → Bool}

/-- **A run in a run, with headed root steps**: its steps are the runs of the
answers of the outer space for the inner run as a whole, and the runs of the
steps of the inner run. -/
theorem headed_nested_step_iff {ambientSpace outer inner subject target : Pattern} :
    Step (regionEvaluator admits ambientSpace) headedContained
        (runPattern outer (runPattern inner subject)) target ↔
      (∃ answer, answer ∈ admittedAnswers admits outer (runPattern inner subject) ∧
        target = runPattern outer answer) ∨
      ∃ next, target = runPattern outer (runPattern inner next) ∧
        Step (regionEvaluator admits ambientSpace) headedContained (runPattern inner subject)
          (runPattern inner next) := by
  constructor
  · rintro ⟨fuel, step⟩
    cases fuel with
    | zero => cases step
    | succ fuel =>
        obtain ⟨rule, member, initial, final, matched, premises, rfl⟩ := exists_rule_of_stepAt step
        rcases mem_headedContained_rewrites.mp member with plain | root | run
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at plain
          rcases plain with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact absurd matched (run_not_matched (label := "App") (by decide))
          · exact absurd matched (run_not_matched (label := "App") (by decide))
          · exact absurd matched (run_not_matched (label := "App") (by decide))
          · exact absurd matched (run_not_matched (label := "Pi") (by decide))
          · exact absurd matched (run_not_matched (label := "Pi") (by decide))
          · exact absurd matched (run_not_matched (label := "Lam") (by decide))
          · exact absurd matched (run_not_matched (label := "Lam") (by decide))
          · exact absurd matched (run_not_matched (label := "prime-drop") (by decide))
        · exact absurd matched (headedRoots_not_matched_run root)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at run
          rcases run with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · obtain ⟨otherSpace, innerRun, answer, shape, found, applied⟩ :=
              regionRunRoot_inv matched premises
            obtain ⟨rfl, rfl⟩ := runPattern_injective shape
            exact .inl ⟨answer, found, applied⟩
          · obtain ⟨otherSpace, function, argument, moved, shape, -, -⟩ :=
              runAppFunction_inv matched premises
            obtain ⟨-, wrong⟩ := runPattern_injective shape
            simp [runPattern] at wrong
          · obtain ⟨otherSpace, function, argument, moved, shape, -, -⟩ :=
              runAppArgument_inv matched premises
            obtain ⟨-, wrong⟩ := runPattern_injective shape
            simp [runPattern] at wrong
          · obtain ⟨otherSpace, domain, binder, body, moved, shape, -, -⟩ :=
              runPiDomain_inv matched premises
            obtain ⟨-, wrong⟩ := runPattern_injective shape
            simp [runPattern] at wrong
          · obtain ⟨otherSpace, domain, binder, body, moved, shape, -, -⟩ :=
              runPiBody_inv matched premises
            obtain ⟨-, wrong⟩ := runPattern_injective shape
            simp [runPattern] at wrong
          · obtain ⟨otherSpace, domain, binder, body, moved, shape, -, -⟩ :=
              runLamDomain_inv matched premises
            obtain ⟨-, wrong⟩ := runPattern_injective shape
            simp [runPattern] at wrong
          · obtain ⟨otherSpace, domain, binder, body, moved, shape, -, -⟩ :=
              runLamBody_inv matched premises
            obtain ⟨-, wrong⟩ := runPattern_injective shape
            simp [runPattern] at wrong
          · obtain ⟨otherSpace, domain, binder, body, argument, shape, -⟩ :=
              runBeta_inv matched premises
            obtain ⟨-, wrong⟩ := runPattern_injective shape
            simp [runPattern] at wrong
          · obtain ⟨otherSpace, atom, shape, -⟩ := runRelease_inv matched premises
            obtain ⟨-, wrong⟩ := runPattern_injective shape
            simp [runPattern, dropped] at wrong
          · obtain ⟨otherOuter, otherInner, innerSubject, next, shape, innerStep, applied⟩ :=
              runBeneathRun_inv matched premises
            obtain ⟨rfl, innerShape⟩ := runPattern_injective shape
            obtain ⟨rfl, rfl⟩ := runPattern_injective innerShape
            exact .inr ⟨next, applied, fuel, innerStep⟩
  · rintro (⟨answer, found, rfl⟩ | ⟨next, rfl, fuel, step⟩)
    · exact ⟨1, step_regionRunRoot (by simp [headedContained_rewrites]) found⟩
    · exact ⟨fuel + 1, step_runBeneathRun (by simp [headedContained_rewrites]) outer step⟩

/-- **Where the outer space answers nothing for the inner run, the steps of a
run in a run are the runs of the steps of the inner run.** -/
theorem headed_nested_outer_silent {ambientSpace outer inner subject target : Pattern}
    (silent : admittedAnswers admits outer (runPattern inner subject) = []) :
    Step (regionEvaluator admits ambientSpace) headedContained
        (runPattern outer (runPattern inner subject)) target ↔
      ∃ next, target = runPattern outer (runPattern inner next) ∧
        Step (regionEvaluator admits ambientSpace) headedContained (runPattern inner subject)
          (runPattern inner next) := by
  rw [headed_nested_step_iff, silent]
  constructor
  · rintro (⟨answer, found, -⟩ | reached)
    · cases found
    · exact reached
  · exact .inr

/-- **The outer space rewrites the inner run as a whole.**  In the space of
the rule `x ⟶ u`, the run of `choose heads tails` in the empty space steps to
`u`, at every ambient space and without a guard. -/
theorem headed_nested_outer_rewrites (ambientSpace : Pattern) :
    Step (regionEvaluator anySubject ambientSpace) headedContained
      (runPattern (ruleSpace [takeAll]) (runPattern (ruleSpace []) (atomAt 0 coin)))
      (runPattern (ruleSpace [takeAll]) (atomAt 0 (.con "u"))) := by
  refine ⟨1, step_regionRunRoot (by simp [headedContained_rewrites]) ?_⟩
  show atomAt 0 (.con "u") ∈ matchResults (contract (ruleSpace [takeAll]))
    (contract (runPattern (ruleSpace []) (atomAt 0 coin)))
  rw [contract_ruleSpace]
  refine (mem_matchResults_ruleSpace takeAll_admitted.1).mpr
    ⟨takeAll, List.mem_singleton.mpr rfl,
      [(metaName 0, contract (runPattern (ruleSpace []) (atomAt 0 coin)))], ?_, ?_⟩
  · show _ ∈ matchPattern (asRule (atomAt 0 (.var 0))) _
    rw [atomAt_freeVariable, asRule_variableAtom]
    simp [matchPattern]
  · show atomAt 0 (.con "u") = applyBindings _ (ruleSide (.con "u"))
    rw [ruleSide_con, applyBindings_symbolAtom]
    rfl

/-- **Negative**: an outer space of rules none of whose left sides is a
variable does not.  In the space of the two rules of choice the run of
`choose heads tails` in the empty space has no step, at every ambient
space. -/
theorem headed_nested_outer_unseen (ambientSpace target : Pattern) :
    ¬ Step (regionEvaluator anySubject ambientSpace) headedContained
      (runPattern (ruleSpace [chooseLeft, chooseRight])
        (runPattern (ruleSpace []) (atomAt 0 coin))) target := by
  intro step
  obtain ⟨next, -, inner⟩ := (headed_nested_outer_silent
    (choiceSpace_runSilent anySubject (ruleSpace []) (atomAt 0 coin))).mp step
  obtain ⟨reduct, -, sourceStep⟩ := (headed_runAtom_step_iff anySubject_admitsAtoms ambientSpace
    (rules := []) noRules_admitted.1 noRules_admitted.2 (theory := Dedukti.Theory.empty)
    (fun _ => ⟨fun member => member.elim, fun member => absurd member List.not_mem_nil⟩)
    (fun _ => rfl)).mp inner
  exact Dedukti.normal_of_normalTest pureCover _ (by decide) _ sourceStep

#print axioms headed_nested_step_iff
#print axioms headed_nested_outer_silent
#print axioms headed_nested_outer_rewrites
#print axioms headed_nested_outer_unseen

end Mettapedia.Logic.HostingStyles.AmbientRegions
