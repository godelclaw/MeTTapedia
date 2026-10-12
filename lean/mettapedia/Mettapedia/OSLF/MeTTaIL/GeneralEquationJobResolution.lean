import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobObligations
import Mettapedia.OSLF.MeTTaIL.GeneralEquationJobCertifiedWork
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseFinishReadout

/-!
# Resolution of every actual typed equation-match branch

The outer job reads and drains the real premise machine for every accepted
scoped match. A local resolution theorem for those independently matched
captures therefore removes the outer job's premise obligations. The source
gate remains a separate requirement, and no completeness claim follows from
drainage alone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution

open GeneralPremise.Scheduler GeneralEquationJobs

theorem matching_expansion_resolved (request : Request) (frame : MatchFrame request) :
    (expand request (.matching frame)).unresolved = [] := by
  simp only [expand, expandMatching]
  split
  · split <;> rfl
  · split <;> rfl

theorem matching_tree_resolved (request : Request) (frame : MatchFrame request)
    (tree : TaskTree (expand request) (.matching frame))
    (resolved : ∀ trace captured,
      GeneralScopedMatchMachine.TracedMatches request.job.equation.rule
        request.job.equation.binding.spec request.job.site.focusBound.length .left [] 0 []
        request.job.equation.rule.left request.job.site.focus.eraseBinderMetadata trace captured →
      GeneralPremise.TypedAssignment request.environment (request.job.context request.plan) captured →
      (GeneralPremise.Execution.finish request.environment (request.premises captured)).unresolved = []) :
    tree.obligations = [] := by
  cases treeEq : tree with
  | branch children =>
      have parentCost : tree.cost = children.cost + 1 := by rw [treeEq]; rfl
      change (expand request (.matching frame)).unresolved ++ children.obligations = []
      rw [matching_expansion_resolved, List.nil_append]
      cases found : frame.state.answers[frame.cursor]? with
      | none =>
          by_cases idle : GeneralScopedMatchMachine.complete frame.state = true
          · have tasks : (expand request (.matching frame)).tasks = [] := by
              simp only [expand, expandMatching]
              split
              next actualFound => simp only [idle, if_true]
              next actual actualFound => cases actualFound.symm.trans found
            rw [← TaskForest.obligations_cast tasks children]
            cases tasks ▸ children
            rfl
          · have pending := Bool.eq_false_iff.mpr idle
            have tasks : (expand request (.matching frame)).tasks =
                [Task.matching {frame with
                  state := GeneralScopedMatchMachine.tick request.matcher frame.state
                  reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable}] := by
              simp only [expand, expandMatching]
              split
              next actualFound => simp only [pending, Bool.false_eq_true, if_false]
              next actual actualFound => cases actualFound.symm.trans found
            let selectedChildren := tasks ▸ children
            have sameObligations := TaskForest.obligations_cast tasks children
            have sameCost := TaskForest.cost_cast tasks children
            cases selectedChildrenEq : selectedChildren with
            | cons child tail =>
                cases tail
                have later := matching_tree_resolved request {frame with
                    state := GeneralScopedMatchMachine.tick request.matcher frame.state
                    reachable := GeneralScopedMatchMachine.reachable_tick frame.reachable}
                  child resolved
                rw [← sameObligations]
                change selectedChildren.obligations = []
                rw [selectedChildrenEq]
                simpa only [TaskForest.obligations, List.append_nil] using later
      | some current =>
          by_cases checked : GeneralPremise.checkTypedAssignment request.environment
              (request.job.context request.plan) current.assignment = true
          · let branch : PremiseFrame request :=
              ⟨frame.licensed, frame.sourceTyped, current.trace, current.assignment,
                GeneralScopedMatchMachine.answers_sound frame.reachable (List.mem_of_getElem? found),
                GeneralPremise.checkTypedAssignment_sound checked,
                GeneralPremise.Execution.start request.environment (request.premises current.assignment), 0⟩
            have tasks : (expand request (.matching frame)).tasks =
                [Task.premises branch, Task.matching {frame with cursor := frame.cursor + 1}] := by
              simp only [expand, expandMatching]
              split
              next unavailable => cases unavailable.symm.trans found
              next actual actualFound =>
                have same : actual = current := Option.some.inj (actualFound.symm.trans found)
                subst actual
                rw [dif_pos checked]
            let selectedChildren := tasks ▸ children
            have sameObligations := TaskForest.obligations_cast tasks children
            have sameCost := TaskForest.cost_cast tasks children
            cases selectedChildrenEq : selectedChildren with
            | cons child tail =>
                cases tail with
                | cons later tail =>
                    cases tail
                    let forest := authoredPremiseForests request current.assignment
                    have localResolved := resolved current.trace current.assignment branch.matching branch.capturedTyped
                    have forestResolved : forest.obligations = [] := by
                      change (GeneralPremise.Execution.treeStart request.environment
                        (request.premises current.assignment)).obligations ++ [] = []
                      rw [← GeneralPremise.Execution.finish_obligations, localResolved, List.append_nil]
                    have branchResolved := premise_tree_obligations request branch forest child
                    have childResolved : child.obligations = [] := by
                      rw [branchResolved, forestResolved]
                      rfl
                    have laterResolved := matching_tree_resolved request {frame with cursor := frame.cursor + 1}
                      later resolved
                    rw [← sameObligations]
                    change selectedChildren.obligations = []
                    rw [selectedChildrenEq]
                    simp only [TaskForest.obligations, childResolved, laterResolved, List.append_nil]
          · have tasks : (expand request (.matching frame)).tasks =
                [Task.matching {frame with cursor := frame.cursor + 1}] := by
              simp only [expand, expandMatching]
              split
              next unavailable => cases unavailable.symm.trans found
              next actual actualFound =>
                have same : actual = current := Option.some.inj (actualFound.symm.trans found)
                subst actual
                rw [dif_neg checked]
            let selectedChildren := tasks ▸ children
            have sameObligations := TaskForest.obligations_cast tasks children
            have sameCost := TaskForest.cost_cast tasks children
            cases selectedChildrenEq : selectedChildren with
            | cons child tail =>
                cases tail
                have later := matching_tree_resolved request {frame with cursor := frame.cursor + 1} child resolved
                rw [← sameObligations]
                change selectedChildren.obligations = []
                rw [selectedChildrenEq]
                simpa only [TaskForest.obligations, List.append_nil] using later
termination_by tree.cost
decreasing_by
  all_goals
    try simp only [TaskTree.cost]
    change selectedChildren.cost = children.cost at sameCost
    rw [selectedChildrenEq] at sameCost
    try simp only [TaskForest.cost] at sameCost
    omega

theorem initial_forest_resolved (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      request.plan.snapshot.language request.plan.snapshot.free request.bound request.expected request.source)
    (forest : TaskForest (expand request) (start request licensed).agenda)
    (resolved : ∀ trace captured,
      GeneralScopedMatchMachine.TracedMatches request.job.equation.rule
        request.job.equation.binding.spec request.job.site.focusBound.length .left [] 0 []
        request.job.equation.rule.left request.job.site.focus.eraseBinderMetadata trace captured →
      GeneralPremise.TypedAssignment request.environment (request.job.context request.plan) captured →
      (GeneralPremise.Execution.finish request.environment (request.premises captured)).unresolved = []) :
    forest.obligations = [] := by
  have environmentTyped := (GeneralPlanEnvironment.typing_iff request.plan request.bound request.expected
    request.source).mpr sourceTyped
  have checked : Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
      request.environment.language request.plan.snapshot.free request.bound request.expected request.source = true :=
    Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_complete environmentTyped
  let frame : MatchFrame request :=
    ⟨licensed, Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound checked,
      GeneralScopedMatchMachine.start request.matcher, .start, 0⟩
  have tasks : (start request licensed).agenda = [Task.matching frame] := by
    unfold start
    rw [dif_pos checked]
  let chosen := tasks ▸ forest
  have sameObligations := TaskForest.obligations_cast tasks forest
  cases chosenEq : chosen with
  | cons tree tail =>
      cases tail
      have branchResolved := matching_tree_resolved request frame tree resolved
      rw [← sameObligations]
      change chosen.obligations = []
      rw [chosenEq]
      simpa only [TaskForest.obligations, List.append_nil] using branchResolved

theorem finishJob_resolved (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      request.plan.snapshot.language request.plan.snapshot.free request.bound request.expected request.source)
    (resolved : ∀ trace captured,
      GeneralScopedMatchMachine.TracedMatches request.job.equation.rule
        request.job.equation.binding.spec request.job.site.focusBound.length .left [] 0 []
        request.job.equation.rule.left request.job.site.focus.eraseBinderMetadata trace captured →
      GeneralPremise.TypedAssignment request.environment (request.job.context request.plan) captured →
      (GeneralPremise.Execution.finish request.environment (request.premises captured)).unresolved = []) :
    (finishJob request licensed).unresolved = [] := by
  have environmentTyped := (GeneralPlanEnvironment.typing_iff request.plan request.bound request.expected
    request.source).mpr sourceTyped
  have checked : Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
      request.environment.language request.plan.snapshot.free request.bound request.expected request.source = true :=
    Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_complete environmentTyped
  have initialResolved : (start request licensed).unresolved = [] := by
    simp only [start, checked, ↓reduceDIte]
  rw [(finishJob_readouts request licensed).2, initialResolved, List.nil_append]
  exact initial_forest_resolved request licensed sourceTyped _ resolved

theorem finishJob_complete_of_resolved (request : Request)
    (licensed : LicensedJob request.plan request.bound request.expected request.source request.job)
    (sourceTyped : Mettapedia.GSLT.LanguageDef.WellSorted.OpenPatternWellSorted
      request.plan.snapshot.language request.plan.snapshot.free request.bound request.expected request.source)
    (resolved : ∀ trace captured,
      GeneralScopedMatchMachine.TracedMatches request.job.equation.rule
        request.job.equation.binding.spec request.job.site.focusBound.length .left [] 0 []
        request.job.equation.rule.left request.job.site.focus.eraseBinderMetadata trace captured →
      GeneralPremise.TypedAssignment request.environment (request.job.context request.plan) captured →
      (GeneralPremise.Execution.finish request.environment (request.premises captured)).unresolved = []) :
    complete (finishJob request licensed) = true :=
  (complete_iff _).mpr ⟨List.isEmpty_iff.mp (finishJob_settled request licensed),
    finishJob_resolved request licensed sourceTyped resolved⟩

end Mettapedia.OSLF.MeTTaIL.GeneralEquationJobExecution
