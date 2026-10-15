import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceEquationReadouts

/-!
# Equation archives cannot hide unresolved work

Draining an equation cursor forwards all of its unresolved obligations to
the global frontier. Global completion therefore earns local completion of
each archived cursor, together with all retained source-universe job checks.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

def EquationArchiveUnresolved (request : Request) (state : State request) : Prop :=
  ∀ archive ∈ state.checkedEquations, ∀ reason ∈ archive.frame.state.unresolved,
    Obligation.equation reason ∈ state.unresolved

theorem expansion_equationArchive_unresolved (request : Request) (state : State request) (task : Task request)
    (archive : EquationArchive request) (archived : archive ∈ (expand request state task).checkedEquations)
    (reason : GeneralEquationJobExecution.Obligation) (member : reason ∈ archive.frame.state.unresolved) :
    Obligation.equation reason ∈ (expand request state task).unresolved := by
  cases task with
  | equation frame =>
      cases found : frame.state.answers[frame.cursor]? with
      | none =>
          by_cases closed : GeneralEquationJobExecution.settled frame.state = true
          · rw [expand, expandEquation_closed request state frame found closed] at archived ⊢
            simp only [List.mem_cons, List.not_mem_nil, or_false] at archived
            subst archive
            exact List.mem_map.mpr ⟨reason, member, rfl⟩
          · rw [expand, expandEquation_pending request state frame found closed] at archived
            simp only [List.not_mem_nil] at archived
      | some answer =>
          rw [expand, expandEquation_found request state frame answer found] at archived
          simp only [List.not_mem_nil] at archived
  | visit representative => simp only [expand] at archived; split at archived <;> simp_all
  | incoming representative edges =>
      cases edges with
      | nil => simp only [expand, List.not_mem_nil] at archived
      | cons edge tail =>
          by_cases backward : representative.pattern = edge.receipt.target
          · simp only [expand, dif_pos backward, List.not_mem_nil] at archived
          · by_cases forward : representative.pattern = edge.source
            · simp only [expand, dif_neg backward, dif_pos forward, List.not_mem_nil] at archived
            · simp only [expand, dif_neg backward, dif_neg forward, List.not_mem_nil] at archived
  | «universe» => simp only [expand, List.not_mem_nil] at archived
  | scanUniverse patterns => cases patterns <;> simp only [expand, List.not_mem_nil] at archived
  | rule frame =>
      simp only [expand, expandRule] at archived
      split at archived
      · split at archived <;> simp only [List.not_mem_nil] at archived
      · simp only [List.not_mem_nil] at archived

theorem equationArchiveUnresolved_start (request : Request) : EquationArchiveUnresolved request (start request) := by
  intro archive member
  simp only [start] at member
  split at member <;> simp only [List.not_mem_nil] at member

theorem equationArchiveUnresolved_tick {request : Request} {state : State request}
    (accounted : EquationArchiveUnresolved request state) : EquationArchiveUnresolved request (tick request state) := by
  intro archive archived reason member
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using
      accounted archive (by simpa only [tick, agenda] using archived) reason member
  | cons task remaining =>
      simp only [tick, agenda, List.mem_append] at archived ⊢
      rcases archived with prior | fresh
      · exact Or.inl (accounted archive prior reason member)
      · exact Or.inr (expansion_equationArchive_unresolved request state task archive fresh reason member)

theorem reachable_equationArchiveUnresolved {request : Request} {state : State request}
    (reached : Reachable request state) : EquationArchiveUnresolved request state := by
  induction reached with
  | start => exact equationArchiveUnresolved_start request
  | tick reached ih => exact equationArchiveUnresolved_tick ih

theorem equationArchive_complete {request : Request} {state : State request}
    (reached : Reachable request state) (resolved : state.unresolved = [])
    (archive : EquationArchive request) (archived : archive ∈ state.checkedEquations) :
    GeneralEquationJobExecution.complete archive.frame.state = true := by
  apply (GeneralEquationJobExecution.complete_iff archive.frame.state).mpr
  refine ⟨List.isEmpty_iff.mp archive.settled, ?_⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro reason member
  have global := reachable_equationArchiveUnresolved reached archive archived reason member
  simp only [resolved, List.not_mem_nil] at global

theorem completed_equationJobCertified {request : Request} {state : State request}
    (admitted : Admitted request) (reached : Reachable request state) (completed : complete request state = true)
    (source : Syntax.Pattern) (within : source ∈ request.universe) (job : GeneralEquationJobs.Job)
    (member : job ∈ GeneralEquationJobs.jobs request.plan request.bound request.expected source) :
    EquationJobCertified request state source job := by
  have facts := (complete_iff request state).mp completed
  obtain ⟨archive, archived, sourceEq, jobEq⟩ := settled_equation_archived admitted reached facts.1 source job within member
  refine ⟨archive, archived, sourceEq, jobEq, equationArchive_complete reached facts.2.1 archive archived, ?_⟩
  have read := reachable_equationArchiveRead reached archive archived
  intro answer member
  exact of_decide_eq_true ((List.all_eq_true.mp read) answer member)

theorem completed_universeJobsChecked {request : Request} {state : State request}
    (admitted : Admitted request) (reached : Reachable request state) (completed : complete request state = true) :
    universeJobsChecked request state = true := by
  apply (universeJobsChecked_iff request state).mpr
  intro source within job member
  exact completed_equationJobCertified admitted reached completed source within job member

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
