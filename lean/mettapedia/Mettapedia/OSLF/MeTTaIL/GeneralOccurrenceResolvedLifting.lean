import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceCompletedCertificate
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceEquationSourceTyping

/-!
# Lifting local execution resolution through saturation

The global scheduler forwards precisely the obligations of its drained local
equation and rule executions. This lemma transports independently established
local resolution through every microstep and the proved finite saturation.
It does not turn local resolution into an admission field: language admission
must earn the two local contracts from its actual schemas.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

abbrev EquationResolution (request : Request) : Prop :=
  ∀ (source : Syntax.Pattern) (job : GeneralEquationJobs.Job)
    (_sourceTyped : EquationSourceTyped request source)
    (licensed : GeneralEquationJobs.LicensedJob request.plan request.bound request.expected source job),
    (GeneralEquationJobExecution.finishJob (equationRequest request source job) licensed).unresolved = []

abbrev RuleResolution (request : Request) : Prop :=
  ∀ (representative : Representative request) (job : GeneralRuleJobs.Job)
    (licensed : job.Valid request.plan request.bound request.expected representative.pattern),
    (GeneralRuleJobExecution.finishState (ruleRequest request representative job) licensed).unresolved = []

theorem expansion_resolved {request : Request}
    (equations : EquationResolution request) (rules : RuleResolution request)
    (state : State request) (task : Task request) (typed : TaskSourcesTyped request task) :
    (expand request state task).unresolved = [] := by
  cases task with
  | visit representative => simp only [expand]; split <;> rfl
  | incoming representative edges =>
      cases edges with
      | nil => rfl
      | cons edge remaining => simp only [expand]; split <;> (try split) <;> rfl
  | «universe» => rfl
  | scanUniverse remaining => cases remaining <;> rfl
  | equation frame =>
      cases found : frame.state.answers[frame.cursor]? with
      | some answer => rw [expand, expandEquation_found request state frame answer found]
      | none =>
          by_cases idle : GeneralEquationJobExecution.settled frame.state = true
          · rw [expand, expandEquation_closed request state frame found idle]
            have final := GeneralEquationJobExecution.settled_reachable_finishJob frame.reachable idle
            change frame.state.unresolved.map Obligation.equation = []
            rw [final, equations frame.source frame.job typed frame.licensed, List.map_nil]
          · rw [expand, expandEquation_pending request state frame found idle]
  | rule frame =>
      cases found : frame.state.answers[frame.cursor]? with
      | some answer => rw [expand, expandRule_found request frame answer found]
      | none =>
          by_cases idle : GeneralRuleJobExecution.settled frame.state = true
          · rw [expand, expandRule_closed request frame found idle]
            have final := GeneralRuleJobExecution.settled_reachable_finishState frame.reachable idle
            change frame.state.unresolved.map Obligation.rule = []
            rw [final, rules frame.representative frame.job frame.licensed, List.map_nil]
          · rw [expand, expandRule_pending request frame found idle]

theorem tick_resolved {request : Request}
    (equations : EquationResolution request) (rules : RuleResolution request)
    {state : State request} (typed : AgendaSourcesTyped request state)
    (resolved : state.unresolved = []) :
    (tick request state).unresolved = [] := by
  cases agenda : state.agenda with
  | nil => simpa only [tick, agenda] using resolved
  | cons task remaining =>
      have taskTyped := typed task (agenda ▸ List.mem_cons_self)
      simp only [tick, agenda, resolved, expansion_resolved equations rules state task taskTyped,
        List.nil_append]

theorem reachable_resolved {request : Request} (admitted : Admitted request)
    (equations : EquationResolution request) (rules : RuleResolution request)
    {state : State request} (reached : Reachable request state) : state.unresolved = [] := by
  induction reached with
  | start =>
      exact start_obligations_empty request admitted.accepted
        (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_complete admitted.rootSorted)
  | tick reached ih => exact tick_resolved equations rules (reachable_sources_typed admitted reached) ih

theorem finish_resolved {request : Request} (admitted : Admitted request)
    (equations : EquationResolution request) (rules : RuleResolution request) :
    (finish request admitted).unresolved = [] := by
  obtain ⟨fuel, same⟩ := finish_actual_run request admitted
  rw [← same]
  exact reachable_resolved admitted equations rules (reachable_run .start fuel)

theorem finish_complete_of_local_resolution {request : Request} (admitted : Admitted request)
    (equations : EquationResolution request) (rules : RuleResolution request) :
    complete request (finish request admitted) = true := by
  obtain ⟨fuel, same⟩ := finish_actual_run request admitted
  have reached : Reachable request (finish request admitted) := same ▸ reachable_run .start fuel
  exact settled_empty_complete
    (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_complete admitted.rootSorted)
    reached (List.isEmpty_iff.mpr (finish_settled request admitted))
    (finish_resolved admitted equations rules)

theorem finish_certificate_of_local_resolution {request : Request} (admitted : Admitted request)
    (equations : EquationResolution request) (rules : RuleResolution request) :
    checkCertificate request (finish request admitted) = true := by
  obtain ⟨fuel, same⟩ := finish_actual_run request admitted
  exact completed_checkCertificate admitted (same ▸ reachable_run .start fuel)
    (finish_complete_of_local_resolution admitted equations rules)

#print axioms expansion_resolved
#print axioms reachable_resolved
#print axioms finish_certificate_of_local_resolution

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
