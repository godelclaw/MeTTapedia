import Mettapedia.Languages.C11.StatementMachineRefinement
import Mettapedia.Languages.C11.StatementDataControls

/-!
# Concrete refinement, suspension and divergence controls

The controls exercise the common stage on the constructed statement machines.
They check pending stores, exact suspension snapshots and terminal outcomes,
and show that a loop with visible iterations remains incomplete at every
finite budget. A valid representation of an unearned cache still fails the
separate history gate. No compiler-instruction account is inferred.

Regional-divergence controls use the existing for-loop cycle and its ordinary
statement transitions. Finishing diagnostic verdicts, missing transitions and
scheduler suspensions remain separate. Iteration receipts are operational
observations of this profile, not external C11 input/output events.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.StatementMachineRefinementControls

open IntegerMemoryModel LocatedExpressions LocatedStatements StatementData StatementDataExecution
open StatementDataInteraction StatementDataHistory StatementMachineRefinement
open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev model := StatementControls.model
abbrev memory := StatementControls.memory
abbrev policy := intervalReductionPolicy

theorem constructed_stage_has_interface_cost_one : (stage model policy).cost = 1 := stage_cost _ _

theorem arbitrary_native_prefix_is_exactly_represented (fuel : Nat) (source : Configuration model) :
    (machineData model policy).run fuel (encodeConfiguration source) =
      (((observedMachine model policy).run fuel source).1,
        encodeObservedOutcome ((observedMachine model policy).run fuel source).2) := run_encoded _ _ _ _

theorem pending_store_prefix_is_preserved :
    ((machineData model policy).run 4 (encodeConfiguration StatementControls.conditionalAssignment)).2 =
      .exhausted StatementDataControls.resultPrefix := by cbv

theorem resumed_store_has_one_commit :
    ((machineData model policy).run 2 StatementDataControls.resultPrefix).1.filterMap (fun receipt =>
      match receipt.event with
      | .occurrence _ _ (.stored value) => some value.integer
      | _ => none) = [-1] := by cbv

theorem original_occurrence_account_survives_both_adapters :
    (machineData model policy).spent (priceData model (StatementMachine.occurrencePrice policy))
        4 (encodeConfiguration StatementControls.conditionalAssignment) =
      (StatementMachine.machine model policy).spent (StatementMachine.occurrencePrice policy)
        4 StatementControls.conditionalAssignment := by
  rw [accounts_encoded]
  exact (StatementMachine.machine model policy).spent_relabel encodeReceipt
    (fun verdict => ResultData.source (encodeVerdict verdict)) encodeRequest _ _ _

def waiting : Configuration model := .expression StatementControls.assignment
  (ExpressionEventExecution.initialState (compile StatementControls.assignment) memory) .returnValue []

theorem native_scheduler_request_retains_concrete_snapshot :
    (observedMachine model policy).step waiting = some
      (.call StatementDataControls.waitingRequest.request waiting) := by cbv

theorem represented_scheduler_request_retains_encoded_snapshot :
    (machineData model policy).step (encodeConfiguration waiting) = some
      (.call StatementDataControls.waitingRequest.request (encodeConfiguration waiting)) := by cbv

theorem suspension_and_saved_state_agree :
    (machineData model policy).run 1 (encodeConfiguration waiting) =
      ([], .suspended StatementDataControls.waitingRequest.request (encodeConfiguration waiting)) :=
  (machineData model policy).run_succ_call (fuel := 0) represented_scheduler_request_retains_encoded_snapshot

theorem scheduler_delivery_has_an_independent_source_endpoint :
    ∃ source, Related source StatementDataControls.delivered ∧
      Delivery (represent waiting) StatementDataControls.response.choice (represent source) := by
  apply scheduling_delivery_realized model waiting (encodeConfiguration waiting)
    StatementDataControls.delivered StatementDataControls.response.choice rfl
  cbv

theorem disabled_choice_cannot_become_a_source_delivery :
    deliverData model (encodeConfiguration waiting)
      (LocatedExpressionData.encodeIndex StatementControls.assignment LocatedExpressionDataControls.storeIndex) = none := by cbv

def malformed : ConfigurationData := .flow .normal .stop ⟨[(7, ⟨true, [some 256]⟩)], []⟩ []

theorem malformed_packet_has_no_related_concrete_configuration :
    ¬ ∃ source : Configuration model, Related source malformed := by
  rintro ⟨source, related⟩
  have decoded := (related_iff_decode source malformed).mp related
  have invalid : decodeConfiguration model malformed = none := by cbv
  rw [invalid] at decoded
  cases decoded

theorem malformed_packet_does_not_become_a_source_fault :
    (machineData model policy).step malformed = some (.finish (.malformed malformed)) := by cbv

theorem represented_arithmetic_terminal_keeps_source_fault :
    (machineData model policy).run 1 StatementDataControls.halted =
      ([], .finished (.source (.terminal
        (LocatedExpressionData.encodeExpression StatementDataControls.division) (.right (.leaf 0))
        (.arithmeticFault .int .divisionByZero) StatementDataControls.halted))) := by cbv

theorem representable_unearned_state_still_fails_historical_admission :
    (∃ source : Configuration model, Related source StatementDataControls.unearned) ∧
      restore model policy {StatementDataControls.historyPrefix with retained := StatementDataControls.unearned} = none := by
  refine ⟨?_, StatementDataControls.unearned_cache_is_not_a_historical_residual⟩
  cases decoded : decodeConfiguration model StatementDataControls.unearned with
  | none =>
      have valid := StatementDataControls.byte_valid_unearned_cache_still_decodes
      simp only [decoded, Option.isSome_none, Bool.false_eq_true] at valid
  | some source => exact ⟨source, (related_iff_decode _ _).mpr decoded⟩

def loopBody : Configuration model :=
  .statement .empty (.forBody none none .empty .stop) memory []

def loopEnd : Configuration model :=
  .flow .normal (.forBody none none .empty .stop) memory []

def loopReceipt : ReceiptData := encodeReceipt ⟨.iteration .forLoop, loopEnd, loopBody⟩

theorem loop_body_has_one_administrative_transition :
    (observedMachine model policy).step loopBody = some (.silent loopEnd) := by cbv

theorem loop_backedge_has_one_visible_iteration :
    (observedMachine model policy).step loopEnd = some (.publish [loopReceipt] loopBody) := by cbv

def Cycling (source : Configuration model) : Prop := source = loopBody ∨ source = loopEnd

theorem arbitrary_loop_prefix_retains_a_cycle (fuel : Nat) (source : Configuration model) (cycling : Cycling source) :
    ∃ events saved, (observedMachine model policy).run fuel source = (events, .exhausted saved) ∧ Cycling saved := by
  induction fuel generalizing source with
  | zero => exact ⟨[], source, rfl, cycling⟩
  | succ fuel ih =>
      rcases cycling with rfl | rfl
      · rw [(observedMachine model policy).run_succ_silent loop_body_has_one_administrative_transition]
        exact ih loopEnd (Or.inr rfl)
      · rw [(observedMachine model policy).run_succ_publish loop_backedge_has_one_visible_iteration]
        obtain ⟨events, saved, reached, retained⟩ := ih loopBody (Or.inl rfl)
        rw [reached]
        exact ⟨[loopReceipt] ++ events, saved, rfl, retained⟩

theorem source_loop_never_completes (fuel : Nat) :
    ¬ ((observedMachine model policy).observe fuel loopBody).status.Final := by
  obtain ⟨events, saved, reached, _⟩ := arbitrary_loop_prefix_retains_a_cycle fuel loopBody (Or.inl rfl)
  simp only [Machine.observe, reached, Outcome.status]
  exact False.elim

theorem represented_loop_never_completes (fuel : Nat) :
    ¬ ((machineData model policy).observe fuel (encodeConfiguration loopBody)).status.Final :=
  noncompletion_preserved model policy loopBody (encodeConfiguration loopBody) rfl source_loop_never_completes fuel

theorem divergence_has_visible_iterations :
    (machineData model policy).run 4 (encodeConfiguration loopBody) =
      ([loopReceipt, loopReceipt], .exhausted (encodeConfiguration loopBody)) := by cbv

/-- A coarse occurrence observer retains the exact represented loop residual. -/
theorem hidden_receipts_retain_each_iteration :
    ((machineData model policy).relabel (fun _ => ()) id id).run 4 (encodeConfiguration loopBody) =
      ([(), ()], .exhausted (encodeConfiguration loopBody)) := by
  rw [(machineData model policy).run_relabel, divergence_has_visible_iterations]
  rfl

/-- The C representation proof instantiates common relabel transport at unchanged cost. -/
theorem coarse_observer_preserves_constructed_refinement :
    CostSimulation ((observedMachine model policy).relabel (fun _ => ()) id id)
      ((machineData model policy).relabel (fun _ => ()) id id) Related 1 :=
  (forward model policy).relabel (fun _ => ()) id id

theorem zero_interface_cost_cannot_match_visible_source_progress :
    ¬ CostSimulation (observedMachine model policy) (machineData model policy) Related 0 := by
  intro simulation
  obtain ⟨count, bound, saved, reached, _⟩ := simulation.publish
    (state := loopEnd) (state' := encodeConfiguration loopEnd) rfl loop_backedge_has_one_visible_iteration
  have zero : count = 0 := Nat.eq_zero_of_le_zero bound
  rw [zero] at reached
  have events := congrArg Prod.fst reached
  simp only [Machine.run] at events
  cases events

/-! ## Full outcome and regional-divergence instances -/

theorem actual_drivers_construct_both_absent_transition_laws :
    MatchesStuck (observedMachine model policy) (machineData model policy) Related 1 ∧
      MatchesStuck (machineData model policy) (observedMachine model policy)
        (fun data source => Related source data) 1 :=
  ⟨forward_matches_stuck _ _, backward_matches_stuck _ _⟩

theorem total_drivers_never_produce_stuck (fuel : Nat)
    (source stoppedSource : Configuration model) (data stoppedData : ConfigurationData) :
    ((observedMachine model policy).run fuel source).2 ≠ .stuck stoppedSource ∧
      ((machineData model policy).run fuel data).2 ≠ .stuck stoppedData :=
  ⟨source_run_ne_stuck _ _ _ _ _, data_run_ne_stuck _ _ _ _ _⟩

theorem all_arbitrary_configuration_outcomes_keep_their_exact_codec_relation
    (fuel : Nat) (source : Configuration model) (data : ConfigurationData) (related : Related source data) :
    ((machineData model policy).run fuel data).1 = ((observedMachine model policy).run fuel source).1 ∧
      OutcomeRel Related ((observedMachine model policy).run fuel source).2
        ((machineData model policy).run fuel data).2 := finite_outcomes_exact _ _ _ _ _ related

theorem cycle_diverges_inside_its_current_interaction_region
    (source : Configuration model) (cycling : Cycling source) :
    (observedMachine model policy).DivergesWithin source := by
  intro fuel
  obtain ⟨events, saved, reached, _⟩ := arbitrary_loop_prefix_retains_a_cycle fuel source cycling
  exact ⟨saved, congrArg Prod.snd reached⟩

theorem both_concrete_cycle_endpoints_and_their_packets_diverge :
    (observedMachine model policy).DivergesWithin loopBody ∧
      (observedMachine model policy).DivergesWithin loopEnd ∧
      (machineData model policy).DivergesWithin (encodeConfiguration loopBody) ∧
      (machineData model policy).DivergesWithin (encodeConfiguration loopEnd) := by
  have body := cycle_diverges_inside_its_current_interaction_region loopBody (Or.inl rfl)
  have backedge := cycle_diverges_inside_its_current_interaction_region loopEnd (Or.inr rfl)
  exact ⟨body, backedge, (divergence_correspondence _ _ _ _ rfl).mp body,
    (divergence_correspondence _ _ _ _ rfl).mp backedge⟩

theorem every_represented_loop_prefix_constructs_its_exact_source_residual
    (fuel : Nat) (source : Configuration model) (cycling : Cycling source) :
    ∃ events saved, (observedMachine model policy).run fuel source = (events, .exhausted saved) ∧
      (machineData model policy).run fuel (encodeConfiguration source) =
        (events, .exhausted (encodeConfiguration saved)) ∧ Cycling saved := by
  obtain ⟨events, saved, reached, retained⟩ := arbitrary_loop_prefix_retains_a_cycle fuel source cycling
  exact ⟨events, saved, reached, pause_encoded _ _ _ _ _ _ reached, retained⟩

theorem arbitrary_represented_loop_pause_retains_regional_divergence
    (fuel : Nat) (events : List ReceiptData) (saved : ConfigurationData)
    (paused : (machineData model policy).run fuel (encodeConfiguration loopBody) =
      (events, .exhausted saved)) :
    ∃ source, (observedMachine model policy).run fuel loopBody = (events, .exhausted source) ∧
      Related source saved ∧ (observedMachine model policy).DivergesWithin source ∧
      (machineData model policy).DivergesWithin saved :=
  divergence_after_represented_pause model policy fuel loopBody _ saved events rfl
    (cycle_diverges_inside_its_current_interaction_region loopBody (Or.inl rfl)) paused

/-- Visible iteration occurrences are retained for every finite number of
loop traversals, rather than erased into a silent-divergence classification. -/
theorem every_two_interface_steps_retain_one_loop_iteration (rounds : Nat) :
    (observedMachine model policy).run (2 * rounds) loopBody =
      (List.replicate rounds loopReceipt, .exhausted loopBody) := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [show 2 * (rounds + 1) = (2 * rounds + 1) + 1 by omega,
        (observedMachine model policy).run_succ_silent loop_body_has_one_administrative_transition,
        (observedMachine model policy).run_succ_publish loop_backedge_has_one_visible_iteration, ih]
      simp only [List.replicate_succ, List.singleton_append]

theorem represented_loop_keeps_every_iteration_and_the_complete_cycle_state (rounds : Nat) :
    (machineData model policy).run (2 * rounds) (encodeConfiguration loopBody) =
      (List.replicate rounds loopReceipt, .exhausted (encodeConfiguration loopBody)) := by
  rw [run_encoded, every_two_interface_steps_retain_one_loop_iteration]
  rfl

theorem scheduler_suspension_is_a_regional_boundary :
    ¬ (observedMachine model policy).DivergesWithin waiting ∧
      ¬ (machineData model policy).DivergesWithin (encodeConfiguration waiting) := by
  have representedStops : ¬ (machineData model policy).DivergesWithin (encodeConfiguration waiting) := by
    intro diverges
    obtain ⟨residual, exhausted⟩ := diverges 1
    rw [suspension_and_saved_state_agree] at exhausted
    cases exhausted
  exact ⟨fun diverges => representedStops ((divergence_correspondence _ _ _ _ rfl).mp diverges),
    representedStops⟩

theorem malformed_representation_verdict_cannot_be_regional_divergence :
    ¬ (machineData model policy).DivergesWithin malformed := by
  intro diverges
  exact malformed_packet_has_no_related_concrete_configuration
    (represented_divergence_is_decodable _ _ _ diverges)

theorem terminal_arithmetic_diagnostic_is_finished_instead_of_faulted :
    ((machineData model policy).run 1 StatementDataControls.halted).2 ≠ .faulted ∧
      ¬ (machineData model policy).DivergesWithin StatementDataControls.halted := by
  constructor
  · rw [represented_arithmetic_terminal_keeps_source_fault]
    intro impossible
    cases impossible
  · intro diverges
    obtain ⟨residual, exhausted⟩ := diverges 1
    rw [represented_arithmetic_terminal_keeps_source_fault] at exhausted
    cases exhausted

theorem refused_partition_keeps_its_own_finishing_verdict :
    (machineData model policy).run 1 (encodeConfiguration StatementControls.stale) =
      ([], .finished (.source (.refused (encodeConfiguration StatementControls.stale)))) := by cbv

theorem refused_partition_is_not_a_stuck_or_divergent_program :
    (∀ stopped, ((machineData model policy).run 1 (encodeConfiguration StatementControls.stale)).2 ≠ .stuck stopped) ∧
      ¬ (machineData model policy).DivergesWithin (encodeConfiguration StatementControls.stale) := by
  refine ⟨data_run_ne_stuck model policy 1 _, ?_⟩
  intro diverges
  obtain ⟨residual, exhausted⟩ := diverges 1
  rw [refused_partition_keeps_its_own_finishing_verdict] at exhausted
  cases exhausted

def conflictingSource : Configuration model := .expression StatementControls.conflicting
  (ExpressionEventExecution.initialState (compile StatementControls.conflicting) memory) (.discard .stop) []

/-- The independent conflict judgment still gives a source diagnostic, rather
than converting a C unsequenced pair into a generic machine stuck outcome. -/
theorem unsequenced_pair_keeps_its_own_finishing_verdict :
    ∃ first second, (machineData model policy).run 1 (encodeConfiguration conflictingSource) =
      ([], .finished (.source (.unsequenced
        (LocatedExpressionData.encodeExpression StatementControls.conflicting) first second
        (encodeConfiguration conflictingSource)))) := by
  have found : ∃ first second,
      (compile StatementControls.conflicting).component.evaluation.findConflict
        (compile StatementControls.conflicting).component.enumeration = some (first, second) := by
    cases conflict : (compile StatementControls.conflicting).component.evaluation.findConflict
      (compile StatementControls.conflicting).component.enumeration with
    | none =>
        have forbidden := StatementControls.unsequenced_access_is_not_admitted
        simp only [ExpressionEventExecution.admissible, conflict, decide_true] at forbidden
        contradiction
    | some pair => cases pair; exact ⟨_, _, rfl⟩
  obtain ⟨first, second, conflict⟩ := found
  have classified := (StatementMachine.conflict_reported policy StatementControls.conflicting
    (ExpressionEventExecution.initialState (compile StatementControls.conflicting) memory)
    (.discard .stop) [] first second conflict).1
  have encoded := machineData_step_encoded model policy conflictingSource _ classified
  refine ⟨LocatedExpressionData.encodeIndex StatementControls.conflicting first,
    LocatedExpressionData.encodeIndex StatementControls.conflicting second, ?_⟩
  simpa only [encodeTransition, encodeVerdict, liftTransition, conflictingSource] using
    (machineData model policy).run_succ_finish (fuel := 0) encoded

theorem unsequenced_diagnostic_cannot_be_regional_divergence :
    ¬ (machineData model policy).DivergesWithin (encodeConfiguration conflictingSource) := by
  obtain ⟨first, second, stopped⟩ := unsequenced_pair_keeps_its_own_finishing_verdict
  intro diverges
  obtain ⟨residual, exhausted⟩ := diverges 1
  rw [stopped] at exhausted
  cases exhausted

end Mettapedia.Languages.C11.StatementMachineRefinementControls
