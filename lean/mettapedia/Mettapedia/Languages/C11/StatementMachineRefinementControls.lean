import Mettapedia.Languages.C11.StatementMachineRefinement
import Mettapedia.Languages.C11.StatementDataControls
import Mettapedia.Languages.C11.FixedCoreControls
import Mettapedia.Languages.C11.LocatedExpressionControls

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

set_option maxRecDepth 2000
namespace Mettapedia.Languages.C11.StatementMachineRefinementControls.FixedLocated
open IntegerMemoryModel LocatedExpressions ExpressionEvents ExpressionEventExecution
open StatementMachineRefinement.FixedLocated

abbrev model := IntegerMemoryControls.model
abbrev memory := IntegerMemoryControls.initial
abbrev policy := intervalReductionPolicy
abbrev one := FixedCoreControls.one
abbrev two := FixedCoreControls.two
abbrev three := FixedCoreControls.three
abbrev six := FixedCoreControls.six
abbrev zero := FixedCoreControls.zero
abbrev maximum := FixedCoreControls.intMax

def first : Expression model := .arithmetic .add (.value two) (.value three)
def second : Expression model := .arithmetic .add (.value six) (.value one)
def product : Expression model := .arithmetic .multiply first second

def productSource : FixedCore.Expression model := .binary .multiply
  (.binary .add (.constant two) (.constant three)) (.binary .add (.constant six) (.constant one))

def leftFirst {left right : Expression model} : List (Index (.arithmetic .multiply left right)) :=
  (LocatedExpressionControls.occurrences left).map (Sum.inl ∘ Sum.inl) ++
    (LocatedExpressionControls.occurrences right).map (Sum.inl ∘ Sum.inr) ++ [.inr 0]
def rightFirst {left right : Expression model} : List (Index (.arithmetic .multiply left right)) :=
  (LocatedExpressionControls.occurrences right).map (Sum.inl ∘ Sum.inr) ++
    (LocatedExpressionControls.occurrences left).map (Sum.inl ∘ Sum.inl) ++ [.inr 0]

def expressionNumber {expression : Expression model} (fuel : Nat) (choices : List (Index expression)) : Option Int :=
  match ((machine model policy).run fuel ⟨compile expression, initialState (compile expression) memory, choices⟩).2 with
  | .finished (.returned value _) => some value.integer.value
  | _ => none

theorem pure_source_is_actually_lowered : lower memory [] [] productSource = some product := by cbv

theorem pure_source_integer_value : observe (FixedCore.evaluate model policy memory [] [] productSource) =
    some ⟨.int, ⟨35, by decide⟩⟩ := by cbv

theorem both_operand_orders_return_same_value :
    (expressionNumber (expression := product) 8 leftFirst, expressionNumber (expression := product) 8 rightFirst) =
      (some 35, some 35) := by cbv

theorem lowered_product_has_general_schedule_theorem
    (events : List (ExpressionEventHistory.Occurrence (Index product) model))
    (final : SemanticState (Index product) model)
    (history : ExpressionEventHistory.SemanticHistory policy (compile product)
      (represent (initialState (compile product) memory)) events final)
    (value : IntegerScalar.Value model.parameters)
    (present : lookupScalar final.cache (result product) = some value) :
    value.integer.value = 35 ∧ final.memory = ObjectAccessMemory.represent memory := by
  obtain ⟨observed, unchanged⟩ := pure_history_no_invention policy memory [] [] productSource product
    (lower_sound policy memory [] [] _ _ pure_source_is_actually_lowered) events final history value present
  rw [pure_source_integer_value] at observed
  cases observed
  exact ⟨rfl, unchanged⟩

def overflowing : Expression model := .arithmetic .add (.value maximum) (.value one)
def dividing : Expression model := .arithmetic .divide (.value one) (.value zero)
def twoFaults : Expression model := .arithmetic .multiply overflowing dividing

def twoFaultsSource : FixedCore.Expression model := .binary .multiply
  (.binary .add (.constant maximum) (.constant one)) (.binary .divide (.constant one) (.constant zero))

def arithmeticDiagnostic {expression : Expression model} (choices : List (Index expression)) : Option ArithmeticFault :=
  match ((machine model policy).run 8 ⟨compile expression, initialState (compile expression) memory, choices⟩).2 with
  | .finished (.terminal _ (.arithmeticFault _ reason) _) => some reason
  | _ => none

theorem two_failing_operands_are_admitted_pure : lower memory [] [] twoFaultsSource = some twoFaults := by cbv

theorem fixed_core_reports_left_fault : FixedCore.evaluate model policy memory [] [] twoFaultsSource =
    .fault (.arithmetic .int .overflow) := by cbv

theorem pure_operand_order_changes_diagnostic :
    (arithmeticDiagnostic (expression := twoFaults) leftFirst,
      arithmeticDiagnostic (expression := twoFaults) rightFirst) = (some .overflow, some .divisionByZero) := by cbv

theorem undefined_expression_has_no_complete_value
    (events : List (ExpressionEventHistory.Occurrence (Index twoFaults) model))
    (final : SemanticState (Index twoFaults) model)
    (history : ExpressionEventHistory.SemanticHistory policy (compile twoFaults)
      (represent (initialState (compile twoFaults) memory)) events final)
    (value : IntegerScalar.Value model.parameters) :
    ¬ LocatedStatements.CompleteExpression twoFaults final value := by
  intro completed
  have observed := (source_boundary_no_invention policy memory [] [] twoFaultsSource twoFaults
    (lower_sound policy memory [] [] _ _ two_failing_operands_are_admitted_pure)
    events final history value completed).1
  rw [fixed_core_reports_left_fault] at observed
  cases observed

def scopes : List (FixedCore.Scope model) :=
  [⟨⟨[("x", IntegerMemoryControls.integer)], [7]⟩, []⟩]
def arrays : ArrayPointers.Catalog := [(7, ⟨7, 4, 4, 1⟩)]
def loadSource : FixedCore.Expression model := .read (.named "x")
def loadTarget : Expression model := .load ⟨IntegerMemoryControls.integer, .int, rfl⟩
def missingCatalog : ObjectAccessMemory.State model.characters := ⟨memory.storage, []⟩

theorem named_read_lowers_to_checked_location : lower memory arrays scopes loadSource = some loadTarget := by cbv

theorem loaded_memory_zero_agrees : observe (FixedCore.evaluate model policy memory arrays scopes loadSource) =
    evaluate policy memory loadTarget :=
  (lower_sound policy memory arrays scopes _ _ named_read_lowers_to_checked_location).evaluate

theorem memory_refusal_is_inside_the_common_fragment :
    lower missingCatalog arrays scopes loadSource = some loadTarget := by cbv

theorem fixed_memory_refusal : FixedCore.evaluate model policy missingCatalog arrays scopes loadSource =
    .fault (.access ⟨.int, ⟨7, 0⟩⟩) := by cbv

theorem located_memory_refusal_has_no_occurrence_or_value :
    (machine model policy).run 1 ⟨compile loadTarget, initialState (compile loadTarget) missingCatalog, [show Index loadTarget from (0 : Fin 1)]⟩ =
      ([], .finished (.refused ⟨compile loadTarget, initialState (compile loadTarget) missingCatalog, [show Index loadTarget from (0 : Fin 1)]⟩)) := by cbv

def deadMemory : ObjectAccessMemory.State model.characters :=
  ⟨[(7, ⟨false, List.replicate 32 IntegerMemoryControls.zero⟩)], memory.catalog⟩

theorem ended_lifetime_is_not_admitted_as_a_live_location : lower deadMemory arrays scopes loadSource = none := by cbv

theorem effectful_assignment_is_not_pure : ¬ Pure LocatedExpressionControls.assignment := by
  intro pure
  cases pure

theorem effectful_prefix_order_changes_memory :
    LocatedExpressionControls.probe policy 3 LocatedExpressionControls.assignment LocatedExpressionControls.valueFirst ≠
      LocatedExpressionControls.probe policy 3 LocatedExpressionControls.assignment LocatedExpressionControls.storeFirst := by
  intro same
  have projected := congrArg (fun value => value.map (fun item => item.integer)) same
  cbv at projected
  contradiction

def loopSource : FixedCore.Statement model := .sequence
  (.whileLoop (.constant one) .breakLoop)
  (.returnValue (some (.binary .add (.constant two) (.constant three))))
def loopTarget : LocatedStatements.Statement model := .sequence
  (.whileLoop (.value one) .breakLoop) (.returnValue (some first))

theorem common_loop_is_actually_lowered : lowerStatement memory [] [] loopSource = some loopTarget := by cbv

def loopChoices : List LocatedExpressionData.IndexData :=
  [LocatedExpressionData.encodeIndex (.value one) 0] ++
    (LocatedExpressionControls.occurrences first).map (LocatedExpressionData.encodeIndex first)

def statementNumber (fuel : Nat) (initial : LocatedStatements.Configuration model) : Option Int :=
  match ((StatementMachine.machine model policy).run fuel initial).2 with
  | .finished (.returned (some value) _) => some value.integer.value
  | _ => none

theorem both_statement_machines_return_five :
    (FixedCoreControls.returned ((FixedCore.machine model policy FixedCoreControls.abi []).run 20
        (fixedConfiguration memory [] [] [] (.execute loopSource) .stop)),
      statementNumber 20 (LocatedStatements.initial loopTarget memory loopChoices)) = (some 5, some 5) := by cbv

theorem unsupported_calls_remain_outside_lowering :
    lowerStatement memory [] [] (.call (some "answer") "f" []) = none := by cbv

def counterSource : FixedCore.Statement model := .sequence
  (.assign (.named "x") (.constant two))
  (.sequence (.whileLoop loadSource (.assign (.named "x") (.binary .subtract loadSource (.constant one))))
    (.returnValue (some loadSource)))
def counterStep : Expression model := .assignment
  ⟨IntegerMemoryControls.integer, .int, rfl⟩ (.arithmetic .subtract loadTarget (.value one))
def counterInit : Expression model := .assignment ⟨IntegerMemoryControls.integer, .int, rfl⟩ (.value two)
def counterTarget : LocatedStatements.Statement model := .sequence (.expression counterInit)
  (.sequence (.whileLoop loadTarget (.expression counterStep)) (.returnValue (some loadTarget)))

theorem counter_loop_is_admitted : lowerStatement memory arrays scopes counterSource = some counterTarget := by cbv

def assignmentChoices (destination : Destination) (operand : Expression model) (copyFirst : Bool) :
    List LocatedExpressionData.IndexData :=
  let earlier : List (Index (.assignment destination operand)) :=
    (LocatedExpressionControls.occurrences (.cast destination.type operand)).map Sum.inl
  let later : List (Index (.assignment destination operand)) :=
    if copyFirst then [.inr 1, .inr 0] else [.inr 0, .inr 1]
  (earlier ++ later).map (LocatedExpressionData.encodeIndex (.assignment destination operand))
def counterChoices (copyFirst : Bool) : List LocatedExpressionData.IndexData :=
  assignmentChoices ⟨IntegerMemoryControls.integer, .int, rfl⟩ (.value two) copyFirst ++
  [LocatedExpressionData.encodeIndex loadTarget (show Index loadTarget from (0 : Fin 1))] ++
  assignmentChoices ⟨IntegerMemoryControls.integer, .int, rfl⟩ (.arithmetic .subtract loadTarget (.value one)) copyFirst ++
  [LocatedExpressionData.encodeIndex loadTarget (show Index loadTarget from (0 : Fin 1))] ++
  assignmentChoices ⟨IntegerMemoryControls.integer, .int, rfl⟩ (.arithmetic .subtract loadTarget (.value one)) copyFirst ++
  [LocatedExpressionData.encodeIndex loadTarget (show Index loadTarget from (0 : Fin 1)),
    LocatedExpressionData.encodeIndex loadTarget (show Index loadTarget from (0 : Fin 1))]

def storedIntegers (events : List (StatementMachine.Receipt model)) : List Int :=
  events.filterMap (fun receipt => match receipt.event with
    | .occurrence _ _ (.stored value) => some value.integer.value
    | _ => none)

theorem counter_loop_updates_and_returns_zero :
    (FixedCoreControls.returned ((FixedCore.machine model policy FixedCoreControls.abi []).run 40
        (fixedConfiguration memory arrays scopes [] (.execute counterSource) .stop)),
      statementNumber 60 (LocatedStatements.initial counterTarget memory (counterChoices false)),
      statementNumber 60 (LocatedStatements.initial counterTarget memory (counterChoices true))) =
      (some 0, some 0, some 0) := by cbv

theorem counter_loop_keeps_all_three_commits :
    (storedIntegers (((StatementMachine.machine model policy).run 60
      (LocatedStatements.initial counterTarget memory (counterChoices false))).1),
      storedIntegers (((StatementMachine.machine model policy).run 60
        (LocatedStatements.initial counterTarget memory (counterChoices true))).1)) =
      ([2, 1, 0], [2, 1, 0]) := by cbv

/-! ## Source refusal, diagnostic freedom and retained faulting runs

The successful prefix stores once. Different legal operand schedules then
expose different arithmetic diagnostics, while both executions refuse. Empty
budgets, missing choices and unready choices remain separately observable. -/

set_option maxRecDepth 3000

def faultAfterStoreSource : FixedCore.Statement model := .sequence
  (.assign (.named "x") (.constant two)) (.returnValue (some twoFaultsSource))
def faultAfterStoreTarget : LocatedStatements.Statement model := .sequence
  (.expression counterInit) (.returnValue (some twoFaults))
def faultAfterStoreChoices : List LocatedExpressionData.IndexData :=
  assignmentChoices ⟨IntegerMemoryControls.integer, .int, rfl⟩ (.value two) false ++
    (rightFirst (left := overflowing) (right := dividing)).map (LocatedExpressionData.encodeIndex twoFaults)
def faultAfterStoreInitial : LocatedStatements.Configuration model :=
  LocatedStatements.initial faultAfterStoreTarget memory faultAfterStoreChoices

def diagnosticOf (outcome : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (LocatedStatements.Configuration model)
    (StatementMachine.Verdict model) (StatementMachine.SelectionRequest model)) : Option ArithmeticFault :=
  match outcome with
  | .finished (.terminal _ _ (.arithmeticFault _ reason) _) => some reason
  | _ => none


theorem fault_after_store_is_admitted :
    lowerStatement memory arrays scopes faultAfterStoreSource = some faultAfterStoreTarget := by cbv

def fixedArithmeticFaults (events : List (FixedCore.Event model)) : List ArithmeticFault :=
  events.filterMap (fun event => match event with
    | .fault (.arithmetic _ reason) => some reason
    | _ => none)

theorem source_and_located_refuse_with_different_valid_diagnostics :
    (fixedArithmeticFaults (((FixedCore.machine model policy FixedCoreControls.abi []).run 20
        (fixedConfiguration memory arrays scopes [] (.execute faultAfterStoreSource) .stop))).1,
      diagnosticOf (((StatementMachine.machine model policy).run 20 faultAfterStoreInitial).2)) =
      ([.overflow], some .divisionByZero) := by cbv

def faultAfterStorePaused : LocatedStatements.Configuration model :=
  match ((StatementMachine.machine model policy).run 6 faultAfterStoreInitial).2 with
  | .exhausted saved => saved
  | _ => faultAfterStoreInitial

theorem fault_prefix_has_a_retained_checkpoint :
    (StatementMachine.machine model policy).run 6 faultAfterStoreInitial =
      (((StatementMachine.machine model policy).run 6 faultAfterStoreInitial).1,
        .exhausted faultAfterStorePaused) := by cbv

theorem fault_resume_does_not_repeat_its_committed_store :
    (storedIntegers (((StatementMachine.machine model policy).run 6 faultAfterStoreInitial).1),
      storedIntegers (((StatementMachine.machine model policy).run 7 faultAfterStorePaused).1),
      diagnosticOf (((StatementMachine.machine model policy).run 7 faultAfterStorePaused).2)) =
      ([2], [], some .divisionByZero) := by cbv

theorem fault_resume_keeps_the_exact_receipt_suffix :
    (StatementMachine.machine model policy).run 13 faultAfterStoreInitial =
      (((StatementMachine.machine model policy).run 6 faultAfterStoreInitial).1 ++
        ((StatementMachine.machine model policy).run 7 faultAfterStorePaused).1,
        ((StatementMachine.machine model policy).run 7 faultAfterStorePaused).2) := by
  rw [show 13 = 6 + 7 from rfl, (StatementMachine.machine model policy).run_add,
    fault_prefix_has_a_retained_checkpoint]
  rfl

def unreadyProduct : LocatedStatements.Configuration model :=
  .expression product (initialState (compile product) memory) .returnValue
    [LocatedExpressionData.encodeIndex product (.inr 0)]

theorem an_unready_scheduler_choice_is_a_machine_refusal :
    (StatementMachine.machine model policy).run 1 unreadyProduct =
      ([], .finished (.refused unreadyProduct)) := by cbv

theorem scheduler_refusal_does_not_make_a_defined_expression_faulty :
    ¬ ExpressionEventHistory.Failure policy (compile product)
      (represent (initialState (compile product) memory)) := by
  intro failed
  exact pure_failure_excludes_value policy memory product
    (lower_sound policy memory [] [] _ _ pure_source_is_actually_lowered).pure [] _ (.nil _)
    (initial_partition (compile product) memory) failed ⟨.int, ⟨35, by decide⟩⟩ (by cbv)

def unfedFault : LocatedStatements.Configuration model :=
  .expression twoFaults (initialState (compile twoFaults) memory) .returnValue []

theorem an_empty_budget_cannot_finish_the_fault :
    (StatementMachine.machine model policy).run 0 unfedFault = ([], .exhausted unfedFault) := rfl

theorem missing_choices_suspend_even_a_faulting_source :
    ∃ request, (StatementMachine.machine model policy).run 1 unfedFault =
      ([], .suspended request unfedFault) := by
  refine ⟨⟨twoFaults, (SequencingSchedule.choices (compile twoFaults).component.evaluation.order
    (initialState (compile twoFaults) memory).pending).map (LocatedExpressionData.encodeIndex twoFaults)⟩, ?_⟩
  cbv

theorem two_faults_construct_an_independent_failed_history :
    ∃ events final, ExpressionEventHistory.SemanticHistory policy (compile twoFaults)
      (represent (initialState (compile twoFaults) memory)) events (represent final) ∧
      Partition (compile twoFaults) final.pending final.cache ∧
      ExpressionEventHistory.Failure policy (compile twoFaults) (represent final) :=
  (source_fault_iff_failed_history policy memory [] [] twoFaultsSource twoFaults
    (lower_sound policy memory [] [] _ _ two_failing_operands_are_admitted_pure)).mp
      ⟨_, fixed_core_reports_left_fault⟩

theorem missing_catalog_constructs_an_independent_refusal_history :
    ∃ events final, ExpressionEventHistory.SemanticHistory policy (compile loadTarget)
      (represent (initialState (compile loadTarget) missingCatalog)) events (represent final) ∧
      Partition (compile loadTarget) final.pending final.cache ∧
      ExpressionEventHistory.Failure policy (compile loadTarget) (represent final) :=
  (source_fault_iff_failed_history policy missingCatalog arrays scopes loadSource loadTarget
    (lower_sound policy missingCatalog arrays scopes _ _ memory_refusal_is_inside_the_common_fragment)).mp
      ⟨_, fixed_memory_refusal⟩

theorem unready_product_is_outside_the_scheduler_admission :
    ¬ LicensedNext (LocatedStatements.represent unreadyProduct) := by
  intro licensed
  obtain ⟨index, decoded, ready⟩ := licensed rfl (by decide)
    (LocatedExpressionData.encodeIndex product (.inr 0)) [] rfl
  have same : (Sum.inr 0 : Index product) = index :=
    Option.some.inj ((LocatedExpressionData.decodeIndex_encode product (.inr 0)).symm.trans decoded)
  subst index
  have refused : (Sum.inr 0 : Index product) ∉ SequencingSchedule.choices
      (compile product).component.evaluation.order (initialState (compile product) memory).pending := by
    cbv
    intro present
    rcases List.mem_cons.mp present with impossible | present
    · cases impossible
    rcases List.mem_cons.mp present with impossible | present
    · cases impossible
    rcases List.mem_cons.mp present with impossible | present
    · cases impossible
    rcases List.mem_cons.mp present with impossible | present
    · cases impossible
    cases present
  exact refused ((SequencingSchedule.mem_choices_iff _ _ _).mpr ready)

private theorem counter_initial_reached (copyFirst : Bool) :
    ReachedControl policy arrays scopes []
      (fixedConfiguration memory arrays scopes [] (.execute counterSource) .stop)
      (LocatedStatements.represent (LocatedStatements.initial counterTarget memory (counterChoices copyFirst))) :=
  .boundary (.statement (lowerStatement_sound policy memory arrays scopes _ _ counter_loop_is_admitted) .stop) _

theorem every_counter_prefix_has_a_real_source_owner (copyFirst : Bool) (fuel : Nat)
    (receipts : List (StatementMachine.Receipt model)) (saved : LocatedStatements.Configuration model)
    (paused : (StatementMachine.machine model policy).run fuel
      (LocatedStatements.initial counterTarget memory (counterChoices copyFirst)) = (receipts, .exhausted saved)) :
    ∃ source events,
      Relation.ReflTransGen (SourceRunningStep policy FixedCoreControls.abi [])
        (fixedConfiguration memory arrays scopes [] (.execute counterSource) .stop) source ∧
      ReachedControl policy arrays scopes [] source (LocatedStatements.represent saved) ∧
      StatementHistory.History policy
        (LocatedStatements.represent (LocatedStatements.initial counterTarget memory (counterChoices copyFirst)))
        events (LocatedStatements.represent saved) ∧ events.length = fuel ∧
      receipts.map StatementMachine.Receipt.event = events.filterMap id :=
  (counter_initial_reached copyFirst).exhausted policy arrays scopes [] FixedCoreControls.abi [] _ saved fuel receipts paused

private theorem fault_initial_reached :
    ReachedControl policy arrays scopes []
      (fixedConfiguration memory arrays scopes [] (.execute faultAfterStoreSource) .stop)
      (LocatedStatements.represent faultAfterStoreInitial) :=
  .boundary (.statement (lowerStatement_sound policy memory arrays scopes _ _ fault_after_store_is_admitted) .stop) _

def faultTerminalCheckpoint : LocatedStatements.Configuration model :=
  match ((StatementMachine.machine model policy).run 12 faultAfterStoreInitial).2 with
  | .exhausted saved => saved
  | _ => faultAfterStoreInitial

theorem fault_run_reaches_exact_terminal_checkpoint :
    (StatementMachine.machine model policy).run 12 faultAfterStoreInitial =
      (((StatementMachine.machine model policy).run 12 faultAfterStoreInitial).1,
        .exhausted faultTerminalCheckpoint) := by cbv

theorem fault_terminal_checkpoint_has_admitted_schedule :
    LicensedNext (LocatedStatements.represent faultTerminalCheckpoint) := by cbv; simp

theorem fault_run_has_admitted_scheduling_at_every_prefix :
    LicensedExecution policy 13 faultAfterStoreInitial := by
  obtain ⟨events, history, length, _⟩ := StatementHistory.exhausted_has_source_history policy 12
    faultAfterStoreInitial faultTerminalCheckpoint _ fault_run_reaches_exact_terminal_checkpoint
  have licensed := history_licensed_execution policy events history faultAfterStoreInitial rfl
    fault_terminal_checkpoint_has_admitted_schedule
  simpa only [length] using licensed

def actualFaultVerdict : StatementMachine.Verdict model :=
  match ((StatementMachine.machine model policy).run 13 faultAfterStoreInitial).2 with
  | .finished verdict => verdict
  | _ => .refused faultAfterStoreInitial

theorem entire_faulting_run_reflects_to_a_source_refusal :
    ReachesTerminal policy FixedCoreControls.abi []
      (fixedConfiguration memory arrays scopes [] (.execute faultAfterStoreSource) .stop) none := by
  have reflected := fault_initial_reached.finished_run_of_licensed policy arrays scopes []
    FixedCoreControls.abi [] faultAfterStoreInitial 13
    (((StatementMachine.machine model policy).run 13 faultAfterStoreInitial).1) actualFaultVerdict
    (by cbv) fault_run_has_admitted_scheduling_at_every_prefix
  have observed : verdictOutput actualFaultVerdict = none := by cbv
  exact observed ▸ reflected

private theorem unfed_fault_reached :
    ReachedControl policy [] [] []
      (fixedConfiguration memory [] [] [] (.execute (.returnValue (some twoFaultsSource))) .stop)
      (LocatedStatements.represent unfedFault) :=
  .expression (.returnValue
    (lower_sound policy memory [] [] _ _ two_failing_operands_are_admitted_pure) .stop)
    [] _ (.nil _) []

theorem suspended_fault_still_has_its_source_and_receipt_history :
    ∃ source events,
      Relation.ReflTransGen (SourceRunningStep policy FixedCoreControls.abi [])
        (fixedConfiguration memory [] [] [] (.execute (.returnValue (some twoFaultsSource))) .stop) source ∧
      ReachedControl policy [] [] [] source (LocatedStatements.represent unfedFault) ∧
      StatementHistory.History policy (LocatedStatements.represent unfedFault) events
        (LocatedStatements.represent unfedFault) ∧ events = [] := by
  obtain ⟨request, suspended⟩ := missing_choices_suspend_even_a_faulting_source
  obtain ⟨count, bound, source, events, _, sourceHistory, reached, history, length, _, _⟩ :=
    unfed_fault_reached.suspended policy [] [] [] FixedCoreControls.abi [] unfedFault unfedFault 1 [] request suspended
  have zero : events.length = 0 := by omega
  exact ⟨source, events, sourceHistory, reached, history, List.length_eq_zero_iff.mp zero⟩

end Mettapedia.Languages.C11.StatementMachineRefinementControls.FixedLocated
