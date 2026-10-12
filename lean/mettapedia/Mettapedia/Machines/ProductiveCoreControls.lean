import Mettapedia.Machines.ProductiveFunctionalMachines
import Mettapedia.Machines.ProductiveCoreOrdered

/-!
# Core adaptation controls: answers, residuals, divergence and frontier costs

The actual CEK and Krivine instances distinguish observed values from open
variables and closed stuck applications. A CEK self-application cycle proves
unbounded computational execution at every fuel. Declaring that cycle silent
administration cannot supply a productive rank. Ordered-frontier controls
retain duplicates and separate lockstep simulation from unequal branch
progress. Operational prices are not hardware or external-effect prices.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProductiveCoreControls

open Mettapedia.GSLT.Distinction
open ProductiveBlocks ProductiveCoreAdapters ProductiveFunctionalMachines ProductiveCoreOrdered

def identityTerm : Tm := .app (.lam (.var 0)) (.lit 7)
def cekLiteralStart : CEK.St := cekCore.load (.lit 7)
def cekLiteralFinal : CEK.St := ⟨.ret (.lit 7), []⟩

theorem bare_core_missing_transition_does_not_invent_answer :
    (coreMachine cekCore).run 2 cekLiteralStart =
      ([(cekLiteralStart, cekLiteralFinal)], .stuck cekLiteralFinal) := rfl

theorem answer_observer_finishes_the_same_computation :
    cekMachine.run 2 cekLiteralStart = ([(cekLiteralStart, cekLiteralFinal)], .finished (.lit 7)) := rfl

theorem completed_cek_uses_one_computation_and_one_boundary :
    cekMachine.spent (computationalPrice cekCore (fun _ => 1)) 2 cekLiteralStart = 1 ∧
      cekMachine.spent (fun _ => 1) 2 cekLiteralStart = 2 := ⟨rfl, rfl⟩

theorem zero_fuel_does_not_poll_even_a_completed_answer :
    krivineMachine.run 0 (krivineCore.load (.lit 7)) = ([], .exhausted (krivineCore.load (.lit 7))) := rfl

theorem krivine_literal_needs_no_control_reduction :
    krivineMachine.run 1 (krivineCore.load (.lit 7)) = ([], .finished (.lit 7)) ∧
      krivineMachine.spent (computationalPrice krivineCore (fun _ => 1)) 1 (krivineCore.load (.lit 7)) = 0 := ⟨rfl, rfl⟩

theorem cek_identity_application_finishes :
    (cekMachine.run 7 (cekCore.load identityTerm)).2 = .finished (.lit 7) := rfl

theorem krivine_identity_application_finishes :
    (krivineMachine.run 4 (krivineCore.load identityTerm)).2 = .finished (.lit 7) := rfl

theorem shared_term_retains_distinct_control_costs :
    cekMachine.spent (computationalPrice cekCore (fun _ => 1)) 7 (cekCore.load identityTerm) = 6 ∧
      krivineMachine.spent (computationalPrice krivineCore (fun _ => 1)) 4 (krivineCore.load identityTerm) = 3 := ⟨rfl, rfl⟩

def cekPrice (state : CEK.St) : Nat := match state.ctl with | .ev _ _ => 2 | .ret _ => 1

theorem declared_nonuniform_computational_price :
    cekMachine.spent (computationalPrice cekCore cekPrice) 7 (cekCore.load identityTerm) = 10 := rfl

def cekIdentityResidual : CEK.St := ⟨.ev (.lit 7) [], [.callWith (.clo (.var 0) [])]⟩
def cekIdentityPrefix : List (Occurrence CEK.St) := (cekMachine.run 3 (cekCore.load identityTerm)).1

theorem cek_prefix_retains_pending_argument_control :
    cekMachine.run 3 (cekCore.load identityTerm) = (cekIdentityPrefix, .exhausted cekIdentityResidual) := rfl

theorem cek_resume_preserves_complete_occurrence_prefix :
    cekMachine.run 7 (cekCore.load identityTerm) =
      (cekIdentityPrefix ++ (cekMachine.run 4 cekIdentityResidual).1, (cekMachine.run 4 cekIdentityResidual).2) :=
  cekMachine.established_and_pending 3 4 (cekCore.load identityTerm) cekIdentityResidual cekIdentityPrefix
    cek_prefix_retains_pending_argument_control

theorem cek_resume_account_is_additive :
    cekMachine.spent (computationalPrice cekCore cekPrice) 7 (cekCore.load identityTerm) =
      cekMachine.spent (computationalPrice cekCore cekPrice) 3 (cekCore.load identityTerm) +
        cekMachine.spent (computationalPrice cekCore cekPrice) 4 cekIdentityResidual := rfl

theorem restart_replays_computational_occurrences :
    (cekIdentityPrefix ++ (cekMachine.run 7 (cekCore.load identityTerm)).1).length = 9 ∧
      (cekMachine.run 7 (cekCore.load identityTerm)).1.length = 6 := ⟨rfl, rfl⟩

def cekOpen : CEK.St := cekCore.load (.var 0)
def krivineOpen : Krivine.KSt := krivineCore.load (.var 0)

theorem cek_open_variable_is_stuck (fuel : Nat) : cekMachine.run (fuel + 1) cekOpen = ([], .stuck cekOpen) :=
  cekMachine.run_succ_stuck rfl

theorem krivine_open_variable_is_stuck (fuel : Nat) : krivineMachine.run (fuel + 1) krivineOpen = ([], .stuck krivineOpen) :=
  krivineMachine.run_succ_stuck rfl

theorem cek_open_variable_never_observes_success (fuel : Nat) : cekMachine.observe fuel cekOpen = ⟨[], .incomplete⟩ :=
  cekMachine.stuck_incomplete cekOpen rfl fuel

theorem krivine_open_variable_never_observes_success (fuel : Nat) : krivineMachine.observe fuel krivineOpen = ⟨[], .incomplete⟩ :=
  krivineMachine.stuck_incomplete krivineOpen rfl fuel

theorem full_cek_state_carrier_is_not_productive : IsEmpty cekMachine.Productive :=
  ⟨fun productive => productive.moves cekOpen rfl⟩

theorem full_krivine_state_carrier_is_not_productive : IsEmpty krivineMachine.Productive :=
  ⟨fun productive => productive.moves krivineOpen rfl⟩

theorem stuck_open_variable_is_not_divergent : ¬ cekMachine.DivergesWithin cekOpen := by
  intro diverges
  have bare := (answer_diverges_iff_core cekAnswerCore cekOpen).mp diverges
  exact (core_diverges_iff_no_reachable_final cekCore cekOpen).mp bare cekOpen .refl rfl

theorem returned_literal_is_not_divergent : ¬ cekMachine.DivergesWithin cekLiteralStart := by
  intro diverges
  have bare := (answer_diverges_iff_core cekAnswerCore cekLiteralStart).mp diverges
  exact (core_diverges_iff_no_reachable_final cekCore cekLiteralStart).mp bare cekLiteralFinal
    (.single (show cekCore.StepRel cekLiteralStart cekLiteralFinal from rfl)) rfl

def invalidApplication : Tm := .app (.lit 1) (.lit 2)
def cekInvalidFinal : CEK.St := ⟨.ret (.lit 2), [.callWith (.lit 1)]⟩
def krivineInvalidFinal : Krivine.KSt := ⟨.lit 1, [], [.mk (.lit 2) []]⟩

theorem closed_cek_application_can_be_stuck :
    (cekMachine.run 5 (cekCore.load invalidApplication)).2 = .stuck cekInvalidFinal := rfl

theorem closed_krivine_application_can_be_stuck :
    (krivineMachine.run 2 (krivineCore.load invalidApplication)).2 = .stuck krivineInvalidFinal := rfl

theorem krivine_pending_argument_is_not_a_completed_literal : krivineAnswer krivineInvalidFinal = none := rfl

def omegaCycle0 : CEK.St := ⟨.ev selfApp [deltaV], []⟩
def omegaCycle1 : CEK.St := ⟨.ev (.var 0) [deltaV], [.argOf (.var 0) [deltaV]]⟩
def omegaCycle2 : CEK.St := ⟨.ret deltaV, [.argOf (.var 0) [deltaV]]⟩
def omegaCycle3 : CEK.St := ⟨.ev (.var 0) [deltaV], [.callWith deltaV]⟩
def omegaCycle4 : CEK.St := ⟨.ret deltaV, [.callWith deltaV]⟩

def omegaRegion (state : CEK.St) : Prop :=
  state = omegaCycle0 ∨ state = omegaCycle1 ∨ state = omegaCycle2 ∨ state = omegaCycle3 ∨ state = omegaCycle4

theorem omega_region_closed (state : CEK.St) (inside : omegaRegion state) :
    ∃ next, cekCore.StepRel state next ∧ omegaRegion next := by
  rcases inside with rfl | rfl | rfl | rfl | rfl
  · exact ⟨omegaCycle1, rfl, .inr (.inl rfl)⟩
  · exact ⟨omegaCycle2, rfl, .inr (.inr (.inl rfl))⟩
  · exact ⟨omegaCycle3, rfl, .inr (.inr (.inr (.inl rfl)))⟩
  · exact ⟨omegaCycle4, rfl, .inr (.inr (.inr (.inr rfl)))⟩
  · exact ⟨omegaCycle0, rfl, .inl rfl⟩

theorem actual_cek_cycle_diverges_with_or_without_answer_observer :
    cekMachine.DivergesWithin omegaCycle0 ∧
      (coreMachine cekCore).DivergesWithin omegaCycle0 := by
  have diverges : cekMachine.DivergesWithin omegaCycle0 := by
    intro fuel
    obtain ⟨events, residual, ran, _, _, _⟩ :=
      perpetual_computation cekAnswerCore omegaRegion omega_region_closed fuel omegaCycle0 (.inl rfl)
    exact ⟨residual, congrArg Prod.snd ran⟩
  exact ⟨diverges, (answer_diverges_iff_core cekAnswerCore omegaCycle0).mp diverges⟩

theorem omega_prefix_reaches_the_cycle :
    (cekMachine.run 5 (cekCore.load bigOmega)).2 = .exhausted omegaCycle0 := rfl

theorem omega_cycle_never_finishes_and_retains_all_steps (fuel : Nat) :
    (cekMachine.observe fuel omegaCycle0).status = .incomplete ∧
      (cekMachine.run fuel omegaCycle0).1.length = fuel := by
  obtain ⟨events, residual, ran, _, count, _⟩ :=
    perpetual_computation cekAnswerCore omegaRegion omega_region_closed fuel omegaCycle0 (.inl rfl)
  change cekMachine.run fuel omegaCycle0 = _ at ran
  simp only [Machine.observe, ran, Outcome.status]
  exact ⟨True.intro, count⟩

theorem loaded_omega_never_finishes_and_retains_all_steps (fuel : Nat) :
    (cekMachine.observe fuel (cekCore.load bigOmega)).status = .incomplete ∧
      (cekMachine.run fuel (cekCore.load bigOmega)).1.length = fuel := by
  by_cases enough : 5 ≤ fuel
  · obtain ⟨second, rfl⟩ := Nat.exists_eq_add_of_le enough
    obtain ⟨events, residual, ran, _, count, _⟩ :=
      perpetual_computation cekAnswerCore omegaRegion omega_region_closed second omegaCycle0 (.inl rfl)
    change cekMachine.run second omegaCycle0 = _ at ran
    have retainedPrefix : cekMachine.run 5 (cekCore.load bigOmega) =
        ((cekMachine.run 5 (cekCore.load bigOmega)).1, .exhausted omegaCycle0) := rfl
    have resumed := cekMachine.established_and_pending 5 second (cekCore.load bigOmega) omegaCycle0
      (cekMachine.run 5 (cekCore.load bigOmega)).1 retainedPrefix
    simp only [Machine.observe, resumed, ran, Outcome.status]
    exact ⟨True.intro, List.length_append.trans (congrArg₂ Nat.add rfl count)⟩
  · have choices : fuel = 0 ∨ fuel = 1 ∨ fuel = 2 ∨ fuel = 3 ∨ fuel = 4 := by omega
    rcases choices with rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

private def silentCekControl : Machine CEK.St (Occurrence CEK.St) CEK.Val Empty where
  step state := (CEK.step state).map .silent

theorem classifying_all_cek_computation_as_silent_has_no_productive_rank :
    IsEmpty silentCekControl.Productive := by
  refine silentCekControl.not_productive_of_silent_region omegaRegion ?_ omegaCycle0 (.inl rfl)
  intro state inside
  obtain ⟨next, step, remains⟩ := omega_region_closed state inside
  refine ⟨next, ?_, remains⟩
  change CEK.step state = some next at step
  simp only [silentCekControl, step]
  rfl

theorem demanded_strategy_computes_while_eager_strategy_has_no_evaluator_answer :
    (∀ fuel, CEK.evalV fuel [] tKO = none) ∧
      (krivineMachine.run 6 (krivineCore.load tKO)).2 = .finished (.lit 7) :=
  ⟨evalV_tKO_none, rfl⟩

abbrev countdown : MachineCore Nat where
  State := Nat
  load := id
  step | 0 => none | remaining + 1 => some remaining

theorem ordered_frontier_retains_duplicate_occurrences :
    (orderedCore countdown).runFrontier 1 [2, 2, 0] = [1, 1, 0] := rfl

theorem frontier_budget_is_per_round :
    (orderedCore countdown).runFrontier 2 [3, 1] = [1, 0] := rfl

theorem frontier_resumes_from_all_residual_occurrences :
    (orderedCore countdown).runFrontier 3 [3, 1] =
      (orderedCore countdown).runFrontier 1 ((orderedCore countdown).runFrontier 2 [3, 1]) := rfl

def sameTerminality (source target : Nat) : Prop := source = 0 ↔ target = 0

theorem eventual_terminal_agreement_is_not_lockstep_ordered_simulation :
    ¬ OrderedSimulation (orderedCore countdown) (orderedCore countdown) sameTerminality := by
  intro simulation
  have related : sameTerminality 1 2 := by simp [sameTerminality]
  have successors := simulation.step related
  change List.Forall₂ sameTerminality [0] [1] at successors
  cases successors with
  | cons matched _ =>
      have impossible : (1 : Nat) = 0 := matched.mp rfl
      cases impossible

theorem different_branch_granularities_change_a_finite_frontier :
    (orderedCore countdown).runFrontier 1 [1, 1] = [0, 0] ∧
      (orderedCore countdown).runFrontier 1 [2, 1] = [1, 0] ∧
      (orderedCore countdown).runFrontier 2 [2, 1] = [0, 0] := ⟨rfl, rfl, rfl⟩

/-! ## Asynchronous reservations with unequal duplicate phases -/

open ScheduledFrontier

abbrev delayedCountdown := latencyCore countdown id

def delayedSeeds (id : Fin 3) : LatencyState countdown :=
  match id.val with
  | 0 => (2, 0)
  | 1 => (2, 2)
  | _ => (1, 1)

def delayedClocks (id : Fin 3) : Nat := boundaryClock countdown id 1 (delayedSeeds id)

def delayedReservation : Slots 3 (LatencyState countdown) :=
  reserve delayedClocks (fun owner => [delayedSeeds owner])

theorem duplicate_source_occurrences_have_unequal_derived_clocks :
    (delayedSeeds 0).1 = (delayedSeeds 1).1 ∧ delayedClocks 0 = 1 ∧ delayedClocks 1 = 3 ∧
      delayedClocks 2 = 2 := ⟨rfl, rfl, rfl, rfl⟩

theorem equal_source_state_with_a_different_phase_is_reachable :
    delayedCountdown.Steps (delayedSeeds 1) (delayedSeeds 0) :=
  Relation.ReflTransGen.head (show delayedCountdown.StepRel (2, 2) (2, 1) from rfl)
    (Relation.ReflTransGen.single (show delayedCountdown.StepRel (2, 1) (2, 0) from rfl))

theorem pause_between_unequal_administrative_transitions :
    execute (orderedCore delayedCountdown) (rounds 1 1) delayedReservation 0 = ⟨1, 0, [(1, 1)]⟩ ∧
      execute (orderedCore delayedCountdown) (rounds 1 1) delayedReservation 1 = ⟨1, 2, [(2, 1)]⟩ ∧
      execute (orderedCore delayedCountdown) (rounds 1 1) delayedReservation 2 = ⟨1, 1, [(1, 0)]⟩ :=
  ⟨rfl, rfl, rfl⟩

theorem completed_duplicate_keeps_its_occurrence_slot :
    execute (orderedCore delayedCountdown) (rounds 1 3) delayedReservation 0 = ⟨1, 0, [(1, 1)]⟩ ∧
      execute (orderedCore delayedCountdown) (rounds 1 3) delayedReservation 1 = ⟨3, 0, [(1, 1)]⟩ ∧
      execute (orderedCore delayedCountdown) (rounds 1 3) delayedReservation 2 = ⟨2, 0, [(0, 0)]⟩ :=
  ⟨rfl, rfl, rfl⟩

theorem duplicate_frontier_readback_is_exact :
    (view (execute (orderedCore delayedCountdown) (rounds 1 3) delayedReservation)).map Prod.fst =
      [1, 1, 0] := rfl

theorem duplicate_tags_remain_distinct :
    taggedView (execute (orderedCore delayedCountdown) (rounds 1 3) delayedReservation) =
      [(0, (1, 1)), (1, (1, 1)), (2, (0, 0))] := rfl

theorem administrative_pause_resumes_all_owned_slots :
    execute (orderedCore delayedCountdown) (rounds 1 1 ++ rounds 1 2) delayedReservation =
      execute (orderedCore delayedCountdown) (rounds 1 2)
        (execute (orderedCore delayedCountdown) (rounds 1 1) delayedReservation) :=
  execute_append (orderedCore delayedCountdown) _ _ _

theorem unsafely_running_all_branches_for_the_max_clock_overruns :
    ((orderedCore delayedCountdown).runFrontier 3 (List.ofFn delayedSeeds)).map Prod.fst = [0, 1, 0] ∧
      (view (execute (orderedCore delayedCountdown) (rounds 1 3) delayedReservation)).map Prod.fst =
        [1, 1, 0] := ⟨rfl, rfl⟩

theorem reordered_services_preserve_retained_occurrence_order :
    view (execute (orderedCore delayedCountdown) [(2, 2), (1, 3), (0, 1)] delayedReservation) =
      [(1, 1), (1, 1), (0, 0)] := rfl

theorem administrative_inspections_and_original_occurrences_have_different_costs :
    (latencyMachine countdown id).spent (fun _ => 1) 3 (2, 2) = 3 ∧
      ((latencyMachine countdown id).run 3 (2, 2)).1 = [(2, 1)] ∧
      (coreMachine countdown).spent (fun _ => 1) 1 2 = 1 := ⟨rfl, rfl, rfl⟩

theorem missing_source_edge_cannot_be_repaired_by_an_administrative_phase :
    delayedCountdown.step (0, 19) = none ∧ boundaryClock countdown id 8 (0, 19) = 0 ∧
      (latencyMachine countdown id).run 1 (0, 19) = ([], .stuck (0, 19)) := ⟨rfl, rfl, rfl⟩

/-! ## Actual CEK and Krivine source-model instances -/

abbrev delayedCek := latencyCore cekCore (fun _ => 2)

def cekSeeds (id : Fin 2) : LatencyState cekCore :=
  (cekCore.load identityTerm, if id = 0 then 0 else 2)

def cekBoundaryClocks (id : Fin 2) : Nat :=
  boundaryClock cekCore (fun _ => 2) 3 (cekSeeds id)

def cekBoundaryReservation : Slots 2 (LatencyState cekCore) :=
  reserve cekBoundaryClocks (fun id => [cekSeeds id])

theorem actual_cek_prefix_derives_unequal_clocks :
    cekBoundaryClocks 0 = 7 ∧ cekBoundaryClocks 1 = 9 := ⟨rfl, rfl⟩

theorem actual_cek_prefix_keeps_duplicate_pending_contexts :
    (view (execute (orderedCore delayedCek) (rounds 1 9) cekBoundaryReservation)).map Prod.fst =
      [cekIdentityResidual, cekIdentityResidual] := rfl

theorem completed_cek_reservations_are_pending_language_computations :
    (execute (orderedCore delayedCek) (rounds 1 9) cekBoundaryReservation 0).remaining = 0 ∧
      (execute (orderedCore delayedCek) (rounds 1 9) cekBoundaryReservation 1).remaining = 0 ∧
      cekAnswer cekIdentityResidual = none := ⟨rfl, rfl, rfl⟩

theorem actual_cek_reserved_prefix_has_the_same_computational_occurrences :
    ((latencyMachine cekCore (fun _ => 2)).run 7 (cekSeeds 0)).1 = cekIdentityPrefix ∧
      ((latencyMachine cekCore (fun _ => 2)).run 9 (cekSeeds 1)).1 = cekIdentityPrefix := ⟨rfl, rfl⟩

theorem actual_cek_observation_does_not_invent_an_answer_at_a_prefix :
    (view (execute (orderedCore delayedCek) (rounds 1 9) cekBoundaryReservation)).filterMap
      (fun state => cekAnswer state.1) = [] := rfl

theorem actual_krivine_latency_reaches_the_existing_answer_observer :
    boundaryClock krivineCore (fun _ => 1) 3 (krivineCore.load identityTerm, 1) = 6 ∧
      krivineAnswer (walk (latencyCore krivineCore (fun _ => 1)) 6
        (krivineCore.load identityTerm, 1)).1 = some (.lit 7) := ⟨rfl, rfl⟩

theorem inserted_administration_does_not_force_a_divergent_cek_source_to_terminate (fuel : Nat) :
    ∃ schedule : List (Command 1),
      (view (execute (orderedCore (latencyCore cekCore (fun _ => 1))) schedule
        (reserve (fun _ => boundaryClock cekCore (fun _ => 1) fuel (omegaCycle0, 1))
          (fun _ => [(omegaCycle0, 1)])))).map Prod.fst =
        (orderedCore cekCore).runFrontier fuel [omegaCycle0] := by
  have finiteObservation := scheduled_latency_realization cekCore (fun _ => 1) fuel
    (fun _ : Fin 1 => (omegaCycle0, 1))
  exact finiteObservation

end Mettapedia.Machines.ProductiveCoreControls
