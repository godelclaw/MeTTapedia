import Mettapedia.GSLT.Distinction.SimulationComposition
import Mettapedia.GSLT.Distinction.ProductiveBlocksControls

/-!
# Controls for composing machine implementations

`FiniteBlocks` gives a size-dependent implementation with no uniform local
instruction bound. Its local proofs compose, preserve duplicate publications
and retain the exact suffix across a pause. The existing forward-only controls
separately show why completion reflection cannot be inferred from preservation.

* **The product, not the sum** (`product_holds`, `sum_bound_fails`,
  `product_bound_tight`).  A source publishing in one transition, a middle
  machine taking three, and a target taking three for each middle transition:
  the stages cost three each, the composite costs nine, and no bound below nine
  holds, in particular not the sum six.  The composite carries the final
  observation (`composite_final`), and the two stages, which move their targets
  on every transition, compose as stages with reflected completion
  (`chain`, `chain_reflected`).
* **A middle stage that stutters silently** (`spin_done`,
  `stutter_composite`, `stutter_not_reflected`, `stutter_no_progress`).  A
  silently looping middle machine is matched by a finishing target without any
  target transition.  Both stages and their composite are forward
  simulations, yet the target finishes while the source never completes.  The
  first stage has progress; the stuttering stage has none at any cost and any
  rank, and the composite has no backward simulation at any cost.
* **A source-only stage** (`halfway_forward`, `source_only_composite`,
  `source_only_not_reflected`, `halfway_no_backward`).  A source that publishes
  and then is stuck is simulated by a target that publishes and finishes; the
  second stage is the identity, with both laws.  The composite does not reflect
  completion, and the first stage has no backward simulation at any cost.
* **Reflection without a backward simulation** (`checker_progress`,
  `checker_interpreter_reflected`, `interpreter_progress`,
  `check_interpret_final_forward`).  The checker and the three-step
  interpreter of `ProductiveBlocksControls`: the forward simulation moves the
  interpreter on every checker transition, so it reflects completion by
  itself; the interpreter's two administrative transitions stutter in the
  checker under a decreasing rank.  Final observations coincide under the
  forward simulation alone.
* **Retained services** (`HandlerControls`). An independently executed service
  realizes an atomic callback with reflected completion. A single partial
  caller covers successful service execution, stuckness, faults and genuine
  divergence. A spurious completed target and a wrong callback environment
  fail the respective progress and service-execution contracts.
* **Middle states are data** (`two_middles`): one composite pair is reached
  through different middle states.
* **Stage laws** (`checker_chain_assoc`, `checker_roundtrip_not_identity`).
  Reassociation and identity insertion preserve a three-stage chain. A
  checker/interpreter round trip preserves final observations but retains its
  cost and is not the identity stage.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks.CompositionControls

open Mettapedia.GSLT.Dynamics.OrderedDemand (Status Observation)
open Mettapedia.GSLT.Distinction.SpanTransport (compose)
open Mettapedia.GSLT.Distinction.DependentComposition (Path)

/-! ## The product, not the sum -/

/-- One publication, then finishing. -/
def quick : Machine Bool ℕ Unit Empty where
  step
    | false => some (.publish [1] true)
    | true => some (.finish ())

/-- Two administrative transitions, then the same publication. -/
def medium : Machine ℕ ℕ Unit Empty where
  step
    | 0 => some (.silent 1)
    | 1 => some (.silent 2)
    | 2 => some (.publish [1] 3)
    | 3 => some (.finish ())
    | _ => none

/-- Eight administrative transitions, then the same publication. -/
def slow : Machine ℕ ℕ Unit Empty where
  step state :=
    if state < 8 then some (.silent (state + 1))
    else if state = 8 then some (.publish [1] 9)
    else if state = 9 then some (.finish ())
    else none

def quickMedium : Bool → ℕ → Prop
  | false, state => state = 0
  | true, state => state = 3

def mediumSlow (state state' : ℕ) : Prop := state ≤ 3 ∧ state' = 3 * state

theorem stage_one : CostSimulation quick medium quickMedium 3 where
  silent := by
    intro state _ _ _ stepped
    cases state <;> simp [quick] at stepped
  publish := by
    intro state state' events next relatedStates stepped
    cases state with
    | false =>
        simp only [quick, Option.some.injEq, Transition.publish.injEq] at stepped
        obtain ⟨rfl, rfl⟩ := stepped
        change state' = 0 at relatedStates
        subst relatedStates
        exact ⟨3, le_rfl, 3, rfl, rfl⟩
    | true => simp [quick] at stepped
  finish := by
    intro state state' verdict relatedStates stepped
    cases state with
    | false => simp [quick] at stepped
    | true =>
        change state' = 3 at relatedStates
        subst relatedStates
        exact ⟨1, by omega, rfl⟩
  fail := by
    intro state _ _ _ stepped
    cases state <;> simp [quick] at stepped
  call := by
    intro state _ _ _ _ stepped
    cases state <;> simp [quick] at stepped

theorem stage_two : CostSimulation medium slow mediumSlow 3 where
  silent := by
    rintro state _ next ⟨bounded, rfl⟩ stepped
    interval_cases state
    · simp only [medium, Option.some.injEq, Transition.silent.injEq] at stepped
      subst stepped
      exact ⟨3, le_rfl, 3, rfl, by omega, rfl⟩
    · simp only [medium, Option.some.injEq, Transition.silent.injEq] at stepped
      subst stepped
      exact ⟨3, le_rfl, 6, rfl, by omega, rfl⟩
    · simp [medium] at stepped
    · simp [medium] at stepped
  publish := by
    rintro state _ events next ⟨bounded, rfl⟩ stepped
    interval_cases state
    · simp [medium] at stepped
    · simp [medium] at stepped
    · simp only [medium, Option.some.injEq, Transition.publish.injEq] at stepped
      obtain ⟨rfl, rfl⟩ := stepped
      exact ⟨3, le_rfl, 9, rfl, by omega, rfl⟩
    · simp [medium] at stepped
  finish := by
    rintro state _ verdict ⟨bounded, rfl⟩ stepped
    interval_cases state
    · simp [medium] at stepped
    · simp [medium] at stepped
    · simp [medium] at stepped
    · exact ⟨1, by omega, rfl⟩
  fail := by
    rintro state _ events ⟨bounded, rfl⟩ stepped
    interval_cases state <;> simp [medium] at stepped
  call := by
    rintro state _ request saved ⟨bounded, rfl⟩ stepped
    interval_cases state <;> simp [medium] at stepped

/-- **The composite holds at the product of the costs.** -/
theorem product_holds : CostSimulation quick slow (compose quickMedium mediumSlow) 9 :=
  stage_one.comp stage_two

theorem slow_quiet (k : ℕ) (small : k ≤ 8) : (slow.run k 0).1 = [] := by
  interval_cases k <;> rfl

/-- **No bound below the product holds**: the target publishes only after nine
transitions. -/
theorem product_bound_tight (cost : ℕ) (small : cost < 9) :
    ¬ CostSimulation quick slow (compose quickMedium mediumSlow) cost := by
  intro simulation
  obtain ⟨k, bound, _, ran, _⟩ :=
    simulation.publish (state := false) (state' := 0) ⟨0, rfl, by omega, rfl⟩ rfl
  have quiet := slow_quiet k (by omega)
  rw [ran] at quiet
  cases quiet

/-- **The naive bound, the sum of the costs, fails.** -/
theorem sum_bound_fails : ¬ CostSimulation quick slow (compose quickMedium mediumSlow) (3 + 3) :=
  product_bound_tight (3 + 3) (by omega)

/-- The composite carries the final observation. -/
theorem composite_final :
    quick.observe 2 false = slow.observe 10 0 ∧ quick.observe 2 false = ⟨[1], .finished ()⟩ :=
  ⟨stage_one.comp_final_eq stage_two (state := false) (state'' := 0) ⟨0, rfl, by omega, rfl⟩
    trivial trivial, rfl⟩

theorem quick_progress : Progress quick medium quickMedium 3 (fun _ => 0) :=
  Progress.of_positive _
    (by
      intro state _ _
      cases state <;> simp [quick])
    (by
      intro state _ _ _ stepped
      cases state <;> simp [quick] at stepped)
    (by
      intro state state' events next relatedStates stepped
      cases state with
      | false =>
          simp only [quick, Option.some.injEq, Transition.publish.injEq] at stepped
          obtain ⟨rfl, rfl⟩ := stepped
          change state' = 0 at relatedStates
          subst relatedStates
          exact ⟨3, le_rfl, by omega, 3, rfl, rfl⟩
      | true => simp [quick] at stepped)

theorem medium_progress : Progress medium slow mediumSlow 3 (fun _ => 0) :=
  Progress.of_positive _
    (by
      rintro state _ ⟨bounded, rfl⟩
      interval_cases state <;> simp [medium])
    (by
      rintro state _ next ⟨bounded, rfl⟩ stepped
      interval_cases state
      · simp only [medium, Option.some.injEq, Transition.silent.injEq] at stepped
        subst stepped
        exact ⟨3, le_rfl, by omega, 3, rfl, by omega, rfl⟩
      · simp only [medium, Option.some.injEq, Transition.silent.injEq] at stepped
        subst stepped
        exact ⟨3, le_rfl, by omega, 6, rfl, by omega, rfl⟩
      · simp [medium] at stepped
      · simp [medium] at stepped)
    (by
      rintro state _ events next ⟨bounded, rfl⟩ stepped
      interval_cases state
      · simp [medium] at stepped
      · simp [medium] at stepped
      · simp only [medium, Option.some.injEq, Transition.publish.injEq] at stepped
        obtain ⟨rfl, rfl⟩ := stepped
        exact ⟨3, le_rfl, by omega, 9, rfl, by omega, rfl⟩
      · simp [medium] at stepped)

/-- **The two stages as a chain**: composite relation, cost nine, and
reflected completion. -/
def chain : Stage quick slow :=
  (Stage.ofProgress quickMedium 3 stage_one quick_progress).comp
    (Stage.ofProgress mediumSlow 3 stage_two medium_progress)

theorem chain_cost : chain.cost = 9 :=
  rfl

theorem chain_reflected (fuel' : ℕ) (final : (slow.observe fuel' 0).status.Final) :
    ∃ fuel, quick.observe fuel false = slow.observe fuel' 0 :=
  chain.reflected (state := false) (state' := 0) ⟨0, rfl, by omega, rfl⟩ final

/-! ## A middle stage that stutters silently -/

/-- A machine that only steps silently. -/
def spin : Machine Unit ℕ Unit Empty where
  step _ := some (.silent ())

/-- A machine that finishes at once. -/
def done : Machine Unit ℕ Unit Empty where
  step _ := some (.finish ())

def anyPair : Unit → Unit → Prop := fun _ _ => True

/-- The first stage moves its target on every transition. -/
theorem spin_spin : CostSimulation spin spin anyPair 1 where
  silent := by
    intro _ _ _ _ _
    exact ⟨1, le_rfl, (), rfl, trivial⟩
  publish := by
    intro _ _ _ _ _ stepped
    cases stepped
  finish := by
    intro _ _ _ _ stepped
    cases stepped
  fail := by
    intro _ _ _ _ stepped
    cases stepped
  call := by
    intro _ _ _ _ _ stepped
    cases stepped

/-- **The stuttering stage**: every silent transition of the middle machine is
matched by a finishing target without a transition. -/
theorem spin_done : CostSimulation spin done anyPair 0 where
  silent := by
    intro _ _ _ _ _
    exact ⟨0, le_rfl, (), rfl, trivial⟩
  publish := by
    intro _ _ _ _ _ stepped
    cases stepped
  finish := by
    intro _ _ _ _ stepped
    cases stepped
  fail := by
    intro _ _ _ _ stepped
    cases stepped
  call := by
    intro _ _ _ _ _ stepped
    cases stepped

/-- The composite of the two stages is a forward simulation. -/
theorem stutter_composite : CostSimulation spin done (compose anyPair anyPair) 0 :=
  spin_spin.comp spin_done

theorem spin_spin_progress : Progress spin spin anyPair 1 (fun _ => 0) :=
  Progress.of_positive _ (fun _ stepped => by cases stepped)
    (fun _ _ => ⟨1, le_rfl, by omega, (), rfl, trivial⟩)
    (fun _ stepped => by cases stepped)

/-- **The stuttering stage has no progress**, at any cost and any rank. -/
theorem stutter_no_progress (cost : ℕ) (rank : Unit → ℕ) : ¬ Progress spin done anyPair cost rank := by
  intro progress
  obtain ⟨k, _, _, ran, _, decreases⟩ :=
    progress.silent (state := ()) (state' := ()) (next := ()) trivial rfl
  cases k with
  | zero => exact lt_irrefl _ (decreases rfl)
  | succ k =>
      have finished : done.run (k + 1) () = ([], .finished ()) := rfl
      rw [finished] at ran
      cases ran

theorem spin_incomplete (fuel : ℕ) : spin.observe fuel () = ⟨[], .incomplete⟩ :=
  spin.silent_region_incomplete (fun _ => True) (fun _ _ => ⟨(), rfl, trivial⟩) fuel () trivial

/-- **The composite does not reflect completion**: the target finishes while the
source never completes. -/
theorem stutter_not_reflected : ¬ ReflectsCompletion spin done (compose anyPair anyPair) := by
  intro reflects
  obtain ⟨fuel, reached⟩ := reflects (state := ()) (state' := ()) ⟨(), trivial, trivial⟩ 1 trivial
  rw [spin_incomplete] at reached
  cases reached

/-- Nor does the composite have a backward simulation, at any cost. -/
theorem stutter_no_backward (back : ℕ) :
    ¬ CostSimulation done spin (fun state'' state => compose anyPair anyPair state state'') back :=
  fun backward => stutter_not_reflected (reflectsCompletion_of_backward backward)

/-! ## A source-only stage -/

/-- Publishes, then is stuck. -/
def halfway : Machine Bool ℕ Unit Empty where
  step
    | false => some (.publish [1] true)
    | true => none

/-- **The source-only stage**: every transition of `halfway` is matched by
`quick`. -/
theorem halfway_forward : CostSimulation halfway quick Eq 1 where
  silent := by
    intro state _ _ _ stepped
    cases state <;> simp [halfway] at stepped
  publish := by
    rintro state _ events next rfl stepped
    cases state with
    | false =>
        simp only [halfway, Option.some.injEq, Transition.publish.injEq] at stepped
        obtain ⟨rfl, rfl⟩ := stepped
        exact ⟨1, le_rfl, true, rfl, rfl⟩
    | true => simp [halfway] at stepped
  finish := by
    intro state _ _ _ stepped
    cases state <;> simp [halfway] at stepped
  fail := by
    intro state _ _ _ stepped
    cases state <;> simp [halfway] at stepped
  call := by
    intro state _ _ _ _ stepped
    cases state <;> simp [halfway] at stepped

/-- The composite with the identity stage, which has both laws. -/
theorem source_only_composite : CostSimulation halfway quick (compose Eq Eq) 1 :=
  halfway_forward.comp (CostSimulation.refl quick)

theorem halfway_incomplete (fuel : ℕ) : (halfway.observe fuel false).status = .incomplete := by
  rcases fuel with _ | _ | fuel <;> rfl

/-- **The composite does not reflect completion.** -/
theorem source_only_not_reflected : ¬ ReflectsCompletion halfway quick (compose Eq Eq) := by
  intro reflects
  obtain ⟨fuel, reached⟩ := reflects (state := false) (state' := false) ⟨false, rfl, rfl⟩ 2 trivial
  have status := congrArg Observation.status reached
  rw [halfway_incomplete] at status
  cases status

/-- **The first stage has no backward simulation**, at any cost. -/
theorem halfway_no_backward (back : ℕ) :
    ¬ CostSimulation quick halfway (fun state' state => state = state') back := by
  intro backward
  obtain ⟨fuel, reached⟩ :=
    reflectsCompletion_of_backward backward (state := false) (state' := false) rfl 2 trivial
  have status := congrArg Observation.status reached
  rw [halfway_incomplete] at status
  cases status

/-! ## Reflection without a backward simulation -/

open Controls (checker interpreter related)

/-- The forward simulation moves the interpreter on every checker transition. -/
theorem checker_progress : Progress checker interpreter related 3 (fun _ => 0) :=
  Progress.of_positive _
    (by
      intro state _ _
      cases state <;> simp [checker])
    (by
      intro state _ _ _ stepped
      cases state <;> simp [checker] at stepped)
    (by
      intro state state' events next relatedStates stepped
      cases state with
      | start =>
          simp only [checker, Option.some.injEq, Transition.publish.injEq] at stepped
          obtain ⟨rfl, rfl⟩ := stepped
          cases state' with
          | start => exact ⟨3, le_rfl, by omega, .emitted, rfl, trivial⟩
          | first => exact ⟨2, by omega, by omega, .emitted, rfl, trivial⟩
          | second => exact ⟨1, by omega, by omega, .emitted, rfl, trivial⟩
          | emitted => exact relatedStates.elim
      | verdict => simp [checker] at stepped)

/-- **Completion is reflected by the forward simulation alone.** -/
theorem checker_interpreter_reflected : ReflectsCompletion checker interpreter related :=
  Controls.forward.reflectsCompletion checker_progress

/-- The rank of the interpreter's administrative states. -/
def interpreterRank : Controls.Interpret → ℕ
  | .start => 2
  | .first => 1
  | _ => 0

/-- **Stuttering under a decreasing rank**: the interpreter's two administrative
transitions are matched without a checker transition. -/
theorem interpreter_progress :
    Progress interpreter checker (fun state' state => related state state') 1 interpreterRank where
  stuck := by
    intro state' _ _ blocked
    cases state' <;> simp [interpreter] at blocked
  silent := by
    intro state' state next relatedStates stepped
    cases state' with
    | start =>
        simp only [interpreter, Option.some.injEq, Transition.silent.injEq] at stepped
        subst stepped
        cases state <;> simp only [related] at relatedStates
        exact ⟨0, by omega, .start, rfl, trivial, fun _ => by decide⟩
    | first =>
        simp only [interpreter, Option.some.injEq, Transition.silent.injEq] at stepped
        subst stepped
        cases state <;> simp only [related] at relatedStates
        exact ⟨0, by omega, .start, rfl, trivial, fun _ => by decide⟩
    | second => simp [interpreter] at stepped
    | emitted => simp [interpreter] at stepped
  publish := by
    intro state' state events next relatedStates stepped
    cases state' with
    | second =>
        simp only [interpreter, Option.some.injEq, Transition.publish.injEq] at stepped
        obtain ⟨rfl, rfl⟩ := stepped
        cases state <;> simp only [related] at relatedStates
        exact ⟨1, le_rfl, .verdict, rfl, trivial, fun zero => absurd zero (by omega)⟩
    | start => simp [interpreter] at stepped
    | first => simp [interpreter] at stepped
    | emitted => simp [interpreter] at stepped

theorem interpreter_checker_reflected :
    ReflectsCompletion interpreter checker (fun state' state => related state state') :=
  Controls.backward.reflectsCompletion interpreter_progress

/-- Final observations coincide under the forward simulation alone. -/
theorem check_interpret_final_forward : checker.observe 2 .start = interpreter.observe 4 .start :=
  Controls.forward.final_eq_forward (state := .start) (state' := .start) trivial trivial trivial

/-! ## Middle states are data -/

/-- **One composite pair, two middle states**: the checker's start reaches the
checker's start through the interpreter's start and through its first
administrative state. -/
theorem two_middles : ∃ first second : Path related (fun state' state => related state state')
    Controls.Check.start Controls.Check.start, first.1 ≠ second.1 :=
  ⟨⟨.start, trivial, trivial⟩, ⟨.first, trivial, trivial⟩, by decide⟩

/-! ## Identity and composition of checked stages -/

def checkerToInterpreter : Stage checker interpreter :=
  .ofProgress related 3 Controls.forward checker_progress

def interpreterToChecker : Stage interpreter checker :=
  .ofProgress (fun state' state => related state state') 1 Controls.backward interpreter_progress

theorem checker_chain_assoc :
    (checkerToInterpreter.comp interpreterToChecker).comp checkerToInterpreter =
      checkerToInterpreter.comp (interpreterToChecker.comp checkerToInterpreter) :=
  Stage.comp_assoc _ _ _

theorem checker_chain_units :
    ((Stage.refl checker).comp checkerToInterpreter).comp (Stage.refl interpreter) =
      checkerToInterpreter := by
  simp only [Stage.refl_comp, Stage.comp_refl]

/-- Returning to the checker preserves the final event and verdict. -/
theorem checker_roundtrip_observation :
    checker.observe 2 .start = checker.observe 6 .start :=
  (checkerToInterpreter.comp interpreterToChecker).final_eq
    (state := .start) (state' := .start) ⟨.start, trivial, trivial⟩ trivial trivial

/-- Observational agreement does not erase the intermediate execution cost. -/
theorem checker_roundtrip_not_identity :
    checkerToInterpreter.comp interpreterToChecker ≠ Stage.refl checker := by
  intro same
  have costs := congrArg Stage.cost same
  change 1 * 3 = 1 at costs
  omega

theorem checker_chain_cost :
    ((checkerToInterpreter.comp interpreterToChecker).comp checkerToInterpreter).cost = 9 :=
  rfl

theorem relabeled_chain_cost : (chain.relabel (fun value => value + 100) id id).cost = 9 :=
  rfl

/-- The same translation can be applied before or after composing the stages. -/
theorem relabeled_chain_composes :
    (checkerToInterpreter.comp interpreterToChecker).relabel (fun value => (true, value)) id id =
      (checkerToInterpreter.relabel (fun value => (true, value)) id id).comp
        (interpreterToChecker.relabel (fun value => (true, value)) id id) :=
  Stage.relabel_comp _ _ _ _ _

/-- The reflected final observation is transported through the existing chain. -/
theorem relabeled_chain_reflected (fuel' : ℕ)
    (final : ((slow.relabel (fun value => value + 100) id id).observe fuel' 0).status.Final) :
    ∃ fuel, (quick.relabel (fun value => value + 100) id id).observe fuel false =
      (slow.relabel (fun value => value + 100) id id).observe fuel' 0 :=
  (chain.relabel (fun value => value + 100) id id).reflected
    (state := false) (state' := 0) ⟨0, rfl, by omega, rfl⟩ final

/-! ## Machine-category consumers -/

namespace MachineCategory

open _root_.CategoryTheory

def quickObject : ObservedMachine ℕ Unit Empty := .of quick
def mediumObject : ObservedMachine ℕ Unit Empty := .of medium
def slowObject : ObservedMachine ℕ Unit Empty := .of slow

def first : quickObject ⟶ mediumObject :=
  Stage.ofProgress quickMedium 3 stage_one quick_progress

def second : mediumObject ⟶ slowObject :=
  Stage.ofProgress mediumSlow 3 stage_two medium_progress

/-- The categorical composite retains the actual fused execution boundary. -/
theorem composite_observation :
    quickObject.machine.observe 2 false = slowObject.machine.observe 10 (0 : ℕ) :=
  (first ≫ second).final_eq (state := false) (state' := (0 : ℕ))
    ⟨(0 : ℕ), rfl, by omega, rfl⟩ trivial trivial

/-- Three target steps per source step at each stage compose to nine. -/
theorem composite_cost : (first ≫ second).cost = 9 := rfl

/-- Observation agreement does not make a costed round trip an identity. -/
theorem roundtrip_not_identity :
    CategoryTheory.CategoryStruct.comp
        (X := ObservedMachine.of checker) (Y := ObservedMachine.of interpreter)
        (Z := ObservedMachine.of checker) checkerToInterpreter interpreterToChecker ≠
      𝟙 (ObservedMachine.of checker) :=
  checker_roundtrip_not_identity

/-- Relabeling exposes the new event through the existing machine runner. -/
theorem relabel_publication :
    ((ObservedMachine.relabelFunctor Nat.succ id id).obj quickObject).machine.observe
        2 false = ⟨[2], .finished ()⟩ := rfl

end MachineCategory

/-! ## Completion reflection does not identify stuckness with divergence -/

def stuckSpin : Controls.Wedge → Controls.Wedge → Prop :=
  fun state state' => state = .wedged ∧ state' = .spinning

/-- This deliberately weak counterexample matches every existing source
transition; the related source has none. -/
theorem stuck_spin_forward : CostSimulation Controls.wedgeMachine Controls.wedgeMachine stuckSpin 0 where
  silent := by
    rintro state state' next ⟨rfl, rfl⟩ stepped
    cases stepped
  publish := by
    rintro state state' events next ⟨rfl, rfl⟩ stepped
    cases stepped
  finish := by
    rintro state state' verdict ⟨rfl, rfl⟩ stepped
    cases stepped
  fail := by
    rintro state state' events ⟨rfl, rfl⟩ stepped
    cases stepped
  call := by
    rintro state state' request saved ⟨rfl, rfl⟩ stepped
    cases stepped

def stuckSpinStage : Stage Controls.wedgeMachine Controls.wedgeMachine where
  related := stuckSpin
  cost := 0
  forward := stuck_spin_forward
  reflects := by
    rintro state state' ⟨rfl, rfl⟩ fuel final
    rw [(Controls.wedge_observations fuel).2.1] at final
    exact final.elim

theorem stage_can_relate_stuckness_to_divergence :
    stuckSpinStage.related .wedged .spinning ∧
      ¬ Controls.wedgeMachine.DivergesWithin .wedged ∧
      Controls.wedgeMachine.DivergesWithin .spinning :=
  ⟨⟨rfl, rfl⟩, Controls.wedged_does_not_diverge, Controls.spinning_diverges⟩

/-- The new endpoint obligation rejects that stage at every proposed bound. -/
theorem stuck_spin_does_not_match_stuck (cost : Nat) :
    ¬ MatchesStuck Controls.wedgeMachine Controls.wedgeMachine stuckSpin cost := by
  intro matchedStuck
  obtain ⟨count, _, stopped, ran, _⟩ := matchedStuck ⟨rfl, rfl⟩ rfl
  exact Controls.spinning_diverges.not_stuck Controls.wedgeMachine count stopped
    (congrArg Prod.snd ran)

/-- The identity retains actual stuckness and its endpoint through the
stronger relation, including after composition. -/
theorem stuck_identity_composes :
    MatchesStuck Controls.wedgeMachine Controls.wedgeMachine (compose Eq Eq) 1 := by
  exact (MatchesStuck.refl Controls.wedgeMachine).comp
    (CostSimulation.refl Controls.wedgeMachine) (MatchesStuck.refl Controls.wedgeMachine)

theorem stuck_identity_outcome :
    ∃ count ≤ 1, (Controls.wedgeMachine.run count .wedged).1 = [] ∧
      OutcomeRel Eq (.stuck .wedged) (Controls.wedgeMachine.run count .wedged).2 :=
  (CostSimulation.refl Controls.wedgeMachine).run_related_all
    (MatchesStuck.refl Controls.wedgeMachine) 1 (state := .wedged) rfl

namespace CallbackControls

open Controls

theorem same_callback_preserves_all_outcomes
    (environment : Environment String LineEvent Nat Unit) (fuel : Nat) (state : Call) :
    ∃ count ≤ fuel,
      ((caller.close protocol environment).run count state).1 =
        ((caller.close protocol environment).run fuel state).1 ∧
      OutcomeRel Eq ((caller.close protocol environment).run fuel state).2
        ((caller.close protocol environment).run count state).2 := by
  have simulation := (CostSimulation.refl caller).closed protocol protocol environment rfl rfl
    (by intro saved saved' same reply; exact congrArg (fun s => protocol.resume s reply) same)
  simpa only [Nat.one_mul] using simulation.run_related_all
    ((MatchesStuck.refl caller).closed protocol protocol environment) fuel rfl

/-- Discarding an actual cancellation changes which answer is emitted. -/
def ignoresCancellation : Callback Call LineEvent String Nat Unit :=
  { protocol with resume := fun saved _ => saved }

theorem same_events_do_not_license_wrong_resumption :
    protocol.callEvent = ignoresCancellation.callEvent ∧
      protocol.replyEvent = ignoresCancellation.replyEvent ∧
      protocol.resume .after .cancelled ≠ ignoresCancellation.resume .after .cancelled := by
  exact ⟨rfl, rfl, by decide⟩

theorem ignored_cancellation_invents_an_answer :
    ((caller.close protocol cancelling).run 3 .start).1 =
      [.effect "lookup", .effect "cancelled"] ∧
    ((caller.close ignoresCancellation cancelling).run 3 .start).1 =
      [.effect "lookup", .effect "cancelled", .answer 1] := ⟨rfl, rfl⟩

theorem mismatched_environments_change_effect_history :
    ((caller.close protocol reentrant).run 3 .start).1 ≠
      ((caller.close protocol plain).run 3 .start).1 := by decide

theorem pause_after_call_does_not_repeat_its_effect :
    (caller.close protocol reentrant).run 1 .start =
      ([.effect "lookup", .effect "reentrant", .effect "returned"], .exhausted .after) ∧
    (caller.close protocol reentrant).run 2 .after = ([.answer 1], .finished ()) ∧
    (caller.close protocol reentrant).run 3 .start =
      ([.effect "lookup", .effect "reentrant", .effect "returned", .answer 1], .finished ()) :=
  ⟨rfl, rfl, rfl⟩

end CallbackControls

/-! ## Refinement through retained services -/

namespace HandlerControls

open Controls

/-- The service is independently defined and computes the environment in
three transitions. Entering it accounts for the fourth transition. -/
def callbackStage : Stage (caller.close protocol reentrant) retainedCaller :=
  Stage.ofHandler caller protocol retainedService (fun _ => 0) reentrant 3
    retained_service_computes_environment

theorem callback_reflects_completed_runs (state : Call) (fuel : Nat)
    (final : (retainedCaller.observe fuel (.running state)).status.Final) :
    ∃ count, (caller.close protocol reentrant).observe count state =
      retainedCaller.observe fuel (.running state) :=
  callbackStage.reflects rfl fuel final

theorem callback_complete_observation :
    (caller.close protocol reentrant).observe 3 .start =
      retainedCaller.observe 6 (.running .start) := by
  exact callbackStage.forward.final_eq_forward rfl (by trivial) (by trivial)

/-- Finishing the target after a source's absent transition cannot satisfy
progress, regardless of its cost or the proposed administrative rank. -/
theorem completing_after_stuck_is_not_progress (cost : Nat) (rank : Bool → Nat) :
    ¬ Progress halfway quick Eq cost rank := by
  intro progress
  exact progress.stuck.not_final (state := true) rfl rfl 1 (by trivial)

/-- One caller exercises service invocation, a stuck endpoint, an uncaught
fault and a genuine infinite computation under the same representation. -/
def partialCaller : Machine Nat LineEvent Unit String where
  step
    | 0 => some (.call "lookup" 1)
    | 1 => some (.publish [.answer 1] 2)
    | 3 => some (.fail [.effect "fault"])
    | 4 => some (.silent 4)
    | 5 => some (.finish ())
    | _ => none

def partialProtocol : Callback Nat LineEvent String Nat Unit where
  callEvent := protocol.callEvent
  replyEvent := protocol.replyEvent
  resume saved _ := saved

def partialRetained := partialCaller.handle partialProtocol retainedService (fun _ => 0)

def partialStage : Stage (partialCaller.close partialProtocol reentrant) partialRetained :=
  Stage.ofHandler partialCaller partialProtocol retainedService (fun _ => 0) reentrant 3
    retained_service_computes_environment

theorem service_keeps_stuck_endpoint :
    (partialCaller.close partialProtocol reentrant).run 3 0 =
      ([.effect "lookup", .effect "reentrant", .effect "returned", .answer 1], .stuck 2) ∧
    partialRetained.run 6 (.running 0) =
      ([.effect "lookup", .effect "reentrant", .effect "returned", .answer 1], .stuck (.running 2)) :=
  ⟨rfl, rfl⟩

theorem service_keeps_fault :
    (partialCaller.close partialProtocol reentrant).run 1 3 =
      ([.effect "fault"], .faulted) ∧
    partialRetained.run 1 (.running 3) = ([.effect "fault"], .faulted) := ⟨rfl, rfl⟩

theorem partial_caller_diverges (fuel : Nat) :
    (partialCaller.close partialProtocol reentrant).run fuel 4 = ([], .exhausted 4) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simpa only [Machine.run, Machine.close, partialCaller, Option.map_some] using ih

/-- Bounded services do not make an infinite caller terminate. Completion
reflection supplies this result for every budget of the retained machine. -/
theorem service_does_not_complete_diverging_caller (fuel : Nat) :
    ¬ (partialRetained.observe fuel (.running 4)).status.Final := by
  apply partialStage.reflects.never_completes (state := 4) rfl _ fuel
  intro count
  simp only [Machine.observe, partial_caller_diverges, Outcome.status, Status.Final, not_false_eq_true]

theorem no_completion_after_stuck (fuel : Nat) :
    ¬ (partialRetained.observe fuel (.running 2)).status.Final :=
  MatchesStuck.not_final
    (partialCaller.close_handle_matchesStuck partialProtocol (fun _ => 0) retainedService reentrant 3)
    (state := 2) rfl rfl fuel

/-- The callback boundary may be summarized only after proving the service's
actual events and reply. An environment that omits its effect fails that test. -/
theorem service_cannot_earn_wrong_environment :
    ¬ (∀ request : String, retainedService.run 3 0 =
      ((plain request).1, .finished (plain request).2)) := by
  intro claimed
  have wrong := claimed "lookup"
  cases wrong

end HandlerControls

end Mettapedia.GSLT.Distinction.ProductiveBlocks.CompositionControls

namespace Mettapedia.GSLT.Distinction.ProductiveBlocks.CompositionControls.FiniteBlocks

open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- One logical publication keeps both equal occurrences. -/
def logical : Machine Nat Nat Unit Empty where
  step
    | 0 => some (.finish ())
    | n + 1 => some (.publish [n + 1, n + 1] n)

/-- The second component counts pending internal work before the next logical
publication. The next operation starts with its own, size-dependent work. -/
def backend : Machine (Nat × Nat) Nat Unit Empty where
  step
    | (n, debt + 1) => some (.silent (n, debt))
    | (0, 0) => some (.finish ())
    | (n + 1, 0) => some (.publish [n + 1, n + 1] (n, n))

def related (n : Nat) (state : Nat × Nat) : Prop :=
  n = state.1 ∧ state.2 ≤ n

theorem debt_before_boundary (n debt count : Nat) (bound : count ≤ debt) :
    backend.run count (n, debt) = ([], .exhausted (n, debt - count)) := by
  induction count generalizing debt with
  | zero => rfl
  | succ count ih =>
      cases debt with
      | zero => omega
      | succ debt =>
          simpa only [Machine.run, backend, Nat.succ_sub_succ_eq_sub] using
            ih debt (Nat.le_of_succ_le_succ bound)

theorem discharge_debt (n debt fuel : Nat) :
    backend.run (debt + fuel) (n, debt) = backend.run fuel (n, 0) := by
  induction debt with
  | zero => simp only [Nat.zero_add]
  | succ debt ih =>
      rw [Nat.succ_add]
      simpa only [Machine.run, backend] using ih

theorem one_forth {n : Nat} {state : Nat × Nat} (retained : related n state) :
    ∃ count, (backend.run count state).1 = (logical.run 1 n).1 ∧
      OutcomeRel related (logical.run 1 n).2 (backend.run count state).2 := by
  rcases state with ⟨n', debt⟩
  rcases retained with ⟨rfl, _⟩
  refine ⟨debt + 1, ?_, ?_⟩
  · rw [discharge_debt]
    cases n <;> rfl
  · rw [discharge_debt]
    cases n with
    | zero => exact .finished ()
    | succ n => exact .exhausted ⟨rfl, le_rfl⟩

theorem one_back {n : Nat} {state : Nat × Nat} (retained : related n state) :
    ∃ count, (logical.run count n).1 = (backend.run 1 state).1 ∧
      OutcomeRel related (logical.run count n).2 (backend.run 1 state).2 := by
  rcases state with ⟨n', debt⟩
  rcases retained with ⟨rfl, bound⟩
  cases debt with
  | zero =>
      refine ⟨1, ?_, ?_⟩
      · cases n <;> rfl
      · cases n with
        | zero => exact .finished ()
        | succ n => exact .exhausted ⟨rfl, le_rfl⟩
  | succ debt =>
      exact ⟨0, rfl, .exhausted ⟨rfl, Nat.le_trans (Nat.le_succ debt) bound⟩⟩

/-- This actual representation has finite local implementations but admits no
single uniform instruction bound for its logical publication operation. -/
theorem no_uniform_cost (cost : Nat) : ¬ CostSimulation logical backend related cost := by
  intro simulation
  obtain ⟨count, bound, next, ran, _⟩ := simulation.publish
    (state := cost + 1) (state' := (cost + 1, cost + 1))
    (show related (cost + 1) (cost + 1, cost + 1) from ⟨rfl, le_rfl⟩) rfl
  have waiting := debt_before_boundary (cost + 1) (cost + 1) count
    (bound.trans (Nat.le_succ cost))
  have events := congrArg Prod.fst (waiting.symm.trans ran)
  cases events

theorem whole_prefixes (fuel n debt : Nat) (admitted : debt ≤ n) :
    ∃ count, (backend.run count (n, debt)).1 = (logical.run fuel n).1 ∧
      OutcomeRel related (logical.run fuel n).2 (backend.run count (n, debt)).2 :=
  logical.run_related_of_one backend related one_forth fuel ⟨rfl, admitted⟩

theorem same_completions (n debt : Nat) (admitted : debt ≤ n) (events : List Nat) :
    (∃ fuel, logical.run fuel n = (events, .finished ())) ↔
      ∃ count, backend.run count (n, debt) = (events, .finished ()) :=
  logical.finished_iff_of_one backend related one_forth one_back
    (state := n) (state' := (n, debt)) ⟨rfl, admitted⟩ events ()

theorem round_trip_one (n debt : Nat) (admitted : debt ≤ n) :
    ∃ count, (logical.run count n).1 = (logical.run 1 n).1 ∧
      OutcomeRel (Mettapedia.GSLT.Distinction.SpanTransport.compose related
        (fun physical abstract => related abstract physical))
        (logical.run 1 n).2 (logical.run count n).2 := by
  have reverse : ∀ {physical abstract}, related abstract physical →
      ∃ count, (logical.run count abstract).1 = (backend.run 1 physical).1 ∧
        OutcomeRel (fun p a => related a p)
          (backend.run 1 physical).2 (logical.run count abstract).2 := by
    intro physical abstract retained
    obtain ⟨count, eventEq, outcome⟩ := one_back retained
    exact ⟨count, eventEq, outcome.symm⟩
  exact logical.run_one_related_comp backend logical related (fun p a => related a p)
    one_forth reverse ⟨(n, debt), ⟨rfl, admitted⟩, ⟨rfl, admitted⟩⟩

theorem retained_publications :
    backend.run 3 (2, 2) = ([2, 2], .exhausted (1, 1)) := rfl

theorem resume_appends_each_occurrence :
    backend.run 6 (2, 2) = ([2, 2, 1, 1], .finished ()) := rfl

theorem resumed_suffix : backend.run 3 (1, 1) = ([1, 1], .finished ()) := rfl

theorem restart_repeats_prefix :
    ([2, 2] ++ (backend.run 6 (2, 2)).1) ≠ (backend.run 6 (2, 2)).1 := by decide

end Mettapedia.GSLT.Distinction.ProductiveBlocks.CompositionControls.FiniteBlocks
