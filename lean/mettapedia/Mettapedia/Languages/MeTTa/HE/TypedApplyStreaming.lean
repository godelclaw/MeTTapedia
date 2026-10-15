import Mettapedia.Languages.MeTTa.HE.TypedApplyDerivation
import Mettapedia.GSLT.Distinction.ProductiveBlocks

/-!
# Typed argument application in the common step and resumption interface

This instance executes `TypedApplyMachine.stepConfig`. It publishes only
new occurrences, retains the complete worklist and history, and reads back
to the existing independent machine runner. Its administrative rank is the
work of the direct argument tree, rather than a caller-supplied progress law.

One transition of the existing application machine may collect an entire
argument service result. The service's cost is separate; its own recursive
control, effects, interruption and native realization are not concealed by
the administrative rank proved here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypedApplyStreaming

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open TypedApplyDerivation (Services Derivation)

abbrev Configuration := TypedApplyConfig

/-- Advance the existing typed application machine. -/
def next (services : Services) (state : Configuration) : Configuration :=
  stepConfig services.evaluate services.apply services.merge services.extend services.raw state

/-- The old history is retained; only its new suffix is published. -/
def events (before after : Configuration) : ResultList :=
  after.emitted.drop before.emitted.length

/-- Classify actual application steps for an ordered occurrence observer. -/
def machine (services : Services) :
    Machine Configuration ResultPair Configuration Empty where
  step state :=
    if state.isDone then some (.finish state)
    else
      let after := next services state
      let emitted := events state after
      if emitted = [] then some (.silent after)
      else some (.publish emitted after)

theorem step_done (services : Services) (state : Configuration)
    (done : state.isDone = true) :
    (machine services).step state = some (.finish state) := by
  simp [machine, done]

theorem step_silent (services : Services) (state : Configuration)
    (done : ¬state.isDone = true) (silent : events state (next services state) = []) :
    (machine services).step state = some (.silent (next services state)) := by
  simp [machine, done, silent]

theorem step_publish (services : Services) (state : Configuration)
    (done : ¬state.isDone = true) (visible : events state (next services state) ≠ []) :
    (machine services).step state =
      some (.publish (events state (next services state)) (next services state)) := by
  simp [machine, done, visible]

/-- Every nonfaulting outcome retains its complete application configuration. -/
def readback : Outcome Configuration Configuration Empty → Option Configuration
  | .finished state | .exhausted state | .stuck state => some state
  | .suspended request _ => nomatch request
  | .faulted => none

/-- A step's published suffix extends exactly the old occurrence history. -/
theorem next_history (services : Services) (state : Configuration)
    (pending : state.worklist ≠ []) :
    state.emitted ++ events state (next services state) = (next services state).emitted := by
  have source := stepConfig_spec services.evaluate services.apply services.merge
    services.extend services.raw state pending
  rcases step_emits_sound _ _ _ _ _ _ _ source with unchanged | ⟨kind, emitted⟩
  · simp [events, next, unchanged]
  · simp [events, next, emitted]

/-- The common driver reads back to the independently defined application
runner at exactly the same transition budget. -/
theorem run_readback (services : Services) (budget : Nat) (state : Configuration) :
    readback ((machine services).run budget state).2 =
      some (machineRun services.evaluate services.apply services.merge services.extend
        services.raw state budget) := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
      by_cases done : state.isDone = true
      · simp only [Machine.run, step_done services state done, readback,
          machineRun, if_pos done]
      · rw [machineRun, if_neg done]
        by_cases silent : events state (next services state) = []
        · rw [(machine services).run_succ_silent (step_silent services state done silent)]
          exact ih (next services state)
        · rw [(machine services).run_succ_publish (step_publish services state done silent)]
          exact ih (next services state)

/-- Equal values remain separate occurrences: the event list is exactly the
new suffix of the independently executed machine's history. -/
theorem run_history (services : Services) (budget : Nat) (state : Configuration) :
    state.emitted ++ ((machine services).run budget state).1 =
      (machineRun services.evaluate services.apply services.merge services.extend
        services.raw state budget).emitted := by
  induction budget generalizing state with
  | zero => simp [Machine.run, machineRun]
  | succ budget ih =>
      by_cases done : state.isDone = true
      · simp only [Machine.run, step_done services state done, machineRun,
          if_pos done, List.append_nil]
      · have pending : state.worklist ≠ [] := by
          simpa [TypedApplyConfig.isDone, List.isEmpty_iff] using done
        have history := next_history services state pending
        rw [machineRun, if_neg done]
        by_cases silent : events state (next services state) = []
        · have same : state.emitted = (next services state).emitted := by
            simpa [silent] using history
          rw [(machine services).run_succ_silent (step_silent services state done silent), same]
          exact ih (next services state)
        · rw [(machine services).run_succ_publish (step_publish services state done silent)]
          change state.emitted ++ (events state (next services state) ++
              ((machine services).run budget (next services state)).1) = _
          rw [← List.append_assoc, history]
          exact ih (next services state)

/-- Every retained result of the common driver is an actual source-machine
path. Finishing administration does not invent an application transition. -/
theorem run_source (services : Services) (budget : Nat) (state final : Configuration)
    (returned : readback ((machine services).run budget state).2 = some final) :
    TypedApplyReaches services.evaluate services.apply services.merge services.extend
      services.raw state final := by
  have equal := (run_readback services budget state).symm.trans returned
  have same := Option.some.inj equal
  subst final
  exact machineRun_reaches _ _ _ _ _ state budget

/-- The independent direct argument tree is partitioned into published
occurrences and the complete retained application frontier. -/
theorem run_residual (services : Services) (budget : Nat) (state final : Configuration)
    (returned : readback ((machine services).run budget state).2 = some final) :
    state.observations services.evaluate services.apply services.merge services.extend
        services.raw =
      state.emitted ++ ((machine services).run budget state).1 ++
        final.worklist.flatMap (TypedApplyFrame.meaning services.evaluate services.apply
          services.merge services.extend services.raw) := by
  have conserved := typedApplyReaches_preserves_observations _ _ _ _ _
    (run_source services budget state final returned)
  have equal := (run_readback services budget state).symm.trans returned
  have same := Option.some.inj equal
  have history := run_history services budget state
  rw [same] at history
  simpa [TypedApplyConfig.observations, ← history] using conserved

/-- The common resumption law retains the precise state at the pause. -/
theorem resume_after_prefix (services : Services) (first second : Nat)
    (initial saved : Configuration) (emitted : ResultList)
    (paused : (machine services).run first initial = (emitted, .exhausted saved)) :
    (machine services).run (first + second) initial =
      (emitted ++ ((machine services).run second saved).1,
        ((machine services).run second saved).2) :=
  (machine services).established_and_pending first second initial saved emitted paused

/-- The direct tree's exact remaining administrative work. -/
def rank (services : Services) (state : Configuration) : Nat :=
  state.work services.evaluate services.apply services.merge services.extend services.raw
    (fun _ _ _ => 0)

/-- Every actual application step strictly consumes this independent work. -/
theorem next_rank (services : Services) (state : Configuration)
    (pending : state.worklist ≠ []) :
    rank services state = 1 + rank services (next services state) := by
  have work := typedApplyStep_work services.evaluate services.apply services.merge
    services.extend services.raw (fun _ _ _ => 0)
      (stepConfig_spec _ _ _ _ _ state pending)
  have zeroService : state.serviceCost services.apply services.raw (fun _ _ _ => 0) = 0 := by
    unfold TypedApplyConfig.serviceCost
    split <;> first | rfl | (split <;> first | rfl | (split <;> rfl))
  simpa [rank, next, zeroService] using work

/-- No infinite silent sequence is admitted at this argument-service
granularity. No claim about termination or latency inside that service follows. -/
def productive (services : Services) : (machine services).Productive where
  rank := rank services
  silent_decreases := by
    intro state after stepped
    by_cases done : state.isDone = true
    · simp [machine, done] at stepped
    · have pending : state.worklist ≠ [] := by
        simpa [TypedApplyConfig.isDone, List.isEmpty_iff] using done
      have smaller := next_rank services state pending
      simp only [machine, if_neg done] at stepped
      split at stepped
      · cases stepped
        omega
      · simp at stepped
  moves := by
    intro state
    by_cases done : state.isDone = true
    · rw [step_done services state done]
      simp
    · by_cases silent : events state (next services state) = []
      · rw [step_silent services state done silent]
        simp
      · rw [step_publish services state done silent]
        simp

/-- A source-derived budget plus finishing administration reaches a genuine
finished state, rather than merely an exhausted cursor. -/
theorem finishes (services : Services) (budget : Nat) (state : Configuration)
    (enough : rank services state + 1 ≤ budget) :
    ∃ emitted final, (machine services).run budget state = (emitted, .finished final) := by
  induction budget generalizing state with
  | zero => omega
  | succ budget ih =>
      by_cases done : state.isDone = true
      · exact ⟨[], state, (machine services).run_succ_finish (step_done services state done)⟩
      · have pending : state.worklist ≠ [] := by
          simpa [TypedApplyConfig.isDone, List.isEmpty_iff] using done
        have decrease := next_rank services state pending
        obtain ⟨emitted, final, finished⟩ := ih (next services state) (by omega)
        by_cases silent : events state (next services state) = []
        · exact ⟨emitted, final, by
            rw [(machine services).run_succ_silent (step_silent services state done silent)]
            exact finished⟩
        · exact ⟨events state (next services state) ++ emitted, final, by
            rw [(machine services).run_succ_publish (step_publish services state done silent), finished]⟩

/-- Finishing is possible only with an actually exhausted worklist. -/
theorem run_finished_empty (services : Services) (budget : Nat)
    (state final : Configuration) (emitted : ResultList)
    (finished : (machine services).run budget state = (emitted, .finished final)) :
    final.worklist = [] := by
  induction budget generalizing state final emitted with
  | zero => cases finished
  | succ budget ih =>
      by_cases done : state.isDone = true
      · have equal := finished
        rw [(machine services).run_succ_finish (step_done services state done)] at equal
        have states := congrArg (fun result => result.2) equal
        cases states
        simpa [TypedApplyConfig.isDone, List.isEmpty_iff] using done
      · by_cases silent : events state (next services state) = []
        · rw [(machine services).run_succ_silent
            (step_silent services state done silent)] at finished
          exact ih _ _ _ finished
        · rw [(machine services).run_succ_publish
            (step_publish services state done silent)] at finished
          have outcome := congrArg Prod.snd finished
          exact ih _ _ _ (Prod.ext rfl outcome)

/-- Completing an initially empty history publishes exactly the direct
 evaluator's ordered result list and constructs every result's derivation. -/
theorem completed_initial (services : Services) (initial : TypedApplyState) (budget : Nat)
    (emitted : ResultList) (final : Configuration)
    (finished : (machine services).run budget (.initial initial) = (emitted, .finished final)) :
    emitted = typedApplyDirect services.evaluate services.apply services.merge services.extend
        services.raw initial ∧
      ∀ result, result ∈ emitted ↔ Derivation services initial result := by
  have returned : readback ((machine services).run budget (.initial initial)).2 = some final := by
    simp [finished, readback]
  have conserved := typedApplyReaches_preserves_observations _ _ _ _ _
    (run_source services budget (.initial initial) final returned)
  have equal := (run_readback services budget (.initial initial)).symm.trans returned
  have same := Option.some.inj equal
  have history := run_history services budget (.initial initial)
  rw [same, finished] at history
  have emittedEqual : emitted = final.emitted := by
    simpa [TypedApplyConfig.initial] using history
  have done := run_finished_empty services budget (.initial initial) final emitted finished
  have exactResults : emitted = typedApplyDirect services.evaluate services.apply services.merge
      services.extend services.raw initial := by
    simpa [TypedApplyConfig.observations, TypedApplyConfig.initial,
      TypedApplyFrame.meaning, done, ← emittedEqual] using conserved.symm
  refine ⟨exactResults, ?_⟩
  intro result
  rw [exactResults]
  exact TypedApplyDerivation.direct_iff services initial result

/-- Administrative transitions and the completed argument-service charge
are separate terms. Finishing an exhausted worklist incurs neither. -/
def price (services : Services) (serviceCharge : Atom → Atom → Bindings → Nat)
    (state : Configuration) : Nat :=
  if state.isDone then 0
  else 1 + state.serviceCost services.apply services.raw serviceCharge

/-- Every bounded run consumes exactly its supplied account and leaves the
rest in the actual saved frontier. This is an account of these operations,
not a claim that their native callbacks take constant physical work. -/
theorem spent_plus_remaining (services : Services)
    (serviceCharge : Atom → Atom → Bindings → Nat) (budget : Nat) (state : Configuration) :
    (machine services).spent (price services serviceCharge) budget state +
      (machineRun services.evaluate services.apply services.merge services.extend services.raw
        state budget).work services.evaluate services.apply services.merge services.extend
          services.raw serviceCharge =
      state.work services.evaluate services.apply services.merge services.extend services.raw
        serviceCharge := by
  induction budget generalizing state with
  | zero => simp [Machine.spent, machineRun]
  | succ budget ih =>
      by_cases done : state.isDone = true
      · simp only [Machine.spent, step_done services state done, price, if_pos done,
          machineRun, Nat.zero_add]
      · have pending : state.worklist ≠ [] := by
          simpa [TypedApplyConfig.isDone, List.isEmpty_iff] using done
        have conserved := typedApplyStep_work services.evaluate services.apply services.merge
          services.extend services.raw serviceCharge
            (stepConfig_spec _ _ _ _ _ state pending)
        have tail := ih (next services state)
        by_cases silent : events state (next services state) = []
        · simp only [Machine.spent, step_silent services state done silent,
            price, if_neg done, machineRun, Nat.add_assoc]
          dsimp only [next] at tail ⊢
          rw [tail]
          simpa only [Nat.add_assoc] using conserved.symm
        · simp only [Machine.spent, step_publish services state done silent,
            price, if_neg done, machineRun, Nat.add_assoc]
          dsimp only [next] at tail ⊢
          rw [tail]
          simpa only [Nat.add_assoc] using conserved.symm

/-- Resumption splits this account at the exact retained configuration. -/
theorem account_split (services : Services)
    (serviceCharge : Atom → Atom → Bindings → Nat) (first second : Nat)
    (initial saved : Configuration) (emitted : ResultList)
    (paused : (machine services).run first initial = (emitted, .exhausted saved)) :
    (machine services).spent (price services serviceCharge) (first + second) initial =
      (machine services).spent (price services serviceCharge) first initial +
        (machine services).spent (price services serviceCharge) second saved := by
  simpa [paused, Machine.spentAfter] using
    (machine services).spent_add (price services serviceCharge) first second initial

end Mettapedia.Languages.MeTTa.HE.TypedApplyStreaming
