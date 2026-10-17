import Mettapedia.OSLF.MeTTaIL.Complete.Step
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceLocalCertificate

/-!
# The complete step search against the plan's GSLT, and whole runs over it

For an equation-free plan the steps of its GSLT (`GeneralOccurrenceSemantics.gslt`) are exactly the
targets of its valid receipts. So the complete step search of `Complete.Step` decides steps in the
limit, for every such plan, recursive premises included:

- `logged_step`: every logged receipt is a step;
- `step_logged`: every step is logged after finitely many rounds;
- `step_exact`: once the search is complete, the log holds every step.

The runner of `Machines.ResumableSearchRunner` over this search follows one path:

- `run_chain`: every run is a reduction sequence of the GSLT, for every plan;
- `done_no_step`: a normal ending is exact;
- `progress`, `stop_or_commit`: for structurally admitted plans every running machine commits a
  receipt or stops after finitely many ticks.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Run

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open Mettapedia.Machines.ResumableSearchRunner (Search Status)
open Mettapedia.Machines

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- The plan's GSLT steps. -/
abbrev PlanStep (source target : Pattern) : Prop :=
  (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target

theorem step_of_valid {source : Pattern} {receipt : GeneralRuleJobs.Receipt}
    (valid : receipt.Valid plan bound expected source) : PlanStep plan bound expected source receipt.target :=
  ⟨source, receipt, .refl _, valid, .refl _⟩

/-- For an equation-free plan, a step is the target of a valid receipt. -/
theorem valid_of_step (empty : plan.equations = []) {source target : Pattern}
    (step : PlanStep plan bound expected source target) :
    ∃ receipt : GeneralRuleJobs.Receipt, receipt.Valid plan bound expected source ∧ receipt.target = target := by
  obtain ⟨representative, receipt, before, valid, after⟩ := step
  let request : GeneralOccurrenceFrontier.Request := ⟨plan, bound, expected, source⟩
  have sameSource : source = representative :=
    GeneralOccurrenceFrontier.LocalEquationFree.equation_equivalence_is_equality (request := request) empty before
  have sameTarget : receipt.target = target :=
    GeneralOccurrenceFrontier.LocalEquationFree.equation_equivalence_is_equality (request := request) empty after
  subst sameSource
  exact ⟨receipt, valid, sameTarget⟩

/-- The log after some rounds. -/
abbrev logAt (source : Pattern) (work : Nat) : List GeneralRuleJobs.Receipt :=
  (Step.rounds plan bound expected work (Step.begin plan bound expected source)).log

theorem logged_step {source : Pattern} {work : Nat} {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ logAt plan bound expected source work) :
    PlanStep plan bound expected source receipt.target :=
  step_of_valid plan bound expected (Step.sound plan bound expected source work receipt member)

/-- **Every step is logged** after finitely many rounds, for every equation-free plan. -/
theorem step_logged (empty : plan.equations = []) {source target : Pattern}
    (step : PlanStep plan bound expected source target) :
    ∃ work, target ∈ (logAt plan bound expected source work).map GeneralRuleJobs.Receipt.target := by
  obtain ⟨receipt, valid, rfl⟩ := valid_of_step plan bound expected empty step
  obtain ⟨work, member⟩ := Step.complete_in_limit plan bound expected valid
  exact ⟨work, List.mem_map.mpr ⟨receipt, member, rfl⟩⟩

/-- **A complete search has every step.** -/
theorem step_exact (empty : plan.equations = []) {source target : Pattern} {work : Nat}
    (done : Step.status plan (Step.rounds plan bound expected work (Step.begin plan bound expected source)) = .complete)
    (step : PlanStep plan bound expected source target) :
    target ∈ (logAt plan bound expected source work).map GeneralRuleJobs.Receipt.target := by
  obtain ⟨receipt, valid, rfl⟩ := valid_of_step plan bound expected empty step
  exact List.mem_map.mpr ⟨receipt, Step.exact_of_complete plan bound expected done valid, rfl⟩

/-! ## Runs -/

/-- A machine of the runner over the complete step search. -/
abbrev Machine := ResumableSearchRunner.Machine Pattern (Step.State plan) GeneralRuleJobs.Receipt

/-- The machine at the source. -/
abbrev begin (source : Pattern) : Machine plan :=
  ResumableSearchRunner.Machine.begin (Step.search plan bound expected) source

/-- A page of ticks. -/
abbrev advance (ticks quantum : Nat) (machine : Machine plan) : Machine plan :=
  ResumableSearchRunner.Machine.advance (Step.search plan bound expected) ticks quantum machine

/-- **Every run is a reduction sequence** of the plan's GSLT, for every plan. -/
theorem run_chain (source : Pattern) (ticks quantum : Nat) :
    let machine := advance plan bound expected ticks quantum (begin plan bound expected source)
    machine.states.reverse.head? = some source ∧
      machine.states.reverse.IsChain (PlanStep plan bound expected) :=
  ResumableSearchRunner.run_chain (Step.search_lawful plan bound expected)
    (fun valid => step_of_valid plan bound expected valid) source ticks quantum

/-- A complete, empty search leaves no step. -/
theorem no_step_of_complete (empty : plan.equations = []) (source : Pattern) (work : Nat)
    (complete : (Step.search plan bound expected).status ((Step.search plan bound expected).run source work) = .complete)
    (published : (Step.search plan bound expected).publication ((Step.search plan bound expected).run source work) = []) :
    ∀ target, ¬ PlanStep plan bound expected source target := by
  intro target step
  have found := step_exact plan bound expected empty complete step
  change target ∈ (Step.rounds plan bound expected work (Step.begin plan bound expected source)).log.map _ at found
  change (Step.rounds plan bound expected work (Step.begin plan bound expected source)).log = [] at published
  rw [published] at found
  cases found

/-- **A normal ending is exact.** A reached machine that is done has no step at its state. -/
theorem done_no_step (empty : plan.equations = [])
    {machine : Machine plan} (reached : ResumableSearchRunner.Reached (Step.search plan bound expected) machine)
    (done : machine.phase = .done) :
    ∀ target, ¬ PlanStep plan bound expected machine.state target :=
  ResumableSearchRunner.done_no_step (no_step_of_complete plan bound expected empty) reached done

/-- The work after which a state's search is complete, for an admitted plan. -/
noncomputable def cost
    (admitted : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true)
    (source : Pattern) : Nat :=
  Classical.choose (Step.eventually_complete plan bound expected admitted source)

theorem settles
    (admitted : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true)
    (source : Pattern) (work : Nat) (_ : True) (enough : cost plan bound expected admitted source ≤ work) :
    (Step.search plan bound expected).status ((Step.search plan bound expected).run source work) ≠ .pending := by
  have done := Step.complete_mono plan bound expected
    (Classical.choose_spec (Step.eventually_complete plan bound expected admitted source)) enough
  change Step.status plan (Step.rounds plan bound expected work (Step.begin plan bound expected source)) ≠ .pending
  rw [done]
  decide

/-- **Every search settles.** For a structurally admitted plan, with a positive quantum, a running
reached machine commits a receipt or stops within finitely many ticks. -/
theorem progress
    (admitted : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true)
    {machine : Machine plan} (reached : ResumableSearchRunner.Reached (Step.search plan bound expected) machine)
    (running : machine.phase = .running) {quantum : Nat} (positive : 0 < quantum) :
    ∃ ticks ≤ cost plan bound expected admitted machine.state + 1,
      machine.receipts.length < (advance plan bound expected ticks quantum machine).receipts.length ∨
        (advance plan bound expected ticks quantum machine).phase ≠ .running :=
  ResumableSearchRunner.progress (Settles := fun _ => True) (settles plan bound expected admitted)
    (Step.search_lawful plan bound expected) reached trivial running positive

/-- **Stop or commit.** For a structurally admitted plan, a running reached machine either stops at
its own state after some page, or commits one receipt valid at that state. -/
theorem stop_or_commit
    (admitted : StructuralDescent.checkEnvironment (GeneralPlanEnvironment.environment plan) = true)
    {machine : Machine plan} (reached : ResumableSearchRunner.Reached (Step.search plan bound expected) machine)
    (running : machine.phase = .running) {quantum : Nat} (positive : 0 < quantum) :
    (∃ ticks, (advance plan bound expected ticks quantum machine).phase ≠ .running ∧
      (advance plan bound expected ticks quantum machine).state = machine.state) ∨
    ∃ ticks, ∃ receipt : GeneralRuleJobs.Receipt, receipt.Valid plan bound expected machine.state ∧
      advance plan bound expected ticks quantum machine =
        ⟨.running, receipt.target, (Step.search plan bound expected).run receipt.target 0,
          receipt.target :: machine.states, receipt :: machine.receipts⟩ :=
  ResumableSearchRunner.stop_or_commit (Settles := fun _ => True) (settles plan bound expected admitted)
    (Step.search_lawful plan bound expected) reached trivial running positive

end Mettapedia.OSLF.MeTTaIL.Complete.Run
