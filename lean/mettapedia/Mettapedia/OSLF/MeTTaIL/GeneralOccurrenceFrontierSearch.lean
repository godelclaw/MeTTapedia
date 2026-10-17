import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceCompletedCertificate
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceModalReadouts
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceTermination
import Mettapedia.Machines.ResumableSearchRunner
import Mettapedia.OSLF.MeTTaIL.GeneralEquationCanonical
import Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceUniversalCompletion

/-!
# The equation-aware frontier as a resumable search

The frontier of `GeneralOccurrenceFrontier` explores a source's equation class and publishes the
rule firings at its representatives. Run step by step it is a lawful resumable search
(`ResumableSearchRunner.Search`): more work never restarts it, its answers only grow, and every
answer is a valid receipt of the plan's GSLT modulo its equations.

- `admitted_of_complete`: a completed run proves its own admission, because the start state
  records every plan obligation and a rejected source as unresolved, and unresolved obligations
  only grow;
- `search_sound`: every answer is a step of the GSLT from the source's class;
- `search_exact`: a complete run with no answers excludes every step;
- `search_classes`: a complete run's answers are exactly the successor classes;
- `search_settles`: at admitted sources the run settles after finitely much work;
- `search_complete_of_total`: under checked totality some finite run is complete, not only
  drained. The work is an existence claim; `cost` is noncomputable and gives no time bound.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Machines.ResumableSearchRunner (Search Status)

/-! ## Runs -/

theorem tick_unresolved_prefix (request : Request) (state : State request) :
    state.unresolved <+: (tick request state).unresolved := by
  unfold tick
  cases state.agenda with
  | nil => exact List.prefix_refl _
  | cons task remaining => exact List.prefix_append _ _

theorem run_unresolved_prefix (request : Request) (fuel : Nat) (state : State request) :
    state.unresolved <+: (run request fuel state).unresolved := by
  induction fuel generalizing state with
  | zero => exact List.prefix_refl _
  | succ fuel ih => exact (tick_unresolved_prefix request state).trans (ih (tick request state))

theorem reachable_unresolved {request : Request} {state : State request} (reached : Reachable request state) :
    (start request).unresolved <+: state.unresolved := by
  induction reached with
  | start => exact List.prefix_refl _
  | tick _ ih => exact ih.trans (tick_unresolved_prefix request _)

theorem tick_idle {request : Request} {state : State request} (idle : state.agenda = []) :
    tick request state = state := by
  simp [tick, idle]

theorem run_idle {request : Request} {state : State request} (idle : state.agenda = []) (fuel : Nat) :
    run request fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [run, tick_idle idle, ih]

/-- **A completed run proves its own admission.** -/
theorem admitted_of_complete {request : Request}
    (compiled : request.plan = compile request.plan.snapshot request.plan.permissions)
    {state : State request} (reached : Reachable request state) (done : complete request state = true) :
    Admitted request := by
  obtain ⟨_, resolved, _⟩ := (complete_iff request state).mp done
  have initial := reachable_unresolved reached
  rw [resolved, List.prefix_nil] at initial
  unfold start at initial
  split at initial
  · rename_i sorted
    simp only [List.map_eq_nil_iff] at initial
    exact ⟨compiled, by simp [Plan.complete, initial], checkOpenPatternWellSorted_sound sorted⟩
  · simp at initial

/-! ## The search -/

section Search

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- The frontier request at a source. -/
def requestAt (source : Pattern) : Request := ⟨plan, bound, expected, source⟩

/-- A retained frontier run, with the source it explores. -/
structure FrontierRun where
  source : Pattern
  state : State (requestAt plan bound expected source)

/-- The frontier as a resumable search. -/
def search : Search Pattern (FrontierRun plan bound expected) GeneralOccurrenceSemantics.Receipt where
  run source work := ⟨source, run _ work (start _)⟩
  resume retained extra := ⟨retained.source, run _ extra retained.state⟩
  publication retained := retained.state.answers.map Subtype.val
  status retained :=
    if complete _ retained.state then .complete
    else if retained.state.agenda.isEmpty then .blocked else .pending
  target := GeneralOccurrenceSemantics.Receipt.target
  Valid source receipt := receipt.Valid plan bound expected source.eraseBinderMetadata

/-- A step from a source's class: the GSLT step from its binder-erased form. -/
def ClassStep (source target : Pattern) : Prop :=
  (GeneralOccurrenceSemantics.gslt plan bound expected).Step source.eraseBinderMetadata target

theorem search_lawful : (search plan bound expected).Lawful where
  resume_run source first extra := by
    simp only [search]
    rw [run_add]
  publication_prefix source first extra := by
    simp only [search]
    obtain ⟨tail, grown⟩ := answers_prefix (requestAt plan bound expected source) extra
      (run _ first (start _))
    rw [run_add, grown, List.map_append]
    exact List.prefix_append _ _
  sound source work receipt member := by
    simp only [search, List.mem_map] at member
    obtain ⟨answer, _, same⟩ := member
    rw [← same]
    exact answer.property

theorem search_sound {source : Pattern} {receipt : GeneralOccurrenceSemantics.Receipt}
    (valid : (search plan bound expected).Valid source receipt) :
    ClassStep plan bound expected source ((search plan bound expected).target receipt) :=
  GeneralOccurrenceSemantics.Receipt.semantic_step plan bound expected valid

private theorem complete_of_status {source : Pattern} {work : Nat}
    (done : (search plan bound expected).status ((search plan bound expected).run source work) = .complete) :
    complete (requestAt plan bound expected source)
      (run (requestAt plan bound expected source) work (start _)) = true := by
  simp only [search] at done
  split at done
  · assumption
  · split at done <;> cases done

/-- **A complete run with no answers excludes every step.** -/
theorem search_exact (compiled : plan = compile plan.snapshot plan.permissions) (source : Pattern) (work : Nat)
    (done : (search plan bound expected).status ((search plan bound expected).run source work) = .complete)
    (empty : (search plan bound expected).publication ((search plan bound expected).run source work) = []) :
    ∀ target, ¬ ClassStep plan bound expected source target := by
  have completed := complete_of_status plan bound expected done
  have reached := reachable_run (Reachable.start (request := requestAt plan bound expected source)) work
  have admitted := admitted_of_complete compiled reached completed
  have checked := completed_checkCertificate admitted reached completed
  have noAnswers : (run (requestAt plan bound expected source) work (start _)).answers = [] := by
    simp only [search] at empty
    exact List.map_eq_nil_iff.mp empty
  intro target step
  exact (certified_absence admitted checked).mp noAnswers ⟨target, step⟩

/-- **A complete run's answers are exactly the successor classes.** -/
theorem search_classes (compiled : plan = compile plan.snapshot plan.permissions) (source : Pattern) (work : Nat)
    (done : (search plan bound expected).status ((search plan bound expected).run source work) = .complete)
    (target : Pattern) :
    (∃ receipt ∈ (search plan bound expected).publication ((search plan bound expected).run source work),
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) receipt.target target) ↔
      ClassStep plan bound expected source target := by
  have completed := complete_of_status plan bound expected done
  have reached := reachable_run (Reachable.start (request := requestAt plan bound expected source)) work
  have admitted := admitted_of_complete compiled reached completed
  have checked := completed_checkCertificate admitted reached completed
  have key := certified_successor_classes admitted checked target
  show _ ↔ (GeneralOccurrenceSemantics.gslt (requestAt plan bound expected source).plan
    (requestAt plan bound expected source).bound (requestAt plan bound expected source).expected).Step
      (requestAt plan bound expected source).root target
  rw [← key]
  simp only [search, List.mem_map]
  constructor
  · rintro ⟨_, ⟨answer, member, rfl⟩, related⟩
    exact ⟨answer, member, related⟩
  · rintro ⟨answer, member, related⟩
    exact ⟨answer.val, ⟨answer, member, rfl⟩, related⟩

/-- Sources whose frontier is admitted. -/
def Settles (source : Pattern) : Prop := Admitted (requestAt plan bound expected source)

/-- The work after which an admitted frontier has drained its agenda. -/
noncomputable def cost (source : Pattern) : Nat := by
  classical
  exact if admitted : Settles plan bound expected source then
    Classical.choose (finite_saturation (requestAt plan bound expected source) admitted)
  else 0

/-- **Admitted frontiers settle** after finitely much work: their status is no longer pending. -/
theorem search_settles (source : Pattern) (work : Nat) (admitted : Settles plan bound expected source)
    (enough : cost plan bound expected source ≤ work) :
    (search plan bound expected).status ((search plan bound expected).run source work) ≠ .pending := by
  have saturated := Classical.choose_spec (finite_saturation (requestAt plan bound expected source) admitted)
  have fuel : cost plan bound expected source =
      Classical.choose (finite_saturation (requestAt plan bound expected source) admitted) := by
    unfold cost
    rw [dif_pos admitted]
  rw [fuel] at enough
  have idle : (run (requestAt plan bound expected source)
      (Classical.choose (finite_saturation (requestAt plan bound expected source) admitted)) (start _)).agenda = [] :=
    List.isEmpty_iff.mp saturated
  have split : work = Classical.choose (finite_saturation (requestAt plan bound expected source) admitted) +
      (work - Classical.choose (finite_saturation (requestAt plan bound expected source) admitted)) := by omega
  have later : (run (requestAt plan bound expected source) work (start _)).agenda = [] := by
    rw [split, run_add, run_idle idle]
    exact idle
  simp only [search]
  split
  · simp
  · simp [later]

/-- Admission passes along a valid receipt: the target is well-sorted, so its erased form is. -/
theorem settles_target (compiled : plan = compile plan.snapshot plan.permissions)
    (accepted : plan.complete = true) {source : Pattern} {receipt : GeneralOccurrenceSemantics.Receipt}
    (valid : (search plan bound expected).Valid source receipt) :
    Settles plan bound expected ((search plan bound expected).target receipt) := by
  have sorted := GeneralOccurrenceSemantics.Receipt.target_sorted plan bound expected valid
  exact ⟨compiled, accepted, GeneralEquationCanonical.open_typed_erase sorted.1 sorted.2.2.1 sorted.2.2.2⟩

/-! ## Whole runs modulo equations -/

open Mettapedia.Machines.ResumableSearchRunner (Machine Reached)

/-- **The run is a reduction sequence modulo equations.** In chronological order the states of
every run start at the source and each one steps, from its class, to the next. -/
theorem run_chain_modulo (source : Pattern) (ticks quantum : Nat) :
    let machine := Machine.advance (search plan bound expected) ticks quantum
      (Machine.begin (search plan bound expected) source)
    machine.states.reverse.head? = some source ∧
      machine.states.reverse.IsChain (ClassStep plan bound expected) :=
  Mettapedia.Machines.ResumableSearchRunner.run_chain (search_lawful plan bound expected)
    (search_sound plan bound expected) source ticks quantum

/-- **A normal ending is exact modulo equations**: the last state's class has no step. -/
theorem done_no_step_modulo (compiled : plan = compile plan.snapshot plan.permissions)
    {machine : Machine Pattern (FrontierRun plan bound expected) GeneralOccurrenceSemantics.Receipt}
    (reached : Reached (search plan bound expected) machine) (done : machine.phase = .done) :
    ∀ target, ¬ ClassStep plan bound expected machine.state target :=
  Mettapedia.Machines.ResumableSearchRunner.done_no_step
    (fun state work complete empty => search_exact plan bound expected compiled state work complete empty)
    reached done

/-- Every state of a run from an admitted source is admitted. -/
theorem run_settles (compiled : plan = compile plan.snapshot plan.permissions) (accepted : plan.complete = true)
    {source : Pattern} (admitted : Settles plan bound expected source) (ticks quantum : Nat) :
    Settles plan bound expected
      (Machine.advance (search plan bound expected) ticks quantum (Machine.begin (search plan bound expected) source)).state :=
  Mettapedia.Machines.ResumableSearchRunner.advance_preserves (search_lawful plan bound expected)
    (fun valid => settles_target plan bound expected compiled accepted valid) quantum ticks
    (Mettapedia.Machines.ResumableSearchRunner.begin_reached source) admitted

/-- **Every search settles in finitely many ticks**, at every state of a run from an admitted
source: with a positive quantum the machine commits or stops. -/
theorem progress_modulo (compiled : plan = compile plan.snapshot plan.permissions) (accepted : plan.complete = true)
    {machine : Machine Pattern (FrontierRun plan bound expected) GeneralOccurrenceSemantics.Receipt}
    (reached : Reached (search plan bound expected) machine) (admitted : Settles plan bound expected machine.state)
    (running : machine.phase = .running) {quantum : Nat} (positive : 0 < quantum) :
    ∃ ticks ≤ cost plan bound expected machine.state + 1,
      machine.receipts.length < (Machine.advance (search plan bound expected) ticks quantum machine).receipts.length ∨
        (Machine.advance (search plan bound expected) ticks quantum machine).phase ≠ .running := by
  have _ := compiled
  have _ := accepted
  exact Mettapedia.Machines.ResumableSearchRunner.progress
    (fun state work settling enough => search_settles plan bound expected state work settling enough)
    (search_lawful plan bound expected) reached admitted running positive

/-- **Checked totality makes settling complete.** For a compiled, accepted plan whose totality
check passes, some finite run from a well-sorted source reports complete, not blocked. -/
theorem search_complete_of_total (compiled : plan = compile plan.snapshot plan.permissions)
    (accepted : plan.complete = true) (source : Pattern)
    (typed : OpenPatternWellSorted plan.snapshot.language plan.snapshot.free bound expected
      source.eraseBinderMetadata)
    (total : GeneralExecutionTotalAdmission.checkTotality plan = true) :
    ∃ work, (search plan bound expected).status ((search plan bound expected).run source work) =
      Mettapedia.Machines.ResumableSearchRunner.Status.complete := by
  let request := requestAt plan bound expected source
  have admitted : Admitted request := ⟨compiled, accepted, typed⟩
  obtain ⟨work, finished⟩ := finish_actual_run request admitted
  have complete := finish_complete_of_total_admission admitted total
  refine ⟨work, ?_⟩
  change (if GeneralOccurrenceFrontier.complete request (run request work (start request)) then
    Mettapedia.Machines.ResumableSearchRunner.Status.complete
    else if (run request work (start request)).agenda.isEmpty then .blocked else .pending) = .complete
  rw [finished, if_pos complete]

end Search

end Mettapedia.OSLF.MeTTaIL.GeneralOccurrenceFrontier
