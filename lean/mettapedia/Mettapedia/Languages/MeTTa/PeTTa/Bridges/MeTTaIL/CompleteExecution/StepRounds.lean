import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Steps
import Mettapedia.OSLF.Framework.DisplayedContextProfile

/-!
# Rounds of rule jobs

A lane is ready when its job is a licensed job of the term, its deepening search is reachable, and
the search stays within the footprint: its level, and the targets of its published firings put
back in the job's context. Ready lanes stay ready under a unit of work, and `gslt:step:advance`,
`advance-all`, `round` and `rounds` compute `Rounds.advance`, `round` and `rounds` on them.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise GeneralRuleJobs DerivedContexts
open StructuralDescent.Scheduled (Goal Result Task Obligation)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec

variable (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern)
  (footprint : List String)

/-- A firing's target, put back in the job's context, stays within the footprint. -/
def RootWithin (job : Job) (firing : Complete.DeepRoot.Firing) : Prop :=
  ∀ name ∈ (job.site.context.fill firing.target).freeFvarNames, name ∈ footprint

/-- What the term, the provider and the footprint satisfy. -/
structure StepScope : Prop where
  finite : plan.snapshot.provider.dynamicRelations = []
  provider : ∀ name ∈ providerFreeNames plan.snapshot.provider, name ∈ footprint
  source : ∀ name ∈ source.freeFvarNames, name ∈ footprint

variable {plan bound expected source footprint}

theorem context_within {job : Job} (licensed : job.Valid plan bound expected source)
    (scope : StepScope plan source footprint) :
    ∀ name ∈ Mettapedia.OSLF.Framework.DisplayedContextProfile.externalFreeFvarNames job.site.context, name ∈ footprint := by
  intro name member
  apply scope.source
  rw [← Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed.source_eq licensed.2]
  exact (Mettapedia.OSLF.Framework.DisplayedContextProfile.mem_freeFvarNames_fill_iff _ _ _).mpr (.inl member)

theorem focus_within {job : Job} (licensed : job.Valid plan bound expected source)
    (scope : StepScope plan source footprint) : ∀ name ∈ job.site.focus.freeFvarNames, name ∈ footprint := by
  intro name member
  apply scope.source
  rw [← Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence.Licensed.source_eq licensed.2]
  exact (Mettapedia.OSLF.Framework.DisplayedContextProfile.mem_freeFvarNames_fill_iff _ _ _).mpr (.inr member)

/-- A licensed job's deepening stays within the footprint. -/
theorem root_footprinted {job : Job} (licensed : job.Valid plan bound expected source)
    (scope : StepScope plan source footprint) :
    Complete.Deep.Footprinted (Complete.Step.family plan job) footprint (RootWithin footprint job) where
  goals _ := focus_within licensed scope
  reads result covered := by
    cases result with
    | root trace captured completed events target valid =>
      intro name member
      rcases (Mettapedia.OSLF.Framework.DisplayedContextProfile.mem_freeFvarNames_fill_iff _ _ _).mp member with outside | inside
      · exact context_within licensed scope name outside
      · exact covered.2.2.2 name inside
  provider := provider_coverage_mono _ footprint plan.snapshot.provider scope.provider
    (provider_covered_by_own_names plan.snapshot.provider)
  dynamic := Query.DynamicOutputsFreeWithin.of_unregistered footprint _ scope.finite

variable (plan bound expected source footprint)

/-- A lane of the step search that the MeTTa computes as the model does. -/
structure LaneReady (entry : Complete.Rounds.Entry (Complete.Step.family plan)) : Prop where
  licensed : entry.1.Valid plan bound expected source
  good : Complete.Deep.Good (Complete.Step.family plan entry.1) entry.2
  covered : Complete.Deep.Covered (Complete.Step.family plan entry.1) footprint (RootWithin footprint entry.1) entry.2

variable {plan bound expected source footprint}

theorem lane_ready_advance (scope : StepScope plan source footprint)
    {entry : Complete.Rounds.Entry (Complete.Step.family plan)} (ready : LaneReady plan bound expected source footprint entry) :
    LaneReady plan bound expected source footprint
      (Complete.Rounds.advance (Complete.Step.family plan) (Complete.Step.lift plan bound expected) entry).1 where
  licensed := ready.licensed
  good := Complete.Deep.tick_good _ ready.good
  covered := Complete.Deep.tick_covered (root_footprinted ready.licensed scope) ready.covered

theorem complete_descent_tick_returns (state : State) (environment : Environment)
    (finiteProvider : environment.provider.dynamicRelations = []) (footprint : List String)
    (provider : ∀ name ∈ providerFreeNames environment.provider, name ∈ footprint)
    (goal : Goal) (search : StructuralDescent.Scheduled.State environment goal)
    (covered : StructuralDescent.Scheduled.stateFreeWithin footprint environment goal search) :
    PureReturns runtime [] state
      (apply "gslt:descent:tick" [environmentValue environment (environment.free.entriesOn footprint),
        descentStateValue search]) state
      (descentStateValue (StructuralDescent.Scheduled.tick environment goal search)) := by
  metta_lift complete_checked ["environment", "state"]
    (descent_tick_returns state environment finiteProvider footprint provider goal search covered)

/-- What one unit of work for a lane returns: `(StepAdvanced entry receipts)`. -/
def advancedTerm (plan : GeneralExecutionAdmission.Plan)
    (advanced : Complete.Rounds.Entry (Complete.Step.family plan) × List Receipt) : Term :=
  .application "StepAdvanced" [entryTerm plan advanced.1, encodeList ScopedRuleJobReadoutExecution.receiptTerm advanced.2]

@[metta_head "gslt:step:advance"]
theorem step_advance_returns (state : State) (table : List (String × TypeExpr))
    (tabled : table = plan.snapshot.free.entriesOn footprint) (scope : StepScope plan source footprint)
    (entry : Complete.Rounds.Entry (Complete.Step.family plan)) (ready : LaneReady plan bound expected source footprint entry) :
    PureReturns runtime [] state
      (apply "gslt:step:advance" [planValue plan table bound expected, patternValue source, encoded (entryTerm plan entry)])
      state (encoded (advancedTerm plan
        (Complete.Rounds.advance (Complete.Step.family plan) (Complete.Step.lift plan bound expected) entry))) := by
  subst tabled
  obtain ⟨job, deep⟩ := entry
  have family := step_family_returns plan state job
  have before := deep_publication_returns (rootWire (Complete.Step.request plan job)) state deep
  have count := complete_length_returns firingTerm state deep.publication
  have level := complete_descent_tick_returns state (GeneralPlanEnvironment.environment plan) scope.finite footprint
    scope.provider _ deep.level ready.covered.level
  have ticked := deep_tick_returns (rootWire (Complete.Step.request plan job)) state _ deep level
  have after := deep_publication_returns (rootWire (Complete.Step.request plan job)) state
    (Complete.Deep.tick (Complete.Step.family plan job) deep)
  have fresh := drop_list_returns firingTerm state deep.publication.length
    (Complete.Deep.tick (Complete.Step.family plan job) deep).publication
  have nextReady := lane_ready_advance scope ready
  have lifted := step_lift_returns plan state (plan.snapshot.free.entriesOn footprint) bound expected footprint rfl
    source job ready.licensed
    ((Complete.Deep.tick (Complete.Step.family plan job) deep).publication.drop deep.publication.length)
    (fun firing member => ⟨Complete.Deep.publication_valid _ nextReady.good firing (List.mem_of_mem_drop member),
      Complete.Deep.publication_covered (root_footprinted ready.licensed scope) nextReady.covered firing
        (List.mem_of_mem_drop member)⟩)
  have freeSame : (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free := rfl
  complete_eval [family, before, count, ticked, after, fresh, lifted]
    unfolding [planValue, CompletePlanWire.planTerm, entryTerm, advancedTerm, Complete.Rounds.advance, rootWire,
      admittedValue, environmentValue, freeSame]

/-- What one unit of work for every lane returns: `(StepAdvanced entries receipts)`. -/
def advancedAllTerm (plan : GeneralExecutionAdmission.Plan)
    (advanced : List (Complete.Rounds.Entry (Complete.Step.family plan)) × List Receipt) : Term :=
  .application "StepAdvanced" [encodeList (entryTerm plan) advanced.1,
    encodeList ScopedRuleJobReadoutExecution.receiptTerm advanced.2]

@[metta_head "gslt:step:advance-all"]
theorem step_advance_all_returns (state : State) (table : List (String × TypeExpr))
    (tabled : table = plan.snapshot.free.entriesOn footprint) (scope : StepScope plan source footprint) :
    ∀ entries : List (Complete.Rounds.Entry (Complete.Step.family plan)),
      (∀ entry ∈ entries, LaneReady plan bound expected source footprint entry) →
      PureReturns runtime [] state
        (apply "gslt:step:advance-all" [planValue plan table bound expected, patternValue source,
          encoded (encodeList (entryTerm plan) entries)])
        state (encoded (advancedAllTerm plan
          (entries.map fun entry =>
              (Complete.Rounds.advance (Complete.Step.family plan) (Complete.Step.lift plan bound expected) entry).1,
            entries.flatMap fun entry =>
              (Complete.Rounds.advance (Complete.Step.family plan) (Complete.Step.lift plan bound expected) entry).2)))
  | [], _ => by
    metta_call complete_checked
    metta_eval unfolding [encodeList, advancedAllTerm]
  | entry :: rest, ready => by
    have head := step_advance_returns state table tabled scope entry (ready entry (by simp))
    have tail := step_advance_all_returns state table tabled scope rest
      (fun other member => ready other (by simp [member]))
    have joined := complete_append_returns ScopedRuleJobReadoutExecution.receiptTerm state
      (Complete.Rounds.advance (Complete.Step.family plan) (Complete.Step.lift plan bound expected) entry).2
      (rest.flatMap fun entry =>
        (Complete.Rounds.advance (Complete.Step.family plan) (Complete.Step.lift plan bound expected) entry).2)
    complete_eval [head, tail, joined] unfolding [encodeList, advancedAllTerm, advancedTerm, List.map_cons, List.flatMap_cons]

variable (plan bound expected source footprint) in
/-- Every lane of a step state is ready. -/
def StepReady (search : Complete.Step.State plan) : Prop :=
  ∀ entry ∈ search.entries, LaneReady plan bound expected source footprint entry

theorem step_ready_round (scope : StepScope plan source footprint) {search : Complete.Step.State plan}
    (ready : StepReady plan bound expected source footprint search) :
    StepReady plan bound expected source footprint
      (Complete.Rounds.round (Complete.Step.family plan) (Complete.Step.lift plan bound expected) search) := by
  intro entry member
  obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
  exact lane_ready_advance scope (ready original inside)

theorem step_ready_begin (scope : StepScope plan source footprint) :
    StepReady plan bound expected source footprint (Complete.Step.begin plan bound expected source) := by
  intro entry member
  obtain ⟨job, listed, rfl⟩ := List.mem_map.mp member
  have licensed := (jobs_spec plan bound expected source job).mp listed
  exact ⟨licensed, Complete.Deep.start_good _, Complete.Deep.start_covered (root_footprinted licensed scope)⟩

@[metta_head "gslt:step:round"]
theorem step_round_returns (state : State) (table : List (String × TypeExpr))
    (tabled : table = plan.snapshot.free.entriesOn footprint) (scope : StepScope plan source footprint)
    (search : Complete.Step.State plan) (ready : StepReady plan bound expected source footprint search) :
    PureReturns runtime [] state
      (apply "gslt:step:round" [planValue plan table bound expected, patternValue source,
        encoded (stepStateTerm plan search)])
      state (encoded (stepStateTerm plan
        (Complete.Rounds.round (Complete.Step.family plan) (Complete.Step.lift plan bound expected) search))) := by
  obtain ⟨entries, log⟩ := search
  have advanced := step_advance_all_returns state table tabled scope entries ready
  have grown := complete_append_returns ScopedRuleJobReadoutExecution.receiptTerm state log
    (entries.flatMap fun entry =>
      (Complete.Rounds.advance (Complete.Step.family plan) (Complete.Step.lift plan bound expected) entry).2)
  complete_eval [advanced, grown] unfolding [stepStateTerm, advancedAllTerm, Complete.Rounds.round]

@[metta_head "gslt:step:rounds"]
theorem step_rounds_returns (state : State) (table : List (String × TypeExpr))
    (tabled : table = plan.snapshot.free.entriesOn footprint) (scope : StepScope plan source footprint) :
    ∀ (work : Nat) (search : Complete.Step.State plan), StepReady plan bound expected source footprint search →
      PureReturns runtime [] state
        (apply "gslt:step:rounds" [planValue plan table bound expected, patternValue source, number work,
          encoded (stepStateTerm plan search)])
        state (encoded (stepStateTerm plan (Complete.Step.rounds plan bound expected work search)))
  | 0, search, _ => by
    metta_call complete_checked
    metta_eval unfolding [Complete.Step.rounds, Complete.Rounds.rounds]
  | work + 1, search, ready => by
    have once := step_round_returns state table tabled scope search ready
    have later := step_rounds_returns state table tabled scope work
      (Complete.Rounds.round (Complete.Step.family plan) (Complete.Step.lift plan bound expected) search)
      (step_ready_round scope ready)
    complete_eval [once, later] unfolding [Complete.Step.rounds, Complete.Rounds.rounds]

@[metta_head "gslt:step:entries-complete"]
theorem step_entries_complete_returns (state : State) :
    ∀ entries : List (Complete.Rounds.Entry (Complete.Step.family plan)),
      PureReturns runtime [] state
        (apply "gslt:step:entries-complete" [admittedValue plan, encoded (encodeList (entryTerm plan) entries)])
        state (Effects.boolean (entries.all fun entry => entry.2.complete))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | ⟨job, deep⟩ :: rest => by
    have family := step_family_returns plan state job
    have done := deep_complete_returns (rootWire (Complete.Step.request plan job)) state deep
    have later := step_entries_complete_returns state rest
    cases finished : deep.complete
    · complete_eval [family, done] unfolding [encodeList, entryTerm, rootWire, finished, List.all_cons]
    · complete_eval [family, done, later] unfolding [encodeList, entryTerm, rootWire, finished, List.all_cons]

/-- The readout of a step state: its log, and whether every lane is complete. -/
def stepReadoutValue (plan : GeneralExecutionAdmission.Plan) (search : Complete.Step.State plan) : Atom :=
  .expression [.symbol "StepReadout", encoded (encodeList ScopedRuleJobReadoutExecution.receiptTerm search.log),
    Effects.boolean (Complete.Rounds.complete (Complete.Step.family plan) search)]

@[metta_head "gslt:step:readout"]
theorem step_readout_returns (state : State) (table : List (String × TypeExpr)) (search : Complete.Step.State plan) :
    PureReturns runtime [] state
      (apply "gslt:step:readout" [planValue plan table bound expected, encoded (stepStateTerm plan search)])
      state (stepReadoutValue plan search) := by
  obtain ⟨entries, log⟩ := search
  have complete := step_entries_complete_returns (plan := plan) state entries
  complete_eval [complete] unfolding [planValue, CompletePlanWire.planTerm, stepStateTerm, stepReadoutValue,
    admittedValue, Complete.Rounds.complete]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
