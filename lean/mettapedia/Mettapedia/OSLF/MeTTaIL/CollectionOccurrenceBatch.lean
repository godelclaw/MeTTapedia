import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceContinuation
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionTraceAccounting
import Mathlib.Data.List.Perm.Basic

/-!
# Retained conditional allocations at typed collection occurrences

Every frame owns its original occurrence, recursive allocation and scheduled
continuation. The chronological log drains each frame's own publication
suffix. Its permutation account preserves complete packets and multiplicity;
it identifies neither logical derivations nor repeated validation evidence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching GeneralPremise
open CollectionOccurrenceHandoff RecursiveCollectionHandoff

variable (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern)

structure Allocation where
  job : Job
  licensed : job.Valid plan bound expected source
  answer : RecursiveCollectionMachine.Answer
  prepared : Prepared
  matching : prepared.Valid job.request answer
  depth : Nat
  request : RecursiveCollectionContinuation.Request
  issued : CollectionOccurrenceContinuation.request? plan bound expected source job licensed
    answer prepared matching depth = some request

variable {plan bound expected source}

theorem Allocation.request_origin (allocation : Allocation plan bound expected source) :
    allocation.request.environment = GeneralPlanEnvironment.environment plan ∧
      allocation.request.prepared = allocation.prepared := by
  have issued := allocation.issued
  unfold CollectionOccurrenceContinuation.request? at issued
  dsimp only at issued
  split at issued
  · split at issued
    · have same := Option.some.inj issued
      rw [← same]
      exact ⟨rfl, rfl⟩
    · cases issued
  · cases issued

/-- Only published recursive matches enter preparation and the existing
local typing/admission checks. No premise outcome is supplied here. -/
def allocate? (job : Job) (licensed : job.Valid plan bound expected source)
    (work : Nat) (answer : RecursiveCollectionMachine.Answer)
    (published : answer ∈ (RecursiveCollectionMachine.run job.request work
      (RecursiveCollectionMachine.start job.request)).answers) (depth : Nat) :
    Option (Allocation plan bound expected source) :=
  match made : prepare job.request answer with
  | none => none
  | some prepared =>
    let matching := prepare_valid job.request answer
      (RecursiveCollectionMachine.published_trace_valid job.request work published) made
    match issued : CollectionOccurrenceContinuation.request? plan bound expected source
        job licensed answer prepared matching depth with
    | none => none
    | some request => some ⟨job, licensed, answer, prepared, matching, depth, request, issued⟩

structure Frame (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) where
  allocation : Allocation plan bound expected source
  state : RecursiveCollectionContinuation.State allocation.request

structure Publication where
  job : Job
  answer : RecursiveCollectionMachine.Answer
  prepared : Prepared
  outcome : Complete.DeepRoot.Firing

/-- Operational provenance before the ordinary receipt projection. Equal
ordinary receipts may come from different recursive allocations; their
allocation traces remain available independently of result aggregation. -/
def Publication.allocationOrigin (packet : Publication) :
    Job × RecursiveCollectionMachine.Answer × List GeneralPremise.Event :=
  (packet.job, packet.answer, packet.outcome.history)

def tag (allocation : Allocation plan bound expected source)
    (outcome : Complete.DeepRoot.Firing) : Publication :=
  ⟨allocation.job, allocation.answer, allocation.prepared, outcome⟩

def Frame.initial (allocation : Allocation plan bound expected source) :
    Frame plan bound expected source :=
  ⟨allocation, RecursiveCollectionContinuation.start allocation.request⟩

def Frame.run (work : Nat) (frame : Frame plan bound expected source) :
    Frame plan bound expected source :=
  { frame with state := RecursiveCollectionContinuation.run frame.allocation.request work frame.state }

def Frame.publication (frame : Frame plan bound expected source) : List Publication :=
  (RecursiveCollectionContinuation.publication frame.allocation.request frame.state).map
    (tag frame.allocation)

theorem Frame.initial_publication (allocation : Allocation plan bound expected source) :
    (Frame.initial allocation).publication = [] := by
  simp only [Frame.publication, Frame.initial, RecursiveCollectionContinuation.publication,
    RecursiveCollectionContinuation.start_no_early_answers, List.filterMap_nil, List.map_nil]

theorem Frame.run_add (first extra : Nat) (frame : Frame plan bound expected source) :
    Frame.run (first + extra) frame = Frame.run extra (Frame.run first frame) := by
  cases frame
  simp only [Frame.run, RecursiveCollectionContinuation.run_add]

theorem Frame.publication_prefix (frame : Frame plan bound expected source) (work : Nat) :
    frame.publication <+: (Frame.run work frame).publication :=
  (RecursiveCollectionContinuation.publication_prefix frame.allocation.request frame.state work).map _

def Frame.fresh (frame : Frame plan bound expected source) : List Publication :=
  (Frame.run 1 frame).publication.drop frame.publication.length

theorem Frame.fresh_balance (frame : Frame plan bound expected source) :
    frame.publication ++ frame.fresh = (Frame.run 1 frame).publication := by
  have grown := Frame.publication_prefix frame 1
  unfold Frame.fresh
  calc
    _ = (Frame.run 1 frame).publication.take frame.publication.length ++
        (Frame.run 1 frame).publication.drop frame.publication.length :=
      congrArg (fun front => front ++ (Frame.run 1 frame).publication.drop frame.publication.length)
        (List.prefix_iff_eq_take.mp grown)
    _ = _ := List.take_append_drop _ _

/-- A published packet retains its source allocation. Finishing it uses the
original rule-job operation, with the complete premise history. -/
def Publication.finish? (packet : Publication) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) : Option GeneralRuleJobs.Receipt :=
  CollectionOccurrenceContinuation.finish? plan bound expected packet.job packet.prepared packet.outcome

theorem Frame.publication_source_sound (frame : Frame plan bound expected source)
    {packet : Publication} (published : packet ∈ frame.publication)
    {receipt : GeneralRuleJobs.Receipt}
    (finished : packet.finish? plan bound expected = some receipt) :
    (Complete.Presented.gslt plan bound expected).Step source receipt.target := by
  obtain ⟨outcome, member, same⟩ := List.mem_map.mp published
  cases same
  exact CollectionOccurrenceContinuation.finish_source_step plan bound expected source
    frame.allocation.job frame.allocation.licensed frame.allocation.answer frame.allocation.prepared
    frame.allocation.matching frame.allocation.depth frame.allocation.issued frame.state member finished

theorem Frame.source_coverage (allocation : Allocation plan bound expected source)
    (trace : List GeneralScopedMatchMachine.BagChoice) (completed : Assignment)
    (history : List Event) (target : Pattern)
    (held : RootFiring allocation.request.environment allocation.request.bound allocation.request.type
      allocation.request.prepared.source allocation.request.index trace
      allocation.request.prepared.ordinary.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ allocation.request.depth) :
    ∃ work, tag allocation
        ⟨allocation.request.prepared.ordinary.trace, allocation.request.prepared.ordinary.assignment,
          completed, history, target⟩ ∈ (Frame.run work (Frame.initial allocation)).publication := by
  obtain ⟨work, published⟩ := RecursiveCollectionContinuation.source_coverage allocation.request
    trace completed history target held bounded
  exact ⟨work, List.mem_map_of_mem published⟩

structure State (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) where
  frames : List (Frame plan bound expected source)
  log : List Publication

def State.begin (allocations : List (Allocation plan bound expected source)) :
    State plan bound expected source :=
  ⟨allocations.map Frame.initial, []⟩

def State.round (state : State plan bound expected source) : State plan bound expected source :=
  ⟨state.frames.map (Frame.run 1), state.log ++ state.frames.flatMap Frame.fresh⟩

def State.run : Nat → State plan bound expected source → State plan bound expected source
  | 0, state => state
  | work + 1, state => State.run work state.round

def State.Balanced (state : State plan bound expected source) : Prop :=
  state.log.Perm (state.frames.flatMap Frame.publication)

theorem State.begin_balanced (allocations : List (Allocation plan bound expected source)) :
    (State.begin allocations).Balanced := by
  have empty : (allocations.map Frame.initial).flatMap Frame.publication = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro frame member
    obtain ⟨allocation, _, rfl⟩ := List.mem_map.mp member
    exact Frame.initial_publication allocation
  change [].Perm ((allocations.map Frame.initial).flatMap Frame.publication)
  rw [empty]

theorem State.round_balanced {state : State plan bound expected source}
    (balanced : state.Balanced) : state.round.Balanced := by
  apply (balanced.append_right _).trans
  apply (List.flatMap_append_perm state.frames Frame.publication Frame.fresh).trans
  change (state.frames.flatMap fun frame => frame.publication ++ frame.fresh).Perm
    ((state.frames.map (Frame.run 1)).flatMap Frame.publication)
  rw [List.flatMap_map]
  apply List.Perm.of_eq
  apply List.flatMap_congr
  intro frame _
  exact Frame.fresh_balance frame

theorem State.run_balanced (work : Nat) {state : State plan bound expected source}
    (balanced : state.Balanced) : (State.run work state).Balanced := by
  induction work generalizing state with
  | zero => exact balanced
  | succ work ih => exact ih (State.round_balanced balanced)

theorem State.run_add (first extra : Nat) (state : State plan bound expected source) :
    State.run (first + extra) state = State.run extra (State.run first state) := by
  induction first generalizing state with
  | zero => simp only [State.run, Nat.zero_add]
  | succ first ih => simpa only [State.run, Nat.succ_add] using ih state.round

theorem State.run_frames (work : Nat) (state : State plan bound expected source) :
    (State.run work state).frames = state.frames.map (Frame.run work) := by
  induction work generalizing state with
  | zero =>
    have idle : (Frame.run 0 : Frame plan bound expected source → _) = id := by
      funext frame
      cases frame
      rfl
    change state.frames = state.frames.map (Frame.run 0)
    rw [idle, List.map_id]
  | succ work ih =>
    simpa only [State.run, ih, State.round, List.map_map, Function.comp_def, Nat.add_comm 1 work] using
      congrArg (List.map · state.frames) (funext fun frame => Frame.run_add 1 work frame).symm

theorem State.log_prefix (work : Nat) (state : State plan bound expected source) :
    state.log <+: (State.run work state).log := by
  induction work generalizing state with
  | zero => exact List.prefix_refl _
  | succ work ih => exact (List.prefix_append _ _).trans (ih state.round)

theorem State.publication_source_sound (work : Nat)
    (allocations : List (Allocation plan bound expected source))
    {packet : Publication} (published : packet ∈ (State.run work (State.begin allocations)).log)
    {receipt : GeneralRuleJobs.Receipt}
    (finished : packet.finish? plan bound expected = some receipt) :
    (Complete.Presented.gslt plan bound expected).Step source receipt.target := by
  have accounted := State.run_balanced work (State.begin_balanced allocations)
  obtain ⟨frame, _, present⟩ := List.mem_flatMap.mp (accounted.subset published)
  exact Frame.publication_source_sound frame present finished

theorem State.source_coverage (allocations : List (Allocation plan bound expected source))
    (allocation : Allocation plan bound expected source) (member : allocation ∈ allocations)
    (trace : List GeneralScopedMatchMachine.BagChoice) (completed : Assignment)
    (history : List Event) (target : Pattern)
    (held : RootFiring allocation.request.environment allocation.request.bound allocation.request.type
      allocation.request.prepared.source allocation.request.index trace
      allocation.request.prepared.ordinary.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ allocation.request.depth) :
    ∃ work, tag allocation
        ⟨allocation.request.prepared.ordinary.trace, allocation.request.prepared.ordinary.assignment,
          completed, history, target⟩ ∈ (State.run work (State.begin allocations)).log := by
  obtain ⟨work, present⟩ := Frame.source_coverage allocation trace completed history target held bounded
  have retained : Frame.run work (Frame.initial allocation) ∈
      (State.run work (State.begin allocations)).frames := by
    rw [State.run_frames]
    exact List.mem_map_of_mem (List.mem_map_of_mem member)
  exact ⟨work, (State.run_balanced work (State.begin_balanced allocations)).symm.subset
    (List.mem_flatMap.mpr ⟨_, retained, present⟩)⟩

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch
