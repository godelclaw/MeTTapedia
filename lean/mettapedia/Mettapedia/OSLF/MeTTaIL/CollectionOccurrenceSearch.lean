import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceCoverage
import Mettapedia.Machines.ResumableSearchRunner
import Mettapedia.OSLF.MeTTaIL.Complete.Graph

/-!
# Retained nested collection execution through the shared search interface

The public search operations use the actual joint matcher/continuation
machine. Receipts retain their complete origin and history; successor states
are committed to the built-in collection canonical form. Status reads both
retained matching and conditional work, including unresolved depth cutoffs.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CanonicalBags CollectionOccurrenceBatch
open Mettapedia.Machines.ResumableSearchRunner

structure Run (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr) where
  source : Pattern
  state : CollectionOccurrenceMachine.State plan bound expected (canon source)

def status {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr}
    (run : Run plan bound expected) : Status :=
  if run.state.matchers.all (fun lane => RecursiveCollectionMachine.complete lane.state) &&
      run.state.batch.frames.all (fun frame => frame.state.agenda.isEmpty) then
    if run.state.batch.frames.all (fun frame => frame.state.unresolved.isEmpty)
    then .complete else .blocked
  else .pending

def search (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (depth : Nat) : Search Pattern (Run plan bound expected) GeneralRuleJobs.Receipt where
  run source work := ⟨source, CollectionOccurrenceMachine.run depth work
    (CollectionOccurrenceMachine.begin plan bound expected (canon source))⟩
  resume run extra := ⟨run.source, CollectionOccurrenceMachine.run depth extra run.state⟩
  publication run := run.state.batch.log.filterMap (fun packet => packet.finish? plan bound expected)
  status := status
  target receipt := canon receipt.target
  Valid source receipt := (Complete.Presented.gslt plan bound expected).Step source (canon receipt.target)

/-- Keep the actual allocation origin alongside each finished receipt. This
readout chooses no logical derivation identity and performs no aggregation. -/
def publicationWithOrigins {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (run : Run plan bound expected) :
    List ((CollectionOccurrenceHandoff.Job × RecursiveCollectionMachine.Answer × List GeneralPremise.Event) ×
      GeneralRuleJobs.Receipt) :=
  run.state.batch.log.filterMap fun packet =>
    (packet.finish? plan bound expected).map (fun receipt => (packet.allocationOrigin, receipt))

theorem publicationWithOrigins_forgets {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (depth : Nat) (run : Run plan bound expected) :
    (publicationWithOrigins run).map Prod.snd = (search plan bound expected depth).publication run := by
  simp only [publicationWithOrigins, search, List.map_filterMap]
  apply List.filterMap_congr
  intro packet member
  cases packet.finish? plan bound expected <;> rfl

theorem publicationWithOrigins_length {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (depth : Nat) (run : Run plan bound expected) :
    (publicationWithOrigins run).length = ((search plan bound expected depth).publication run).length := by
  rw [← publicationWithOrigins_forgets depth run, List.length_map]

private theorem status_complete {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (run : Run plan bound expected) :
    status run = .complete ↔
      run.state.matchers.all (fun lane => RecursiveCollectionMachine.complete lane.state) = true ∧
      run.state.batch.frames.all (fun frame => frame.state.agenda.isEmpty) = true ∧
      run.state.batch.frames.all (fun frame => frame.state.unresolved.isEmpty) = true := by
  unfold status
  split
  · split <;> simp_all [Bool.and_eq_true]
  · rename_i missing
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨matching, idle, _⟩
      exact False.elim (missing (by simp only [Bool.and_eq_true]; exact ⟨matching, idle⟩))

private theorem idle_frame {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (frame : Frame plan bound expected source)
    (idle : frame.state.agenda = []) : Frame.run 1 frame = frame := by
  have same : RecursiveCollectionContinuation.run frame.allocation.request 1 frame.state = frame.state := by
    change GeneralPremise.Scheduler.run _ 1 frame.state = frame.state
    simp only [GeneralPremise.Scheduler.run, GeneralPremise.Scheduler.tick_idle _ _ idle]
  change { frame with state := RecursiveCollectionContinuation.run _ 1 frame.state } = frame
  rw [same]

private theorem drained_round {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (depth : Nat)
    (state : CollectionOccurrenceMachine.State plan bound expected source)
    (matching : ∀ lane ∈ state.matchers, RecursiveCollectionMachine.complete lane.state = true)
    (idle : ∀ frame ∈ state.batch.frames, frame.state.agenda = []) :
    (CollectionOccurrenceMachine.round depth state).batch = state.batch ∧
      ∀ lane ∈ (CollectionOccurrenceMachine.round depth state).matchers,
        RecursiveCollectionMachine.complete lane.state = true := by
  have fresh : state.matchers.flatMap (CollectionOccurrenceMatcher.Lane.allocations depth) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro lane member
    simp only [CollectionOccurrenceMatcher.Lane.allocations, CollectionOccurrenceMatcher.Lane.fresh,
      RecursiveCollectionMachine.run_complete lane.job.request 1 (matching lane member),
      List.drop_length, CollectionOccurrenceMatcher.collect]
  have retained : state.batch.frames.map (Frame.run 1) = state.batch.frames := by
    calc
      _ = state.batch.frames.map id := List.map_congr_left (fun frame member => idle_frame frame (idle frame member))
      _ = _ := List.map_id _
  have noPublication : state.batch.frames.flatMap Frame.fresh = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro frame member
    simp only [Frame.fresh, idle_frame frame (idle frame member), List.drop_length]
  constructor
  · simp only [CollectionOccurrenceMachine.round, fresh, State.install, List.map_nil, List.append_nil,
      State.round, retained, noPublication]
  · intro lane member
    obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
    simpa only [CollectionOccurrenceMatcher.Lane.resume,
      RecursiveCollectionMachine.run_complete original.job.request 1 (matching original inside)]
      using matching original inside

private theorem drained_run {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (depth work : Nat)
    (state : CollectionOccurrenceMachine.State plan bound expected source)
    (matching : ∀ lane ∈ state.matchers, RecursiveCollectionMachine.complete lane.state = true)
    (idle : ∀ frame ∈ state.batch.frames, frame.state.agenda = []) :
    (CollectionOccurrenceMachine.run depth work state).batch = state.batch ∧
      ∀ lane ∈ (CollectionOccurrenceMachine.run depth work state).matchers,
        RecursiveCollectionMachine.complete lane.state = true := by
  induction work generalizing state with
  | zero => exact ⟨rfl, matching⟩
  | succ work ih =>
    obtain ⟨same, matching'⟩ := drained_round depth state matching idle
    have idle' : ∀ frame ∈ (CollectionOccurrenceMachine.round depth state).batch.frames,
        frame.state.agenda = [] := by
      rw [same]
      exact idle
    obtain ⟨same', matching''⟩ := ih _ matching' idle'
    exact ⟨same'.trans same, matching''⟩

/-- Completion is stable for the actual retained machine. Exhausted matcher
lanes install no new allocations, idle continuations publish no suffix, and
the unresolved-obligation check remains in force after resumption. -/
theorem search_stable (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (depth : Nat) : Complete.Settled.Stable (search plan bound expected depth) := by
  intro run work done
  have ready := (status_complete run).mp done
  have idle : ∀ frame ∈ run.state.batch.frames, frame.state.agenda = [] := by
    intro frame member
    exact List.isEmpty_iff.mp (List.all_eq_true.mp ready.2.1 frame member)
  obtain ⟨same, matching⟩ := drained_run depth work run.state (List.all_eq_true.mp ready.1) idle
  constructor
  · change (CollectionOccurrenceMachine.run depth work run.state).batch.log.filterMap _ = _
    rw [same]
    rfl
  · apply (status_complete _).mpr
    refine ⟨List.all_eq_true.mpr matching, ?_, ?_⟩
    · simpa only [search, same] using ready.2.1
    · simpa only [search, same] using ready.2.2

theorem search_lawful (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (depth : Nat) : (search plan bound expected depth).Lawful where
  resume_run := by
    intro source first extra
    simp only [search, CollectionOccurrenceMachine.run_add]
  publication_prefix := by
    intro source first extra
    simp only [search, CollectionOccurrenceMachine.run_add]
    exact (CollectionOccurrenceMachine.log_prefix depth extra _).filterMap _
  sound := by
    intro source work receipt member
    obtain ⟨packet, logged, finished⟩ := List.mem_filterMap.mp member
    obtain ⟨representative, original, before, valid, after⟩ :=
      CollectionOccurrenceMachine.publication_source_sound depth work logged finished
    exact ⟨representative, original,
      .trans _ _ _ (Complete.Presented.canon_equiv plan bound expected source) before,
      valid, .trans _ _ _ after (Complete.Presented.canon_equiv plan bound expected receipt.target)⟩

/-- Source coverage for the shared five-operation search. Its continuation
depth is fixed in advance: the admitted input guard histories have depth zero. The
equivalence concerns successor classes, with raw receipts still available
for separately declared occurrence and provenance observations. -/
theorem presented_iff_published {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr} {source target : Pattern}
    (checked : CollectionOccurrenceMachine.checkGuardFragment plan = true)
    (noEquations : plan.equations = [])
    (noLaws : Complete.Normalized.laws plan = [])
    (noExtrusions : Complete.Normalized.extrusions plan = []) (depth : Nat) :
    (Complete.Presented.gslt plan bound expected).Step source target ↔
      ∃ work receipt, receipt ∈ (search plan bound expected depth).publication
          ((search plan bound expected depth).run source work) ∧ Same target receipt.target := by
  rw [CollectionOccurrenceMachine.presented_iff_published checked noEquations noLaws noExtrusions depth]
  constructor
  · rintro ⟨work, packet, receipt, logged, finished, same⟩
    exact ⟨work, receipt, List.mem_filterMap.mpr ⟨packet, logged, finished⟩, same⟩
  · rintro ⟨work, receipt, published, same⟩
    obtain ⟨packet, logged, finished⟩ := List.mem_filterMap.mp published
    exact ⟨work, packet, receipt, logged, finished, same⟩

/-- Every outgoing source step from an explored node has a receipt-bearing
edge once the generic explorer settles. This is coverage over the explored
reachable universe; it supplies no global incoming-coverage obligation. -/
theorem settled_edges_cover_steps {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr}
    (checked : CollectionOccurrenceMachine.checkGuardFragment plan = true)
    (noEquations : plan.equations = [])
    (noLaws : Complete.Normalized.laws plan = [])
    (noExtrusions : Complete.Normalized.extrusions plan = [])
    (depth : Nat) (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (search plan bound expected depth)
      (Complete.Explore.explore (search plan bound expected depth) source work) = true) :
    ∀ node ∈ (Complete.Explore.explore (search plan bound expected depth) source work).nodes,
      ∀ target, (Complete.Presented.gslt plan bound expected).Step node.state target →
        ∃ receipt target', (node.state, receipt, target') ∈ Complete.Graph.edges
            (search plan bound expected depth)
            (Complete.Explore.explore (search plan bound expected depth) source work) ∧
          Same target target' := by
  intro node member target stepped
  obtain ⟨rounds, receipt, published, same⟩ :=
    (presented_iff_published checked noEquations noLaws noExtrusions depth).mp stepped
  have edge := Complete.Graph.edges_complete (S := search plan bound expected depth)
    (search_lawful plan bound expected depth) (search_stable plan bound expected depth)
    source work done node member rounds receipt published
  refine ⟨receipt, canon receipt.target, edge, ?_⟩
  simpa only [Same, canon_idempotent] using same

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch
