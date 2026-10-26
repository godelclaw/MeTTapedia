import Mettapedia.GSLT.Dynamics.ProvenanceInterpretation
import Mettapedia.GSLT.Dynamics.ObservationDiscipline
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

structure Run (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (matcher : GeneralPremise.MatchingExecution := GeneralPremise.MatchingExecution.ordinary) where
  source : Pattern
  state : CollectionOccurrenceMachine.State plan bound expected (canon source) matcher

/-- The existing source traversal starts with retained lanes and no installed continuations. -/
def beginWith (matcher : GeneralPremise.MatchingExecution) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) : Run plan bound expected matcher :=
  ⟨source, CollectionOccurrenceMachine.beginWith matcher plan bound expected (canon source)⟩

/-- A selected seed profile advances the same joint machine. No source-validity policy is inferred. -/
def runWith {matcher : GeneralPremise.MatchingExecution} (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr)
    (profile : (source : Pattern) → SeedProfile matcher plan bound expected (canon source))
    (depth : Nat) (source : Pattern) (work : Nat) : Run plan bound expected matcher :=
  ⟨source, CollectionOccurrenceMachine.runWith (profile source) depth work
    (CollectionOccurrenceMachine.beginWith matcher plan bound expected (canon source))⟩

def resumeWith {matcher : GeneralPremise.MatchingExecution} {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr}
    (profile : (source : Pattern) → SeedProfile matcher plan bound expected (canon source))
    (depth : Nat) (run : Run plan bound expected matcher) (extra : Nat) : Run plan bound expected matcher :=
  ⟨run.source, CollectionOccurrenceMachine.runWith (profile run.source) depth extra run.state⟩

/-- A prefix receipt projection selects its finisher explicitly and retains no completion claim. -/
def publicationWith {matcher : GeneralPremise.MatchingExecution} {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr}
    (finish : Publication matcher.Choice → Option (GeneralRuleJobs.Receipt matcher.Choice))
    (run : Run plan bound expected matcher) : List (GeneralRuleJobs.Receipt matcher.Choice) :=
  run.state.batch.log.filterMap finish

/-- Full packets remain paired with their finished receipts before any declared identity is applied. -/
def committedWith {matcher : GeneralPremise.MatchingExecution} {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr}
    (finish : Publication matcher.Choice → Option (GeneralRuleJobs.Receipt matcher.Choice))
    (run : Run plan bound expected matcher) : List (CollectionCommittedObservation.Committed matcher.Choice) :=
  CollectionCommittedObservation.retainedWith finish run.state.batch.log

def statusWith {matcher : GeneralPremise.MatchingExecution} {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr}
    (run : Run plan bound expected matcher) : Status :=
  if run.state.matchers.all (fun lane => RecursiveCollectionMachine.complete lane.state) &&
      run.state.batch.frames.all (fun frame => frame.state.agenda.isEmpty) then
    if run.state.batch.frames.all (fun frame => frame.state.unresolved.isEmpty)
    then .complete else .blocked
  else .pending


def status {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr}
    (run : Run plan bound expected) : Status := statusWith run

/-- Resuming preserves the complete retained machine and chronological publication account. -/
theorem resumeWith_runWith {matcher : GeneralPremise.MatchingExecution} (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr)
    (profile : (source : Pattern) → SeedProfile matcher plan bound expected (canon source))
    (depth : Nat) (source : Pattern) (first extra : Nat) :
    resumeWith profile depth (runWith plan bound expected profile depth source first) extra =
      runWith plan bound expected profile depth source (first + extra) := by
  simp only [resumeWith, runWith, CollectionOccurrenceMachine.runWith_add]

theorem resumeWith_log_prefix {matcher : GeneralPremise.MatchingExecution} {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr}
    (profile : (source : Pattern) → SeedProfile matcher plan bound expected (canon source))
    (depth : Nat) (run : Run plan bound expected matcher) (extra : Nat) :
    run.state.batch.log <+: (resumeWith profile depth run extra).state.batch.log :=
  CollectionOccurrenceMachine.runWith_log_prefix (profile run.source) depth extra run.state

theorem committedWith_forgets {matcher : GeneralPremise.MatchingExecution} {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr}
    (finish : Publication matcher.Choice → Option (GeneralRuleJobs.Receipt matcher.Choice))
    (run : Run plan bound expected matcher) :
    (committedWith finish run).map Prod.snd = publicationWith finish run := by
  simp only [committedWith, publicationWith, CollectionCommittedObservation.retainedWith, List.map_filterMap]
  apply List.filterMap_congr
  intro packet _
  simp only [CollectionCommittedObservation.commitWith?]
  cases finish packet <;> rfl

theorem resumeWith_committed_prefix {matcher : GeneralPremise.MatchingExecution} {plan : GeneralExecutionAdmission.Plan}
    {bound : List TypeExpr} {expected : TypeExpr}
    (profile : (source : Pattern) → SeedProfile matcher plan bound expected (canon source))
    (finish : Publication matcher.Choice → Option (GeneralRuleJobs.Receipt matcher.Choice))
    (depth : Nat) (run : Run plan bound expected matcher) (extra : Nat) :
    committedWith finish run <+: committedWith finish (resumeWith profile depth run extra) :=
  (resumeWith_log_prefix profile depth run extra).filterMap _

def search (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (depth : Nat) : Search Pattern (Run plan bound expected) GeneralRuleJobs.Receipt where
  run source work := ⟨source, CollectionOccurrenceMachine.run depth work
    (CollectionOccurrenceMachine.begin plan bound expected (canon source))⟩
  resume run extra := ⟨run.source, CollectionOccurrenceMachine.run depth extra run.state⟩
  publication run := run.state.batch.log.filterMap (fun packet => packet.finish? plan bound expected)
  status := status
  target receipt := canon receipt.target
  Valid source receipt := (Complete.Presented.gslt plan bound expected).Step source (canon receipt.target)


theorem runWith_ordinary (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (depth : Nat) (source : Pattern) (work : Nat) :
    runWith plan bound expected (fun source => ordinarySeedProfile plan bound expected (canon source)) depth source work =
      (search plan bound expected depth).run source work := rfl

theorem resumeWith_ordinary {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (depth : Nat) (run : Run plan bound expected) (extra : Nat) :
    resumeWith (fun source => ordinarySeedProfile plan bound expected (canon source)) depth run extra =
      (search plan bound expected depth).resume run extra := rfl

theorem publicationWith_ordinary {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (depth : Nat) (run : Run plan bound expected) :
    publicationWith (fun packet => packet.finish? plan bound expected) run =
      (search plan bound expected depth).publication run := rfl

theorem statusWith_ordinary {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (run : Run plan bound expected) : statusWith run = status run := rfl

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

/-- A prefix readout retaining every committed packet before any declared
identity or result aggregation is chosen. Completion remains separate. -/
def publicationWithPackets {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (run : Run plan bound expected) :
    List CollectionCommittedObservation.Committed :=
  CollectionCommittedObservation.retained plan bound expected run.state.batch.log

theorem publicationWithPackets_forgets {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (depth : Nat) (run : Run plan bound expected) :
    (publicationWithPackets run).map Prod.snd = (search plan bound expected depth).publication run :=
  CollectionCommittedObservation.retained_receipts plan bound expected run.state.batch.log

theorem publicationWithPackets_origins {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (run : Run plan bound expected) :
    (publicationWithPackets run).map (fun committed => (committed.1.allocationOrigin, committed.2)) =
      publicationWithOrigins run := by
  simp only [publicationWithPackets, CollectionCommittedObservation.retained,
    publicationWithOrigins, List.map_filterMap]
  apply List.filterMap_congr
  intro packet _
  simp only [CollectionCommittedObservation.commit?]
  cases packet.finish? plan bound expected <;> rfl

private theorem status_complete {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (run : Run plan bound expected) :
    status run = .complete ↔
      run.state.matchers.all (fun lane => RecursiveCollectionMachine.complete lane.state) = true ∧
      run.state.batch.frames.all (fun frame => frame.state.agenda.isEmpty) = true ∧
      run.state.batch.frames.all (fun frame => frame.state.unresolved.isEmpty) = true := by
  unfold status statusWith
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
  · simp only [CollectionOccurrenceMachine.round, CollectionOccurrenceMachine.roundWith,
      fresh, State.installWith, List.map_nil, List.append_nil, State.round, retained, noPublication]
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


theorem committedWith_ordinary {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (run : Run plan bound expected) :
    committedWith (fun packet => packet.finish? plan bound expected) run = publicationWithPackets run := rfl

/-- Canonical receipts select the original allocation history through the existing declared finisher. -/
theorem committedWith_canonical {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} (run : Run plan bound expected RecursiveCollectionHandoff.canonicalMatchingExecution) :
    committedWith (fun packet => packet.finishCanonical? plan bound expected) run =
      CollectionCommittedObservation.retainedCanonical plan bound expected run.state.batch.log := rfl

#print axioms resumeWith_runWith
#print axioms resumeWith_log_prefix
#print axioms committedWith_forgets
#print axioms resumeWith_committed_prefix
#print axioms runWith_ordinary
#print axioms resumeWith_ordinary
#print axioms publicationWith_ordinary
#print axioms statusWith_ordinary
#print axioms committedWith_ordinary
#print axioms committedWith_canonical
#print axioms search_stable
#print axioms search_lawful
#print axioms presented_iff_published
#print axioms settled_edges_cover_steps

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch

/-! Prefix observations retain their complete committed packets.
These readouts make no enumeration-completion assertion. -/

namespace Mettapedia.OSLF.MeTTaIL.CollectionCommittedObservation

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CanonicalBags
open CollectionOccurrenceBatch GeneralPremise
open Mettapedia.GSLT.Dynamics

noncomputable def declaredProvenance {Key Cause : Type} [DecidableEq Key]
    (identity : Committed → Key) (causes : Key → List Cause)
    (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (packets : List Publication) : MvPolynomial Cause ℕ :=
  ProvenanceInterpretation.provenance
    ((declaredKeys identity plan bound expected packets).toList.map causes)

theorem declaredProvenance_interpretation {Key Cause Value : Type} [DecidableEq Key] [CommSemiring Value]
    (identity : Committed → Key) (causes : Key → List Cause) (valuation : Cause → Value)
    (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (packets : List Publication) :
    MvPolynomial.eval₂ (Nat.castRingHom Value) valuation
      (declaredProvenance identity causes plan bound expected packets) =
      ProvenanceInterpretation.interpSet valuation
        ((declaredKeys identity plan bound expected packets).toList.map causes) :=
  ProvenanceInterpretation.interp_provenance valuation _

/-- A key for the declared validation-only occurrence reading. The snapshot
is fixed. Exact allocation decisions and all nested child matching traces
remain identity data. Provider row positions and freshness checks are validation data in this
reading. Query argument-allocation traces remain in the key. Full validation
witnesses stay in the retained packets. -/
structure AllocationKey where
  selectedRule : Nat
  authoredRule : Nat
  originalSite : GeneralTypedSites.SiteData
  variant : CollectionSelection.SiteVariant
  allocation : RecursiveCollectionMachine.Answer
  ordinaryTrace : List GeneralScopedMatchMachine.BagChoice
  captured : ScopedRuleMatching.Assignment
  completed : ScopedRuleMatching.Assignment
  childHistory : List GeneralPremise.Event
  conclusion : Pattern
  deriving DecidableEq

def allocationKey (committed : Committed) : AllocationKey :=
  let packet := committed.1
  let receipt := committed.2
  ⟨packet.job.origin.ordinal, packet.job.origin.declaration.declarationIndex,
    packet.job.origin.site, packet.job.variant, packet.answer,
    receipt.matcherTrace, receipt.captured, receipt.completed,
    validationHistoryReadout receipt.premiseHistory, canon receipt.target⟩

theorem key_preserves_allocation {first second : Committed}
    (same : allocationKey first = allocationKey second) : first.1.answer = second.1.answer :=
  congrArg AllocationKey.allocation same

theorem different_allocation_distinct {first second : Committed}
    (different : first.1.answer ≠ second.1.answer) : allocationKey first ≠ allocationKey second := by
  intro same
  exact different (key_preserves_allocation same)

theorem different_authored_route_distinct {first second : Committed}
    (different : first.1.job.origin.declaration.declarationIndex ≠
      second.1.job.origin.declaration.declarationIndex) : allocationKey first ≠ allocationKey second := by
  intro same
  exact different (congrArg AllocationKey.authoredRule same)

theorem query_row_revalidation_same_key (packet : Publication) (receipt : GeneralRuleJobs.Receipt)
    (p q first second : Nat) (origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)) :
    allocationKey (packet, {receipt with premiseHistory := [.query p q first origins]}) =
      allocationKey (packet, {receipt with premiseHistory := [.query p q second origins]}) := rfl

theorem query_allocation_distinct_key (packet : Publication) (receipt : GeneralRuleJobs.Receipt)
    (p q row : Nat) (first second : List (Nat × List GeneralScopedMatchMachine.BagChoice))
    (different : first ≠ second) :
    allocationKey (packet, {receipt with premiseHistory := [.query p q row first]}) ≠
      allocationKey (packet, {receipt with premiseHistory := [.query p q row second]}) := by
  intro same
  have history := congrArg AllocationKey.childHistory same
  simp only [allocationKey, validationHistoryReadout, validationEventReadout,
    List.append_nil, List.cons.injEq, GeneralPremise.Event.query.injEq, true_and] at history
  exact different history.1

def allocationKeys (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (packets : List Publication) : Finset AllocationKey :=
  declaredKeys allocationKey plan bound expected packets

/-- Alternative keys may conclude the same value. The value bag retains one
occurrence per declared key, rather than one occurrence per validation row. -/
def allocationBag (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (packets : List Publication) : Multiset Pattern :=
  (allocationKeys plan bound expected packets).val.map AllocationKey.conclusion

def successorStates (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (packets : List Publication) : Finset Pattern :=
  (allocationKeys plan bound expected packets).image AllocationKey.conclusion

theorem facts_actual_targets (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (packets : List Publication) :
    successorStates plan bound expected packets =
      ((retained plan bound expected packets).map fun committed => canon committed.2.target).toFinset := by
  ext target
  simp [successorStates, allocationKeys, declaredKeys, committedKeys, allocationKey]

theorem allocationKeys_perm (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) {first second : List Publication} (same : first.Perm second) :
    allocationKeys plan bound expected first = allocationKeys plan bound expected second :=
  declaredKeys_perm allocationKey plan bound expected same

theorem allocationBag_perm (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) {first second : List Publication} (same : first.Perm second) :
    allocationBag plan bound expected first = allocationBag plan bound expected second := by
  unfold allocationBag
  rw [allocationKeys_perm plan bound expected same]

theorem facts_perm (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) {first second : List Publication} (same : first.Perm second) :
    successorStates plan bound expected first = successorStates plan bound expected second := by
  unfold successorStates
  rw [allocationKeys_perm plan bound expected same]

theorem allocationKeys_append (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (first second : List Publication) :
    allocationKeys plan bound expected (first ++ second) =
      allocationKeys plan bound expected first ∪ allocationKeys plan bound expected second := by
  simp only [allocationKeys, declaredKeys, committedKeys, retained_append, List.map_append, List.toFinset_append]

/-- Revalidating a declared occurrence changes neither observation. The
condition concerns the declared key, not raw packet or endpoint equality. -/
theorem validation_replay_invariant (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (earlier validation : List Publication)
    (already : allocationKeys plan bound expected validation ⊆
      allocationKeys plan bound expected earlier) :
    allocationBag plan bound expected (earlier ++ validation) =
        allocationBag plan bound expected earlier ∧
      successorStates plan bound expected (earlier ++ validation) = successorStates plan bound expected earlier := by
  have same : allocationKeys plan bound expected (earlier ++ validation) =
      allocationKeys plan bound expected earlier := by
    rw [allocationKeys_append, Finset.union_eq_left.mpr already]
  simp only [allocationBag, successorStates, same, and_self]

theorem balanced_observations {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {state : State plan bound expected source}
    (balanced : state.Balanced) :
    allocationBag plan bound expected state.log =
        allocationBag plan bound expected (state.frames.flatMap Frame.publication) ∧
      successorStates plan bound expected state.log =
        successorStates plan bound expected (state.frames.flatMap Frame.publication) :=
  ⟨allocationBag_perm plan bound expected balanced, facts_perm plan bound expected balanced⟩

theorem run_observation_account {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (depth work : Nat) :
    let state := CollectionOccurrenceMachine.run depth work
      (CollectionOccurrenceMachine.begin plan bound expected source)
    allocationBag plan bound expected state.batch.log =
        allocationBag plan bound expected (state.batch.frames.flatMap Frame.publication) ∧
      successorStates plan bound expected state.batch.log =
        successorStates plan bound expected (state.batch.frames.flatMap Frame.publication) :=
  balanced_observations
    (CollectionOccurrenceMachine.run_invariant depth work
      (CollectionOccurrenceMachine.begin_invariant depth)).1

theorem resumed_observations {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (depth first extra : Nat)
    (state : CollectionOccurrenceMachine.State plan bound expected source) :
    let whole := CollectionOccurrenceMachine.run depth (first + extra) state
    let resumed := CollectionOccurrenceMachine.run depth extra
      (CollectionOccurrenceMachine.run depth first state)
    retained plan bound expected whole.batch.log = retained plan bound expected resumed.batch.log ∧
      allocationBag plan bound expected whole.batch.log = allocationBag plan bound expected resumed.batch.log ∧
      successorStates plan bound expected whole.batch.log = successorStates plan bound expected resumed.batch.log := by
  simp only [CollectionOccurrenceMachine.run_add, and_self]

def discipline (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr) :
    ObservationDiscipline Publication where
  collection := { Container := List Committed, collect := fun packets => some (retained plan bound expected packets) }
  Value := Finset Pattern × Multiset Pattern
  readout := fun committed =>
    let keys := (committed.map allocationKey).toFinset
    (keys.image AllocationKey.conclusion, keys.val.map AllocationKey.conclusion)

theorem discipline_observe (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (packets : List Publication) :
    (discipline plan bound expected).observe packets =
      some (successorStates plan bound expected packets, allocationBag plan bound expected packets) := rfl

noncomputable def provenance {Cause : Type} (causes : AllocationKey → List Cause)
    (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (packets : List Publication) : MvPolynomial Cause ℕ :=
  ProvenanceInterpretation.provenance
    ((allocationKeys plan bound expected packets).toList.map causes)

theorem provenance_interpretation {Cause S : Type} [CommSemiring S]
    (causes : AllocationKey → List Cause) (valuation : Cause → S)
    (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (packets : List Publication) :
    MvPolynomial.eval₂ (Nat.castRingHom S) valuation
      (provenance causes plan bound expected packets) =
      ProvenanceInterpretation.interpSet valuation
        ((allocationKeys plan bound expected packets).toList.map causes) :=
  ProvenanceInterpretation.interp_provenance valuation _

end Mettapedia.OSLF.MeTTaIL.CollectionCommittedObservation


namespace Mettapedia.OSLF.MeTTaIL.CollectionCommittedObservation
open GeneralPremise

/-- Partial form of the declared validation readout. Erased events contribute no key. -/
def administrativeEvent? {Choice : Type} (policy : QueryIdentity) (event : Event Choice) :
    Option (Event Choice) := (validationEventReadout event policy).head?

theorem administrativeEvent?_toList {Choice : Type} (policy : QueryIdentity) (event : Event Choice) :
    (administrativeEvent? policy event).toList = validationEventReadout event policy := by
  cases event <;> cases policy <;> rfl

/-- The single ordered filterMap projection is exactly the established history policy. -/
theorem administrative_history_filterMap {Choice : Type} (policy : QueryIdentity)
    (history : List (Event Choice)) :
    history.filterMap (administrativeEvent? policy) = validationHistoryReadout history policy := by
  induction history with
  | nil => rfl
  | cons event rest ih =>
    rw [validationHistoryReadout, ← administrativeEvent?_toList]
    cases found : administrativeEvent? policy event <;>
      simp only [List.filterMap_cons, found, Option.toList, List.nil_append, List.cons_append, ih]

theorem administrative_history_append {Choice : Type} (policy : QueryIdentity)
    (first second : List (Event Choice)) :
    validationHistoryReadout (first ++ second) policy =
      validationHistoryReadout first policy ++ validationHistoryReadout second policy := by
  simp only [← administrative_history_filterMap, List.filterMap_append]

theorem query_administration_erases {Choice : Type} (before after : List (Event Choice))
    (premise quantifier row : Nat) (origins : List (Nat × List Choice)) :
    validationHistoryReadout (before ++ .query premise quantifier row origins :: after) .factValidation =
      validationHistoryReadout (before ++ after) .factValidation := by
  simp only [administrative_history_append, validationHistoryReadout, validationEventReadout,
    List.nil_append]

theorem freshness_administration_erases {Choice : Type} (policy : QueryIdentity)
    (before after : List (Event Choice)) (premise quantifier : Nat) (atom : String) (subject : Syntax.Pattern) :
    validationHistoryReadout (before ++ .freshness premise quantifier atom subject :: after) policy =
      validationHistoryReadout (before ++ after) policy := by
  simp only [administrative_history_append, validationHistoryReadout, validationEventReadout,
    List.nil_append]

theorem evidence_query_is_retained {Choice : Type} (premise quantifier row : Nat)
    (origins : List (Nat × List Choice)) :
    administrativeEvent? .evidence (.query premise quantifier row origins) =
      some (.query premise quantifier row origins) := rfl

#print axioms administrativeEvent?_toList
#print axioms administrative_history_filterMap
#print axioms administrative_history_append
#print axioms query_administration_erases
#print axioms freshness_administration_erases
#print axioms evidence_query_is_retained
end Mettapedia.OSLF.MeTTaIL.CollectionCommittedObservation

namespace Mettapedia.OSLF.MeTTaIL.CollectionCommittedObservation

private theorem declared_eraseDups_loop_nodup {Key : Type} [BEq Key] [LawfulBEq Key]
    (keys seen : List Key) (distinct : seen.Nodup) :
    (List.eraseDupsBy.loop (· == ·) keys seen).Nodup := by
  induction keys generalizing seen with
  | nil => simpa only [List.eraseDupsBy.loop, List.nodup_reverse] using distinct
  | cons first rest ih =>
    simp only [List.eraseDupsBy.loop, List.any_beq]
    cases present : seen.contains first
    · apply ih
      simpa using List.nodup_cons.mpr ⟨by simpa using present, distinct⟩
    · exact ih seen distinct

theorem declared_eraseDups_multiset {Key : Type} [DecidableEq Key] [BEq Key] [LawfulBEq Key]
    (keys : List Key) : (keys.eraseDups : Multiset Key) = keys.toFinset.val := by
  have same : keys.eraseDups.toFinset = keys.toFinset := by
    ext key
    simp only [List.mem_toFinset, List.mem_eraseDups]
  have ready := congrArg Finset.val
    (List.toFinset_eq (declared_eraseDups_loop_nodup keys [] (by simp)))
  exact ready.trans (congrArg Finset.val same)

/-- A chronological presentation of the existing declared-key carrier. -/
def orderedCommittedKeys {Choice Key : Type} [DecidableEq Key]
    (identity : Committed Choice → Key) (pairs : List (Committed Choice)) : List Key :=
  (pairs.map identity).eraseDups

theorem orderedCommittedKeys_carrier {Choice Key : Type} [DecidableEq Key]
    (identity : Committed Choice → Key) (pairs : List (Committed Choice)) :
    (orderedCommittedKeys identity pairs : Multiset Key) = (committedKeys identity pairs).val :=
  declared_eraseDups_multiset _

theorem orderedCommittedKeys_bag {Choice Key Value : Type} [DecidableEq Key]
    (identity : Committed Choice → Key) (value : Key → Value) (pairs : List (Committed Choice)) :
    ((orderedCommittedKeys identity pairs).map value : Multiset Value) =
      committedBag identity value pairs := by
  change (orderedCommittedKeys identity pairs : Multiset Key).map value = _
  rw [orderedCommittedKeys_carrier]
  rfl

theorem orderedCommittedKeys_partial_bag {Choice Key Value : Type} [DecidableEq Key]
    (identity : Committed Choice → Key) (value : Key → Option Value) (pairs : List (Committed Choice)) :
    ((orderedCommittedKeys identity pairs).filterMap value : Multiset Value) =
      (committedKeys identity pairs).val.filterMap value := by
  change (orderedCommittedKeys identity pairs : Multiset Key).filterMap value = _
  rw [orderedCommittedKeys_carrier]

theorem orderedCommittedKeys_partial_facts {Choice Key Value : Type} [DecidableEq Key] [DecidableEq Value]
    (identity : Committed Choice → Key) (value : Key → Option Value) (pairs : List (Committed Choice)) :
    ((orderedCommittedKeys identity pairs).filterMap value).toFinset =
      ((committedKeys identity pairs).val.filterMap value).toFinset := by
  exact congrArg Multiset.toFinset (orderedCommittedKeys_partial_bag identity value pairs)

theorem declared_eraseDups_replay {Key : Type} [BEq Key] [LawfulBEq Key]
    (earlier replay : List Key) (seen : ∀ key ∈ replay, key ∈ earlier) :
    (earlier ++ replay).eraseDups = earlier.eraseDups := by
  have none : replay.removeAll earlier = [] := by
    unfold List.removeAll
    apply List.filter_eq_nil_iff.mpr
    intro key member
    simpa using seen key member
  rw [List.eraseDups_append, none, List.eraseDups_nil, List.append_nil]

theorem orderedCommittedKeys_replay {Choice Key : Type} [DecidableEq Key]
    (identity : Committed Choice → Key) (earlier replay : List (Committed Choice))
    (seen : committedKeys identity replay ⊆ committedKeys identity earlier) :
    orderedCommittedKeys identity (earlier ++ replay) = orderedCommittedKeys identity earlier := by
  simp only [orderedCommittedKeys, List.map_append]
  apply declared_eraseDups_replay
  intro key member
  exact List.mem_toFinset.mp (seen (List.mem_toFinset.mpr member))

#print axioms declared_eraseDups_multiset
#print axioms orderedCommittedKeys_carrier
#print axioms orderedCommittedKeys_bag
#print axioms orderedCommittedKeys_partial_bag
#print axioms orderedCommittedKeys_partial_facts
#print axioms declared_eraseDups_replay
#print axioms orderedCommittedKeys_replay

end Mettapedia.OSLF.MeTTaIL.CollectionCommittedObservation
