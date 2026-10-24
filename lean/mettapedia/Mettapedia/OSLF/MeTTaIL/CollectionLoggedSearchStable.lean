import Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearch
import Mettapedia.OSLF.MeTTaIL.Complete.Graph

/-!
# Completion and exact collection source coverage

A complete logged search has finished matching and published every available
firing. Further resumption can change work counters but cannot add an event or
make the search pending again. This is the stability contract required for
stopping the generic explorer at a settled graph. Per-allocation publication
conservation gives exact receipt and target coverage, finite completion and
coverage through the existing generic explorer and transition graph.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearch

private theorem append_shuffle {α : Type} (a b c d : List α) :
    (a ++ b ++ (c ++ d)).Perm ((a ++ c) ++ (b ++ d)) := by
  simpa only [List.append_assoc] using
    List.Perm.append_left a ((List.perm_append_comm (l₁ := b) (l₂ := c)).append_right d)

/-- Each allocation has its own append-only matcher publication, even when
flattening all allocations changes the position of an older result. -/
theorem job_firings_prefix (request : ScopedCollectionMachine.Request)
    (job : ScopedCollectionMachine.Job) :
    ScopedCollectionMachine.firings request [job] <+:
      ScopedCollectionMachine.firings request
        [{ job with state := GeneralScopedMatchMachine.run request.machine 1 job.state }] := by
  simpa only [ScopedCollectionMachine.firings, ScopedCollectionMachine.publication,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] using
    ((GeneralScopedMatchMachine.run_answers_prefix request.machine 1 job.state).map
      (fun answer => ScopedCollectionMachine.Receipt.mk job.allocation answer)).filterMap
        (ScopedCollectionMachine.firing? request)

/-- Draining each allocation accounts for every old and new occurrence
exactly once. Permutation forgets chronology while retaining multiplicity
and the complete authored receipt. -/
theorem advanceJobs_balance (request : ScopedCollectionMachine.Request)
    (consumed : Nat) (jobs : ScopedCollectionMachine.State) :
    ((ScopedCollectionMachine.firings request jobs).take consumed ++
      (advanceJobs request consumed jobs).2).Perm
      (ScopedCollectionMachine.firings request
        (ScopedCollectionMachine.resume request 1 jobs)) := by
  induction jobs generalizing consumed with
  | nil => simp [advanceJobs, ScopedCollectionMachine.resume,
      ScopedCollectionMachine.firings, ScopedCollectionMachine.publication]
  | cons job jobs ih =>
      let old := ScopedCollectionMachine.firings request [job]
      let next := ScopedCollectionMachine.firings request
        [{ job with state := GeneralScopedMatchMachine.run request.machine 1 job.state }]
      have initialSegment : old <+: next := job_firings_prefix request job
      have taken : next.take (min consumed old.length) = old.take consumed := by
        have same := congrArg (List.take consumed) (List.prefix_iff_eq_take.mp initialSegment)
        simpa only [List.take_take] using same.symm
      have head : (old.take consumed ++ next.drop (min consumed old.length)) = next := by
        rw [← taken, List.take_append_drop]
      have split (rest : ScopedCollectionMachine.State) :
          ScopedCollectionMachine.firings request (job :: rest) =
            old ++ ScopedCollectionMachine.firings request rest := by
        simp [old, ScopedCollectionMachine.firings, ScopedCollectionMachine.publication,
          List.filterMap_append]
      rw [split, List.take_append]
      change ((old.take consumed ++ _) ++ (next.drop (min consumed old.length) ++ _)).Perm _
      apply (append_shuffle _ _ _ _).trans
      rw [head]
      simpa only [ScopedCollectionMachine.resume, List.map_cons,
        ScopedCollectionMachine.firings, ScopedCollectionMachine.publication,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filterMap_append,
        next, old] using (List.Perm.refl next).append (ih (consumed - old.length))

def Lane.published (lane : Lane) : List CollectionPlanMachine.Firing :=
  ((ScopedCollectionMachine.firings lane.request lane.state).take lane.consumed).map (tag lane)

def Balanced (state : State) : Prop :=
  state.log.Perm (state.lanes.flatMap Lane.published)

theorem advanceLane_balance (lane : Lane) :
    (lane.published ++ (advanceLane lane).2).Perm (advanceLane lane).1.published := by
  have balance := (advanceJobs_balance lane.request lane.consumed lane.state).map (tag lane)
  simp only [Lane.published, advanceLane, advanceJobs_state, List.take_length,
    ]
  simp only [List.map_append] at balance
  convert balance using 2
  funext receipt
  rfl

private theorem advanceLanes_balance (lanes : List Lane) :
    (lanes.flatMap Lane.published ++ (lanes.map advanceLane).flatMap Prod.snd).Perm
      (((lanes.map advanceLane).map Prod.fst).flatMap Lane.published) := by
  induction lanes with
  | nil => exact List.Perm.refl []
  | cons lane lanes ih =>
      simp only [List.flatMap_cons, List.map_cons]
      exact (append_shuffle _ _ _ _).trans ((advanceLane_balance lane).append ih)

theorem begin_balanced (requests : List (Nat × ScopedCollectionMachine.Request)) :
    Balanced (begin requests) := by
  change [].Perm ((requests.map Lane.begin).flatMap Lane.published)
  have empty : (requests.map Lane.begin).flatMap Lane.published = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro lane member
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    simp [Lane.published, Lane.begin]
  rw [empty]

theorem round_balanced {state : State} (balance : Balanced state) : Balanced (round state) :=
  (balance.append_right _).trans (advanceLanes_balance state.lanes)

theorem resume_balanced (fuel : Nat) {state : State} (balance : Balanced state) :
    Balanced (resume fuel state) := by
  induction fuel generalizing state with
  | zero => exact balance
  | succ fuel ih => exact ih (round_balanced balance)

/-- The public successor observation retains the authored rule coordinate and
canonical target. Full allocation receipts remain in the balanced log. -/
def outcome (firing : CollectionPlanMachine.Firing) : Nat × Syntax.Pattern :=
  (firing.ordinal, CanonicalBags.canon firing.receipt.target)

def Lane.sourceTargets (lane : Lane) : List (Nat × Syntax.Pattern) :=
  ((ScopedCollectionMatching.run lane.request.rule lane.request.spec lane.request.ambient
    lane.request.site lane.request.path lane.request.depth lane.request.index lane.request.initial
    lane.request.schemas lane.request.rest lane.request.kind lane.request.targets).filterMap
    (ScopedRuleMatching.reduct? lane.request.rule lane.request.spec lane.request.ambient)).map
      (fun target => (lane.ordinal, CanonicalBags.canon target))

theorem advanceLane_sourceTargets (lane : Lane) :
    (advanceLane lane).1.sourceTargets = lane.sourceTargets := rfl

theorem round_sourceTargets (state : State) :
    (round state).lanes.flatMap Lane.sourceTargets = state.lanes.flatMap Lane.sourceTargets := by
  simp only [round, List.flatMap_map, advanceLane_sourceTargets]

theorem resume_sourceTargets (fuel : Nat) (state : State) :
    (resume fuel state).lanes.flatMap Lane.sourceTargets = state.lanes.flatMap Lane.sourceTargets := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => exact (ih (round state)).trans (round_sourceTargets state)

theorem lane_complete_targets (lane : Lane) (finished : lane.complete = true) :
    lane.published.map outcome = lane.sourceTargets := by
  have parts : ScopedCollectionMachine.complete lane.state = true ∧
      lane.consumed = (ScopedCollectionMachine.firings lane.request lane.state).length := by
    simpa only [Lane.complete, Bool.and_eq_true, beq_iff_eq] using finished
  have matchingDone : ScopedCollectionMachine.complete
      (ScopedCollectionMachine.resume lane.request lane.spent
        (ScopedCollectionMachine.start lane.request)) = true := lane.state_eq ▸ parts.1
  have exactTargets := ScopedCollectionMachine.completed_targets lane.request lane.spent matchingDone
  have exactOutcomes := congrArg (List.map (fun target => (lane.ordinal, CanonicalBags.canon target))) exactTargets
  simp only [Lane.published, parts.2, List.take_length, List.map_map]
  simpa only [Lane.sourceTargets, lane.state_eq, List.map_map, Function.comp_def, tag, outcome]
    using exactOutcomes

/-- Completion gives both no invention and no loss, with exact occurrence
multiplicity, against the source collection matcher and authored reduct.
Chronological order may differ from declaration/allocation order. -/
theorem completed_source_targets
    (requests : List (Nat × ScopedCollectionMachine.Request)) (fuel : Nat)
    (finished : complete (resume fuel (begin requests)) = true) :
    ((resume fuel (begin requests)).log.map outcome).Perm
      (requests.flatMap fun entry => (Lane.begin entry).sourceTargets) := by
  have balanced := (resume_balanced fuel (begin_balanced requests)).map outcome
  have agrees : ((resume fuel (begin requests)).lanes.flatMap Lane.published).map outcome =
      (resume fuel (begin requests)).lanes.flatMap Lane.sourceTargets := by
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro lane member
    exact lane_complete_targets lane (List.all_eq_true.mp finished lane member)
  rw [agrees, resume_sourceTargets] at balanced
  simpa only [begin, List.flatMap_map, Function.comp_def] using balanced

theorem lane_pending_of_unpublished (lane : Lane)
    (unpublished : lane.consumed < (ScopedCollectionMachine.firings lane.request lane.state).length) :
    lane.complete = false := by
  simp [Lane.complete, Nat.ne_of_lt unpublished]

theorem advanceLane_complete (lane : Lane) (finished : lane.complete = true) :
    (advanceLane lane).2 = [] ∧ (advanceLane lane).1.complete = true := by
  have parts : ScopedCollectionMachine.complete lane.state = true ∧
      lane.consumed = (ScopedCollectionMachine.firings lane.request lane.state).length := by
    simpa only [Lane.complete, Bool.and_eq_true, beq_iff_eq] using finished
  have unchanged := ScopedCollectionMachine.complete_resume lane.request lane.state parts.1 1
  have balance := advanceJobs_balance lane.request lane.consumed lane.state
  rw [unchanged, parts.2, List.take_length] at balance
  have empty : (advanceJobs lane.request lane.consumed lane.state).2 = [] := by
    rw [parts.2]
    have lengths := balance.length_eq
    simp only [List.length_append] at lengths
    exact List.eq_nil_of_length_eq_zero (by omega)
  simp only [advanceLane, empty, List.map_nil, advanceJobs_state, unchanged]
  constructor
  · trivial
  · simp only [Lane.complete, parts.1, Bool.true_and, beq_self_eq_true]

/-- Iteration of the actual retained lane transition, used only to establish
finite completion of a batch of independent lanes. -/
def Lane.advanceFor : Nat → Lane → Lane
  | 0, lane => lane
  | fuel + 1, lane => Lane.advanceFor fuel (advanceLane lane).1

theorem Lane.advanceFor_add (first extra : Nat) (lane : Lane) :
    lane.advanceFor (first + extra) = (lane.advanceFor first).advanceFor extra := by
  induction first generalizing lane with
  | zero => simp only [Nat.zero_add, Lane.advanceFor]
  | succ first ih => simpa only [Nat.succ_add, Lane.advanceFor] using ih (advanceLane lane).1

theorem Lane.advanceFor_state (fuel : Nat) (lane : Lane) :
    (lane.advanceFor fuel).state = ScopedCollectionMachine.resume lane.request fuel lane.state := by
  induction fuel generalizing lane with
  | zero => exact (ScopedCollectionMachine.resume_zero _ _).symm
  | succ fuel ih =>
      rw [Lane.advanceFor, ih]
      simp only [advanceLane, advanceJobs_state]
      simpa only [Nat.add_comm 1 fuel] using
        (ScopedCollectionMachine.resume_add lane.request 1 fuel lane.state).symm

theorem Lane.advanceFor_consumed (fuel : Nat) (lane : Lane) :
    (lane.advanceFor (fuel + 1)).consumed =
      (ScopedCollectionMachine.firings (lane.advanceFor (fuel + 1)).request
        (lane.advanceFor (fuel + 1)).state).length := by
  induction fuel generalizing lane with
  | zero => rfl
  | succ fuel ih => exact ih (advanceLane lane).1

theorem Lane.advanceFor_request (fuel : Nat) (lane : Lane) :
    (lane.advanceFor fuel).request = lane.request := by
  induction fuel generalizing lane with
  | zero => rfl
  | succ fuel ih => exact ih (advanceLane lane).1

theorem Lane.advanceFor_ordinal (fuel : Nat) (lane : Lane) :
    (lane.advanceFor fuel).ordinal = lane.ordinal := by
  induction fuel generalizing lane with
  | zero => rfl
  | succ fuel ih => exact ih (advanceLane lane).1

theorem Lane.advanceFor_complete (fuel : Nat) (lane : Lane) (finished : lane.complete = true) :
    (lane.advanceFor fuel).complete = true := by
  induction fuel generalizing lane with
  | zero => exact finished
  | succ fuel ih => exact ih _ (advanceLane_complete lane finished).2

theorem Lane.eventually_complete (lane : Lane) :
    ∃ fuel, (lane.advanceFor fuel).complete = true := by
  obtain ⟨fuel, done⟩ := ScopedCollectionMachine.eventually_complete lane.request lane.state
  refine ⟨fuel + 1, ?_⟩
  simp only [Lane.complete, Lane.advanceFor_consumed, beq_self_eq_true, Bool.and_true,
    Lane.advanceFor_request, Lane.advanceFor_state]
  rw [ScopedCollectionMachine.resume_add]
  rw [ScopedCollectionMachine.complete_resume lane.request _ done]
  exact done

theorem resume_lanes (fuel : Nat) (state : State) :
    (resume fuel state).lanes = state.lanes.map (Lane.advanceFor fuel) := by
  induction fuel generalizing state with
  | zero => simp [resume, Lane.advanceFor]
  | succ fuel ih =>
      rw [resume, ih]
      simp only [round, List.map_map, Function.comp_def, Lane.advanceFor]

/-- After one or more rounds, completion can be checked directly on the
retained matcher states; the chronological log need not be evaluated. -/
theorem complete_resume_begin_succ
    (requests : List (Nat × ScopedCollectionMachine.Request)) (fuel : Nat) :
    complete (resume (fuel + 1) (begin requests)) =
      requests.all (fun entry => ScopedCollectionMachine.complete
        (ScopedCollectionMachine.resume entry.2 (fuel + 1)
          (ScopedCollectionMachine.start entry.2))) := by
  unfold complete
  rw [resume_lanes]
  simp only [begin, List.all_map, Function.comp_def, Lane.complete,
    Lane.advanceFor_consumed, beq_self_eq_true, Bool.and_true,
    Lane.advanceFor_request, Lane.advanceFor_state, Lane.begin]

private theorem lanes_eventually_complete (lanes : List Lane) :
    ∃ fuel, ∀ lane ∈ lanes, (lane.advanceFor fuel).complete = true := by
  induction lanes with
  | nil => exact ⟨0, by simp⟩
  | cons lane lanes ih =>
      obtain ⟨first, firstDone⟩ := lane.eventually_complete
      obtain ⟨later, laterDone⟩ := ih
      refine ⟨first + later, ?_⟩
      intro item present
      rcases List.mem_cons.mp present with rfl | remaining
      · rw [Lane.advanceFor_add]
        exact Lane.advanceFor_complete later _ firstDone
      · rw [Nat.add_comm, Lane.advanceFor_add]
        exact Lane.advanceFor_complete first _ (laterDone item remaining)

/-- Every finite retained collection batch finishes and drains publication.
No fairness or completion hypothesis is supplied by the caller. -/
theorem eventually_complete (state : State) :
    ∃ fuel, complete (resume fuel state) = true := by
  obtain ⟨fuel, done⟩ := lanes_eventually_complete state.lanes
  refine ⟨fuel, ?_⟩
  unfold complete
  rw [resume_lanes]
  apply List.all_eq_true.mpr
  intro lane member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact done original present

theorem eventually_source_exact
    (requests : List (Nat × ScopedCollectionMachine.Request)) :
    ∃ fuel, complete (resume fuel (begin requests)) = true ∧
      ((resume fuel (begin requests)).log.map outcome).Perm
        (requests.flatMap fun entry => (Lane.begin entry).sourceTargets) := by
  obtain ⟨fuel, finished⟩ := eventually_complete (begin requests)
  exact ⟨fuel, finished, completed_source_targets requests fuel finished⟩

/-- Exact receipt coverage, including each allocation decision and nested
match trace. A semantic witness is neither lost nor published twice through
another allocation's cursor. Multiplicity conservation is `resume_balanced`. -/
theorem completed_log_exact
    (requests : List (Nat × ScopedCollectionMachine.Request)) (fuel : Nat)
    (finished : complete (resume fuel (begin requests)) = true)
    (firing : CollectionPlanMachine.Firing) :
    firing ∈ (resume fuel (begin requests)).log ↔ Valid requests firing := by
  refine ⟨(resume_invariant fuel (begin_invariant requests)).2 firing, ?_⟩
  rintro ⟨origin, valid⟩
  let lane := (Lane.begin (firing.ordinal, firing.request)).advanceFor fuel
  have member : lane ∈ (resume fuel (begin requests)).lanes := by
    rw [resume_lanes]
    exact List.mem_map.mpr ⟨Lane.begin (firing.ordinal, firing.request),
      List.mem_map.mpr ⟨(firing.ordinal, firing.request), origin, rfl⟩, rfl⟩
  have done : lane.complete = true := List.all_eq_true.mp finished lane member
  have parts : ScopedCollectionMachine.complete lane.state = true ∧
      lane.consumed = (ScopedCollectionMachine.firings lane.request lane.state).length := by
    simpa only [Lane.complete, Bool.and_eq_true, beq_iff_eq] using done
  have sameRequest : lane.request = firing.request := Lane.advanceFor_request fuel _
  have sameOrdinal : lane.ordinal = firing.ordinal := Lane.advanceFor_ordinal fuel _
  have matchingDone : ScopedCollectionMachine.complete
      (ScopedCollectionMachine.resume lane.request lane.spent
        (ScopedCollectionMachine.start lane.request)) = true := lane.state_eq ▸ parts.1
  have published : firing.receipt ∈ ScopedCollectionMachine.firings lane.request lane.state := by
    rw [lane.state_eq, ScopedCollectionMachine.firings_exact lane.request lane.spent matchingDone]
    simpa only [sameRequest, CollectionPlanMachine.Firing.Valid] using valid
  have tagged : tag lane firing.receipt = firing := by
    cases firing
    simp only [tag, sameRequest, sameOrdinal]
  have inLane : firing ∈ lane.published := by
    simp only [Lane.published, parts.2, List.take_length]
    exact List.mem_map.mpr ⟨firing.receipt, published, tagged⟩
  exact (resume_balanced fuel (begin_balanced requests)).mem_iff.mpr
    (List.mem_flatMap.mpr ⟨lane, member, inLane⟩)

/-- The target observation is also exact against the independent relational
source judgment, rather than only agreement of two execution functions. -/
theorem completed_target_iff
    (requests : List (Nat × ScopedCollectionMachine.Request)) (fuel : Nat)
    (finished : complete (resume fuel (begin requests)) = true)
    (unordered : ∀ entry ∈ requests, entry.2.kind ≠ .vec)
    (distinct : ∀ entry ∈ requests, entry.2.kind = .hashSet → entry.2.targets.Nodup)
    (observation : Nat × Syntax.Pattern) :
    observation ∈ (resume fuel (begin requests)).log.map outcome ↔
      ∃ entry ∈ requests, ∃ assignment target,
        ScopedCollectionMatching.Matches entry.2.rule entry.2.spec entry.2.ambient
          entry.2.site entry.2.path entry.2.depth entry.2.index entry.2.initial
          entry.2.schemas entry.2.rest entry.2.kind entry.2.targets assignment ∧
        ScopedRuleMatching.reduct? entry.2.rule entry.2.spec entry.2.ambient assignment = some target ∧
        (entry.1, CanonicalBags.canon target) = observation := by
  rw [(completed_source_targets requests fuel finished).mem_iff]
  simp only [List.mem_flatMap, Lane.sourceTargets, Lane.begin, List.mem_map,
    List.mem_filterMap]
  constructor
  · rintro ⟨entry, member, target, ⟨assignment, matched, reduced⟩, observed⟩
    exact ⟨entry, member, assignment, target,
      (ScopedCollectionMatching.run_exact _ _ _ _ _ _ _ _ _ _ _
        (unordered entry member) (distinct entry member)).mp matched, reduced, observed⟩
  · rintro ⟨entry, member, assignment, target, matched, reduced, observed⟩
    exact ⟨entry, member, target, ⟨assignment,
      (ScopedCollectionMatching.run_exact _ _ _ _ _ _ _ _ _ _ _
        (unordered entry member) (distinct entry member)).mpr matched, reduced⟩, observed⟩

theorem round_complete (state : State) (finished : complete state = true) :
    (round state).log = state.log ∧ complete (round state) = true := by
  have each : ∀ lane ∈ state.lanes, (advanceLane lane).2 = [] ∧
      (advanceLane lane).1.complete = true := by
    intro lane member
    exact advanceLane_complete lane (List.all_eq_true.mp finished lane member)
  have drained : (state.lanes.map advanceLane).flatMap Prod.snd = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro pair member
    obtain ⟨lane, present, rfl⟩ := List.mem_map.mp member
    exact (each lane present).1
  constructor
  · simp only [round, drained, List.append_nil]
  · change ((state.lanes.map advanceLane).map Prod.fst).all Lane.complete = true
    apply List.all_eq_true.mpr
    intro lane member
    obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp pairMember
    exact (each original originalMember).2

theorem resume_complete (fuel : Nat) (state : State) (finished : complete state = true) :
    (resume fuel state).log = state.log ∧ complete (resume fuel state) = true := by
  induction fuel generalizing state with
  | zero => exact ⟨rfl, finished⟩
  | succ fuel ih =>
      have first := round_complete state finished
      have later := ih (round state) first.2
      exact ⟨later.1.trans first.1, later.2⟩

theorem search_stable (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan) :
    Complete.Settled.Stable (search plan certificate) := by
  intro run work finished
  have completed : complete run.state = true := by
    change (if complete run.state then
      Mettapedia.Machines.ResumableSearchRunner.Status.complete else .pending) = .complete at finished
    split at finished
    · assumption
    · cases finished
  have stable := resume_complete work run.state completed
  refine ⟨stable.1, ?_⟩
  change (if complete (resume work run.state) then
    Mettapedia.Machines.ResumableSearchRunner.Status.complete else .pending) = .complete
  rw [stable.2]
  rfl

/-- Every independently checked collection receipt is eventually published. -/
theorem search_complete_in_limit (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Syntax.Pattern) (firing : CollectionPlanMachine.Firing)
    (valid : (search plan certificate).Valid source firing) :
    ∃ work, firing ∈ (search plan certificate).publication
      ((search plan certificate).run source work) := by
  obtain ⟨work, finished⟩ := eventually_complete (begin (requests plan certificate source))
  exact ⟨work, (completed_log_exact _ work finished firing).mpr valid⟩

/-- The unchanged generic explorer reaches the target of every checked
source receipt, including one published after another allocation finishes. -/
theorem explores_firing (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    {source state : Syntax.Pattern}
    (explored : Complete.Explore.Explored (S := search plan certificate) source state)
    (firing : CollectionPlanMachine.Firing)
    (valid : (search plan certificate).Valid state firing) :
    Complete.Explore.Explored (S := search plan certificate) source
      (CanonicalBags.canon firing.receipt.target) := by
  obtain ⟨work, published⟩ := search_complete_in_limit plan certificate state firing valid
  exact Complete.Explore.explored_target (search_lawful plan certificate) explored published

/-- A settled graph retains every checked collection receipt as an edge;
merging equal target states does not merge their occurrence evidence. -/
theorem edges_cover_firing (plan : GeneralExecutionAdmission.Plan)
    (certificate : CollectionExecutionAdmission.Certificate plan)
    (source : Syntax.Pattern) (work : Nat)
    (done : Complete.Settled.settled (search plan certificate)
      (Complete.Explore.explore (search plan certificate) source work) = true)
    (node : Complete.Explore.Node Syntax.Pattern Run CollectionPlanMachine.Firing)
    (present : node ∈ (Complete.Explore.explore (search plan certificate) source work).nodes)
    (firing : CollectionPlanMachine.Firing)
    (valid : (search plan certificate).Valid node.state firing) :
    (node.state, firing, CanonicalBags.canon firing.receipt.target) ∈
      Complete.Graph.edges (search plan certificate)
        (Complete.Explore.explore (search plan certificate) source work) := by
  obtain ⟨rounds, published⟩ := search_complete_in_limit plan certificate node.state firing valid
  exact Complete.Graph.edges_complete (search_lawful plan certificate) (search_stable plan certificate)
    source work done node present rounds firing published

end Mettapedia.OSLF.MeTTaIL.CollectionLoggedSearch
