import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMatcher

/-!
# Joint retained matching and conditional occurrence execution

Every round advances the actual source-derived matchers, installs only their
new allocations, and advances retained conditional work. The installation
account and chronological receipt account remain separate invariants. Neither
an exhausted matching budget nor a drained depth cutoff licenses completion.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceBatch CollectionOccurrenceMatcher

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern}

variable {matcher : GeneralPremise.MatchingExecution}

structure State (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern)
    (matcher : GeneralPremise.MatchingExecution := GeneralPremise.MatchingExecution.ordinary) where
  matchers : List (Lane plan bound expected source)
  batch : CollectionOccurrenceBatch.State plan bound expected source matcher

/-- Discovery starts with the same source-derived lanes and no installed work. -/
def beginWith (matcher : GeneralPremise.MatchingExecution)
    (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) : State plan bound expected source matcher :=
  ⟨lanes plan bound expected source, ⟨[], []⟩⟩

def roundWith (profile : SeedProfile matcher plan bound expected source)
    (depth : Nat) (state : State plan bound expected source matcher) :
    State plan bound expected source matcher :=
  ⟨state.matchers.map (Lane.resume 1),
    (state.batch.installWith profile (state.matchers.flatMap (Lane.allocations depth))).round⟩

/-- One retained outer loop serves every selected matching execution. -/
def runWith (profile : SeedProfile matcher plan bound expected source) (depth : Nat) :
    Nat → State plan bound expected source matcher → State plan bound expected source matcher
  | 0, state => state
  | work + 1, state => runWith profile depth work (roundWith profile depth state)

def begin (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) : State plan bound expected source :=
  beginWith GeneralPremise.MatchingExecution.ordinary plan bound expected source

def round (depth : Nat) (state : State plan bound expected source) : State plan bound expected source :=
  roundWith (ordinarySeedProfile plan bound expected source) depth state

def run (depth work : Nat) (state : State plan bound expected source) : State plan bound expected source :=
  runWith (ordinarySeedProfile plan bound expected source) depth work state

theorem runWith_ordinary (depth work : Nat) (state : State plan bound expected source) :
    runWith (ordinarySeedProfile plan bound expected source) depth work state = run depth work state := rfl

theorem runWith_add (profile : SeedProfile matcher plan bound expected source)
    (depth first extra : Nat) (state : State plan bound expected source matcher) :
    runWith profile depth (first + extra) state =
      runWith profile depth extra (runWith profile depth first state) := by
  induction first generalizing state with
  | zero => simp only [runWith, Nat.zero_add]
  | succ first ih => simpa only [runWith, Nat.succ_add] using ih (roundWith profile depth state)

def Invariant (depth : Nat) (state : State plan bound expected source matcher) : Prop :=
  state.batch.Balanced ∧
    (state.batch.frames.map Frame.allocation).Perm
      (state.matchers.flatMap (Lane.account depth))

theorem beginWith_invariant (matcher : GeneralPremise.MatchingExecution) (depth : Nat) :
    Invariant depth (beginWith matcher plan bound expected source) := by
  constructor
  · exact List.Perm.refl []
  · change [].Perm ((lanes plan bound expected source).flatMap (Lane.account depth))
    have empty : (lanes plan bound expected source).flatMap (Lane.account depth) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro lane member
      obtain ⟨selected, _, rfl⟩ := List.mem_map.mp member
      rfl
    rw [empty]

theorem roundWith_invariant (profile : SeedProfile matcher plan bound expected source)
    (depth : Nat) {state : State plan bound expected source matcher}
    (valid : Invariant depth state) : Invariant depth (roundWith profile depth state) := by
  constructor
  · exact CollectionOccurrenceBatch.State.round_balanced
      (CollectionOccurrenceBatch.State.installWith_balanced profile _ valid.1)
  · have frameAccount :
        ((roundWith profile depth state).batch.frames.map Frame.allocation) =
          state.batch.frames.map Frame.allocation ++ state.matchers.flatMap (Lane.allocations depth) := by
      simp only [roundWith, CollectionOccurrenceBatch.State.round, CollectionOccurrenceBatch.State.installWith,
        List.map_map, List.map_append]
      change (state.batch.frames.map Frame.allocation ++
        (state.matchers.flatMap (Lane.allocations depth)).map (fun allocation => allocation)) = _
      exact congrArg (state.batch.frames.map Frame.allocation ++ ·) (List.map_id _)
    rw [frameAccount]
    apply (valid.2.append_right _).trans
    apply (List.flatMap_append_perm state.matchers (Lane.account depth) (Lane.allocations depth)).trans
    simp only [roundWith, List.flatMap_map]
    apply List.Perm.of_eq
    apply List.flatMap_congr
    intro lane _
    exact Lane.allocation_balance depth lane

theorem runWith_invariant (profile : SeedProfile matcher plan bound expected source)
    (depth work : Nat) {state : State plan bound expected source matcher}
    (valid : Invariant depth state) : Invariant depth (runWith profile depth work state) := by
  induction work generalizing state with
  | zero => exact valid
  | succ work ih => exact ih (roundWith_invariant profile depth valid)

theorem runWith_log_prefix (profile : SeedProfile matcher plan bound expected source)
    (depth work : Nat) (state : State plan bound expected source matcher) :
    state.batch.log <+: (runWith profile depth work state).batch.log := by
  induction work generalizing state with
  | zero => exact List.prefix_refl _
  | succ work ih => exact (List.prefix_append _ _).trans (ih (roundWith profile depth state))

/-- Every existing continuation receives its next quantum in place. -/
theorem roundWith_retains_frames (profile : SeedProfile matcher plan bound expected source)
    (depth : Nat) (state : State plan bound expected source matcher) :
    state.batch.frames.map (Frame.run 1) <+: (roundWith profile depth state).batch.frames :=
  (CollectionOccurrenceBatch.State.installWith_frames_prefix profile _ state.batch).map (Frame.run 1)

theorem runWith_retains_frames (profile : SeedProfile matcher plan bound expected source)
    (depth work : Nat) (state : State plan bound expected source matcher) :
    state.batch.frames.map (Frame.run work) <+: (runWith profile depth work state).batch.frames := by
  induction work generalizing state with
  | zero =>
    have idle : (Frame.run 0 : Frame plan bound expected source matcher → _) = id := by
      funext frame
      cases frame
      rfl
    simp only [runWith, idle, List.map_id]
    exact List.prefix_refl _
  | succ work ih =>
    have preserved := ((roundWith_retains_frames profile depth state).map (Frame.run work)).trans
      (ih (roundWith profile depth state))
    simpa only [runWith, List.map_map, Function.comp_def, ← Frame.run_add, Nat.add_comm 1 work]
      using preserved

theorem installed_accountWith (profile : SeedProfile matcher plan bound expected source)
    (depth work : Nat) :
    let state := runWith profile depth work (beginWith matcher plan bound expected source)
    (state.batch.frames.map Frame.allocation).Perm
      (state.matchers.flatMap (Lane.account depth)) :=
  (runWith_invariant profile depth work (beginWith_invariant matcher depth)).2

theorem run_add (depth first extra : Nat) (state : State plan bound expected source) :
    run depth (first + extra) state = run depth extra (run depth first state) :=
  runWith_add (ordinarySeedProfile plan bound expected source) depth first extra state

theorem begin_invariant (depth : Nat) :
    Invariant depth (begin plan bound expected source) :=
  beginWith_invariant GeneralPremise.MatchingExecution.ordinary depth

theorem round_invariant (depth : Nat) {state : State plan bound expected source}
    (valid : Invariant depth state) : Invariant depth (round depth state) :=
  roundWith_invariant (ordinarySeedProfile plan bound expected source) depth valid

theorem run_invariant (depth work : Nat) {state : State plan bound expected source}
    (valid : Invariant depth state) : Invariant depth (run depth work state) :=
  runWith_invariant (ordinarySeedProfile plan bound expected source) depth work valid

theorem log_prefix (depth work : Nat) (state : State plan bound expected source) :
    state.batch.log <+: (run depth work state).batch.log :=
  runWith_log_prefix (ordinarySeedProfile plan bound expected source) depth work state

theorem round_retains_frames (depth : Nat) (state : State plan bound expected source) :
    state.batch.frames.map (Frame.run 1) <+: (round depth state).batch.frames :=
  roundWith_retains_frames (ordinarySeedProfile plan bound expected source) depth state

theorem run_retains_frames (depth work : Nat) (state : State plan bound expected source) :
    state.batch.frames.map (Frame.run work) <+: (run depth work state).batch.frames :=
  runWith_retains_frames (ordinarySeedProfile plan bound expected source) depth work state

/-- Once an allocation has been installed, later matching cannot starve any
of its depth-qualified premise outcomes. Exact completed assignments and
histories reach the chronological log while other allocations keep arriving. -/
theorem retained_source_coverage (depth : Nat) (state : State plan bound expected source)
    (valid : Invariant depth state) (allocation : Allocation plan bound expected source)
    (already : Nat) (retained : Frame.run already (Frame.initial allocation) ∈ state.batch.frames)
    (trace : List GeneralScopedMatchMachine.BagChoice) (completed : ScopedRuleMatching.Assignment)
    (history : List GeneralPremise.Event) (target : Pattern)
    (held : GeneralPremise.RootFiring allocation.request.environment allocation.request.bound
      allocation.request.type allocation.request.prepared.source allocation.request.index trace
      allocation.request.prepared.ordinary.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ allocation.request.depth) :
    ∃ work, tag allocation
        ⟨allocation.request.prepared.ordinary.trace, allocation.request.prepared.ordinary.assignment,
          completed, history, target⟩ ∈ (run depth work state).batch.log := by
  obtain ⟨work, emitted⟩ := Frame.source_coverage allocation trace completed history target held bounded
  have later := (Frame.publication_prefix
    (Frame.run work (Frame.initial allocation)) already).subset emitted
  rw [← Frame.run_add, Nat.add_comm work already, Frame.run_add] at later
  have kept := (run_retains_frames depth work state).subset (List.mem_map_of_mem retained)
  exact ⟨work, (run_invariant depth work valid).1.symm.subset
    (List.mem_flatMap.mpr ⟨_, kept, later⟩)⟩

/-- At every work allowance the retained frames account for exactly the
accepted matcher allocations so far, with full occurrence multiplicity. -/
theorem installed_account (depth work : Nat) :
    let state := run depth work (begin plan bound expected source)
    (state.batch.frames.map Frame.allocation).Perm
      (state.matchers.flatMap (Lane.account depth)) :=
  (run_invariant depth work (begin_invariant depth)).2

theorem publication_source_sound (depth work : Nat) {packet : Publication}
    (published : packet ∈ (run depth work (begin plan bound expected source)).batch.log)
    {receipt : GeneralRuleJobs.Receipt}
    (finished : packet.finish? plan bound expected = some receipt) :
    (Complete.Presented.gslt plan bound expected).Step source receipt.target :=
  CollectionOccurrenceBatch.State.balanced_source_sound
    (run_invariant depth work (begin_invariant depth)).1 published finished

/-- Canonical execution uses the allocation producer's original answer seed. -/
def beginCanonical (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) :
    State plan bound expected (CanonicalBags.canon source) RecursiveCollectionHandoff.canonicalMatchingExecution :=
  beginWith RecursiveCollectionHandoff.canonicalMatchingExecution plan bound expected (CanonicalBags.canon source)

def runCanonical (depth work : Nat)
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution) :=
  runWith (canonicalSeedProfile plan bound expected source) depth work state

theorem canonical_run_add (depth first extra : Nat)
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution) :
    runCanonical depth (first + extra) state = runCanonical depth extra (runCanonical depth first state) :=
  runWith_add (canonicalSeedProfile plan bound expected source) depth first extra state

theorem canonical_installed_account (depth work : Nat) :
    let state := runCanonical depth work (beginCanonical plan bound expected source)
    (state.batch.frames.map Frame.allocation).Perm
      (state.matchers.flatMap (Lane.account depth)) :=
  installed_accountWith (canonicalSeedProfile plan bound expected source) depth work

/-- Canonical prefix readout retains interpreted validity and source equivalence.
It makes no admission or enumeration-completion assertion. -/
theorem canonical_publication_valid (depth work : Nat)
    {packet : Publication EquationalScopedReceipts.Event}
    (published : packet ∈ (runCanonical depth work (beginCanonical plan bound expected source)).batch.log)
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (finished : packet.finishCanonical? plan bound expected = some receipt) :
    receipt.ValidInWith RecursiveCollectionHandoff.canonicalMatchingInterpretation GeneralPremise.DynamicProvider.empty
      plan bound expected (packet.job.presentedSource packet.prepared) ∧
      CanonicalBags.Same source (packet.job.presentedSource packet.prepared) := by
  have balanced := (runWith_invariant (canonicalSeedProfile plan bound expected source) depth work
    (beginWith_invariant RecursiveCollectionHandoff.canonicalMatchingExecution depth)).1
  obtain ⟨frame, _, inside⟩ := List.mem_flatMap.mp (balanced.subset published)
  exact Frame.publication_canonical_valid frame inside finished

/-- Later source matching cannot starve any already installed canonical continuation.
The published packet retains the original allocation trace and complete premise history. -/
theorem canonical_retained_source_coverage (depth : Nat)
    (state : State plan bound expected (CanonicalBags.canon source)
      RecursiveCollectionHandoff.canonicalMatchingExecution)
    (valid : Invariant depth state)
    (allocation : Allocation plan bound expected (CanonicalBags.canon source))
    (already : Nat) (retained : Frame.run already (Frame.initialCanonical allocation) ∈ state.batch.frames)
    (trace : List EquationalScopedReceipts.Event) (completed : ScopedRuleMatching.Assignment)
    (history : List (GeneralPremise.Event EquationalScopedReceipts.Event)) (target : Pattern)
    (held : GeneralPremise.Interpreted.RootFiring RecursiveCollectionHandoff.canonicalMatchingInterpretation
      allocation.request.environment allocation.request.bound allocation.request.type
      allocation.request.prepared.source allocation.request.index trace
      allocation.request.answer.assignment completed history target)
    (bounded : StructuralDescent.eventsDepth history ≤ allocation.request.depth) :
    ∃ work, tag allocation
      ⟨allocation.request.answer.trace, allocation.request.answer.assignment, completed, history, target⟩ ∈
        (runCanonical depth work state).batch.log := by
  obtain ⟨work, emitted⟩ := Frame.source_coverageCanonical allocation trace completed history target held bounded
  have later := (Frame.publication_prefix (Frame.run work (Frame.initialCanonical allocation)) already).subset emitted
  rw [← Frame.run_add, Nat.add_comm work already, Frame.run_add] at later
  have kept := (runWith_retains_frames (canonicalSeedProfile plan bound expected source)
    depth work state).subset (List.mem_map_of_mem retained)
  exact ⟨work, (runWith_invariant (canonicalSeedProfile plan bound expected source) depth work valid).1.symm.subset
    (List.mem_flatMap.mpr ⟨_, kept, later⟩)⟩

#print axioms runWith_ordinary
#print axioms runWith_add
#print axioms runWith_invariant
#print axioms runWith_log_prefix
#print axioms runWith_retains_frames
#print axioms installed_accountWith
#print axioms canonical_run_add
#print axioms canonical_installed_account
#print axioms canonical_retained_source_coverage
#print axioms canonical_publication_valid

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine
