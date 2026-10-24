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

structure State (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) where
  matchers : List (Lane plan bound expected source)
  batch : CollectionOccurrenceBatch.State plan bound expected source

def begin (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) : State plan bound expected source :=
  ⟨lanes plan bound expected source, CollectionOccurrenceBatch.State.begin []⟩

def round (depth : Nat) (state : State plan bound expected source) : State plan bound expected source :=
  ⟨state.matchers.map (Lane.resume 1),
    (state.batch.install (state.matchers.flatMap (Lane.allocations depth))).round⟩

def run (depth : Nat) : Nat → State plan bound expected source → State plan bound expected source
  | 0, state => state
  | work + 1, state => run depth work (round depth state)

theorem run_add (depth first extra : Nat) (state : State plan bound expected source) :
    run depth (first + extra) state = run depth extra (run depth first state) := by
  induction first generalizing state with
  | zero => simp only [run, Nat.zero_add]
  | succ first ih => simpa only [run, Nat.succ_add] using ih (round depth state)

def Invariant (depth : Nat) (state : State plan bound expected source) : Prop :=
  state.batch.Balanced ∧
    (state.batch.frames.map Frame.allocation).Perm
      (state.matchers.flatMap (Lane.account depth))

theorem begin_invariant (depth : Nat) :
    Invariant depth (begin plan bound expected source) := by
  constructor
  · exact CollectionOccurrenceBatch.State.begin_balanced []
  · change [].Perm ((lanes plan bound expected source).flatMap (Lane.account depth))
    have empty : (lanes plan bound expected source).flatMap (Lane.account depth) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro lane member
      obtain ⟨selected, _, rfl⟩ := List.mem_map.mp member
      rfl
    rw [empty]

theorem round_invariant (depth : Nat) {state : State plan bound expected source}
    (valid : Invariant depth state) : Invariant depth (round depth state) := by
  constructor
  · exact CollectionOccurrenceBatch.State.round_balanced
      (CollectionOccurrenceBatch.State.install_balanced _ valid.1)
  · have frameAccount :
        ((round depth state).batch.frames.map Frame.allocation) =
          state.batch.frames.map Frame.allocation ++ state.matchers.flatMap (Lane.allocations depth) := by
      simp only [round, CollectionOccurrenceBatch.State.round, CollectionOccurrenceBatch.State.install,
        List.map_map, List.map_append]
      change (state.batch.frames.map Frame.allocation ++
        (state.matchers.flatMap (Lane.allocations depth)).map (fun allocation => allocation)) = _
      exact congrArg (state.batch.frames.map Frame.allocation ++ ·) (List.map_id _)
    rw [frameAccount]
    apply (valid.2.append_right _).trans
    apply (List.flatMap_append_perm state.matchers (Lane.account depth) (Lane.allocations depth)).trans
    simp only [round, List.flatMap_map]
    apply List.Perm.of_eq
    apply List.flatMap_congr
    intro lane _
    exact Lane.allocation_balance depth lane

theorem run_invariant (depth work : Nat) {state : State plan bound expected source}
    (valid : Invariant depth state) : Invariant depth (run depth work state) := by
  induction work generalizing state with
  | zero => exact valid
  | succ work ih => exact ih (round_invariant depth valid)

theorem log_prefix (depth work : Nat) (state : State plan bound expected source) :
    state.batch.log <+: (run depth work state).batch.log := by
  induction work generalizing state with
  | zero => exact List.prefix_refl _
  | succ work ih =>
    exact (List.prefix_append _ _).trans (ih (round depth state))

/-- New matching publications append fresh work after the retained frames.
Every earlier continuation receives its next quantum in place. -/
theorem round_retains_frames (depth : Nat) (state : State plan bound expected source) :
    state.batch.frames.map (Frame.run 1) <+: (round depth state).batch.frames := by
  exact (CollectionOccurrenceBatch.State.install_frames_prefix _ state.batch).map (Frame.run 1)

theorem run_retains_frames (depth work : Nat) (state : State plan bound expected source) :
    state.batch.frames.map (Frame.run work) <+: (run depth work state).batch.frames := by
  induction work generalizing state with
  | zero =>
    have idle : (Frame.run 0 : Frame plan bound expected source → _) = id := by
      funext frame
      cases frame
      rfl
    simp only [run, idle, List.map_id]
    exact List.prefix_refl _
  | succ work ih =>
    have preserved := ((round_retains_frames depth state).map (Frame.run work)).trans
      (ih (round depth state))
    simpa only [run, List.map_map, Function.comp_def, ← Frame.run_add, Nat.add_comm 1 work]
      using preserved

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

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceMachine
