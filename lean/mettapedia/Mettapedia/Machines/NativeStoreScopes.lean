import Mettapedia.Machines.NativeStoreTransactions

/-!
# Scoped validation for native stores

Complete scope views, including empty answers, replace whole-store revision
conflicts. Validation uses full records, not a query's lossy projection. Every
written row is covered, and write scopes are validated alongside read scopes.

The theorem is about observable scopes. Independent appends to an ordered
global journal need not commute as complete lists; their per-channel views
can remain unchanged. A matcher/codec implements these predicates, and the
storage owner must validate and publish without an intervening mutation.
-/

namespace Mettapedia.Machines.NativeStoreScopes

open SpaceService NativeStoreTransactions

def compatible (captured live : Store) (scopes : List Scope) : Bool :=
  scopes.all (fun scope => observe scope captured == observe scope live)

def commit (live : Store) (proposal : Proposal) (reads : List Scope) : Except Rejection Store :=
  if !covered proposal then .error .scope
  else if live.identity ≠ proposal.captured.identity then .error .identity
  else if !compatible proposal.captured live (proposal.writes :: reads) then .error .stale
  else .ok { live with
    revision := live.revision + 1
    rows := applyBatch live.rows proposal.operations }

private theorem filter_erase_outside (rows : List Nat) (scope : Scope) (row : Nat)
    (outside : scope row = false) :
    (rows.erase row).filter scope = rows.filter scope := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    by_cases same : head = row
    · subst head
      simp [outside]
    · simp [List.filter_cons, same, ih]

theorem mutation_outside_preserves_view (rows : List Nat) (scope : Scope)
    (operation : Mutation) (outside : scope operation.row = false) :
    (Mutation.apply rows operation).filter scope = rows.filter scope := by
  cases operation with
  | add row => simpa [Mutation.apply, Mutation.row, outside]
  | remove row => exact filter_erase_outside rows scope row outside

theorem batch_outside_preserves_view (rows : List Nat) (scope : Scope)
    (operations : List Mutation)
    (outside : ∀ operation ∈ operations, scope operation.row = false) :
    (applyBatch rows operations).filter scope = rows.filter scope := by
  induction operations generalizing rows with
  | nil => rfl
  | cons operation rest ih =>
    change (applyBatch (Mutation.apply rows operation) rest).filter scope = _
    rw [ih _ (fun op member => outside op (List.mem_cons_of_mem _ member))]
    exact mutation_outside_preserves_view rows scope operation (outside operation (by simp))

theorem compatible_of_foreign_batch (captured : Store) (scopes : List Scope)
    (operations : List Mutation) (revision : Nat)
    (outside : ∀ scope ∈ scopes, ∀ operation ∈ operations, scope operation.row = false) :
    compatible captured
      { captured with revision := revision, rows := applyBatch captured.rows operations } scopes = true := by
  simp only [compatible, List.all_eq_true]
  intro scope member
  have stable := batch_outside_preserves_view captured.rows scope operations (outside scope member)
  simpa [observe] using stable.symm

/-- An unrelated mutation may advance the physical journal revision. It does
not invalidate a proposal whose complete dependency views are unchanged. -/
theorem independent_batch_does_not_conflict (proposal : Proposal) (reads : List Scope)
    (foreign : List Mutation) (revision : Nat)
    (writes : covered proposal = true)
    (outside : ∀ scope ∈ proposal.writes :: reads,
      ∀ operation ∈ foreign, scope operation.row = false) :
    commit { proposal.captured with
      revision := revision
      rows := applyBatch proposal.captured.rows foreign } proposal reads =
      .ok { proposal.captured with
        revision := revision + 1
        rows := applyBatch (applyBatch proposal.captured.rows foreign) proposal.operations } := by
  simp [commit, writes, compatible_of_foreign_batch proposal.captured _ foreign revision outside]

theorem valid_views_include_absence (captured live : Store) (scopes : List Scope)
    (valid : compatible captured live scopes = true)
    (scope : Scope) (member : scope ∈ scopes) (absent : observe scope captured = []) :
    observe scope live = [] := by
  have same := (List.all_eq_true.mp valid) scope member
  simpa [absent] using same.symm

theorem changing_a_negative_dependency_conflicts :
    let initial : Store := ⟨1, 0, []⟩
    let proposal : Proposal := ⟨initial, (· == 7), [.add 7]⟩
    commit ⟨1, 1, [7]⟩ proposal [] = .error .stale := by decide

theorem one_occurrence_cannot_be_claimed_twice :
    let initial : Store := ⟨1, 0, [7]⟩
    let proposal : Proposal := ⟨initial, (· == 7), [.remove 7]⟩
    commit initial proposal [] = .ok ⟨1, 1, []⟩ ∧
      commit ⟨1, 1, []⟩ proposal [] = .error .stale := by decide

theorem scoped_validation_avoids_a_global_false_conflict :
    let initial : Store := ⟨1, 0, [0]⟩
    let proposal : Proposal := ⟨initial, fun n => n % 2 == 0, [.remove 0, .add 2]⟩
    NativeStoreTransactions.commit ⟨1, 1, [0, 1]⟩ proposal = .error .stale ∧
      commit ⟨1, 1, [0, 1]⟩ proposal [] = .ok ⟨1, 2, [1, 2]⟩ := by decide

/-- Do not turn scope independence into a false theorem about global history. -/
theorem disjoint_appends_need_not_commute_as_global_sequences :
    applyBatch [] [.add 7, .add 8] ≠ applyBatch [] [.add 8, .add 7] := by decide

/-- View equality alone does not retire a no-op request. The service also
uses one-use observation handles, independent of its bounded reply cache. -/
theorem views_alone_do_not_make_noop_retry_idempotent :
    let initial : Store := ⟨1, 0, [7]⟩
    let proposal : Proposal := ⟨initial, (· == 7), []⟩
    commit initial proposal [] = .ok ⟨1, 1, [7]⟩ ∧
      commit ⟨1, 1, [7]⟩ proposal [] = .ok ⟨1, 2, [7]⟩ := by decide

/-- None means the handle is retired; it says nothing about whether an
earlier publication was acknowledged. Application receipts answer that. -/
def useObservation (available : Bool) (live : Store) (proposal : Proposal)
    (reads : List Scope) : Bool × Option (Except Rejection Store) :=
  if available then (false, some (commit live proposal reads)) else (false, none)

theorem observation_is_one_use (available : Bool) (live later : Store)
    (proposal another : Proposal) (reads more : List Scope) :
    (useObservation (useObservation available live proposal reads).1 later another more).2 = none := by
  cases available <;> rfl

structure ResolvedBatch where
  identity : Nat
  revision : Nat
  operations : List Mutation

/-- The journal retains the original operations and the resolved physical
revision. It does not retain a dependency on the old process's lease table. -/
def resolve (live : Store) (proposal : Proposal) : ResolvedBatch :=
  ⟨live.identity, live.revision, proposal.operations⟩

def replay (live : Store) (record : ResolvedBatch) : Except Rejection Store :=
  if live.identity ≠ record.identity then .error .identity
  else if live.revision ≠ record.revision then .error .stale
  else .ok { live with
    revision := live.revision + 1
    rows := applyBatch live.rows record.operations }

/-- Replay assumes a valid journal prefix and a record made after successful
validation. It needs neither the old scopes nor their observation handle. -/
theorem accepted_publication_replays_from_resolved_record (live next : Store)
    (proposal : Proposal) (reads : List Scope)
    (accepted : commit live proposal reads = .ok next) :
    replay live (resolve live proposal) = .ok next := by
  unfold commit at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · simpa [replay, resolve] using accepted

theorem resolved_record_cannot_reapply (live : Store) (proposal : Proposal) :
    replay { live with revision := live.revision + 1 }
      (resolve live proposal) = .error .stale := by
  simp [replay, resolve]

/-! The same finite schedules are also executed against the native MeTTa
caller and an independent SQLite oracle. Retirement is explicit: it must
not be inferred from a successful mutation, because a rejected proposal
and a no-op both retire their observation too. -/

inductive ScopedCommand where
  | observe (name : Nat) (reads : List WriteScope) (writes : WriteScope)
  | external (operations : List Mutation)
  | commit (name : Nat) (operations : List Mutation)
  | close (name : Nat)
  | restart
deriving Repr

structure ScopedCapture where
  name : Nat
  captured : Store
  reads : List WriteScope
  writes : WriteScope

structure ScopedTrace where
  store : Store := ⟨1, 0, []⟩
  observations : List ScopedCapture := []

def scopedStep (state : ScopedTrace) (command : ScopedCommand) : String × ScopedTrace × List (List Nat) :=
  match command with
  | .observe name reads writes =>
      ("observed", { state with observations :=
        ⟨name, state.store, reads, writes⟩ :: state.observations.filter (·.name != name) },
        reads.map (fun scope => observe scope.admits state.store))
  | .external operations =>
      ("external", { state with store := { state.store with
        revision := state.store.revision + 1
        rows := applyBatch state.store.rows operations } }, [])
  | .commit name operations =>
      match state.observations.find? (·.name == name) with
      | none => ("retired", state, [])
      | some captured =>
          let retired := { state with observations := state.observations.filter (·.name != name) }
          match commit state.store ⟨captured.captured, captured.writes.admits, operations⟩
              (captured.reads.map WriteScope.admits) with
          | .ok next => ("committed", { retired with store := next }, [])
          | .error .scope => ("scope", retired, [])
          | .error .stale => ("stale", retired, [])
          | .error .identity => ("identity", retired, [])
  | .close name =>
      (if state.observations.any (·.name == name) then "closed" else "retired",
        { state with observations := state.observations.filter (·.name != name) }, [])
  | .restart => ("restarted", { state with observations := [] }, [])

def scopedTraceLines (state : ScopedTrace) : List ScopedCommand → List String
  | [] => []
  | command :: rest =>
      let (status, next, views) := scopedStep state command
      (status ++ "|" ++ toString next.store.revision ++ "|" ++ reprStr next.store.rows ++
        "|" ++ reprStr views) :: scopedTraceLines next rest

end Mettapedia.Machines.NativeStoreScopes
