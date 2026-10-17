import Mettapedia.Logic.DerivationGraph

/-!
# Borrowed cursors for finite derivation graphs

Source addresses are distinct from chronological cache positions. The worker
reads the supplied node and its ordered premise occurrences; it does not build
an expanded proof tree or call the comparison materializer. Inference meaning
comes from the existing independent `RuleWitness` interface.

Raw states are execution data, not authenticated evidence. Sound reuse requires
a checked prefix in the same rule system and source snapshot. Native ownership,
source decoding and physical indexing costs remain separate refinements.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.DerivationGraph.BorrowedCursor

universe u v w

variable {J : Type u} {W : Type v} {Origin : Type w}
variable {rules : List J → J → Prop}

abbrev NodeId := Nat
abbrev IndexMap := List (NodeId × Nat)

structure StoredNode (J : Type u) (W : Type v) (Origin : Type w) where
  conclusion : J
  request : W
  parents : List NodeId
  origin : Origin
  deriving DecidableEq

structure Store (J : Type u) (W : Type v) (Origin : Type w) where
  revision : Nat
  read : NodeId → Option (StoredNode J W Origin)

/-- The map contains only already checked source nodes. Its list representation
is an executable specification, rather than a claimed native indexing bound. -/
def indexAt : IndexMap → NodeId → Option Nat
  | [], _ => none
  | (source, index) :: rest, wanted =>
      if source = wanted then some index else indexAt rest wanted

structure State (J : Type u) where
  revision : Nat
  checked : IndexMap
  cache : Array J
  deriving DecidableEq

def start (store : Store J W Origin) : State J := ⟨store.revision, [], #[]⟩

/-- Resolve ordered source edges. Neither equal edges nor equal judgments are
deduplicated. This function does not inspect any source theorem payload. -/
def resolveParents (checked : IndexMap) : List NodeId → Option (List Nat)
  | [] => some []
  | source :: rest => do
      let index ← indexAt checked source
      let indices ← resolveParents checked rest
      pure (index :: indices)

/-- The actual worker reads checked values directly through source addresses. -/
def premiseValues (state : State J) : List NodeId → Option (List J)
  | [] => some []
  | source :: rest =>
      match indexAt state.checked source with
      | none => none
      | some index => do
          let fact ← state.cache[index]?
          let values ← premiseValues state rest
          pure (fact :: values)

/-- One borrowed step. Duplicate schedule entries, absent or unchecked parents,
changed revisions, and invalid rule instances refuse before publication. -/
def step (interface : RuleWitness rules) (store : Store J interface.W Origin)
    (state : State J) (source : NodeId) : Option (State J) :=
  if state.revision ≠ store.revision then none else
    if (indexAt state.checked source).isSome then none else
      match store.read source with
      | none => none
      | some node => do
          let values ← premiseValues state node.parents
          if interface.isInstance node.request values node.conclusion then
            pure ⟨state.revision, (source, state.cache.size) :: state.checked,
              state.cache.push node.conclusion⟩
          else none

/-- A finite schedule can be resumed from the exact retained state. -/
def run (interface : RuleWitness rules) (store : Store J interface.W Origin) :
    State J → List NodeId → Option (State J)
  | state, [] => some state
  | state, source :: rest => do
      let next ← step interface store state source
      run interface store next rest

/-- Materialization is a comparison specification. It reads source nodes and
relocates only their premise addresses; it is not called by `step` or `run`. -/
def materialize (store : Store J W Origin) : IndexMap → Nat → List NodeId →
    Option (List (Node J W Origin) × IndexMap)
  | checked, _, [] => some ([], checked)
  | checked, next, source :: rest =>
      if (indexAt checked source).isSome then none else
        match store.read source with
        | none => none
        | some node =>
            match resolveParents checked node.parents with
            | none => none
            | some parents => do
                let later ← materialize store ((source, next) :: checked) (next + 1) rest
                pure (⟨node.conclusion, node.request, parents, node.origin⟩ :: later.1, later.2)

/-- Ordered edge lookup is exactly lookup in the chronological checked cache,
when the source-address resolution succeeds. -/
theorem premiseValues_resolved (state : State J) {sources indices : List Nat}
    (resolved : resolveParents state.checked sources = some indices) :
    premiseValues state sources = DerivationGraph.lookupPremises state.cache indices := by
  induction sources generalizing indices with
  | nil => cases Option.some.inj resolved; rfl
  | cons source rest ih =>
      cases head : indexAt state.checked source with
      | none => simp [resolveParents, head] at resolved
      | some index =>
          cases tail : resolveParents state.checked rest with
          | none => simp [resolveParents, head, tail] at resolved
          | some later =>
              have shape : index :: later = indices := by
                simpa [resolveParents, head, tail] using resolved
              subst indices
              simp only [premiseValues, head]
              rw [ih tail]
              rfl

/-- A successful direct lookup has a complete chronological address vector. -/
theorem premiseValues_has_resolution (state : State J) {sources : List Nat}
    {values : List J} (found : premiseValues state sources = some values) :
    ∃ indices, resolveParents state.checked sources = some indices := by
  induction sources generalizing values with
  | nil => exact ⟨[], rfl⟩
  | cons source rest ih =>
      cases head : indexAt state.checked source with
      | none => simp [premiseValues, head] at found
      | some index =>
          cases value : state.cache[index]? with
          | none => simp [premiseValues, head, value] at found
          | some fact =>
              cases tail : premiseValues state rest with
              | none => simp [premiseValues, head, tail] at found
              | some earlier =>
                  obtain ⟨indices, resolved⟩ := ih tail
                  exact ⟨index :: indices, by simp [resolveParents, head, resolved]⟩

/-- Each successful borrowed step has exactly the ordinary chronological
receipt semantics, including the actual source rule and premise occurrences. -/
theorem step_correspondence (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (state next : State J) (source : NodeId)
    (accepted : step interface store state source = some next) :
    ∃ node parents, store.read source = some node ∧
      resolveParents state.checked node.parents = some parents ∧
      (⟨node.conclusion, node.request, parents, node.origin⟩ : Node J interface.W Origin).replay
        interface state.cache = some next.cache ∧
      next.checked = (source, state.cache.size) :: state.checked ∧
      next.revision = state.revision ∧
      next.cache = state.cache.push node.conclusion := by
  unfold step at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · cases read : store.read source with
      | none => simp [read] at accepted
      | some node =>
          cases values : premiseValues state node.parents with
          | none => simp [read, values] at accepted
          | some earlier =>
              simp [read, values] at accepted
              obtain ⟨valid, equal⟩ := accepted
              cases equal
              obtain ⟨parents, resolved⟩ := premiseValues_has_resolution state values
              have lookup : DerivationGraph.lookupPremises state.cache parents = some earlier :=
                (premiseValues_resolved state resolved).symm.trans values
              refine ⟨node, parents, rfl, resolved, ?_, rfl, rfl, rfl⟩
              simp [DerivationGraph.Node.replay, lookup, valid]

/-- One source address used twice supplies two theorem occurrences. -/
theorem repeated_parent (state : State J) (source index : Nat) (fact : J)
    (address : indexAt state.checked source = some index)
    (found : state.cache[index]? = some fact) :
    premiseValues state [source, source] = some [fact, fact] := by
  simp [premiseValues, address, found]

/-- The revision test is part of the actual execution, including resumed work. -/
theorem changed_revision_refused (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (state : State J) (source : NodeId)
    (changed : state.revision ≠ store.revision) : step interface store state source = none := by
  simp [step, changed]

/-- A source node is admitted at most once in a schedule. Separate source
nodes carrying equal requests are still separate accepted publications. -/
theorem step_fresh (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (state next : State J) (source : NodeId)
    (accepted : step interface store state source = some next) :
    indexAt state.checked source = none := by
  cases found : indexAt state.checked source with
  | none => rfl
  | some index =>
      by_cases changed : state.revision ≠ store.revision
      · simp [step, changed] at accepted
      · simp [step, changed, found] at accepted

/-- Successful cursor execution produces exactly a materialized chronological
replay, with the same checked results and address map. The implementation never
calls the materializer and never expands a dependency to a proof tree. -/
theorem run_materializes (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (state result : State J) (schedule : List NodeId)
    (accepted : run interface store state schedule = some result) :
    ∃ nodes, materialize store state.checked state.cache.size schedule =
        some (nodes, result.checked) ∧
      DerivationGraph.replayFrom interface state.cache nodes = some result.cache ∧
      result.revision = state.revision := by
  induction schedule generalizing state with
  | nil =>
      cases Option.some.inj accepted
      exact ⟨[], rfl, rfl, rfl⟩
  | cons source rest ih =>
      cases first : step interface store state source with
      | none => simp [run, first] at accepted
      | some next =>
          have remaining : run interface store next rest = some result := by
            simpa [run, first] using accepted
          obtain ⟨nodes, materialized, replayed, revision⟩ := ih next remaining
          obtain ⟨node, parents, read, resolved, receipt, checked, keptRevision, cache⟩ :=
            step_correspondence interface store state next source first
          have fresh := step_fresh interface store state next source first
          rw [checked, cache, Array.size_push] at materialized
          refine ⟨⟨node.conclusion, node.request, parents, node.origin⟩ :: nodes, ?_, ?_,
            revision.trans keptRevision⟩
          · simp [materialize, fresh, read, resolved, materialized]
          · simp only [DerivationGraph.replayFrom, receipt]
            exact replayed

/-- A direct source-node step and independently materialized receipt have the
same acceptance and output cache, provided the source admission checks pass. -/
theorem step_matches_receipt (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (state : State J) (source : NodeId) (node : StoredNode J interface.W Origin)
    (parents : List Nat) (revision : state.revision = store.revision)
    (fresh : indexAt state.checked source = none) (read : store.read source = some node)
    (resolved : resolveParents state.checked node.parents = some parents) :
    step interface store state source =
      ((⟨node.conclusion, node.request, parents, node.origin⟩ : Node J interface.W Origin).replay
        interface state.cache).map fun cache =>
          ⟨state.revision, (source, state.cache.size) :: state.checked, cache⟩ := by
  simp only [step]
  simp [revision, fresh, read, premiseValues_resolved state resolved,
    DerivationGraph.Node.replay]

/-- Conversely, a materialized chronological replay is accepted by the cursor.
Thus chronological replay is a comparison semantics, rather than an extra
trusted acceptance condition attached to an unrelated implementation. -/
theorem run_of_materialized (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (state : State J) (schedule : List NodeId)
    (nodes : List (Node J interface.W Origin)) (checked : IndexMap) (cache : Array J)
    (revision : state.revision = store.revision)
    (materialized : materialize store state.checked state.cache.size schedule =
      some (nodes, checked))
    (replayed : DerivationGraph.replayFrom interface state.cache nodes = some cache) :
    run interface store state schedule = some ⟨state.revision, checked, cache⟩ := by
  induction schedule generalizing state nodes checked cache with
  | nil =>
      have shape : ([], state.checked) = (nodes, checked) := Option.some.inj materialized
      cases shape
      cases Option.some.inj replayed
      rfl
  | cons source rest ih =>
      cases fresh : indexAt state.checked source with
      | some index => simp [materialize, fresh] at materialized
      | none =>
          cases read : store.read source with
          | none => simp [materialize, fresh, read] at materialized
          | some node =>
              cases resolved : resolveParents state.checked node.parents with
              | none => simp [materialize, fresh, read, resolved] at materialized
              | some parents =>
                  cases tail : materialize store ((source, state.cache.size) :: state.checked)
                      (state.cache.size + 1) rest with
                  | none => simp [materialize, fresh, read, resolved, tail] at materialized
                  | some pair =>
                      obtain ⟨later, finalMap⟩ := pair
                      have shape :
                          (⟨node.conclusion, node.request, parents, node.origin⟩ :: later,
                            finalMap) = (nodes, checked) := by
                        simpa [materialize, fresh, read, resolved, tail] using materialized
                      cases shape
                      let receipt : Node J interface.W Origin := ⟨node.conclusion, node.request, parents, node.origin⟩
                      cases first : receipt.replay interface state.cache with
                      | none => simp [DerivationGraph.replayFrom, receipt, first] at replayed
                      | some middle =>
                          have remaining : DerivationGraph.replayFrom interface
                              middle later = some cache := by
                            simpa [DerivationGraph.replayFrom, receipt, first] using replayed
                          let next : State J :=
                            ⟨state.revision, (source, state.cache.size) :: state.checked, middle⟩
                          have actual : step interface store state source = some next := by
                            rw [step_matches_receipt interface store state source node parents
                              revision fresh read resolved]
                            simpa [next, receipt] using congrArg
                              (fun value : Option (Array J) => value.map fun result =>
                                State.mk state.revision
                                  ((source, state.cache.size) :: state.checked) result) first
                          have grown : middle = state.cache.push node.conclusion :=
                            receipt.replay_eq_push interface first
                          have tail' : materialize store next.checked next.cache.size rest =
                              some (later, checked) := by
                            simpa [next, grown] using tail
                          have finish := ih next later checked cache revision tail' remaining
                          simpa [run, actual, next] using finish

/-- Exact two-way correspondence, including the address map and retained
revision, for a cursor admitted against the store's current revision. -/
theorem run_iff_materialized (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (state result : State J) (schedule : List NodeId)
    (revision : state.revision = store.revision) :
    run interface store state schedule = some result ↔
      ∃ nodes, materialize store state.checked state.cache.size schedule =
          some (nodes, result.checked) ∧
        DerivationGraph.replayFrom interface state.cache nodes = some result.cache ∧
        result.revision = state.revision := by
  constructor
  · exact run_materializes interface store state result schedule
  · rintro ⟨nodes, materialized, replayed, keptRevision⟩
    have accepted := run_of_materialized interface store state schedule nodes result.checked
      result.cache revision materialized replayed
    have shape : State.mk state.revision result.checked result.cache = result := by
      cases result
      simp_all
    exact accepted.trans (congrArg some shape)

/-- The retained cache and source-address map grow exactly once per checked
source node. This is a logical storage count, not an allocation or byte bound. -/
theorem run_publication_count (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (state result : State J) (schedule : List NodeId)
    (accepted : run interface store state schedule = some result) :
    result.cache.size = state.cache.size + schedule.length ∧
      result.checked.length = state.checked.length + schedule.length := by
  induction schedule generalizing state with
  | nil =>
      cases Option.some.inj accepted
      exact ⟨by simp, by simp⟩
  | cons source rest ih =>
      cases first : step interface store state source with
      | none => simp [run, first] at accepted
      | some next =>
          have remaining : run interface store next rest = some result := by
            simpa [run, first] using accepted
          obtain ⟨cacheCount, mapCount⟩ := ih next remaining
          obtain ⟨node, _, _, _, _, checked, _, cache⟩ :=
            step_correspondence interface store state next source first
          rw [cache, Array.size_push] at cacheCount
          rw [checked, List.length_cons] at mapCount
          constructor <;> simp only [List.length_cons] <;> omega

/-- Query an already checked root by its original source address. -/
def rootAt (state : State J) (source : NodeId) : Option J :=
  match indexAt state.checked source with
  | none => none
  | some index => state.cache[index]?

/-- A returned source-addressed root has a derivation in the existing complete
supplied rule system; source labels and addresses grant no logical authority. -/
theorem root_derivable (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (schedule : List NodeId) (result : State J)
    (accepted : run interface store (start store) schedule = some result)
    (source : NodeId) (claim : J) (found : rootAt result source = some claim) :
    Derives rules claim := by
  obtain ⟨nodes, _, replayed, _⟩ :=
    run_materializes interface store (start store) result schedule accepted
  cases address : indexAt result.checked source with
  | none => simp [rootAt, address] at found
  | some index =>
      have atIndex : result.cache[index]? = some claim := by simpa [rootAt, address] using found
      exact DerivationGraph.root_sound interface replayed atIndex

/-- Prefix and suffix schedules compose on the exact retained state. No source
node or committed check is replayed merely to resume the suffix. -/
theorem run_append (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (state : State J) (first later : List NodeId) :
    run interface store state (first ++ later) =
      (run interface store state first).bind (fun middle => run interface store middle later) := by
  induction first generalizing state with
  | nil => rfl
  | cons source rest ih =>
      simp only [List.cons_append, run]
      cases step interface store state source with
      | none => rfl
      | some next => exact ih next

/-- Read stability is local to actual source nodes on the schedule. This also
covers writes outside the read set when the store provider preserves revision.
A retained checked prefix additionally requires its earlier reads to be stable. -/
theorem run_read_stable (interface : RuleWitness rules)
    (left right : Store J interface.W Origin) (state : State J) (schedule : List NodeId)
    (revision : left.revision = right.revision)
    (reads : ∀ source ∈ schedule, left.read source = right.read source) :
    run interface left state schedule = run interface right state schedule := by
  induction schedule generalizing state with
  | nil => rfl
  | cons source rest ih =>
      have head : step interface left state source = step interface right state source := by
        simp only [step, revision, reads source (by simp)]
      simp only [run, head]
      cases step interface right state source with
      | none => rfl
      | some next => exact ih next (fun source member => reads source (by simp [member]))

/-- Appending a checked theorem preserves every earlier checked root, even
when the appended theorem is structurally equal to an earlier result. -/
theorem step_preserves_root (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (before after : State J) (source earlier : NodeId) (claim : J)
    (accepted : step interface store before source = some after)
    (found : rootAt before earlier = some claim) : rootAt after earlier = some claim := by
  obtain ⟨node, _, _, _, _, checked, _, cache⟩ :=
    step_correspondence interface store before after source accepted
  have fresh := step_fresh interface store before after source accepted
  cases address : indexAt before.checked earlier with
  | none => simp [rootAt, address] at found
  | some index =>
      have selected : before.cache[index]? = some claim := by
        simpa [rootAt, address] using found
      have different : source ≠ earlier := by
        intro equal
        subst source
        rw [fresh] at address
        cases address
      have inside : index < before.cache.size := (Array.getElem?_eq_some_iff.mp selected).1
      simp only [rootAt, checked, indexAt, if_neg different, address]
      change after.cache[index]? = some claim
      rw [cache, Array.getElem?_push, if_neg (Nat.ne_of_lt inside)]
      exact selected

/-- Accepted steps retain the complete earlier address map. -/
theorem run_checked_extension (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (before after : State J)
    (schedule : List NodeId) (accepted : run interface store before schedule = some after) :
    ∀ entry ∈ before.checked, entry ∈ after.checked := by
  induction schedule generalizing before with
  | nil => cases Option.some.inj accepted; exact fun _ present => present
  | cons source rest ih =>
      cases first : step interface store before source with
      | none => simp [run, first] at accepted
      | some next =>
          have later : run interface store next rest = some after := by
            simpa [run, first] using accepted
          obtain ⟨_, _, _, _, _, checked, _, _⟩ :=
            step_correspondence interface store before next source first
          intro entry present
          exact ih next later entry (by rw [checked]; exact List.mem_cons_of_mem _ present)

/-- Every performed source read is represented in the retained address map. -/
theorem run_sources_checked (interface : RuleWitness rules)
    (store : Store J interface.W Origin) (before after : State J)
    (schedule : List NodeId) (accepted : run interface store before schedule = some after) :
    ∀ source ∈ schedule, ∃ index, (source, index) ∈ after.checked := by
  induction schedule generalizing before with
  | nil => simp
  | cons source rest ih =>
      cases first : step interface store before source with
      | none => simp [run, first] at accepted
      | some next =>
          have later : run interface store next rest = some after := by
            simpa [run, first] using accepted
          obtain ⟨_, _, _, _, _, checked, _, _⟩ :=
            step_correspondence interface store before next source first
          intro wanted present
          rcases List.mem_cons.mp present with rfl | present
          · exact ⟨before.cache.size,
              run_checked_extension interface store next after rest later
                (wanted, before.cache.size) (by rw [checked]; simp)⟩
          · exact ih next later wanted present

/-- Explicitly replace the source revision after a separate dependency check. -/
def atRevision (revision : Nat) (state : State J) : State J :=
  { state with revision := revision }

theorem premiseValues_atRevision (revision : Nat) (state : State J) (sources : List NodeId) :
    premiseValues (atRevision revision state) sources = premiseValues state sources := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
      simp only [atRevision] at ih
      simp only [premiseValues, atRevision, ih]

/-- A coherent source node has the same computation under a newly admitted
revision. Updating the revision never changes premises or cached judgments. -/
theorem step_rebased_read_stable (interface : RuleWitness rules)
    (left right : Store J interface.W Origin) (state : State J) (source : NodeId)
    (current : state.revision = left.revision)
    (read : left.read source = right.read source) :
    step interface right (atRevision right.revision state) source =
      (step interface left state source).map (atRevision right.revision) := by
  have views := premiseValues_atRevision (J := J) right.revision state
  simp only [step, atRevision, current, ne_eq, not_true_eq_false, if_false]
  rw [read]
  by_cases seen : (indexAt state.checked source).isSome = true
  · simp [seen]
  · simp only [if_neg seen]
    simp only [atRevision] at views
    simp only [views]
    cases nodeRead : right.read source with
    | none => simp [seen]
    | some node =>
        cases values : premiseValues state node.parents with
        | none => simp [seen, values]
        | some premises =>
            by_cases valid : interface.isInstance node.request premises node.conclusion = true <;>
              simp [seen, values, valid, atRevision]

/-- Actual read coherence permits resumption after an unrelated source change,
including a different coarse revision. This is a two-way equality of execution,
not a claim that a revision label establishes coherence. -/
theorem run_rebased_read_stable (interface : RuleWitness rules)
    (left right : Store J interface.W Origin) (state : State J) (schedule : List NodeId)
    (current : state.revision = left.revision)
    (reads : ∀ source ∈ schedule, left.read source = right.read source) :
    run interface right (atRevision right.revision state) schedule =
      (run interface left state schedule).map (atRevision right.revision) := by
  induction schedule generalizing state with
  | nil => rfl
  | cons source rest ih =>
      simp only [run]
      rw [step_rebased_read_stable interface left right state source current
        (reads source (by simp))]
      cases first : step interface left state source with
      | none => rfl
      | some next =>
          simp only [Option.map_some]
          obtain ⟨_, _, _, _, _, _, revision, _⟩ :=
            step_correspondence interface left state next source first
          exact ih next (revision.trans current)
            (fun source present => reads source (List.mem_cons_of_mem _ present))

end Mettapedia.Logic.DerivationGraph.BorrowedCursor
