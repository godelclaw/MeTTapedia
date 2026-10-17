import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Logic.DerivationGraph.CheckedCursor

/-!
# Checking a stored HOL proof graph through a borrowed cursor

The source store is read through stable node addresses. The checker retains a
source-address-to-cache-position map and checked results; it does not construct
or rewrite a source proof tree. Its rule dispatcher is the existing complete
HOL Light dispatcher, including all ten inference operations and the selected
axiom policy. A separate materializer is used only to state correspondence to
chronological proof replay.

The store revision is an admission condition, not a collision-prone digest.
A provider must ensure that an unchanged revision preserves all previously
read nodes. These abstract read-only laws do not establish a native pointer,
allocation, or zero-copy implementation theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.BorrowedProofCursor

open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open ProofExecution (Origin Receipt)

open Mettapedia.Logic.DerivationGraph

abbrev NodeId := BorrowedCursor.NodeId
abbrev IndexMap := BorrowedCursor.IndexMap
abbrev StoredNode := BorrowedCursor.StoredNode Theorem RuleRequest Origin
abbrev Store := BorrowedCursor.Store Theorem RuleRequest Origin
abbrev State := BorrowedCursor.State Theorem

abbrev indexAt := BorrowedCursor.indexAt
abbrev start (store : Store) := BorrowedCursor.start store
abbrev resolveParents := BorrowedCursor.resolveParents
abbrev premiseValues (state : State) := BorrowedCursor.premiseValues state
abbrev step (policy : AxiomPolicy) [DecidablePred policy] (store : Store)
    (state : State) (source : NodeId) : Option State :=
  BorrowedCursor.step (ruleWitness policy) store state source
abbrev run (policy : AxiomPolicy) [DecidablePred policy] (store : Store)
    (state : State) (schedule : List NodeId) : Option State :=
  BorrowedCursor.run (ruleWitness policy) store state schedule
abbrev materialize (store : Store) := BorrowedCursor.materialize store
abbrev rootAt (state : State) := BorrowedCursor.rootAt state

theorem premiseValues_resolved (state : State) {sources indices : List Nat}
    (resolved : resolveParents state.checked sources = some indices) :
    premiseValues state sources = DerivationGraph.lookupPremises state.cache indices :=
  BorrowedCursor.premiseValues_resolved state resolved

theorem premiseValues_has_resolution (state : State) {sources : List Nat}
    {values : List Theorem} (found : premiseValues state sources = some values) :
    ∃ indices, resolveParents state.checked sources = some indices :=
  BorrowedCursor.premiseValues_has_resolution state found

theorem step_correspondence (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (state next : State) (source : NodeId)
    (accepted : step policy store state source = some next) :
    ∃ node parents, store.read source = some node ∧
      resolveParents state.checked node.parents = some parents ∧
      (⟨node.conclusion, node.request, parents, node.origin⟩ : Receipt).replay
        (ruleWitness policy) state.cache = some next.cache ∧
      next.checked = (source, state.cache.size) :: state.checked ∧
      next.revision = state.revision ∧
      next.cache = state.cache.push node.conclusion :=
  BorrowedCursor.step_correspondence (ruleWitness policy) store state next source accepted

theorem repeated_parent (state : State) (source index : Nat) (fact : Theorem)
    (address : indexAt state.checked source = some index)
    (found : state.cache[index]? = some fact) :
    premiseValues state [source, source] = some [fact, fact] :=
  BorrowedCursor.repeated_parent state source index fact address found

theorem changed_revision_refused (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (state : State) (source : NodeId)
    (changed : state.revision ≠ store.revision) : step policy store state source = none :=
  BorrowedCursor.changed_revision_refused (ruleWitness policy) store state source changed

theorem step_fresh (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (state next : State) (source : NodeId)
    (accepted : step policy store state source = some next) :
    indexAt state.checked source = none :=
  BorrowedCursor.step_fresh (ruleWitness policy) store state next source accepted

theorem run_materializes (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (state result : State) (schedule : List NodeId)
    (accepted : run policy store state schedule = some result) :
    ∃ nodes, materialize store state.checked state.cache.size schedule =
        some (nodes, result.checked) ∧
      DerivationGraph.replayFrom (ruleWitness policy) state.cache nodes = some result.cache ∧
      result.revision = state.revision :=
  BorrowedCursor.run_materializes (ruleWitness policy) store state result schedule accepted

theorem step_matches_receipt (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (state : State) (source : NodeId) (node : StoredNode)
    (parents : List Nat) (revision : state.revision = store.revision)
    (fresh : indexAt state.checked source = none) (read : store.read source = some node)
    (resolved : resolveParents state.checked node.parents = some parents) :
    step policy store state source =
      ((⟨node.conclusion, node.request, parents, node.origin⟩ : Receipt).replay
        (ruleWitness policy) state.cache).map fun cache =>
          ⟨state.revision, (source, state.cache.size) :: state.checked, cache⟩ :=
  BorrowedCursor.step_matches_receipt (ruleWitness policy) store state source node parents revision fresh read resolved

theorem run_of_materialized (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (state : State) (schedule : List NodeId)
    (nodes : List Receipt) (checked : IndexMap) (cache : Array Theorem)
    (revision : state.revision = store.revision)
    (materialized : materialize store state.checked state.cache.size schedule =
      some (nodes, checked))
    (replayed : DerivationGraph.replayFrom (ruleWitness policy) state.cache nodes = some cache) :
    run policy store state schedule = some ⟨state.revision, checked, cache⟩ :=
  BorrowedCursor.run_of_materialized (ruleWitness policy) store state schedule nodes checked cache revision materialized replayed

theorem run_iff_materialized (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (state result : State) (schedule : List NodeId)
    (revision : state.revision = store.revision) :
    run policy store state schedule = some result ↔
      ∃ nodes, materialize store state.checked state.cache.size schedule =
          some (nodes, result.checked) ∧
        DerivationGraph.replayFrom (ruleWitness policy) state.cache nodes = some result.cache ∧
        result.revision = state.revision :=
  BorrowedCursor.run_iff_materialized (ruleWitness policy) store state result schedule revision

theorem run_publication_count (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (state result : State) (schedule : List NodeId)
    (accepted : run policy store state schedule = some result) :
    result.cache.size = state.cache.size + schedule.length ∧
      result.checked.length = state.checked.length + schedule.length :=
  BorrowedCursor.run_publication_count (ruleWitness policy) store state result schedule accepted

theorem root_derivable (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (schedule : List NodeId) (result : State)
    (accepted : run policy store (start store) schedule = some result)
    (source : NodeId) (claim : Theorem) (found : rootAt result source = some claim) :
    Derives (Rule policy) claim :=
  BorrowedCursor.root_derivable (ruleWitness policy) store schedule result accepted source claim found

theorem run_append (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (state : State) (first later : List NodeId) :
    run policy store state (first ++ later) =
      (run policy store state first).bind (fun middle => run policy store middle later) :=
  BorrowedCursor.run_append (ruleWitness policy) store state first later

theorem run_read_stable (policy : AxiomPolicy) [DecidablePred policy]
    (left right : Store) (state : State) (schedule : List NodeId)
    (revision : left.revision = right.revision)
    (reads : ∀ source ∈ schedule, left.read source = right.read source) :
    run policy left state schedule = run policy right state schedule :=
  BorrowedCursor.run_read_stable (ruleWitness policy) left right state schedule revision reads

theorem step_preserves_root (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (before after : State) (source earlier : NodeId) (claim : Theorem)
    (accepted : step policy store before source = some after)
    (found : rootAt before earlier = some claim) : rootAt after earlier = some claim :=
  BorrowedCursor.step_preserves_root (ruleWitness policy) store before after source earlier claim accepted found

/-- Retained checked work is indexed by its actual source and axiom policy.
Native theorem-handle authentication is a separate implementation contract. -/
abbrev CheckedCursor (policy : AxiomPolicy) [DecidablePred policy] (store : Store) :=
  BorrowedCursor.CheckedCursor (ruleWitness policy) store

def beginChecked (policy : AxiomPolicy) [DecidablePred policy] (store : Store) :
    CheckedCursor policy store :=
  BorrowedCursor.CheckedCursor.begin (ruleWitness policy) store

/-- The complete original HOL checker can independently replay every protected
cursor root. No expansion is performed on the execution path. -/
theorem checked_root_has_certificate (policy : AxiomPolicy) [DecidablePred policy]
    (store : Store) (cursor : CheckedCursor policy store) (source : NodeId) (claim : Theorem)
    (found : rootAt cursor.state source = some claim) :
    ∃ certificate, (ProofSystem.checker policy).check claim certificate = true := by
  obtain ⟨nodes, root, accepted⟩ := cursor.root_has_certificate source claim found
  obtain ⟨cache, replayed, rooted⟩ :=
    (CheckedJudgment.mint_iff (ruleWitness policy) nodes root claim).mp accepted
  exact ⟨(nodes, root), (ProofSystem.checker_check_iff policy claim (nodes, root)).mpr
    ⟨cache, replayed, rooted⟩⟩

namespace Controls

open ProofExecution.Controls

def reflexiveNode : StoredNode :=
  ⟨reflexivityTheorem, .inference (.refl proposition), [], ("stored", 101)⟩

def sharedTransitivity : StoredNode :=
  ⟨reflexivityTheorem, .inference (.trans reflexivityTheorem reflexivityTheorem),
    [101, 101], ("stored", 305)⟩

def missingOccurrence : StoredNode :=
  { sharedTransitivity with parents := [101] }

def proofStore : Store :=
  ⟨7, fun source =>
    if source = 101 then some reflexiveNode
    else if source = 305 then some sharedTransitivity
    else if source = 306 then some missingOccurrence
    else none⟩

/-- Sparse store addresses are unrelated to chronological cache positions. -/
def firstState : State := ⟨7, [(101, 0)], #[reflexivityTheorem]⟩
def finalState : State :=
  ⟨7, [(305, 1), (101, 0)], #[reflexivityTheorem, reflexivityTheorem]⟩

private theorem refl_instance :
    (RuleRequest.inference (.refl proposition)).isInstance emptyAxiomPolicy []
      reflexivityTheorem = true := by
  have checked : checkRefl proposition = some reflexivityTheorem :=
    (checkRefl_eq_some_iff _ _).mpr
      ⟨equality, CanonicalTerm.equalityOfSameType_semantics _ _ rfl, rfl, rfl, rfl⟩
  exact (RuleRequest.isInstance_eq_true_iff _ _ _ _).mpr
    ⟨rfl, (checkRefl_eq_some_iff _ _).mp checked⟩

private theorem trans_instance :
    (RuleRequest.inference (.trans reflexivityTheorem reflexivityTheorem)).isInstance
      emptyAxiomPolicy [reflexivityTheorem, reflexivityTheorem] reflexivityTheorem = true := by
  apply (RuleRequest.isInstance_eq_true_iff _ _ _ _).mpr
  refine ⟨rfl, proposition, proposition, proposition, proposition, equality,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl,
    CanonicalTerm.equalityOfSameType_semantics _ _ rfl, ?_⟩
  simp [HasParts, reflexivityTheorem, Theorem.emptyResult]

theorem first_step : step emptyAxiomPolicy proofStore (start proofStore) 101 =
    some firstState := by
  simp [step, BorrowedCursor.step, proofStore, BorrowedCursor.start, BorrowedCursor.indexAt, BorrowedCursor.premiseValues, reflexiveNode, ruleWitness,
    refl_instance, firstState]

theorem second_step : step emptyAxiomPolicy proofStore firstState 305 =
    some finalState := by
  simp [step, BorrowedCursor.step, proofStore, firstState, BorrowedCursor.indexAt, BorrowedCursor.premiseValues, sharedTransitivity, ruleWitness,
    trans_instance, finalState]

theorem sparse_shared_graph_accepted :
    run emptyAxiomPolicy proofStore (start proofStore) [101, 305] = some finalState := by
  simp [run, BorrowedCursor.run, first_step, second_step]

theorem separate_publications_retained :
    (run emptyAxiomPolicy proofStore (start proofStore) [101, 305]).map
      (fun state => state.cache.size) = some 2 := by
  rw [sparse_shared_graph_accepted]
  rfl

theorem repeated_edge_retained :
    premiseValues firstState [101, 101] = some [reflexivityTheorem, reflexivityTheorem] :=
  repeated_parent firstState 101 0 reflexivityTheorem rfl rfl

theorem missing_edge_rejected :
    run emptyAxiomPolicy proofStore (start proofStore) [101, 306] = none := by
  simp only [run, BorrowedCursor.run, first_step]
  simp [BorrowedCursor.step, proofStore, firstState, missingOccurrence, sharedTransitivity,
    BorrowedCursor.premiseValues, BorrowedCursor.indexAt, ruleWitness, RuleRequest.isInstance, RuleRequest.premises,
    InferenceRequest.premises]

theorem forward_reference_rejected :
    run emptyAxiomPolicy proofStore (start proofStore) [305, 101] = none := by decide

theorem absent_node_rejected :
    step emptyAxiomPolicy proofStore (start proofStore) 999 = none := by decide

theorem duplicate_schedule_rejected :
    run emptyAxiomPolicy proofStore (start proofStore) [101, 101] = none := by
  simp only [run, BorrowedCursor.run, first_step]
  simp [BorrowedCursor.step, firstState, BorrowedCursor.indexAt, proofStore]

theorem resumed_suffix_accepted :
    run emptyAxiomPolicy proofStore firstState [305] = some finalState := by
  simp [run, BorrowedCursor.run, second_step]

theorem stale_resume_rejected :
    step emptyAxiomPolicy { proofStore with revision := 8 } firstState 305 = none := by decide

/-- A non-read node can change without disturbing a checked schedule. The
revision provider permits this only when its read-stability contract allows it. -/
def unrelatedWrite : Store :=
  { proofStore with read := fun source =>
      if source = 999 then some missingOccurrence else proofStore.read source }

theorem unrelated_write_accepted :
    run emptyAxiomPolicy unrelatedWrite (start unrelatedWrite) [101, 305] = some finalState := by
  have same := run_read_stable emptyAxiomPolicy proofStore unrelatedWrite
    (start proofStore) [101, 305] rfl (by
      intro source member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl)
  exact same.symm.trans sparse_shared_graph_accepted

theorem returned_root_derivable : Derives (Rule emptyAxiomPolicy) reflexivityTheorem :=
  root_derivable emptyAxiomPolicy proofStore [101, 305] finalState
    sparse_shared_graph_accepted 305 reflexivityTheorem rfl

end Controls

end Mettapedia.Languages.HOLLight.BorrowedProofCursor
