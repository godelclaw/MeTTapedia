import Mettapedia.CognitiveArchitecture.Agent.ContextCertificate
import Mettapedia.Logic.WorldModel.Generative

/-!
# A weak relational Atlas world-model core

This file formalizes the small semantic contract used by a shared research
Atlas.  An Atlas state retains source-scoped claims, explicit nongluing
witnesses, a conflict-audit state, and an opaque revision receipt.  Revision
is permissive union.  Extraction is a query-relative projection whose omitted
claims and hidden conflicts remain visible.

The interface deliberately assumes nothing cryptographic about revision or
receipt identities.  Concrete runtimes may use content digests as engineering
identifiers, but the theorems below rely only on the informative records.

The construction reuses the repository's representation-neutral `WorldModel`
and relational generative semantics.  It does not introduce a second
world-model foundation, a global gluing rule, or an action policy.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.RelationalAtlas

open Mettapedia.Logic.WorldModel.Generative

universe uSource uClaim uConflict uRevision uReceipt uQuery uPhase uViewId

/-- Whether the current claim carrier was actually checked for conflicts.
An empty conflict set under `unchecked` is not positive evidence of gluing. -/
inductive ConflictAudit where
  | unchecked
  | checked
deriving DecidableEq, Repr

/-- One finite, revision-bearing Atlas evidence state.  Identifiers are opaque:
the type does not identify equality with hash equality. -/
structure State
    (Source : Type uSource) (Claim : Type uClaim)
    (Conflict : Type uConflict) (Revision : Type uRevision)
    (Receipt : Type uReceipt) where
  revision : Revision
  sources : Finset Source
  claims : Finset Claim
  conflicts : Finset Conflict
  conflictAudit : ConflictAudit
  receipt : Receipt

/-- A weak query asks only for a finite claim carrier.  Ranking, lexical
retrieval, trust, and scheduling remain replaceable policies above this core. -/
structure Query (Claim : Type uClaim) where
  requested : Finset Claim

/-- The three query-relative outcomes used by the Atlas projection. -/
inductive Status where
  | witnessedGlobal
  | contextualFamily
  | unavailable
deriving DecidableEq, Repr

/-- An informative view retains projection loss and the visible/hidden split
of explicit nongluing witnesses before exposing a status readout. -/
structure View
    (Source : Type uSource) (Claim : Type uClaim)
    (Conflict : Type uConflict) (Revision : Type uRevision)
    (Receipt : Type uReceipt) where
  stateRevision : Revision
  selectedSources : Finset Source
  selectedClaims : Finset Claim
  omittedClaims : Finset Claim
  visibleConflicts : Finset Conflict
  hiddenConflicts : Finset Conflict
  conflictAudit : ConflictAudit
  status : Status
  receipt : Receipt

/-- Replaceable identity issuance for empty, revised, and extracted states. -/
structure Policy
    (Revision : Type uRevision) (Receipt : Type uReceipt)
    (Claim : Type uClaim) where
  emptyRevision : Revision
  emptyReceipt : Receipt
  combineRevision : Revision → Revision → Revision
  combineReceipt : Revision → Revision → Revision → Receipt
  viewReceipt : Revision → Query Claim → Receipt

section Core

variable {Source : Type uSource} {Claim : Type uClaim}
variable {Conflict : Type uConflict} {Revision : Type uRevision}
variable {Receipt : Type uReceipt}
variable [DecidableEq Source] [DecidableEq Claim] [DecidableEq Conflict]

/-- A conflict audit remains complete only when one checked input already
covers the combined claim and conflict carrier.  This is the permissive
runtime rule; newly adjacent evidence is not silently declared conflict-free. -/
def combineAudit
    (left right : State Source Claim Conflict Revision Receipt) : ConflictAudit := by
  classical
  exact if left.claims ⊆ right.claims ∧
      left.conflicts ⊆ right.conflicts ∧
      right.conflictAudit = .checked then
    .checked
  else if right.claims ⊆ left.claims ∧
      right.conflicts ⊆ left.conflicts ∧
      left.conflictAudit = .checked then
    .checked
  else
    .unchecked

/-- The empty Atlas state is positively audited. -/
def empty (policy : Policy Revision Receipt Claim) :
    State Source Claim Conflict Revision Receipt where
  revision := policy.emptyRevision
  sources := ∅
  claims := ∅
  conflicts := ∅
  conflictAudit := .checked
  receipt := policy.emptyReceipt

/-- Revision combines evidence without resolving or dropping a distinct
source, claim, or conflict. -/
def revise
    (policy : Policy Revision Receipt Claim)
    (left right : State Source Claim Conflict Revision Receipt) :
    State Source Claim Conflict Revision Receipt :=
  let revision := policy.combineRevision left.revision right.revision
  {
    revision := revision
    sources := left.sources ∪ right.sources
    claims := left.claims ∪ right.claims
    conflicts := left.conflicts ∪ right.conflicts
    conflictAudit := combineAudit left right
    receipt := policy.combineReceipt left.revision right.revision revision
  }

@[simp] theorem mem_revise_claims_iff
    (policy : Policy Revision Receipt Claim)
    (left right : State Source Claim Conflict Revision Receipt)
    (claim : Claim) :
    claim ∈ (revise policy left right).claims ↔
      claim ∈ left.claims ∨ claim ∈ right.claims := by
  simp [revise]

theorem revise_preserves_left_claims
    (policy : Policy Revision Receipt Claim)
    (left right : State Source Claim Conflict Revision Receipt) :
    left.claims ⊆ (revise policy left right).claims := by
  intro claim member
  exact (mem_revise_claims_iff policy left right claim).2 (Or.inl member)

theorem revise_preserves_right_claims
    (policy : Policy Revision Receipt Claim)
    (left right : State Source Claim Conflict Revision Receipt) :
    right.claims ⊆ (revise policy left right).claims := by
  intro claim member
  exact (mem_revise_claims_iff policy left right claim).2 (Or.inr member)

/-- Revision cannot invent a claim outside its two inputs. -/
theorem revise_no_claim_invention
    (policy : Policy Revision Receipt Claim)
    (left right : State Source Claim Conflict Revision Receipt)
    (claim : Claim)
    (member : claim ∈ (revise policy left right).claims) :
    claim ∈ left.claims ∨ claim ∈ right.claims :=
  (mem_revise_claims_iff policy left right claim).1 member

theorem combineAudit_checked_of_right_covers
    (left right : State Source Claim Conflict Revision Receipt)
    (claims : left.claims ⊆ right.claims)
    (conflicts : left.conflicts ⊆ right.conflicts)
    (checked : right.conflictAudit = .checked) :
    combineAudit left right = .checked := by
  simp [combineAudit, claims, conflicts, checked]

/-- Claims selected from the current state. -/
def selectedClaims
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) : Finset Claim :=
  state.claims ∩ query.requested

/-- Sources that actually support at least one selected claim. -/
def selectedSources
    (supports : Source → Claim → Prop) [DecidableRel supports]
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) : Finset Source :=
  state.sources.filter fun source =>
    ∃ claim ∈ selectedClaims state query, supports source claim

/-- A visible conflict has at least one endpoint in the selected view. -/
def visibleConflicts
    (conflictClaims : Conflict → Finset Claim)
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) : Finset Conflict :=
  state.conflicts.filter fun conflict =>
    (conflictClaims conflict ∩ selectedClaims state query).Nonempty

/-- Every retained conflict not visible in the result is reported as hidden;
this includes dangling conflicts whose endpoints are absent from the state. -/
def hiddenConflicts
    (conflictClaims : Conflict → Finset Claim)
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) : Finset Conflict :=
  state.conflicts \ visibleConflicts conflictClaims state query

/-- Status is query-relative.  A nonempty result is called globally witnessed
only when the carrier was checked and contains no explicit conflict. -/
def status
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) : Status :=
  if selectedClaims state query = ∅ then
    .unavailable
  else if state.conflictAudit = .checked ∧ state.conflicts = ∅ then
    .witnessedGlobal
  else
    .contextualFamily

/-- Extract a bounded view while retaining every omitted claim and hidden
conflict as data. -/
def extract
    (supports : Source → Claim → Prop) [DecidableRel supports]
    (conflictClaims : Conflict → Finset Claim)
    (policy : Policy Revision Receipt Claim)
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) : View Source Claim Conflict Revision Receipt where
  stateRevision := state.revision
  selectedSources := selectedSources supports state query
  selectedClaims := selectedClaims state query
  omittedClaims := state.claims \ selectedClaims state query
  visibleConflicts := visibleConflicts conflictClaims state query
  hiddenConflicts := hiddenConflicts conflictClaims state query
  conflictAudit := state.conflictAudit
  status := status state query
  receipt := policy.viewReceipt state.revision query

@[simp] theorem extract_stateRevision
    (supports : Source → Claim → Prop) [DecidableRel supports]
    (conflictClaims : Conflict → Finset Claim)
    (policy : Policy Revision Receipt Claim)
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) :
    (extract supports conflictClaims policy state query).stateRevision =
      state.revision := rfl

@[simp] theorem extract_receipt
    (supports : Source → Claim → Prop) [DecidableRel supports]
    (conflictClaims : Conflict → Finset Claim)
    (policy : Policy Revision Receipt Claim)
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) :
    (extract supports conflictClaims policy state query).receipt =
      policy.viewReceipt state.revision query := rfl

theorem status_witnessedGlobal_iff
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) :
    status state query = .witnessedGlobal ↔
      (selectedClaims state query).Nonempty ∧
      state.conflictAudit = .checked ∧ state.conflicts = ∅ := by
  by_cases selected : selectedClaims state query = ∅
  · simp [status, selected]
  · by_cases audited :
        state.conflictAudit = .checked ∧ state.conflicts = ∅
    · simp [status, selected, audited, Finset.nonempty_iff_ne_empty]
    · simp [status, selected, audited, Finset.nonempty_iff_ne_empty]

/-- An unchecked empty conflict list cannot be upgraded to a global result. -/
theorem unchecked_result_is_contextual
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim)
    (selected : (selectedClaims state query).Nonempty)
    (unchecked : state.conflictAudit = .unchecked) :
    status state query = .contextualFamily := by
  simp [status, Finset.nonempty_iff_ne_empty.mp selected, unchecked]

/-- A checked empty conflict list is positive evidence, not mere absence. -/
theorem checked_conflict_free_result_is_global
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim)
    (selected : (selectedClaims state query).Nonempty)
    (checked : state.conflictAudit = .checked)
    (conflictFree : state.conflicts = ∅) :
    status state query = .witnessedGlobal := by
  simp [status, Finset.nonempty_iff_ne_empty.mp selected, checked, conflictFree]

/-- Truncation or filtering cannot dissolve a retained conflict into a global
answer, even when every endpoint lies outside the selected suffix. -/
theorem retained_conflict_prevents_global
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim)
    (selected : (selectedClaims state query).Nonempty)
    (conflict : state.conflicts.Nonempty) :
    status state query = .contextualFamily := by
  have notEmpty : state.conflicts ≠ ∅ := Finset.nonempty_iff_ne_empty.mp conflict
  simp [status, Finset.nonempty_iff_ne_empty.mp selected, notEmpty]

theorem hidden_conflict_is_retained
    (conflictClaims : Conflict → Finset Claim)
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) (conflict : Conflict)
    (hidden : conflict ∈ hiddenConflicts conflictClaims state query) :
    conflict ∈ state.conflicts := by
  exact (Finset.mem_sdiff.mp hidden).1

theorem hidden_conflict_prevents_global
    (conflictClaims : Conflict → Finset Claim)
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) (conflict : Conflict)
    (selected : (selectedClaims state query).Nonempty)
    (hidden : conflict ∈ hiddenConflicts conflictClaims state query) :
    status state query = .contextualFamily := by
  exact retained_conflict_prevents_global state query selected
    ⟨conflict, hidden_conflict_is_retained conflictClaims state query conflict hidden⟩

/-- Positive losslessness and witnessed loss are kept distinct. -/
inductive LossAssertion where
  | lossless
  | lossy
deriving DecidableEq, Repr

def lossAssertion
    (view : View Source Claim Conflict Revision Receipt) : LossAssertion :=
  if view.omittedClaims = ∅ ∧ view.hiddenConflicts = ∅ then
    .lossless
  else
    .lossy

theorem lossAssertion_lossless_iff
    (view : View Source Claim Conflict Revision Receipt) :
    lossAssertion view = .lossless ↔
      view.omittedClaims = ∅ ∧ view.hiddenConflicts = ∅ := by
  simp [lossAssertion]

/-! ## The existing representation-neutral world-model interface -/

/-- The Atlas is an ordinary three-operation world model.  Concrete retrieval
and conflict relations are parameters, not kernel policy. -/
@[reducible] def asWorldModel
    (supports : Source → Claim → Prop) [DecidableRel supports]
    (conflictClaims : Conflict → Finset Claim)
    (policy : Policy Revision Receipt Claim) :
    _root_.WorldModel
      (State Source Claim Conflict Revision Receipt)
      (Query Claim)
      (View Source Claim Conflict Revision Receipt) where
  revise := revise policy
  empty := empty policy
  extract := extract supports conflictClaims policy

@[simp] theorem asWorldModel_extract
    (supports : Source → Claim → Prop) [DecidableRel supports]
    (conflictClaims : Conflict → Finset Claim)
    (policy : Policy Revision Receipt Claim)
    (state : State Source Claim Conflict Revision Receipt)
    (query : Query Claim) :
    (asWorldModel supports conflictClaims policy).extract state query =
      extract supports conflictClaims policy state query := rfl

end Core

/-! ## Revision currentness is independent of semantic status -/

/-- The exact identity returned across an Atlas transport boundary. -/
structure ReturnedResult
    (Revision : Type uRevision) (ViewId : Type uViewId)
    (Receipt : Type uReceipt) where
  stateRevision : Revision
  viewId : ViewId
  receipt : Receipt
  status : Status
deriving DecidableEq, Repr

/-- Currentness compares revisions; it does not assert truth, completeness, or
conflict freedom. -/
def Current
    {Revision : Type uRevision} {ViewId : Type uViewId}
    {Receipt : Type uReceipt}
    (expected : Revision) (result : ReturnedResult Revision ViewId Receipt) : Prop :=
  expected = result.stateRevision

theorem currentness_ignores_status
    {Revision : Type uRevision} {ViewId : Type uViewId}
    {Receipt : Type uReceipt}
    (expected : Revision) (result : ReturnedResult Revision ViewId Receipt)
    (newStatus : Status) :
    Current expected { result with status := newStatus } ↔
      Current expected result := by
  rfl

def currentContextualExample : ReturnedResult Nat Nat Nat where
  stateRevision := 7
  viewId := 11
  receipt := 13
  status := .contextualFamily

theorem current_does_not_mean_global :
    Current 7 currentContextualExample ∧
      currentContextualExample.status ≠ .witnessedGlobal := by
  constructor
  · rfl
  · intro impossible
    cases impossible

/-! ## Context-certificate bridge -/

section Certificate

open Mettapedia.CognitiveArchitecture.Agent.ContextCertificate

variable {Revision : Type uRevision} {ViewId : Type uViewId}
variable {Receipt : Type uReceipt} {QueryId : Type uQuery}
variable {Phase : Type uPhase} {ViewValue : Type uSource}
variable [DecidableEq QueryId]
variable [DecidableEq Revision] [DecidableEq ViewId] [DecidableEq Receipt]

/-- Put the returned Atlas identity into the source set of the next context
projection.  The context's aggregate evidence revision remains separate. -/
def contextPayload
    (contextRevision : Revision) (query : QueryId) (phase : Phase)
    (result : ReturnedResult Revision ViewId Receipt) (view : ViewValue) :
    ProjectionPayload Revision QueryId Phase
      (ReturnedResult Revision ViewId Receipt) ViewValue where
  evidenceRevision := contextRevision
  activeQueries := {query}
  commitmentPhase := phase
  sources := {result}
  view := view

theorem returned_result_enters_certificate
    (issuer : Issuer Revision QueryId Phase
      (ReturnedResult Revision ViewId Receipt) ViewValue Receipt)
    (contextRevision : Revision) (query : QueryId) (phase : Phase)
    (result : ReturnedResult Revision ViewId Receipt) (view : ViewValue) :
    result ∈ (certify issuer
      (contextPayload contextRevision query phase result view)).sources := by
  simp [contextPayload]

theorem certificate_retains_aggregate_revision
    (issuer : Issuer Revision QueryId Phase
      (ReturnedResult Revision ViewId Receipt) ViewValue Receipt)
    (contextRevision : Revision) (query : QueryId) (phase : Phase)
    (result : ReturnedResult Revision ViewId Receipt) (view : ViewValue) :
    (certify issuer
      (contextPayload contextRevision query phase result view)).evidenceRevision =
        contextRevision := by
  rfl

end Certificate

/-! ## Relational generative interpretation -/

section Generative

variable {Source : Type uSource} {Claim : Type uClaim}
variable {Conflict : Type uConflict} {Revision : Type uRevision}
variable {Receipt : Type uReceipt}
variable [DecidableEq Claim]

/-- A state relationally realizes exactly its retained claims.  No global
joint world or probabilistic coherence is assumed. -/
def claimSemantics :
    Semantics
      (State Source Claim Conflict Revision Receipt) Unit Claim where
  admissible state _ := state.claims.Nonempty
  realizes state _ claim := claim ∈ state.claims
  realizes_admissible := by
    intro state _ claim member
    exact ⟨claim, member⟩

theorem claimSemantics_entails_iff
    (state : State Source Claim Conflict Revision Receipt)
    (property : Claim → Prop) :
    Entails claimSemantics state property ↔
      ∀ claim ∈ state.claims, property claim := by
  constructor
  · intro entails claim member
    exact entails () claim member
  · intro allClaims _ claim member
    exact allClaims claim member

end Generative

end Mettapedia.CognitiveArchitecture.Agent.RelationalAtlas

#print axioms Mettapedia.CognitiveArchitecture.Agent.RelationalAtlas.revise_no_claim_invention
#print axioms Mettapedia.CognitiveArchitecture.Agent.RelationalAtlas.status_witnessedGlobal_iff
#print axioms Mettapedia.CognitiveArchitecture.Agent.RelationalAtlas.hidden_conflict_prevents_global
#print axioms Mettapedia.CognitiveArchitecture.Agent.RelationalAtlas.current_does_not_mean_global
#print axioms Mettapedia.CognitiveArchitecture.Agent.RelationalAtlas.returned_result_enters_certificate
#print axioms Mettapedia.CognitiveArchitecture.Agent.RelationalAtlas.claimSemantics_entails_iff
