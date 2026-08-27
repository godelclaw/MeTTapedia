import ProtectedPlasticity

/-!
# IterAuthoring — a live authoring criterion for hosted Iter

This file isolates the authoring mismatch found while auditing the hosted Iter
adapter against `patham9/iter` at revision
`f4064d97849ecaccac7939315a3f1a68de15c3ef`.

The upstream reducer reloads active transformation files before each request.
Writing such a file therefore leaves the current request snapshot unchanged
and makes the program available at the next capture.  A protected-source
proposal is a different object: until a separate principal promotes it, the
active directory has not changed.  Advertising only that proposal operation
as Iter's structured authoring surface therefore fails the next-capture
criterion, even though a separately available shell can still write the
directory.

The repair is deliberately small.  Direct authoring changes only the mutable
development store, returns a receipt bound to the resulting store revision,
and leaves Iter's replace-or-stutter reducer unchanged.  Syntax failure is
already local and transactional by
`IterArchitecture.failed_transformation_is_transactional`.

The natural numbers below are opaque program identities.  Lists model exact
directory revisions; runtime receipts strengthen these identities with source
digests.
-/

namespace IterAuthoring

open IterArchitecture

/-! ## Active programs and separately pending proposals -/

/-- The upstream-observed program store plus proposals that are not yet in it. -/
structure HostedStore where
  programs : ProgramStore
  pending : List Nat
deriving Repr, DecidableEq

def emptyHostedStore : HostedStore := ⟨emptyStore, []⟩

/-- Capture the active directory for a new request. -/
def nextCapture (store : HostedStore) : HostedStore :=
  { store with programs := reload store.programs }

/-- The old structured surface creates evidence for another principal but does
not change the directory observed by Iter. -/
def proposalWrite (store : HostedStore) (program : Nat) : HostedStore :=
  { store with pending := program :: store.pending }

/-- The upstream-compatible operation writes the mutable transformation
directory.  It does not mutate the request-local loaded snapshot. -/
def directWrite (store : HostedStore) (program : Nat) : HostedStore :=
  { store with programs := install store.programs program }

/-- A structured authoring surface is live when every authored program is
present in the request snapshot obtained by the next capture. -/
def HasNextCaptureActivation
    (author : HostedStore → Nat → HostedStore) : Prop :=
  ∀ store program,
    program ∈ (nextCapture (author store program)).programs.loaded

theorem direct_write_preserves_current_capture
    (store : HostedStore) (program : Nat) :
    (directWrite store program).programs.loaded = store.programs.loaded := by
  rfl

theorem direct_write_has_next_capture_activation :
    HasNextCaptureActivation directWrite := by
  intro store program
  simp [nextCapture, directWrite, install, reload]

/-- The proposal-only surface does not satisfy Iter's authoring contract.  The
empty store and program `7` are a concrete counterexample. -/
theorem proposal_only_lacks_next_capture_activation :
    ¬ HasNextCaptureActivation proposalWrite := by
  intro claimed
  have impossible := claimed emptyHostedStore 7
  simp [emptyHostedStore, emptyStore, proposalWrite, nextCapture, reload] at impossible

/-- This pair is the formal diagnosis: the hosted proposal surface fails the
property that direct upstream-compatible authoring satisfies. -/
theorem exact_authoring_gap :
    ¬ HasNextCaptureActivation proposalWrite ∧
      HasNextCaptureActivation directWrite :=
  ⟨proposal_only_lacks_next_capture_activation,
    direct_write_has_next_capture_activation⟩

/-! ## Repetition does not turn a proposal into an active program -/

def proposeAll : List Nat → HostedStore → HostedStore
  | [], store => store
  | program :: rest, store => proposeAll rest (proposalWrite store program)

theorem proposals_do_not_change_program_store
    (proposals : List Nat) (store : HostedStore) :
    (proposeAll proposals store).programs = store.programs := by
  induction proposals generalizing store with
  | nil => rfl
  | cons program rest ih =>
      simpa [proposeAll, proposalWrite] using ih (proposalWrite store program)

theorem arbitrarily_many_pending_proposals_remain_inactive
    (proposals : List Nat) :
    (nextCapture (proposeAll proposals emptyHostedStore)).programs.loaded = [] := by
  change (proposeAll proposals emptyHostedStore).programs.disk = []
  rw [proposals_do_not_change_program_store]
  rfl

/-! ## The shell witness prevents an overclaim -/

/-- A shell write has the same store effect as direct structured authoring.
The diagnosed defect is therefore a missing structured seam, not global
incapacity of the agent process. -/
def shellWrite : HostedStore → Nat → HostedStore := directWrite

theorem shell_write_refutes_global_authoring_incapacity :
    HasNextCaptureActivation shellWrite :=
  direct_write_has_next_capture_activation

/-! ## Revision-bound receipts -/

/-- The mathematical receipt retains exact before/after directory revisions.
The runtime representation additionally hashes every source byte. -/
structure ActivationReceipt where
  program : Nat
  beforeRevision : List Nat
  activationRevision : List Nat
deriving Repr, DecidableEq

def directWriteWithReceipt (store : HostedStore) (program : Nat) :
    HostedStore × ActivationReceipt :=
  let next := directWrite store program
  (next, {
    program := program
    beforeRevision := store.programs.disk
    activationRevision := next.programs.disk
  })

theorem receipt_binds_installed_revision
    (store : HostedStore) (program : Nat) :
    (directWriteWithReceipt store program).2.activationRevision =
      (directWriteWithReceipt store program).1.programs.disk := by
  rfl

theorem receipted_write_activates_at_next_capture
    (store : HostedStore) (program : Nat) :
    program ∈
      (nextCapture (directWriteWithReceipt store program).1).programs.loaded := by
  simp [directWriteWithReceipt, directWrite, nextCapture, install, reload]

/-! ## Protected-plasticity integration -/

/-- Direct authoring is an ordinary developmental revision; it does not need a
new constitution, scheduler, or promotion kernel. -/
def authorDevelopment {K L : Type}
    (state : ProtectedPlasticity.Coordinates K HostedStore L)
    (program : Nat) : ProtectedPlasticity.Coordinates K HostedStore L :=
  ProtectedPlasticity.revise state (fun store => directWrite store program)

theorem repaired_authoring_preserves_kernel_and_life_and_activates
    {K L : Type}
    (state : ProtectedPlasticity.Coordinates K HostedStore L)
    (program : Nat) :
    let next := authorDevelopment state program
    next.kernel = state.kernel ∧
      next.life = state.life ∧
      program ∈ (nextCapture next.development).programs.loaded := by
  simp [authorDevelopment, ProtectedPlasticity.revise, nextCapture,
    directWrite, install, reload]

end IterAuthoring

/-! ## Axiom audit -/
#print axioms IterAuthoring.direct_write_has_next_capture_activation
#print axioms IterAuthoring.proposal_only_lacks_next_capture_activation
#print axioms IterAuthoring.exact_authoring_gap
#print axioms IterAuthoring.arbitrarily_many_pending_proposals_remain_inactive
#print axioms IterAuthoring.shell_write_refutes_global_authoring_incapacity
#print axioms IterAuthoring.receipt_binds_installed_revision
#print axioms IterAuthoring.receipted_write_activates_at_next_capture
#print axioms IterAuthoring.repaired_authoring_preserves_kernel_and_life_and_activates
