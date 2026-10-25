import Mettapedia.GSLT.LanguageDef.OperationContracts
import Mettapedia.Machines.NativeCostLedger
import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Machines.ReadyQueue
import Mettapedia.Machines.ValidatedCommit
import Mettapedia.GSLT.Contracts.IndexedAuthority
import Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

/-!
# Operation invoices, retained budgets and cursor outcomes

A declaration associates each named charge with a native ledger kind, or
explicitly leaves it unknown. Its inspection bound is an allowance, not a
termination proof. A handler's conformance to its invoice is a separate
implementation obligation: the laws below concern the declared protocol.

The protocol authorizes an invoice before running the action. Refusal retains
the world and its complete account. Accepted actions retain their invoice on
failure and suspension as well as success. Work is the existing native ledger
valuation; scheduler inspections and billed work remain distinct quantities.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OperationCostProtocol

open Mettapedia.GSLT.LanguageDef.OperationContracts
open Mettapedia.GSLT.LanguageDef.MacroExportPlan (Atom)
open Mettapedia.Machines

/-! ## Declared may-reads versus captured read manifests

A declared footprint bounds which resources an implementation may read.  It
does not record that a particular read occurred.  The interface below joins
that declaration boundary to the existing adaptive-query certificate without
identifying them: `Conforms` checks the declared resource abstraction, while
`Complete` separately requires the manifest to be the exact ordered list of
observed `(key, value)` occurrences.

Exactness intentionally retains repeated reads and their order.  A separately
proved compressed validation certificate may be useful, but it is not this
observation.  Native-handler conformance and native observer coverage remain
realization obligations; these definitions do not establish either. -/

namespace ObservedReadManifest

open Mettapedia.GSLT.LanguageDef.OperationContracts

variable {Resource Key Value Answer : Type}

/-- The concrete read footprint represented by an ordered read observation. -/
def footprint (observed : ReadOnlyQuery.Reads Key Value) : Footprint Key :=
  ⟨observed.map Prod.fst, []⟩

/-- Complete capture has two independent obligations: every actual read stays
inside the declared may-read footprint, and the retained manifest contains the
exact ordered observations.  The first obligation alone is insufficient for a
validated commit. -/
def Complete (abstract : Key → Resource) (declared : Footprint Resource)
    (observed manifest : ReadOnlyQuery.Reads Key Value) : Prop :=
  Conforms abstract (footprint observed) declared ∧ manifest = observed

/-- The canonical adaptive-query runner supplies exact capture when its actual
read footprint conforms to the declaration. -/
theorem run_complete (abstract : Key → Resource) (declared : Footprint Resource)
    (store : Key → Value) (program : ReadOnlyQuery.Program Key Value Answer)
    (conforms : Conforms abstract (footprint (ReadOnlyQuery.run store program).reads) declared) :
    Complete abstract declared (ReadOnlyQuery.run store program).reads
      (ReadOnlyQuery.run store program).reads :=
  ⟨conforms, rfl⟩

/-- An exact captured manifest agrees whenever the actual observations agree. -/
theorem complete_agrees (abstract : Key → Resource) (declared : Footprint Resource)
    (store : Key → Value) {observed manifest : ReadOnlyQuery.Reads Key Value}
    (complete : Complete abstract declared observed manifest)
    (agrees : ReadOnlyQuery.Agrees store observed) :
    ReadOnlyQuery.Agrees store manifest := by
  rw [complete.2]
  exact agrees

/-- An accepted validated publication whose manifest completely captures the
actual observations has all three boundaries simultaneously: the actual reads
conform to the declared may-footprint, the proposal carries those exact
ordered observations, and those observations agree with the current store.
The resulting store applies exactly the proposal's writes.

This is a model composition theorem. It does not prove that a native observer
captured every read, that native writes realize `proposal.writes`, or that an
effect declaration by itself supplies either fact. -/
theorem commit_of_complete_capture [DecidableEq Key] [DecidableEq Value]
    (abstract : Key → Resource) (declared : Footprint Resource)
    (observed : ReadOnlyQuery.Reads Key Value)
    (proposal : ValidatedCommit.Proposal Key Value)
    (complete : Complete abstract declared observed proposal.reads)
    (current next : Key → Value)
    (accepted : ValidatedCommit.commit current proposal = some next) :
    Conforms abstract (footprint observed) declared ∧
      proposal.reads = observed ∧
      ReadOnlyQuery.Agrees current observed ∧
      next = ValidatedCommit.write current proposal.writes := by
  have manifestAgrees : ReadOnlyQuery.Agrees current proposal.reads := by
    unfold ValidatedCommit.commit at accepted
    split at accepted
    · rename_i checked
      exact (ReadOnlyQuery.checkReads_iff _ _).mp checked
    · contradiction
  have observedAgrees : ReadOnlyQuery.Agrees current observed := by
    rw [← complete.2]
    exact manifestAgrees
  have exactWrite := ValidatedCommit.commit_of_agrees current proposal manifestAgrees
  rw [exactWrite] at accepted
  exact ⟨complete.1, complete.2, observedAgrees, (Option.some.inj accepted).symm⟩

namespace Controls

/-- The second key is selected by the first observed value. -/
def adaptive : ReadOnlyQuery.Program Nat Nat Nat :=
  .read 0 fun selected => .read selected fun value => .pure value

def snapshot : Nat → Nat
  | 0 => 1
  | 1 => 7
  | _ => 0

def changed : Nat → Nat
  | 0 => 1
  | 1 => 8
  | _ => 0

def observed : ReadOnlyQuery.Reads Nat Nat :=
  (ReadOnlyQuery.run snapshot adaptive).reads

def missing : ReadOnlyQuery.Reads Nat Nat := [(0, 1)]

def declared : Footprint String := ⟨["space"], []⟩

def abstract (_ : Nat) : String := "space"

def declaration : Atom :=
  exampleOperation "space-read" "space_read" (footprintAtom ["space"] []) "no" "no"

def operation : Option Operation := decodeOperation declaration

def placement : Option WorkerPlacementAdvice := examplePlacement declaration

def writes : ValidatedCommit.Writes Nat Nat :=
  [(2, (ReadOnlyQuery.run snapshot adaptive).answer)]

def completeProposal : ValidatedCommit.Proposal Nat Nat := ⟨observed, writes⟩

def missingProposal : ValidatedCommit.Proposal Nat Nat := ⟨missing, writes⟩

/-- Positive: the adaptive run captures both ordered observations, conforms to
the declared may-read and detects a change in the selected dependency. -/
theorem complete_capture_detects_selected_change :
    observed = [(0, 1), (1, 7)] ∧
      Complete abstract declared observed observed ∧
      ReadOnlyQuery.checkReads changed observed = false := by
  refine ⟨rfl, ?_, rfl⟩
  exact ⟨by simp [Conforms, footprint, observed, adaptive, snapshot, abstract, declared,
    ReadOnlyQuery.run], rfl⟩

/-- Negative: coordinator placement and declaration conformance do not fill a
manifest.  Dropping the selected read accepts precisely the change that the
complete manifest rejects. -/
theorem may_read_placement_does_not_capture_a_missing_read :
    operation.map Operation.footprint = some (some declared) ∧
      placement = some .coordinator ∧
      Conforms abstract (footprint observed) declared ∧
      ¬ Complete abstract declared observed missing ∧
      ReadOnlyQuery.checkReads changed missing = true ∧
      ReadOnlyQuery.checkReads changed observed = false := by
  refine ⟨by decide, by decide, ?_, ?_, rfl, rfl⟩
  · simp [Conforms, footprint, observed, adaptive, snapshot, abstract, declared,
      ReadOnlyQuery.run]
  · simp [Complete, missing, observed, adaptive, snapshot, ReadOnlyQuery.run]

/-- Positive publication control: exact adaptive capture licenses the existing
current-store validator and exposes the declaration, exact manifest, current
agreement and resulting write in one theorem. -/
theorem complete_capture_justifies_validated_publication :
    ValidatedCommit.commit snapshot completeProposal =
        some (ValidatedCommit.write snapshot writes) ∧
      Conforms abstract (footprint observed) declared ∧
      completeProposal.reads = observed ∧
      ReadOnlyQuery.Agrees snapshot observed := by
  have complete : Complete abstract declared observed completeProposal.reads := by
    exact ⟨by simp [Conforms, footprint, observed, adaptive, snapshot, abstract, declared,
      ReadOnlyQuery.run], rfl⟩
  have accepted : ValidatedCommit.commit snapshot completeProposal =
      some (ValidatedCommit.write snapshot writes) := by rfl
  have joined := commit_of_complete_capture abstract declared observed completeProposal
    complete snapshot (ValidatedCommit.write snapshot writes) accepted
  exact ⟨accepted, joined.1, joined.2.1, joined.2.2.1⟩

/-- Negative publication control: declaration and coordinator placement remain
true, yet omitting the adaptive second read admits stale writes. The exact
proposal refuses the same changed store. -/
theorem declaration_without_capture_cannot_justify_publication :
    operation.map Operation.footprint = some (some declared) ∧
      placement = some .coordinator ∧
      Conforms abstract (footprint observed) declared ∧
      ¬ Complete abstract declared observed missingProposal.reads ∧
      ValidatedCommit.commit changed missingProposal =
        some (ValidatedCommit.write changed writes) ∧
      (ValidatedCommit.write changed writes) 2 = 7 ∧
      (ReadOnlyQuery.run changed adaptive).answer = 8 ∧
      ValidatedCommit.commit changed completeProposal = none := by
  refine ⟨by decide, by decide, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp [Conforms, footprint, observed, adaptive, snapshot, abstract, declared,
      ReadOnlyQuery.run]
  · simp [Complete, missingProposal, missing, observed, adaptive, snapshot,
      ReadOnlyQuery.run]

end Controls

#print axioms run_complete
#print axioms complete_agrees
#print axioms commit_of_complete_capture
#print axioms Controls.complete_capture_detects_selected_change
#print axioms Controls.may_read_placement_does_not_capture_a_missing_read
#print axioms Controls.complete_capture_justifies_validated_publication
#print axioms Controls.declaration_without_capture_cannot_justify_publication

end ObservedReadManifest

abbrev Kind := NativeCostLedger.Kind
abbrev Event := NativeCostLedger.Event

/-- The native receipt vocabulary, rather than a second cost-category type. -/
def kindName : Kind → String
  | .quantum => "quantum" | .candidateRow => "candidateRow" | .indexVisit => "indexVisit"
  | .matchAttempt => "matchAttempt" | .matchNode => "matchNode" | .heapLookup => "heapLookup"
  | .heapIndexVisit => "heapIndexVisit" | .heapUpdate => "heapUpdate" | .receiptAppend => "receiptAppend"
  | .bindingClone => "bindingClone" | .queueInsert => "queueInsert" | .queueTake => "queueTake"
  | .queueVisit => "queueVisit" | .queueMove => "queueMove" | .capture => "capture" | .restore => "restore"
  | .frameAllocate => "frameAllocate" | .frameRetire => "frameRetire" | .publish => "publish"
  | .coefficientAppend => "coefficientAppend" | .coefficientMultiply => "coefficientMultiply"
  | .costRead => "costRead" | .analysisStep => "analysisStep" | .workerDispatch => "workerDispatch"
  | .workerJoin => "workerJoin" | .commitCheck => "commitCheck" | .equationActivation => "equationActivation"
  | .storageProbe => "storageProbe" | .coefficientHandle => "coefficientHandle"

def decodeKind : String → Option Kind
  | "quantum" => some .quantum
  | "candidateRow" => some .candidateRow
  | "indexVisit" => some .indexVisit
  | "matchAttempt" => some .matchAttempt
  | "matchNode" => some .matchNode
  | "heapLookup" => some .heapLookup
  | "heapIndexVisit" => some .heapIndexVisit
  | "heapUpdate" => some .heapUpdate
  | "receiptAppend" => some .receiptAppend
  | "bindingClone" => some .bindingClone
  | "queueInsert" => some .queueInsert
  | "queueTake" => some .queueTake
  | "queueVisit" => some .queueVisit
  | "queueMove" => some .queueMove
  | "capture" => some .capture
  | "restore" => some .restore
  | "frameAllocate" => some .frameAllocate
  | "frameRetire" => some .frameRetire
  | "publish" => some .publish
  | "coefficientAppend" => some .coefficientAppend
  | "coefficientMultiply" => some .coefficientMultiply
  | "costRead" => some .costRead
  | "analysisStep" => some .analysisStep
  | "workerDispatch" => some .workerDispatch
  | "workerJoin" => some .workerJoin
  | "commitCheck" => some .commitCheck
  | "equationActivation" => some .equationActivation
  | "storageProbe" => some .storageProbe
  | "coefficientHandle" => some .coefficientHandle
  | _ => none

theorem decodeKind_name (kind : Kind) : decodeKind (kindName kind) = some kind := by
  cases kind <;> decide

inductive Progress where
  | single | bounded | steps | suspends | unknown
deriving DecidableEq, Repr

def Progress.name : Progress → String
  | .single => "single" | .bounded => "bounded" | .steps => "steps"
  | .suspends => "suspends" | .unknown => "unknown"

def decodeProgress : String → Option Progress
  | "single" => some .single | "bounded" => some .bounded | "steps" => some .steps
  | "suspends" => some .suspends | "unknown" => some .unknown | _ => none

inductive Replay where
  | transparent | refused
deriving DecidableEq, Repr

def Replay.name : Replay → String
  | .transparent => "transparent" | .refused => "refused"

def decodeReplay : String → Option Replay
  | "transparent" => some .transparent | "refused" => some .refused | _ => none

structure Profile where
  operation : String
  kinds : List (String × Option Kind)
  progress : Progress
  bound : Option Nat
  replay : Replay
deriving DecidableEq, Repr

/-- `none` remains unknown; it is not the known empty charge list. -/
def Profile.nativeKinds (profile : Profile) : Option (List Kind) := profile.kinds.mapM (·.2)

def boundOk (progress : Progress) (bound : Option Nat) : Bool :=
  match progress, bound with
  | .single, some 1 => true
  | .bounded, none => true
  | .bounded, some n => decide (0 < n)
  | .steps, none | .suspends, none | .unknown, none => true
  | _, _ => false

def decodeKindBinding : Atom → Option (String × Option Kind)
  | .list [.symbol label, .text "unknown"] => some (label, none)
  | .list [.symbol label, .symbol name] => (decodeKind name).map fun kind => (label, some kind)
  | _ => none

def decodeBound : Atom → Option (Option Nat)
  | .text "unknown" => some none
  | value => (LayoutDeclarations.number value).map some

/-- The additional record leaves the existing operation record unchanged. -/
def decodeProfile : Atom → Option Profile
  | .list [.symbol "cesta-operation-protocol/1", .symbol operation,
      .list (.symbol "ChargeKinds" :: kinds),
      .list [.symbol "Progress", .text progress, .list [.symbol "Bound", bound]],
      .list [.symbol "Replay", .text replay]] => do
      pure ⟨operation, ← kinds.mapM decodeKindBinding, ← decodeProgress progress,
        ← decodeBound bound, ← decodeReplay replay⟩
  | _ => none

def profileOk (operation : Operation) (profile : Profile) : Bool :=
  profile.operation == operation.name && profile.kinds.map Prod.fst == operation.charges &&
    profile.progress.name == operation.progress && profile.replay.name == operation.replay &&
    boundOk profile.progress profile.bound

def admitted (operationAtom profileAtom : Atom) : Bool :=
  match decodeOperation operationAtom, decodeProfile profileAtom with
  | some operation, some profile => profileOk operation profile
  | _, _ => false

theorem source_of_admitted {oa pa : Atom} (accepted : admitted oa pa = true) :
    ∃ operation profile, decodeOperation oa = some operation ∧ decodeProfile pa = some profile ∧
      profile.operation = operation.name ∧ profile.kinds.map Prod.fst = operation.charges ∧
      profile.progress.name = operation.progress ∧ profile.replay.name = operation.replay ∧
      boundOk profile.progress profile.bound = true := by
  unfold admitted at accepted
  cases ho : decodeOperation oa with
  | none => rw [ho] at accepted; simp at accepted
  | some operation =>
      cases hp : decodeProfile pa with
      | none => rw [ho, hp] at accepted; simp at accepted
      | some profile =>
          rw [ho, hp] at accepted
          simp only [profileOk, Bool.and_eq_true, beq_iff_eq] at accepted
          exact ⟨operation, profile, rfl, rfl, accepted.1.1.1.1, accepted.1.1.1.2,
            accepted.1.1.2, accepted.1.2, accepted.2⟩

/-! ## Exact budget debit over the native receipt -/

def work (events : List Event) : Nat := (NativeCostLedger.totals events).2

@[simp] theorem work_nil : work [] = 0 := rfl

@[simp] theorem work_cons (event : Event) (events : List Event) :
    work (event :: events) = event.2.units + work events := by
  simp [work, NativeCostLedger.totals, NativeCostLedger.eventGrade]

theorem work_append (first second : List Event) : work (first ++ second) = work first + work second := by
  rw [work, NativeCostLedger.totals_append]
  rfl

/-- Subtraction is performed only after a successful comparison. No summed
machine-word accumulator is required by this algorithm. -/
def debit : Nat → List Event → Option Nat
  | remaining, [] => some remaining
  | remaining, event :: rest =>
      if event.2.units ≤ remaining then debit (remaining - event.2.units) rest else none

theorem debit_some_iff (remaining after : Nat) (events : List Event) :
    debit remaining events = some after ↔ work events ≤ remaining ∧ after + work events = remaining := by
  induction events generalizing remaining with
  | nil => simp [debit, eq_comm]
  | cons event events ih =>
      simp only [debit, work_cons]
      split
      · rw [ih]; omega
      · rename_i denied
        constructor
        · simp
        · rintro ⟨bounded, _⟩; omega

theorem debit_none_iff (remaining : Nat) (events : List Event) :
    debit remaining events = none ↔ remaining < work events := by
  cases h : debit remaining events with
  | none =>
      simp only [true_iff]
      by_contra notLess
      have fit : work events ≤ remaining := by omega
      have accepted := (debit_some_iff remaining (remaining - work events) events).mpr ⟨fit, by omega⟩
      rw [h] at accepted
      cases accepted
  | some after =>
      have bound := ((debit_some_iff remaining after events).mp h).1
      simp; omega

/-- A retained budget can be debited in any chronological chunking. -/
theorem debit_append (remaining : Nat) (first second : List Event) :
    debit remaining (first ++ second) = (debit remaining first).bind (fun rest => debit rest second) := by
  induction first generalizing remaining with
  | nil => rfl
  | cons event first ih =>
      simp only [List.cons_append, debit]
      split <;> simp_all

structure Account where
  remaining : Nat
  inspections : Option Nat
  calls : Nat
  events : List Event
deriving DecidableEq, Repr

def initial (profile : Profile) (budget : Nat) : Account := ⟨budget, profile.bound, 0, []⟩

inductive Refusal where
  | unknownCharge | replayForbidden | undeclaredKind | repeatedIdentity | budget | inspectionLimit
deriving DecidableEq, Repr

/-- Successful inspection allowance consumption is separate from event work. -/
def inspectAllowance : Option Nat → Except Refusal (Option Nat)
  | none => .ok none
  | some 0 => .error .inspectionLimit
  | some (n + 1) => .ok (some n)

/-- Admission precedes the action. A replay licence never waives charging or
permits a retained physical event identity to be charged a second time. -/
def prepare (profile : Profile) (replay : Bool) (invoice : List Event) (account : Account) :
    Except Refusal Account :=
  if replay && profile.replay != .transparent then .error .replayForbidden
  else match profile.nativeKinds with
  | none => .error .unknownCharge
  | some kinds =>
      if !(invoice.all fun event => kinds.contains event.2.kind) then .error .undeclaredKind
      else if !decide ((account.events ++ invoice).map Prod.fst).Nodup then .error .repeatedIdentity
      else match debit account.remaining invoice with
      | none => .error .budget
      | some remaining => match inspectAllowance account.inspections with
        | .error reason => .error reason
        | .ok inspections =>
            .ok ⟨remaining, inspections, account.calls + 1, account.events ++ invoice⟩

theorem prepare_ok {profile : Profile} {replay : Bool} {invoice : List Event}
    {before after : Account} (accepted : prepare profile replay invoice before = .ok after) :
    after.remaining + work invoice = before.remaining ∧
      after.events = before.events ++ invoice ∧ after.calls = before.calls + 1 ∧
      inspectAllowance before.inspections = .ok after.inspections := by
  unfold prepare at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · split at accepted
      · contradiction
      · split at accepted
        · contradiction
        · split at accepted
          · contradiction
          · rename_i remaining hd
            split at accepted
            · contradiction
            · rename_i inspections hi
              cases accepted
              exact ⟨((debit_some_iff _ _ _).mp hd).2, rfl, rfl, hi⟩

/-- Every accepted event has one of the declared actual native kinds. An
unknown binding cannot be silently treated as an empty invoice signature. -/
theorem prepare_known {profile : Profile} {replay : Bool} {invoice : List Event}
    {before after : Account} (accepted : prepare profile replay invoice before = .ok after) :
    ∃ kinds, profile.nativeKinds = some kinds ∧ ∀ event ∈ invoice, event.2.kind ∈ kinds := by
  cases hk : profile.nativeKinds with
  | none =>
      unfold prepare at accepted
      split at accepted
      · contradiction
      · simp [hk] at accepted
  | some kinds =>
      refine ⟨kinds, rfl, ?_⟩
      have allowed : (invoice.all fun event => kinds.contains event.2.kind) = true := by
        cases ha : (invoice.all fun event => kinds.contains event.2.kind) with
        | true => rfl
        | false =>
            unfold prepare at accepted
            split at accepted
            · contradiction
            · simp only [hk] at accepted
              rw [ha] at accepted
              contradiction
      intro event member
      simpa using List.all_eq_true.mp allowed event member

/-- The append-only account rejects reuse of any retained physical event
identity. Native issuer authenticity is an additional implementation duty. -/
theorem prepare_unique {profile : Profile} {replay : Bool} {invoice : List Event}
    {before after : Account} (accepted : prepare profile replay invoice before = .ok after) :
    (after.events.map Prod.fst).Nodup := by
  have history := (prepare_ok accepted).2.1
  rw [history]
  by_contra repeated
  unfold prepare at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · split at accepted
      · contradiction
      · simp only [repeated, decide_false, Bool.not_false, if_true] at accepted
        contradiction

/-- Exact ordered history preservation also preserves each native kind's
counter, not merely an untyped total of all work. -/
theorem prepare_native_totals {profile : Profile} {replay : Bool} {invoice : List Event}
    {before after : Account} (accepted : prepare profile replay invoice before = .ok after) :
    NativeCostLedger.totals after.events =
      NativeCostLedger.totals before.events + NativeCostLedger.totals invoice := by
  rw [(prepare_ok accepted).2.1, NativeCostLedger.totals_append]

theorem inspectAllowance_ok {before after : Option Nat}
    (accepted : inspectAllowance before = .ok after) :
    ∀ bound, before = some bound → ∃ left, after = some left ∧ left + 1 = bound := by
  intro bound heq
  subst before
  cases bound with
  | zero => contradiction
  | succ bound =>
      simp only [inspectAllowance, Except.ok.injEq] at accepted
      exact ⟨bound, accepted.symm, rfl⟩

/-- Completed cost is never rolled back when a handler later faults. -/
theorem prepare_total {profile : Profile} {replay : Bool} {invoice : List Event}
    {before after : Account} (accepted : prepare profile replay invoice before = .ok after) :
    after.remaining + work after.events = before.remaining + work before.events := by
  obtain ⟨budget, history, _, _⟩ := prepare_ok accepted
  rw [history, work_append]
  omega

/-- A declared finite inspection allowance controls accepted calls even when
invoices contain no work. It does not assert that a handler succeeds. -/
theorem prepare_inspections {profile : Profile} {replay : Bool} {invoice : List Event}
    {before after : Account} (accepted : prepare profile replay invoice before = .ok after)
    {bound : Nat} (limited : before.inspections = some bound) :
    ∃ left, after.inspections = some left ∧ left + after.calls = bound + before.calls := by
  obtain ⟨_, _, calls, allowance⟩ := prepare_ok accepted
  obtain ⟨left, heq, decrement⟩ := inspectAllowance_ok allowance bound limited
  exact ⟨left, heq, by omega⟩

theorem unknown_charge_refused (profile : Profile) (invoice : List Event) (account : Account)
    (unknown : profile.nativeKinds = none) :
    prepare profile false invoice account = .error .unknownCharge := by
  simp [prepare, unknown]

theorem replay_refused (profile : Profile) (invoice : List Event) (account : Account)
    (unlicensed : profile.replay = .refused) :
    prepare profile true invoice account = .error .replayForbidden := by
  simp [prepare, unlicensed]

/-- A replay licence cannot make the second accepted invoice free. Each
acceptance consumes one call and all of its declared native work. -/
theorem prepare_twice {profile : Profile} {firstReplay secondReplay : Bool}
    {first second : List Event} {before middle after : Account}
    (one : prepare profile firstReplay first before = .ok middle)
    (two : prepare profile secondReplay second middle = .ok after) :
    after.remaining + work first + work second = before.remaining ∧
      after.calls = before.calls + 2 ∧ after.events = before.events ++ first ++ second := by
  obtain ⟨costOne, historyOne, callsOne, _⟩ := prepare_ok one
  obtain ⟨costTwo, historyTwo, callsTwo, _⟩ := prepare_ok two
  exact ⟨by omega, by omega, by rw [historyTwo, historyOne]⟩

/-! ## Complete service-slot receipts and progress realization

`ReadyQueue` already owns the whole-slot service account and its cumulative
bound.  The bridge below keeps one chronological native receipt, tags every
occurrence by the part of the slot that caused it, and projects that receipt
to the existing three-part ready-queue charge.  The phase tag does not replace
the native event identity or its order.

Progress metadata contributes an admission requirement.  It does not prove
that a handler meets a bound, yields with an exact residual, or executes behind
an isolation boundary; those are separate realization obligations.  Effect
declaration, current authority and ordered-output permission also remain
separate contracts.
-/

inductive HandlerBoundary where
  | local
  | isolated
deriving DecidableEq, Repr

inductive ProgressAdvice where
  | bounded (inspections : Nat)
  | yielding
  | isolated
  | unresolved
deriving DecidableEq, Repr

/-- Explicit isolation is a host choice.  A local bounded declaration retains
its positive inspection allowance; this number is not a work bound or a proof
of termination.  `steps`/`suspends` require a resumable yielding realization.
Unknown metadata remains unresolved. -/
def progressAdvice (profile : Profile) : HandlerBoundary → ProgressAdvice
  | .isolated => .isolated
  | .local =>
      match profile.progress, profile.bound with
      | .single, some 1 => .bounded 1
      | .bounded, some (bound + 1) => .bounded (bound + 1)
      | .steps, none | .suspends, none => .yielding
      | _, _ => .unresolved

/-- The three physical boundaries at which generated placement and progress
advice are consumed. A coordinator is still an inline service boundary; an
isolated handler is a separate execution boundary. -/
inductive ServiceBoundary where
  | worker
  | coordinator
  | isolated
deriving DecidableEq, Repr

/-- Bounded and yielding handlers may occupy a responsive inline slot.
Isolation and unresolved progress require another boundary. -/
def ProgressAdvice.inline : ProgressAdvice → Bool
  | .bounded _ | .yielding => true
  | .isolated | .unresolved => false

/-- Join effect-derived placement with progress advice at the selected native
boundary. This is admission advice, not a proof that a C handler conforms to
either declaration. -/
def admitsServiceBoundary (boundary : ServiceBoundary)
    (placement : WorkerPlacementAdvice) (progress : ProgressAdvice) : Bool :=
  match boundary with
  | .worker => placement == .local && progress.inline
  | .coordinator => placement != .unresolved && progress.inline
  | .isolated => placement != .unresolved && progress == .isolated

/-- Positive bounded/yielding controls and separating coordinator, isolated
and unresolved controls for the combined admission boundary. -/
theorem admitsServiceBoundary_controls :
    admitsServiceBoundary .worker .local (.bounded 1) = true ∧
    admitsServiceBoundary .worker .local .yielding = true ∧
    admitsServiceBoundary .worker .coordinator .yielding = false ∧
    admitsServiceBoundary .coordinator .coordinator .yielding = true ∧
    admitsServiceBoundary .coordinator .coordinator .isolated = false ∧
    admitsServiceBoundary .isolated .coordinator .isolated = true ∧
    admitsServiceBoundary .isolated .unresolved .isolated = false := by
  decide

#print axioms admitsServiceBoundary_controls

/-- Phases of the exact service receipt.  Arrival processing and queue
bookkeeping remain separate because the maintained ready-queue theorem prices
them separately from handling the visited task. -/
inductive SlotPhase where
  | admission
  | preparation
  | execution
  | delivery
  | teardown
  | arrivals
  | bookkeeping
deriving DecidableEq, Repr

abbrev PhasedEvent := SlotPhase × Event
abbrev SlotReceipt := List PhasedEvent

/-- Erasing phase tags preserves the exact chronological native receipt. -/
def slotInvoice (receipt : SlotReceipt) : List Event := receipt.map Prod.snd

/-- Project a phase-tagged receipt to the existing ready-queue charge.  The
first five phases are the complete handling lifecycle; arrivals and queue
bookkeeping retain their existing independent components. -/
def slotCharge : SlotReceipt → ReadyQueue.SlotCharge Nat
  | [] => ⟨0, 0, 0⟩
  | (phase, event) :: rest =>
      let later := slotCharge rest
      match phase with
      | .admission | .preparation | .execution | .delivery | .teardown =>
          ⟨event.2.units + later.handling, later.arrivals, later.bookkeeping⟩
      | .arrivals =>
          ⟨later.handling, event.2.units + later.arrivals, later.bookkeeping⟩
      | .bookkeeping =>
          ⟨later.handling, later.arrivals, event.2.units + later.bookkeeping⟩

/-- Phase projection neither loses nor duplicates work. -/
theorem slotCharge_total_eq_work (receipt : SlotReceipt) :
    (slotCharge receipt).total = work (slotInvoice receipt) := by
  induction receipt with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨phase, event⟩
      change (slotCharge rest).handling + (slotCharge rest).arrivals +
        (slotCharge rest).bookkeeping = work (rest.map Prod.snd) at ih
      cases phase <;>
        simp only [slotCharge, slotInvoice, List.map_cons, work_cons,
          ReadyQueue.SlotCharge.total] <;> omega

/-! ### Ordered native poll receipts

The retained-host poll account exposes exact callback counts and three work
deltas, but those aggregates do not contain occurrence order or identity.  A
lossless native boundary therefore needs the initial pending state, the final
step verdict and an ordered tagged native event list.  The last admission
verdict is derived from that list rather than stored a second time.

This is the model schema the native boundary can realize.  It is not a claim
that the current C aggregate already emits these events.
-/

namespace NativePoll

inductive AdmissionVerdict where
  | ready
  | paused
  | refused
  | invalidated
deriving DecidableEq, Repr

inductive StepVerdict where
  | returned
  | complete
  | paused
  | handoff
  | interrupted
deriving DecidableEq, Repr

/-- Tags whose counts or work deltas are exposed by one retained-host poll.
The native event still carries its physical identity, origin, ledger kind and
units.  A call marker may have zero units; a later native price may give it a
nonzero event without changing the schema. -/
inductive Tag where
  | setup
  | admission (verdict : AdmissionVerdict)
  | producer
  | sourceWork
  | preparation
  | consumer
  | transport
  | finalCurrent
  | retirement
deriving DecidableEq, Repr

abbrev Occurrence := Tag × Event

structure Receipt where
  initialPending : Bool
  step : StepVerdict
  occurrences : List Occurrence
deriving DecidableEq, Repr

abbrev History := List Receipt

def receiptEvents (receipt : Receipt) : List Event := receipt.occurrences.map Prod.snd

def historyEvents (history : History) : List Event := history.flatMap receiptEvents

theorem historyEvents_append (first second : History) :
    historyEvents (first ++ second) = historyEvents first ++ historyEvents second := by
  simp [historyEvents]

/-- The aggregate currently available at the native poll boundary.  `none`
means that no admission callback was observed. -/
structure Aggregate where
  initialPending : Bool
  step : StepVerdict
  lastAdmission : Option AdmissionVerdict := none
  setupWork : Nat := 0
  admissionCalls : Nat := 0
  producerCalls : Nat := 0
  consumerCalls : Nat := 0
  finalCurrentCalls : Nat := 0
  retirements : Nat := 0
  sourceWork : Nat := 0
  preparationWork : Nat := 0
  transportWork : Nat := 0
deriving DecidableEq, Repr

def addOccurrence (aggregate : Aggregate) (occurrence : Occurrence) : Aggregate :=
  match occurrence.1 with
  | .setup => { aggregate with setupWork := aggregate.setupWork + occurrence.2.2.units }
  | .admission verdict => { aggregate with
      lastAdmission := some verdict
      admissionCalls := aggregate.admissionCalls + 1 }
  | .producer => { aggregate with producerCalls := aggregate.producerCalls + 1 }
  | .sourceWork => { aggregate with
      sourceWork := aggregate.sourceWork + occurrence.2.2.units }
  | .preparation => { aggregate with
      preparationWork := aggregate.preparationWork + occurrence.2.2.units }
  | .consumer => { aggregate with consumerCalls := aggregate.consumerCalls + 1 }
  | .transport => { aggregate with
      transportWork := aggregate.transportWork + occurrence.2.2.units }
  | .finalCurrent => { aggregate with
      finalCurrentCalls := aggregate.finalCurrentCalls + 1 }
  | .retirement => { aggregate with retirements := aggregate.retirements + 1 }

def summarize (receipt : Receipt) : Aggregate :=
  receipt.occurrences.foldl addOccurrence
    { initialPending := receipt.initialPending, step := receipt.step }

/-- The generic slot phase is a deliberate erasure of the more precise native
poll tag. -/
def Tag.slotPhase : Tag → SlotPhase
  | .setup => .preparation
  | .admission _ => .admission
  | .producer | .sourceWork => .execution
  | .preparation => .preparation
  | .consumer | .transport | .finalCurrent => .delivery
  | .retirement => .teardown

def toSlotReceipt (receipt : Receipt) : SlotReceipt :=
  receipt.occurrences.map fun occurrence => (occurrence.1.slotPhase, occurrence.2)

/-- Erasing poll tags preserves the exact ordered native events. -/
theorem slotInvoice_toSlotReceipt (receipt : Receipt) :
    slotInvoice (toSlotReceipt receipt) = receiptEvents receipt := by
  unfold slotInvoice toSlotReceipt receiptEvents
  rw [List.map_map]
  apply List.map_congr_left
  intro occurrence _
  rfl

/-- The ordered schema is extensionally sufficient: initial pending state,
final verdict and the tagged occurrence sequence determine the receipt. -/
def orderedView (receipt : Receipt) : Bool × StepVerdict × List Occurrence :=
  (receipt.initialPending, receipt.step, receipt.occurrences)

theorem orderedView_injective : Function.Injective orderedView := by
  rintro ⟨pendingA, stepA, occurrencesA⟩ ⟨pendingB, stepB, occurrencesB⟩ equal
  simp only [orderedView, Prod.mk.injEq] at equal
  cases equal.1
  cases equal.2.1
  cases equal.2.2
  rfl

#print axioms slotInvoice_toSlotReceipt
#print axioms historyEvents_append
#print axioms orderedView_injective

end NativePoll

abbrev SlotReceiptMeter := ReadyQueue.State → Bool → List Nat → SlotReceipt

/-- Feed exact phase receipts to the maintained ready-queue service account. -/
def receiptServiceMeter (meter : SlotReceiptMeter) : ReadyQueue.ServiceMeter Nat :=
  fun state keep offered => slotCharge (meter state keep offered)

@[simp] theorem receiptServiceMeter_total (meter : SlotReceiptMeter)
    (state : ReadyQueue.State) (keep : Bool) (offered : List Nat) :
    (receiptServiceMeter meter state keep offered).total =
      work (slotInvoice (meter state keep offered)) :=
  slotCharge_total_eq_work _

/-- An explicit bound on every complete receipt discharges the existing
whole-slot service admission contract.  No dispatch-count premise appears. -/
theorem serviceCostBound_of_receipts (meter : SlotReceiptMeter) (bound slots : Nat)
    (keep : Nat → Bool) (offered : Nat → List Nat) (state : ReadyQueue.State)
    (bounded : ∀ n, n < slots →
      work (slotInvoice (meter (ReadyQueue.serviceRun n keep offered state).2
        (keep n) (offered n))) ≤ bound) :
    ReadyQueue.ServiceCostBound (receiptServiceMeter meter) bound slots keep offered state := by
  intro n before
  simpa only [receiptServiceMeter_total] using bounded n before

/-- The finite exact account can quote and debit a complete phase receipt in
one operation.  Handler conformance to that quoted receipt remains a native
obligation. -/
def prepareSlot (profile : Profile) (replay : Bool) (receipt : SlotReceipt)
    (account : Account) : Except Refusal Account :=
  prepare profile replay (slotInvoice receipt) account

theorem prepareSlot_ok {profile : Profile} {replay : Bool} {receipt : SlotReceipt}
    {before after : Account} (accepted : prepareSlot profile replay receipt before = .ok after) :
    after.remaining + (slotCharge receipt).total = before.remaining ∧
      after.events = before.events ++ slotInvoice receipt ∧
      after.calls = before.calls + 1 := by
  have exact := prepare_ok accepted
  rw [slotCharge_total_eq_work]
  exact ⟨exact.1, exact.2.1, exact.2.2.1⟩

/-- A selectable work ceiling over the separately retained receipt.
`unlimited` performs no finite balance comparison or subtraction. -/
inductive WorkAllowance where
  | unlimited
  | finite (remaining : Nat)
deriving DecidableEq, Repr

def debitAllowance : WorkAllowance → List Event → Option WorkAllowance
  | .unlimited, _ => some .unlimited
  | .finite remaining, events => (debit remaining events).map .finite

@[simp] theorem debitAllowance_unlimited (events : List Event) :
    debitAllowance .unlimited events = some .unlimited := rfl

theorem debitAllowance_finite_some_iff (remaining after : Nat) (events : List Event) :
    debitAllowance (.finite remaining) events = some (.finite after) ↔
      work events ≤ remaining ∧ after + work events = remaining := by
  simp [debitAllowance, debit_some_iff]

#print axioms slotCharge_total_eq_work
#print axioms serviceCostBound_of_receipts
#print axioms prepareSlot_ok
#print axioms debitAllowance_finite_some_iff

/-! ## Post-commit delivery and recovery policies

This handler starts only after validated publication.  A stable key can make
the local durable delivery operation idempotent.  An external operation whose
outcome cannot be queried instead remains explicitly unknown after a lost
acknowledgment; the handler does not replay it automatically.

The `effects` list is a mathematical observation of physical attempts.  It is
not a claim that an arbitrary remote service is exactly-once, transactional or
recoverable from this local model.
-/

namespace DeliveryRecovery

inductive Policy where
  | idempotentByKey
  | explicitUnknown
deriving DecidableEq, Repr

structure State (Key Payload : Type) where
  pending : List Key := []
  records : List (Key × Payload) := []
  effects : List (Key × Payload) := []
deriving DecidableEq, Repr

def State.lookup {Key Payload : Type} [DecidableEq Key]
    (state : State Key Payload) (key : Key) : Option Payload :=
  (state.records.find? fun entry => decide (entry.1 = key)).map Prod.snd

def State.retire {Key Payload : Type} [DecidableEq Key]
    (state : State Key Payload) (key : Key) : List Key :=
  state.pending.filter fun other => decide (other ≠ key)

/-- `stored` is evidence from the durable result ledger.  `acknowledged` is
only the caller's observed outcome for an effect without such a ledger; it
does not make that effect queryable after recovery. -/
inductive Status where
  | pending
  | stored
  | acknowledged
  | conflict
  | unknown
deriving DecidableEq, Repr

structure Result (Key Payload : Type) where
  status : Status
  state : State Key Payload
  history : NativePoll.History
deriving DecidableEq, Repr

def attempt {Key Payload : Type} [DecidableEq Key] [DecidableEq Payload]
    (policy : Policy) (acknowledged : Bool) (state : State Key Payload)
    (history : NativePoll.History) (receipt : NativePoll.Receipt)
    (key : Key) (payload : Payload) : Result Key Payload :=
  let laterHistory := history ++ [receipt]
  match policy with
  | .idempotentByKey =>
      let status := if acknowledged then Status.stored else .unknown
      match state.lookup key with
      | none =>
          if key ∈ state.pending then
            ⟨status, ⟨state.retire key, state.records ++ [(key, payload)],
              state.effects ++ [(key, payload)]⟩, laterHistory⟩
          else ⟨.unknown, state, laterHistory⟩
      | some previous =>
          if previous = payload then ⟨status, state, laterHistory⟩
          else ⟨.conflict, state, laterHistory⟩
  | .explicitUnknown =>
      if key ∈ state.pending then
        let pending := if acknowledged then state.retire key else state.pending
        let status := if acknowledged then Status.acknowledged else .unknown
        ⟨status, ⟨pending, state.records, state.effects ++ [(key, payload)]⟩, laterHistory⟩
      else ⟨.unknown, state, laterHistory⟩

/-- Query the durable result ledger without executing the effect.  Its three
answers correspond to STORED, PENDING and UNKNOWN. -/
def queryReceipt {Key Payload : Type} [DecidableEq Key]
    (state : State Key Payload) (history : NativePoll.History)
    (receipt : NativePoll.Receipt) (key : Key) : Result Key Payload :=
  let status := match state.lookup key with
    | some _ => Status.stored
    | none => if key ∈ state.pending then .pending else .unknown
  ⟨status, state, history ++ [receipt]⟩

/-- Retry only the policy whose stable key makes repetition observationally
idempotent.  Explicitly unknown effects remain parked for inspection or an
authorized external resolution. -/
def recover {Key Payload : Type} [DecidableEq Key] [DecidableEq Payload]
    (policy : Policy) (result : Result Key Payload)
    (receipt : NativePoll.Receipt) (key : Key) : Result Key Payload :=
  match result.status with
  | .unknown => match policy with
      | .idempotentByKey => queryReceipt result.state result.history receipt key
      | .explicitUnknown => result
  | _ => result

theorem attempt_history {Key Payload : Type} [DecidableEq Key] [DecidableEq Payload]
    (policy : Policy) (acknowledged : Bool) (state : State Key Payload)
    (history : NativePoll.History) (receipt : NativePoll.Receipt)
    (key : Key) (payload : Payload) :
    (attempt policy acknowledged state history receipt key payload).history = history ++ [receipt] := by
  cases policy <;> simp only [attempt]
  · cases found : state.lookup key <;> simp only
    · split <;> rfl
    · split <;> rfl
  · split <;> rfl

theorem queryReceipt_history {Key Payload : Type} [DecidableEq Key]
    (state : State Key Payload) (history : NativePoll.History)
    (receipt : NativePoll.Receipt) (key : Key) :
    (queryReceipt state history receipt key).history = history ++ [receipt] := by
  simp [queryReceipt]

@[simp] theorem queryReceipt_state {Key Payload : Type} [DecidableEq Key]
    (state : State Key Payload) (history : NativePoll.History)
    (receipt : NativePoll.Receipt) (key : Key) :
    (queryReceipt state history receipt key).state = state := by
  simp [queryReceipt]

/-- Repeating the same keyed payload cannot append another durable effect.
The acknowledgment may still be lost, so this theorem deliberately says
nothing stronger than preservation of the durable state. -/
theorem repeated_same_payload_preserves_state {Key Payload : Type}
    [DecidableEq Key] [DecidableEq Payload]
    (acknowledged : Bool) (state : State Key Payload)
    (history : NativePoll.History) (receipt : NativePoll.Receipt)
    (key : Key) (payload : Payload)
    (stored : state.lookup key = some payload) :
    (attempt .idempotentByKey acknowledged state history receipt key payload).state = state := by
  simp [attempt, stored]

/-- Reusing a durable key with different bytes is a conflict and leaves the
stored result and physical-effect observation unchanged. -/
theorem changed_payload_conflicts {Key Payload : Type}
    [DecidableEq Key] [DecidableEq Payload]
    (acknowledged : Bool) (state : State Key Payload)
    (history : NativePoll.History) (receipt : NativePoll.Receipt)
    (key : Key) (previous payload : Payload)
    (stored : state.lookup key = some previous) (changed : previous ≠ payload) :
    let result := attempt .idempotentByKey acknowledged state history receipt key payload
    result.status = .conflict ∧ result.state = state := by
  simp [attempt, stored, changed]

theorem idempotent_recovery_queries_unknown {Key Payload : Type}
    [DecidableEq Key] [DecidableEq Payload]
    (result : Result Key Payload) (receipt : NativePoll.Receipt) (key : Key)
    (unknown : result.status = .unknown) :
    recover .idempotentByKey result receipt key =
      queryReceipt result.state result.history receipt key := by
  simp [recover, unknown]

theorem explicitUnknown_recovery_holds {Key Payload : Type}
    [DecidableEq Key] [DecidableEq Payload]
    (result : Result Key Payload) (receipt : NativePoll.Receipt) (key : Key)
    (unknown : result.status = .unknown) :
    recover .explicitUnknown result receipt key = result := by
  simp [recover, unknown]

#print axioms attempt_history
#print axioms queryReceipt_history
#print axioms queryReceipt_state
#print axioms repeated_same_payload_preserves_state
#print axioms changed_payload_conflicts
#print axioms idempotent_recovery_queries_unknown
#print axioms explicitUnknown_recovery_holds

end DeliveryRecovery

/-! ## A stateful provider for the existing cursor protocol -/

open Mettapedia.TypeTheory Mettapedia.TypeTheory.IndexedPolynomial _root_.CategoryTheory

inductive Terminal (Answer Fault Waiting : Type) where
  | done (answer : Answer)
  | fault (error : Fault)
  | suspended (waiting : Waiting)
  | refused (reason : Refusal)
deriving DecidableEq, Repr

/-- `paid` asks for another handler step; it does not report completion. -/
inductive Reply (Answer Fault Waiting : Type) where
  | paid
  | terminal (result : Terminal Answer Fault Waiting)
deriving DecidableEq, Repr

abbrev protocol (Answer Fault Waiting : Type) :
    IndexedPolynomial PUnit (fun _ => PUnit) where
  Shape _ _ := Bool
  Position _ := Reply Answer Fault Waiting
  next _ _ := PUnit.unit

variable {Answer Fault Waiting World : Type}

/-- An invoice is quoted before the action. A refused operation does not call
that action, and accepted failure/suspension retains the paid account. -/
def provider (profile : Profile) (invoice : Bool → World → List Event)
    (action : Bool → World → Reply Answer Fault Waiting × World) :
    Cursor.Provider (protocol Answer Fault Waiting) where
  State _ _ := World × Account
  step state replay :=
    match prepare profile replay (invoice replay state.1) state.2 with
    | .error reason => ⟨.terminal (.refused reason), state⟩
    | .ok account => let response := action replay state.1
                     ⟨response.1, response.2, account⟩

/-- This is the accepted native invoice valuation. The physical cost of
checking admission is not claimed to be zero by this abstract charge. -/
def charge (profile : Profile) (invoice : Bool → World → List Event)
    (action : Bool → World → Reply Answer Fault Waiting × World) :
    Cursor.Charge (provider profile invoice action) := fun state replay =>
  match prepare profile replay (invoice replay state.1) state.2 with
  | .error _ => 0
  | .ok _ => work (invoice replay state.1)

inductive Control (Answer Fault Waiting : Type) where
  | running (replay : Bool)
  | terminal (result : Terminal Answer Fault Waiting)
deriving DecidableEq, Repr

def nextControl (replay : Bool) : Reply Answer Fault Waiting → Control Answer Fault Waiting
  | .paid => .running replay
  | .terminal result => .terminal result

def expose (control : Control Answer Fault Waiting) :
    ((protocol Answer Fault Waiting).withHoles (fun _ _ => Terminal Answer Fault Waiting)).Extension
      (fun _ _ => Control Answer Fault Waiting) PUnit.unit PUnit.unit :=
  match control with
  | .terminal result => ⟨.inl result, PEmpty.elim⟩
  | .running replay => ⟨.inr replay, nextControl replay⟩

/-- A potentially unbounded operation uses the existing polynomial
coalgebra. A scheduler pause retains its actual reply-dependent control. -/
abbrev client (Answer Fault Waiting : Type) :
    Cursor.Client (P := protocol Answer Fault Waiting)
      (Return := fun _ _ => Terminal Answer Fault Waiting) where
  V _ _ := Control Answer Fault Waiting
  str := fun _ _ => ↾(expose (Answer := Answer) (Fault := Fault) (Waiting := Waiting))

variable (profile : Profile) (invoice : Bool → World → List Event)
    (action : Bool → World → Reply Answer Fault Waiting × World)

abbrev Packet := Cursor.Packet (provider profile invoice action)
  (client Answer Fault Waiting) PUnit.unit
abbrev Outcome := Cursor.Outcome (provider profile invoice action)
  (client Answer Fault Waiting) PUnit.unit

abbrev Finished := Cursor.Finished (provider profile invoice action)
  (Return := fun _ _ => Terminal Answer Fault Waiting) PUnit.unit

def outcomeState : Outcome profile invoice action → World × Account
  | .paused ⟨_, _, state⟩ => state
  | .done ⟨_, _, state⟩ => state

def run (fuel : Nat) (packet : Packet profile invoice action) : Nat × Outcome profile invoice action :=
  Cursor.advance (provider profile invoice action)
    (client Answer Fault Waiting) (charge profile invoice action) fuel packet

def resume (fuel : Nat) (previous : Nat × Outcome profile invoice action) :
    Nat × Outcome profile invoice action :=
  Cursor.resume (provider profile invoice action)
    (client Answer Fault Waiting) (charge profile invoice action) fuel previous

theorem refused_step {state : World × Account} {replay : Bool} {reason : Refusal}
    (refused : prepare profile replay (invoice replay state.1) state.2 = .error reason) :
    (provider profile invoice action).step (base := PUnit.unit) (index := PUnit.unit) state replay =
      ⟨.terminal (.refused reason), state⟩ := by
  simp [provider, refused]

theorem paid_step {state : World × Account} {replay : Bool} {account : Account}
    (accepted : prepare profile replay (invoice replay state.1) state.2 = .ok account) :
    (provider profile invoice action).step (base := PUnit.unit) (index := PUnit.unit) state replay =
      ⟨(action replay state.1).1, (action replay state.1).2, account⟩ := by
  simp [provider, accepted]

/-- The provider debits every accepted action, regardless of its outcome. -/
theorem step_budget (state : World × Account) (replay : Bool) :
    ((provider profile invoice action).step (base := PUnit.unit) (index := PUnit.unit) state replay).2.2.remaining +
      charge profile invoice action (base := PUnit.unit) (index := PUnit.unit) state replay = state.2.remaining := by
  cases admitted : prepare profile replay (invoice replay state.1) state.2 with
  | error reason => simp [provider, charge, admitted]
  | ok account =>
      simpa [provider, charge, admitted] using (prepare_ok admitted).1

theorem step_total (state : World × Account) (replay : Bool) :
    let after := ((provider profile invoice action).step (base := PUnit.unit) (index := PUnit.unit) state replay).2.2
    after.remaining + work after.events = state.2.remaining + work state.2.events := by
  cases admitted : prepare profile replay (invoice replay state.1) state.2 with
  | error reason => simp [provider, admitted]
  | ok account => simpa [provider, admitted] using prepare_total admitted

/-- A local provider invariant lifts to the actual retained cursor, including
both scheduler pause and all tagged terminal outcomes. -/
theorem run_invariant {Value : Type} (observe : World × Account → Value)
    (localLaw : ∀ state replay,
      observe ((provider profile invoice action).step
        (base := PUnit.unit) (index := PUnit.unit) state replay).2 = observe state)
    (fuel : Nat) (packet : Packet profile invoice action) :
    observe (outcomeState profile invoice action (run profile invoice action fuel packet).2) =
      observe packet.2.2 := by
  induction fuel generalizing packet with
  | zero => rfl
  | succ fuel ih =>
      rcases packet with ⟨⟨⟩, control, state⟩
      cases control with
      | terminal result => rfl
      | running replay =>
          let response := (provider profile invoice action).step
            (base := PUnit.unit) (index := PUnit.unit) state replay
          change observe (outcomeState profile invoice action
            (run profile invoice action fuel ⟨PUnit.unit,
              nextControl replay response.1, response.2⟩).2) = observe state
          exact (ih _).trans (localLaw state replay)

/-- Accepted work is debited once from the retained budget over any finite
scheduler prefix. Refusals cannot underflow it. -/
theorem run_budget (fuel : Nat) (packet : Packet profile invoice action) :
    (outcomeState profile invoice action (run profile invoice action fuel packet).2).2.remaining +
      (run profile invoice action fuel packet).1 = packet.2.2.2.remaining := by
  induction fuel generalizing packet with
  | zero => rfl
  | succ fuel ih =>
      rcases packet with ⟨⟨⟩, control, state⟩
      cases control with
      | terminal result => change state.2.remaining + 0 = state.2.remaining; rfl
      | running replay =>
          let response := (provider profile invoice action).step
            (base := PUnit.unit) (index := PUnit.unit) state replay
          let rest := run profile invoice action fuel ⟨PUnit.unit,
            nextControl replay response.1, response.2⟩
          change (outcomeState profile invoice action rest.2).2.remaining +
            (charge profile invoice action (base := PUnit.unit) (index := PUnit.unit) state replay +
              rest.1) = state.2.remaining
          have tail := ih ⟨PUnit.unit, nextControl replay response.1, response.2⟩
          have localLaw := step_budget profile invoice action state replay
          change response.2.2.remaining + charge profile invoice action
            (base := PUnit.unit) (index := PUnit.unit) state replay = state.2.remaining at localLaw
          change (outcomeState profile invoice action rest.2).2.remaining + rest.1 =
            response.2.2.remaining at tail
          omega

theorem run_budget_bound (fuel : Nat) (packet : Packet profile invoice action) :
    (run profile invoice action fuel packet).1 ≤ packet.2.2.2.remaining := by
  have conserved := run_budget profile invoice action fuel packet
  omega

theorem run_total (fuel : Nat) (packet : Packet profile invoice action) :
    let after := (outcomeState profile invoice action (run profile invoice action fuel packet).2).2
    after.remaining + work after.events =
      packet.2.2.2.remaining + work packet.2.2.2.events :=
  run_invariant profile invoice action (fun state => state.2.remaining + work state.2.events)
    (step_total profile invoice action) fuel packet

/-- Ordered history and accepted-work accounting agree on every cursor
prefix; failed and suspended operations have the same conservation law. -/
theorem run_ledger (fuel : Nat) (packet : Packet profile invoice action) :
    work (outcomeState profile invoice action (run profile invoice action fuel packet).2).2.events =
      work packet.2.2.2.events + (run profile invoice action fuel packet).1 := by
  have balance := run_budget profile invoice action fuel packet
  have total := run_total profile invoice action fuel packet
  dsimp only at total
  omega

/-- The allowance includes accepted calls, independently of their work. -/
def allowanceTotal (account : Account) : Option Nat := account.inspections.map (· + account.calls)

theorem prepare_allowance {before after : Account} {replay : Bool} {bill : List Event}
    (accepted : prepare profile replay bill before = .ok after) :
    allowanceTotal after = allowanceTotal before := by
  obtain ⟨_, _, calls, allowance⟩ := prepare_ok accepted
  cases hi : before.inspections with
  | none =>
      simp only [hi, inspectAllowance, Except.ok.injEq] at allowance
      simp [allowanceTotal, hi, ← allowance]
  | some bound =>
      obtain ⟨left, heq, decrement⟩ := inspectAllowance_ok allowance bound hi
      simp only [allowanceTotal, heq, hi, Option.map_some]
      congr 1
      omega

theorem step_allowance (state : World × Account) (replay : Bool) :
    allowanceTotal ((provider profile invoice action).step
      (base := PUnit.unit) (index := PUnit.unit) state replay).2.2 = allowanceTotal state.2 := by
  cases admitted : prepare profile replay (invoice replay state.1) state.2 with
  | error reason => simp [provider, admitted]
  | ok account => simpa [provider, admitted] using prepare_allowance profile admitted

theorem run_allowance (fuel : Nat) (packet : Packet profile invoice action) :
    allowanceTotal (outcomeState profile invoice action
      (run profile invoice action fuel packet).2).2 = allowanceTotal packet.2.2.2 :=
  run_invariant profile invoice action (fun state => allowanceTotal state.2)
    (step_allowance profile invoice action) fuel packet

/-- A declared bound limits accepted calls, including zero-work ones. The
last observation may still be a refusal, fault or handler suspension. -/
theorem run_calls_bound (fuel budget bound : Nat) (world : World)
    (control : Control Answer Fault Waiting) (limited : profile.bound = some bound) :
    (outcomeState profile invoice action
      (run profile invoice action fuel ⟨PUnit.unit, control, world, initial profile budget⟩).2).2.calls ≤
        bound := by
  let result := run profile invoice action fuel ⟨PUnit.unit, control, world, initial profile budget⟩
  have conserved := run_allowance profile invoice action fuel
    ⟨PUnit.unit, control, world, initial profile budget⟩
  change allowanceTotal (outcomeState profile invoice action result.2).2 =
    allowanceTotal (initial profile budget) at conserved
  simp only [allowanceTotal, initial, limited, Nat.add_zero, Option.map_some] at conserved
  cases hi : (outcomeState profile invoice action result.2).2.inspections with
  | none => simp [hi] at conserved
  | some left =>
      simp only [hi, Option.map_some, Option.some.injEq] at conserved
      change (outcomeState profile invoice action result.2).2.calls ≤ bound
      omega

/-- A rank is attached to the actual retained control and world, rather
than to a declared progress word. Terminal observations need no handler call. -/
def controlRank (rank : World → Nat) : Control Answer Fault Waiting → World × Account → Nat
  | .running _, state => rank state.1 + 1
  | .terminal _, _ => 0

/-- A real decreasing-rank argument suffices for paid continuation steps.
Admission refusals, handler faults and suspension all stop this episode. -/
theorem step_rank (rank : World → Nat)
    (descent : ∀ replay world, (action replay world).1 = .paid →
      rank (action replay world).2 < rank world) (state : World × Account) (replay : Bool) :
    let response := (provider profile invoice action).step
      (base := PUnit.unit) (index := PUnit.unit) state replay
    controlRank rank (nextControl replay response.1) response.2 <
      controlRank rank (.running replay : Control Answer Fault Waiting) state := by
  cases admitted : prepare profile replay (invoice replay state.1) state.2 with
  | error reason => simp [provider, admitted, nextControl, controlRank]
  | ok account =>
      cases hr : (action replay state.1).1 with
      | paid =>
          simpa [provider, admitted, hr, nextControl, controlRank] using
            Nat.add_lt_add_right (descent replay state.1 hr) 1
      | terminal result => simp [provider, admitted, hr, nextControl, controlRank]

/-- A decreasing rank on actual handler continuation proves that a finite
cursor inspection finishes. Its tagged result still distinguishes successful
delivery, fault, suspension and refusal. No rank follows from metadata alone. -/
theorem ranked_inspection_finishes (rank : World → Nat)
    (descent : ∀ replay world, (action replay world).1 = .paid →
      rank (action replay world).2 < rank world)
    (fuel : Nat) (packet : Packet profile invoice action)
    (enough : controlRank rank packet.2.1 packet.2.2 < fuel) :
    ∃ (spent : Nat) (result : Finished profile invoice action),
      run profile invoice action fuel packet = (spent, .done result) := by
  induction fuel generalizing packet with
  | zero => omega
  | succ fuel ih =>
      rcases packet with ⟨⟨⟩, control, state⟩
      cases control with
      | terminal result => exact ⟨0, ⟨PUnit.unit, result, state⟩, rfl⟩
      | running replay =>
          let response := (provider profile invoice action).step
            (base := PUnit.unit) (index := PUnit.unit) state replay
          have decreases := step_rank profile invoice action rank descent state replay
          change controlRank rank (nextControl replay response.1) response.2 <
            controlRank rank (.running replay : Control Answer Fault Waiting) state at decreases
          change controlRank rank (.running replay : Control Answer Fault Waiting) state < fuel + 1 at enough
          have smaller : controlRank rank (nextControl replay response.1) response.2 < fuel := by
            omega
          obtain ⟨spent, result, tail⟩ :=
            ih ⟨PUnit.unit, nextControl replay response.1, response.2⟩ smaller
          refine ⟨charge profile invoice action (base := PUnit.unit) (index := PUnit.unit) state replay +
            spent, result, ?_⟩
          change
            (charge profile invoice action (base := PUnit.unit) (index := PUnit.unit) state replay +
              (run profile invoice action fuel
                ⟨PUnit.unit, nextControl replay response.1, response.2⟩).1,
              (run profile invoice action fuel
                ⟨PUnit.unit, nextControl replay response.1, response.2⟩).2) = _
          rw [tail]

/-- Splitting scheduler time resumes the actual retained packet, never the
original control, and preserves the entire charged outcome. -/
theorem run_split (first second : Nat) (packet : Packet profile invoice action) :
    resume profile invoice action second (run profile invoice action first packet) =
      run profile invoice action (first + second) packet :=
  (Cursor.advance_add (provider profile invoice action) (client Answer Fault Waiting)
    (charge profile invoice action) first second packet).symm

/-- Cursor completion is inert even when its terminal payload is suspended,
faulted or refused. Waking a service is a separate transition. -/
theorem terminal_inert (fuel spent : Nat) (result : Terminal Answer Fault Waiting)
    (state : World × Account) :
    resume profile invoice action fuel (spent, .done ⟨PUnit.unit, result, state⟩) =
      (spent, .done ⟨PUnit.unit, result, state⟩) := rfl

end Mettapedia.GSLT.LanguageDef.OperationCostProtocol

/-! ## Indexed preparation services

The decoration below retains an existing provider's request, dependent reply,
and reply-selected successor index. It adds admission and invoicing, not a
second preparation grammar. A refused request returns its original client
control. Rearming that refusal therefore resumes the exact phase, whereas a
scheduler pause already contains its exact successor control.

The invoice is the existing native receipt. Its authenticity, and the cost of
admission, allocation, and an individual provider transition, are realization
obligations. In particular, a finite number of inspections is not a CPU bound.
-/

namespace Mettapedia.GSLT.LanguageDef.OperationCostProtocol.Indexed

open Mettapedia.TypeTheory Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.Machines Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.Logic.SeparationTransport
open _root_.CategoryTheory

variable {Base : Type} {Index : Base → Type}
  {P : IndexedPolynomial.{0, 0, 0, 0} Base Index} {Denied : Type}
  {Return : (base : Base) → Index base → Type}

abbrev Reason (Denied : Type) := Denied ⊕ Refusal

/-- Failed admission keeps the original index. Only an actual original reply
can select an original successor phase. -/
abbrev protocol (P : IndexedPolynomial.{0, 0, 0, 0} Base Index) (Denied : Type) :
    IndexedPolynomial.{0, 0, 0, 0} Base Index where
  Shape := P.Shape
  Position request := Except (Reason Denied) (P.Position request)
  next := fun {_} {index} request reply => match reply with
    | .error _ => index
    | .ok value => P.next request value

variable (source : Cursor.Provider P)

abbrev Gate := {base : Base} → {index : Index base} → source.State base index →
  P.Shape base index → Except Denied Unit

abbrev Invoice := {base : Base} → {index : Index base} → source.State base index →
  P.Shape base index → List Event

variable (gate : Gate (Denied := Denied) source)
  (profiles : {base : Base} → {index : Index base} → P.Shape base index → Profile)
  (replay : {base : Base} → {index : Index base} → P.Shape base index → Bool)
  (invoice : Invoice source)

/-- Current permission is checked before validating the retained read view.
Neither a module designation nor a read stamp supplies that permission. -/
def currentGate {World Key Value : Type} [Category.{0} World]
    (authority : IndexedAuthority.{0, 0, 0} World)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [Decidable (FrameUpdate point.authority required)] [DecidableEq Value]
    (current : Key → Value) (reads : ReadOnlyQuery.Reads Key Value)
    (denied changed : Denied) : Except Denied Unit :=
  if FrameUpdate point.authority required then
    if ReadOnlyQuery.checkReads current reads then .ok () else .error changed
  else .error denied

theorem currentGate_ok_iff {World Key Value : Type} [Category.{0} World]
    (authority : IndexedAuthority.{0, 0, 0} World)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [Decidable (FrameUpdate point.authority required)] [DecidableEq Value]
    (current : Key → Value) (reads : ReadOnlyQuery.Reads Key Value)
    (denied changed : Denied) :
    currentGate authority point required current reads denied changed = .ok () ↔
      FrameUpdate point.authority required ∧ ReadOnlyQuery.Agrees current reads := by
  by_cases allowed : FrameUpdate point.authority required <;>
    by_cases valid : ReadOnlyQuery.checkReads current reads = true <;>
    simp [currentGate, allowed, valid, ← ReadOnlyQuery.checkReads_iff]

/-- This checks the same append-only event account used by ordinary native
operations. An admission refusal performs no original provider transition. -/
def admit {base : Base} {index : Index base} (state : source.State base index)
    (request : P.Shape base index) (account : Account) : Except (Reason Denied) Account :=
  match gate state request with
  | .error reason => .error (.inl reason)
  | .ok _ => (prepare (profiles request) (replay request) (invoice state request) account).mapError Sum.inr

theorem admit_ok {base : Base} {index : Index base} {state : source.State base index}
    {request : P.Shape base index} {before after : Account}
    (accepted : admit source gate profiles replay invoice state request before = .ok after) :
    gate state request = .ok () ∧
      prepare (profiles request) (replay request) (invoice state request) before = .ok after := by
  unfold admit at accepted
  cases permitted : gate state request with
  | error reason => simp [permitted] at accepted
  | ok trivialValue =>
      cases trivialValue
      cases paid : prepare (profiles request) (replay request) (invoice state request) before with
      | error reason => simp [permitted, paid, Except.mapError] at accepted
      | ok account =>
          simp only [permitted, paid, Except.mapError, Except.ok.injEq] at accepted
          subst account
          exact ⟨rfl, rfl⟩

def provider : Cursor.Provider (protocol P Denied) where
  State base index := source.State base index × Account
  step state request :=
    match admit source gate profiles replay invoice state.1 request state.2 with
    | .error reason => ⟨.error reason, state⟩
    | .ok account =>
        let response := source.step state.1 request
        ⟨.ok response.1, response.2, account⟩

def charge : Cursor.Charge (provider source gate profiles replay invoice) := fun state request =>
  match admit source gate profiles replay invoice state.1 request state.2 with
  | .error _ => 0
  | .ok _ => work (invoice state.1 request)

theorem refused_step {base : Base} {index : Index base}
    (state : source.State base index × Account) (request : P.Shape base index)
    (reason : Reason Denied)
    (refused : admit source gate profiles replay invoice state.1 request state.2 = .error reason) :
    (provider source gate profiles replay invoice).step state request = ⟨.error reason, state⟩ ∧
      charge source gate profiles replay invoice state request = 0 := by
  simp [provider, charge, refused]

theorem accepted_step {base : Base} {index : Index base}
    (state : source.State base index × Account) (request : P.Shape base index) (account : Account)
    (accepted : admit source gate profiles replay invoice state.1 request state.2 = .ok account) :
    (provider source gate profiles replay invoice).step state request =
      ⟨.ok (source.step state.1 request).1, (source.step state.1 request).2, account⟩ ∧
      charge source gate profiles replay invoice state request = work (invoice state.1 request) := by
  simp [provider, charge, accepted]

/-- Every original transition is admitted at its actual retained state. Its
invoice is paid even when the reply subsequently proves incompatibility. -/
theorem step_account {base : Base} {index : Index base}
    (state : source.State base index × Account) (request : P.Shape base index) :
    let after := ((provider source gate profiles replay invoice).step state request).2.2
    after.remaining + charge source gate profiles replay invoice state request = state.2.remaining ∧
      after.remaining + work after.events = state.2.remaining + work state.2.events ∧
      allowanceTotal after = allowanceTotal state.2 := by
  cases accepted : admit source gate profiles replay invoice state.1 request state.2 with
  | error reason =>
      obtain ⟨stepped, free⟩ := refused_step source gate profiles replay invoice state request reason accepted
      rw [stepped, free]
      exact ⟨Nat.add_zero _, rfl, rfl⟩
  | ok account =>
      have paid := (admit_ok source gate profiles replay invoice accepted).2
      obtain ⟨stepped, priced⟩ := accepted_step source gate profiles replay invoice state request account accepted
      rw [stepped, priced]
      exact ⟨(prepare_ok paid).1, prepare_total paid, prepare_allowance _ paid⟩

def outcomeAccount {OtherReturn : (base : Base) → Index base → Type}
    (other : Cursor.Client (P := protocol P Denied) (Return := OtherReturn)) {base : Base} :
    Cursor.Outcome (provider source gate profiles replay invoice) other base → Account
  | .paused ⟨_, _, state⟩ => state.2
  | .done ⟨_, _, state⟩ => state.2

theorem advance_account {OtherReturn : (base : Base) → Index base → Type}
    (other : Cursor.Client (P := protocol P Denied) (Return := OtherReturn))
    (fuel : Nat) {base : Base}
    (packet : Cursor.Packet (provider source gate profiles replay invoice) other base) :
    let result := Cursor.advance (provider source gate profiles replay invoice) other
      (charge source gate profiles replay invoice) fuel packet
    let after := outcomeAccount source gate profiles replay invoice other result.2
    after.remaining + result.1 = packet.2.2.2.remaining ∧
      after.remaining + work after.events =
        packet.2.2.2.remaining + work packet.2.2.2.events ∧
      allowanceTotal after = allowanceTotal packet.2.2.2 := by
  induction fuel generalizing packet with
  | zero => exact ⟨Nat.add_zero _, rfl, rfl⟩
  | succ fuel ih =>
      rcases packet with ⟨index, control, state⟩
      cases exposed : other.str base index control with
      | mk shape children =>
          cases shape with
          | inl value =>
              simp [Cursor.advance, exposed, outcomeAccount]
          | inr request =>
              dsimp only [withHoles] at children
              simp only [Cursor.advance, exposed]
              dsimp only [withHoles]
              let response := (provider source gate profiles replay invoice).step state request
              have tail := ih ⟨_, children response.1, response.2⟩
              have localLaw := step_account source gate profiles replay invoice state request
              dsimp only [response] at tail localLaw ⊢
              exact ⟨by omega, tail.2.1.trans localLaw.2.1, tail.2.2.trans localLaw.2.2⟩

/-- A source reply may report a paid pause/refusal after changing its private
state. Its original reply-dependent child is the next retry residual. -/
abbrev Notice (P : IndexedPolynomial.{0, 0, 0, 0} Base Index) (Denied : Type) :=
  {base : Base} → {index : Index base} → (request : P.Shape base index) →
    P.Position request → Option Denied

variable (reader : Cursor.Client (P := P) (Return := Return))

abbrev Control (base : Base) (index : Index base) :=
  reader.V base index ⊕ (Reason Denied × reader.V base index)

abbrev Result (base : Base) (index : Index base) :=
  Return base index ⊕ (Reason Denied × reader.V base index)

variable (notice : Notice P Denied)

def expose {base : Base} {index : Index base} :
    Control (Denied := Denied) reader base index →
      ((protocol P Denied).withHoles (Result (Denied := Denied) reader)).Extension
        (Control (Denied := Denied) reader) base index
  | .inr refused => ⟨.inl (.inr refused), fun impossible => nomatch impossible⟩
  | .inl control =>
      match reader.str base index control with
      | ⟨.inl value, _⟩ => ⟨.inl (.inl value), fun impossible => nomatch impossible⟩
      | ⟨.inr request, children⟩ =>
          ⟨.inr request, fun reply => match reply with
            | .error reason => .inr (reason, control)
            | .ok value => match notice request value with
                | none => .inl (children value)
                | some reason => .inr (.inl reason, children value)⟩

abbrev client : Cursor.Client (P := protocol P Denied)
    (Return := Result (Denied := Denied) reader) where
  V := Control (Denied := Denied) reader
  str := fun _ _ => ↾(expose reader notice)

theorem client_call {base : Base} {index : Index base}
    (control : reader.V base index) (request : P.Shape base index)
    (children : (reply : P.Position request) → reader.V base (P.next request reply))
    (exposed : reader.str base index control = ⟨.inr request, children⟩) :
    (client reader notice).str base index (.inl control) =
      ⟨.inr request, fun reply => match reply with
        | .error reason => .inr (reason, control)
        | .ok value => match notice request value with
          | none => .inl (children value)
          | some reason => .inr (.inl reason, children value)⟩ := by
  change expose reader notice (.inl control) = _
  simp only [expose, exposed]
  apply Sigma.ext rfl
  apply heq_of_eq
  funext reply
  cases reply with
  | error reason => rfl
  | ok value => cases notice request value <;> rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem client_refused {base : Base} {index : Index base}
    (reason : Reason Denied) (control : reader.V base index) :
    (client reader notice).str base index (.inr (reason, control)) =
      ⟨.inl (.inr (reason, control)), fun impossible => nomatch impossible⟩ := by
  change expose reader notice (.inr (reason, control)) = _
  dsimp only [expose]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext impossible
  nomatch impossible

abbrev Outcome (base : Base) := Cursor.Outcome (provider source gate profiles replay invoice)
  (client (Denied := Denied) reader notice) base

def accountOf {base : Base} : Outcome source gate profiles replay invoice reader notice base → Account
  := outcomeAccount source gate profiles replay invoice (client reader notice)

/-- Rearming is an explicit caller action. It drops only the refusal notice;
the saved original phase, reply-selected index, source state and invoice
account survive. A genuine completed row is inert. -/
def retry {base : Base} : Outcome source gate profiles replay invoice reader notice base →
    Outcome source gate profiles replay invoice reader notice base
  | .done ⟨index, .inr (_, control), state⟩ => .paused ⟨index, .inl control, state⟩
  | other => other

theorem retry_preserves_account {base : Base}
    (previous : Outcome source gate profiles replay invoice reader notice base) :
    accountOf source gate profiles replay invoice reader notice
      (retry source gate profiles replay invoice reader notice previous) =
        accountOf source gate profiles replay invoice reader notice previous := by
  cases previous with
  | paused packet => rfl
  | done result => rcases result with ⟨index, value, state⟩; cases value <;> rfl

theorem retry_refused {base : Base} {index : Index base}
    (reason : Reason Denied) (control : reader.V base index)
    (state : source.State base index × Account) :
    retry source gate profiles replay invoice reader notice
      (.done ⟨index, .inr (reason, control), state⟩) =
        .paused ⟨index, .inl control, state⟩ := rfl

theorem retry_ready {base : Base} {index : Index base}
    (value : Return base index) (state : source.State base index × Account) :
    retry source gate profiles replay invoice reader notice
      (.done ⟨index, .inl value, state⟩) = .done ⟨index, .inl value, state⟩ := rfl

/-- Install the service owner's current checker without evaluating or
reconstructing retained work. This is representation transport, not a proof
that the new checker is authentic, current, or equivalent to the old one. -/
def replaceGate (next : Gate (Denied := Denied) source) {base : Base}
    (previous : Outcome source gate profiles replay invoice reader notice base) :
    Outcome source next profiles replay invoice reader notice base :=
  Cursor.Outcome.mapState (client reader notice)
    (source := provider source gate profiles replay invoice)
    (target := provider source next profiles replay invoice) (fun state => state) previous

/-- Replacing a checker retains the exact state/account and original client
control; a reverse replacement recovers the entire old cursor outcome. -/
theorem replaceGate_roundtrip (next : Gate (Denied := Denied) source) {base : Base}
    (previous : Outcome source gate profiles replay invoice reader notice base) :
    replaceGate source next profiles replay invoice reader notice gate
      (replaceGate source gate profiles replay invoice reader notice next previous) = previous := by
  cases previous with
  | paused packet => rcases packet with ⟨index, control, state⟩; rfl
  | done result => rcases result with ⟨index, value, state⟩; rfl

theorem replaceGate_injective (next : Gate (Denied := Denied) source) {base : Base} :
    Function.Injective (replaceGate source gate profiles replay invoice reader notice next (base := base)) := by
  intro first second same
  have restored := congrArg (replaceGate source next profiles replay invoice reader notice gate) same
  simpa only [replaceGate_roundtrip] using restored

theorem replaceGate_preserves_account (next : Gate (Denied := Denied) source) {base : Base}
    (previous : Outcome source gate profiles replay invoice reader notice base) :
    accountOf source next profiles replay invoice reader notice
      (replaceGate source gate profiles replay invoice reader notice next previous) =
        accountOf source gate profiles replay invoice reader notice previous := by
  cases previous with
  | paused packet => rcases packet with ⟨index, control, state⟩; rfl
  | done result => rcases result with ⟨index, value, state⟩; rfl

theorem replaceGate_retry (next : Gate (Denied := Denied) source) {base : Base}
    (previous : Outcome source gate profiles replay invoice reader notice base) :
    retry source next profiles replay invoice reader notice
      (replaceGate source gate profiles replay invoice reader notice next previous) =
        replaceGate source gate profiles replay invoice reader notice next
          (retry source gate profiles replay invoice reader notice previous) := by
  cases previous with
  | paused packet => rcases packet with ⟨index, control, state⟩; rfl
  | done result => rcases result with ⟨index, value, state⟩; cases value <;> rfl

def run (fuel : Nat) {base : Base}
    (packet : Cursor.Packet (provider source gate profiles replay invoice)
      (client (Denied := Denied) reader notice) base) :
    Nat × Outcome source gate profiles replay invoice reader notice base :=
  Cursor.advance (provider source gate profiles replay invoice) (client reader notice)
    (charge source gate profiles replay invoice) fuel packet

def resume (fuel : Nat) {base : Base}
    (previous : Nat × Outcome source gate profiles replay invoice reader notice base) :
    Nat × Outcome source gate profiles replay invoice reader notice base :=
  Cursor.resume (provider source gate profiles replay invoice) (client reader notice)
    (charge source gate profiles replay invoice) fuel previous

theorem run_split (first second : Nat) {base : Base}
    (packet : Cursor.Packet (provider source gate profiles replay invoice)
      (client (Denied := Denied) reader notice) base) :
    run source gate profiles replay invoice reader notice (first + second) packet =
      resume source gate profiles replay invoice reader notice second
        (run source gate profiles replay invoice reader notice first packet) :=
  Cursor.advance_add _ _ _ _ _ _

theorem resume_zero {base : Base}
    (previous : Nat × Outcome source gate profiles replay invoice reader notice base) :
    resume source gate profiles replay invoice reader notice 0 previous = previous :=
  Cursor.resume_zero _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Refusing a request before invocation preserves the original pending
phase. No original provider action or native invoice is performed. -/
theorem pre_call_refusal_retains_pending_phase {base : Base} {index : Index base}
    (control : reader.V base index) (request : P.Shape base index)
    (children : (reply : P.Position request) → reader.V base (P.next request reply))
    (exposed : reader.str base index control = ⟨.inr request, children⟩)
    (state : source.State base index × Account) (reason : Reason Denied)
    (refused : admit source gate profiles replay invoice state.1 request state.2 = .error reason) :
    run source gate profiles replay invoice reader notice 2 ⟨index, .inl control, state⟩ =
      (0, .done ⟨index, .inr (reason, control), state⟩) := by
  have stepped := (refused_step source gate profiles replay invoice state request reason refused).1
  have priced := (refused_step source gate profiles replay invoice state request reason refused).2
  have head := client_call reader notice control request children exposed
  unfold run
  rw [Cursor.advance.eq_def]
  dsimp only
  rw [head]
  dsimp only [withHoles]
  rw [stepped, priced]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A refusal reported by an actual reply keeps that reply's selected child
and updated source state. Its already accepted invoice remains paid. -/
theorem post_reply_refusal_retains_selected_phase {base : Base} {index : Index base}
    (control : reader.V base index) (request : P.Shape base index)
    (children : (reply : P.Position request) → reader.V base (P.next request reply))
    (exposed : reader.str base index control = ⟨.inr request, children⟩)
    (state : source.State base index × Account) (account : Account) (reason : Denied)
    (accepted : admit source gate profiles replay invoice state.1 request state.2 = .ok account)
    (reported : notice request (source.step state.1 request).1 = some reason) :
    run source gate profiles replay invoice reader notice 2 ⟨index, .inl control, state⟩ =
      (work (invoice state.1 request), .done
        ⟨P.next request (source.step state.1 request).1,
          .inr (.inl reason, children (source.step state.1 request).1),
          (source.step state.1 request).2, account⟩) := by
  have stepped := (accepted_step source gate profiles replay invoice state request account accepted).1
  have priced := (accepted_step source gate profiles replay invoice state request account accepted).2
  have head := client_call reader notice control request children exposed
  unfold run
  rw [Cursor.advance.eq_def]
  dsimp only
  rw [head]
  dsimp only [withHoles]
  rw [stepped, priced]
  simp only [reported]
  rfl

/-- Conservation is proved for the actual indexed traversal, including a
pause immediately after a refusal or a successful reply. -/
theorem run_account (fuel : Nat) {base : Base}
    (packet : Cursor.Packet (provider source gate profiles replay invoice)
      (client (Denied := Denied) reader notice) base) :
    let result := run source gate profiles replay invoice reader notice fuel packet
    let after := accountOf source gate profiles replay invoice reader notice result.2
    after.remaining + result.1 = packet.2.2.2.remaining ∧
      after.remaining + work after.events =
        packet.2.2.2.remaining + work packet.2.2.2.events ∧
      allowanceTotal after = allowanceTotal packet.2.2.2 :=
  advance_account source gate profiles replay invoice (client reader notice) fuel packet

/-- The accepted event work is precisely the additional native ledger work,
not the number of phases, calls, or successful rows. -/
theorem run_ledger (fuel : Nat) {base : Base}
    (packet : Cursor.Packet (provider source gate profiles replay invoice)
      (client (Denied := Denied) reader notice) base) :
    work (accountOf source gate profiles replay invoice reader notice
      (run source gate profiles replay invoice reader notice fuel packet).2).events =
        work packet.2.2.2.events + (run source gate profiles replay invoice reader notice fuel packet).1 := by
  have conserved := run_account source gate profiles replay invoice reader notice fuel packet
  dsimp only at conserved
  omega

theorem resume_account (fuel : Nat) {base : Base}
    (previous : Nat × Outcome source gate profiles replay invoice reader notice base) :
    let result := resume source gate profiles replay invoice reader notice fuel previous
    let before := accountOf source gate profiles replay invoice reader notice previous.2
    let after := accountOf source gate profiles replay invoice reader notice result.2
    after.remaining + result.1 = before.remaining + previous.1 ∧
      work after.events + previous.1 = work before.events + result.1 ∧
      allowanceTotal after = allowanceTotal before := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done result => exact ⟨rfl, rfl, rfl⟩
  | paused packet =>
      have balance := run_account source gate profiles replay invoice reader notice fuel packet
      have ledger := run_ledger source gate profiles replay invoice reader notice fuel packet
      dsimp only at balance ledger
      change
        (accountOf source gate profiles replay invoice reader notice
          (run source gate profiles replay invoice reader notice fuel packet).2).remaining +
            (paid + (run source gate profiles replay invoice reader notice fuel packet).1) =
              packet.2.2.2.remaining + paid ∧
          work (accountOf source gate profiles replay invoice reader notice
            (run source gate profiles replay invoice reader notice fuel packet).2).events + paid =
              work packet.2.2.2.events + (paid +
                (run source gate profiles replay invoice reader notice fuel packet).1) ∧
          allowanceTotal (accountOf source gate profiles replay invoice reader notice
            (run source gate profiles replay invoice reader notice fuel packet).2) =
              allowanceTotal packet.2.2.2
      exact ⟨by omega, by omega, balance.2.2⟩

/-! ### Retained invocations and validated publication

An invocation below retains the exact indexed outcome, paid account and source
submission.  Its installed gate is a parameter of the outcome, not an
authority token stored in the invocation.  A service may therefore install its
current gate before resumption without changing the dependency manifest or
the retained computation.

Publication delegates to `ValidatedCommit`.  The readiness witness connects
the actual terminal reply to the transaction's writes; it is not reconstructed
from a payload.  Current permission is supplied separately at publication
time, so a completed invocation does not acquire ambient publication
authority. -/

variable {Key Value : Type}

/-- One source submission together with its exact paid indexed residual.
The submission is the declared publication dependency certificate.  Proving
that a native handler records every read it actually performs is a separate
realization obligation. -/
structure Invocation (base : Base) where
  submission : ValidatedCommit.Submission Key Value
  spent : Nat
  outcome : Outcome source gate profiles replay invoice reader notice base

def Invocation.reads {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) :
    ReadOnlyQuery.Reads Key Value :=
  (ReadOnlyQuery.run held.submission.1 held.submission.2).reads

def Invocation.account {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) : Account :=
  accountOf source gate profiles replay invoice reader notice held.outcome

/-- Every operation event retained by the invocation occurs, in order, in the
native poll history.  The history may additionally contain admission,
preparation, delivery and teardown events owned by the surrounding service.
Authenticity and completeness of the native history remain realization
obligations. -/
def Invocation.PollHistoryCovers {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (history : NativePoll.History) : Prop :=
  held.account.events.Sublist (NativePoll.historyEvents history)

/-- Install the service owner's current gate without changing the submission,
manifest, paid work, private source state or reply-selected continuation. -/
def Invocation.replaceGate (next : Gate (Denied := Denied) source) {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) :
    Invocation (Key := Key) (Value := Value)
      source next profiles replay invoice reader notice base where
  submission := held.submission
  spent := held.spent
  outcome := OperationCostProtocol.Indexed.replaceGate source gate profiles replay invoice
    reader notice next held.outcome

@[simp] theorem Invocation.replaceGate_submission
    (next : Gate (Denied := Denied) source) {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) :
    (held.replaceGate source gate profiles replay invoice reader notice next).submission =
      held.submission := rfl

@[simp] theorem Invocation.replaceGate_reads
    (next : Gate (Denied := Denied) source) {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) :
    (held.replaceGate source gate profiles replay invoice reader notice next).reads = held.reads := rfl

@[simp] theorem Invocation.replaceGate_spent
    (next : Gate (Denied := Denied) source) {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) :
    (held.replaceGate source gate profiles replay invoice reader notice next).spent = held.spent := rfl

theorem Invocation.replaceGate_account
    (next : Gate (Denied := Denied) source) {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) :
    (held.replaceGate source gate profiles replay invoice reader notice next).account = held.account :=
  replaceGate_preserves_account source gate profiles replay invoice reader notice next held.outcome

/-- Rearm a refusal and run under an explicitly supplied current gate.  A
ready result remains inert. -/
def Invocation.resumeWith (next : Gate (Denied := Denied) source) (fuel : Nat) {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) :
    Invocation (Key := Key) (Value := Value)
      source next profiles replay invoice reader notice base :=
  let installed := held.replaceGate source gate profiles replay invoice reader notice next
  let later := resume source next profiles replay invoice reader notice fuel
    (installed.spent, retry source next profiles replay invoice reader notice installed.outcome)
  ⟨installed.submission, later.1, later.2⟩

@[simp] theorem Invocation.resumeWith_submission
    (next : Gate (Denied := Denied) source) (fuel : Nat) {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) :
    (held.resumeWith source gate profiles replay invoice reader notice next fuel).submission =
      held.submission := rfl

@[simp] theorem Invocation.resumeWith_reads
    (next : Gate (Denied := Denied) source) (fuel : Nat) {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) :
    (held.resumeWith source gate profiles replay invoice reader notice next fuel).reads = held.reads := rfl

theorem Invocation.resumeWith_account
    (next : Gate (Denied := Denied) source) (fuel : Nat) {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) :
    let later := held.resumeWith source gate profiles replay invoice reader notice next fuel
    later.account.remaining + later.spent = held.account.remaining + held.spent ∧
      work later.account.events + held.spent = work held.account.events + later.spent ∧
      allowanceTotal later.account = allowanceTotal held.account := by
  let installed := held.replaceGate source gate profiles replay invoice reader notice next
  have law := resume_account source next profiles replay invoice reader notice fuel
    (installed.spent, retry source next profiles replay invoice reader notice installed.outcome)
  rw [retry_preserves_account] at law
  have sameAccount : installed.account = held.account :=
    Invocation.replaceGate_account source gate profiles replay invoice reader notice next held
  change accountOf source next profiles replay invoice reader notice installed.outcome =
    accountOf source gate profiles replay invoice reader notice held.outcome at sameAccount
  rw [sameAccount] at law
  have sameSpent : installed.spent = held.spent := rfl
  rw [sameSpent] at law
  change
    let later := held.resumeWith source gate profiles replay invoice reader notice next fuel
    later.account.remaining + later.spent = held.account.remaining + held.spent ∧
      work later.account.events + held.spent = work held.account.events + later.spent ∧
      allowanceTotal later.account = allowanceTotal held.account
  simpa only [Invocation.resumeWith, Invocation.account, installed,
    Invocation.replaceGate_spent] using law

/-- Evidence that the actual terminal reply realizes the stored transaction's
writes.  A logical incompatibility can inhabit this view only if a caller maps
it to writes and proves the equality.  An operational refusal cannot inhabit
it because it is not an original terminal reply. -/
def Invocation.Ready {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base) : Prop :=
  ∃ index : Index base, ∃ value : Return base index,
    ∃ state : source.State base index × Account,
      held.outcome = Cursor.Outcome.done ⟨index, .inl value, state⟩ ∧
        writes value = (ReadOnlyQuery.run held.submission.1 held.submission.2).answer

/-! ## Generation-stamped authority at resumable boundaries -/

namespace PrincipalIncarnation

open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

/-- One service's current binding from an externally authenticated account to
its nonreused incarnation generation.  The registry does not claim to detect
operating-system account deletion or uid reuse; an owner or trusted launcher
must request rotation at that lifecycle boundary. -/
structure Registry (Service Account : Type) where
  service : Service
  nextGeneration : Nat
  binding : Account → Option Nat

def Registry.empty {Service Account : Type} (service : Service) : Registry Service Account where
  service := service
  nextGeneration := 0
  binding := fun _ => none

/-- Every installed generation was minted by this registry and is nonzero. -/
def Registry.Lawful {Service Account : Type} (registry : Registry Service Account) : Prop :=
  ∀ account generation, registry.binding account = some generation →
    0 < generation ∧ generation ≤ registry.nextGeneration

/-- A service-wide generation identifies at most one current account binding.
Historical handles may retain older generations, but no live binding reuses
one for another account. -/
def Registry.Unique {Service Account : Type} (registry : Registry Service Account) : Prop :=
  ∀ left right generation,
    registry.binding left = some generation →
    registry.binding right = some generation → left = right

/-- A principal reference is current only at its issuing service and exact
account-incarnation generation. -/
def Registry.Current {Service Account : Type}
    (registry : Registry Service Account) (reference : Handle Service Account) : Prop :=
  reference.provider = registry.service ∧
    registry.binding reference.resource = some reference.generation

/-- Explicitly rotate one account to the next nonreused generation. -/
def Registry.rotate {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (account : Account) :
    Handle Service Account × Registry Service Account :=
  let generation := registry.nextGeneration + 1
  (⟨registry.service, account, generation⟩,
    { service := registry.service
      nextGeneration := generation
      binding := fun candidate =>
        if candidate = account then some generation else registry.binding candidate })

/-- Resolve the account's current incarnation, minting the next generation
only when no binding exists.  This is the first-grant path; repeated grants do
not silently rotate an account. -/
def Registry.ensure {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (account : Account) :
    Handle Service Account × Registry Service Account :=
  match registry.binding account with
  | some generation => (⟨registry.service, account, generation⟩, registry)
  | none => registry.rotate account

theorem Registry.empty_lawful {Service Account : Type} (service : Service) :
    (Registry.empty (Account := Account) service).Lawful := by
  intro account generation installed
  cases installed

theorem Registry.empty_unique {Service Account : Type} (service : Service) :
    (Registry.empty (Account := Account) service).Unique := by
  intro left right generation installed
  cases installed

theorem Registry.rotate_current {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (account : Account) :
    (registry.rotate account).2.Current (registry.rotate account).1 := by
  simp [Registry.rotate, Registry.Current]

theorem Registry.ensure_current {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (account : Account) :
    (registry.ensure account).2.Current (registry.ensure account).1 := by
  cases installed : registry.binding account with
  | none => simp [Registry.ensure, installed, Registry.rotate_current]
  | some generation => simp [Registry.ensure, installed, Registry.Current]

theorem Registry.ensure_existing {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (account : Account) (generation : Nat)
    (installed : registry.binding account = some generation) :
    registry.ensure account = (⟨registry.service, account, generation⟩, registry) := by
  simp [Registry.ensure, installed]

theorem Registry.ensure_missing {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (account : Account)
    (missing : registry.binding account = none) :
    registry.ensure account = registry.rotate account := by
  simp [Registry.ensure, missing]

theorem Registry.rotate_lawful {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (account : Account)
    (lawful : registry.Lawful) : (registry.rotate account).2.Lawful := by
  intro candidate generation installed
  by_cases same : candidate = account
  · subst candidate
    simp [Registry.rotate] at installed
    subst generation
    change 0 < registry.nextGeneration + 1 ∧
      registry.nextGeneration + 1 ≤ registry.nextGeneration + 1
    exact ⟨Nat.zero_lt_succ _, le_rfl⟩
  · have prior : registry.binding candidate = some generation := by
      simpa [Registry.rotate, same] using installed
    obtain ⟨positive, bounded⟩ := lawful candidate generation prior
    change 0 < generation ∧ generation ≤ registry.nextGeneration + 1
    exact ⟨positive, bounded.trans (Nat.le_succ _)⟩

theorem Registry.rotate_unique {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (account : Account)
    (lawful : registry.Lawful) (unique : registry.Unique) :
    (registry.rotate account).2.Unique := by
  intro left right generation leftInstalled rightInstalled
  by_cases leftTarget : left = account
  · subst left
    simp [Registry.rotate] at leftInstalled
    subst generation
    by_cases rightTarget : right = account
    · exact rightTarget.symm
    · have prior : registry.binding right = some (registry.nextGeneration + 1) := by
        simpa [Registry.rotate, rightTarget] using rightInstalled
      have bounded := (lawful right (registry.nextGeneration + 1) prior).2
      omega
  · have leftPrior : registry.binding left = some generation := by
      simpa [Registry.rotate, leftTarget] using leftInstalled
    by_cases rightTarget : right = account
    · subst right
      simp [Registry.rotate] at rightInstalled
      subst generation
      have bounded := (lawful left (registry.nextGeneration + 1) leftPrior).2
      omega
    · have rightPrior : registry.binding right = some generation := by
        simpa [Registry.rotate, rightTarget] using rightInstalled
      exact unique left right generation leftPrior rightPrior

theorem Registry.ensure_lawful {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (account : Account)
    (lawful : registry.Lawful) : (registry.ensure account).2.Lawful := by
  cases installed : registry.binding account with
  | none =>
      simpa [Registry.ensure, installed] using registry.rotate_lawful account lawful
  | some generation => simpa [Registry.ensure, installed] using lawful

theorem Registry.ensure_unique {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (account : Account)
    (lawful : registry.Lawful) (unique : registry.Unique) :
    (registry.ensure account).2.Unique := by
  cases installed : registry.binding account with
  | none =>
      simpa [Registry.ensure, installed] using registry.rotate_unique account lawful unique
  | some generation => simpa [Registry.ensure, installed] using unique

theorem Registry.current_generation_identifies_account
    {Service Account : Type} (registry : Registry Service Account)
    (unique : registry.Unique) (left right : Handle Service Account)
    (leftCurrent : registry.Current left) (rightCurrent : registry.Current right)
    (sameGeneration : left.generation = right.generation) :
    left.resource = right.resource := by
  apply unique left.resource right.resource left.generation leftCurrent.2
  simpa [sameGeneration] using rightCurrent.2

/-- Rotation preserves a different account's exact current reference. -/
theorem Registry.rotate_preserves_other {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (account : Account)
    (reference : Handle Service Account)
    (different : reference.resource ≠ account)
    (current : registry.Current reference) :
    (registry.rotate account).2.Current reference := by
  exact ⟨current.1, by simpa [Registry.rotate, different] using current.2⟩

/-- Rotation cannot revive or silently retarget the prior incarnation. -/
theorem Registry.rotate_invalidates_prior {Service Account : Type} [DecidableEq Account]
    (registry : Registry Service Account) (reference : Handle Service Account)
    (lawful : registry.Lawful) (current : registry.Current reference) :
    ¬ (registry.rotate reference.resource).2.Current reference := by
  intro retained
  have bounded := (lawful reference.resource reference.generation current.2).2
  have reused : registry.nextGeneration + 1 = reference.generation := by
    simpa [Registry.rotate] using retained.2
  omega

/-- A raw account spelling cannot identify an incarnation: equal account
components coexist with distinct principal references. -/
theorem same_account_does_not_identify_incarnation
    {Service Account : Type} (service : Service) (account : Account)
    (first second : Nat) (different : first ≠ second) :
    (⟨service, account, first⟩ : Handle Service Account) ≠
      ⟨service, account, second⟩ := by
  intro equal
  exact different (congrArg Handle.generation equal)

namespace Controls

def initial : Registry Nat Nat := Registry.empty 5
def first : Handle Nat Nat × Registry Nat Nat := initial.rotate 17
def second : Handle Nat Nat × Registry Nat Nat := first.2.rotate 17
def ensured : Handle Nat Nat × Registry Nat Nat := first.2.ensure 17

theorem first_rotation_is_current_and_lawful :
    first.2.Current first.1 ∧ first.2.Lawful := by
  exact ⟨Registry.rotate_current initial 17,
    Registry.rotate_lawful initial 17 (Registry.empty_lawful 5)⟩

theorem first_rotation_is_unique : first.2.Unique := by
  exact Registry.rotate_unique initial 17
    (Registry.empty_lawful 5) (Registry.empty_unique 5)

theorem second_rotation_invalidates_first :
    second.2.Current second.1 ∧ ¬ second.2.Current first.1 := by
  exact ⟨Registry.rotate_current first.2 17,
    Registry.rotate_invalidates_prior first.2 first.1
      first_rotation_is_current_and_lawful.2 first_rotation_is_current_and_lawful.1⟩

theorem account_value_alone_is_unchanged :
    first.1.resource = second.1.resource ∧ first.1 ≠ second.1 := by
  exact ⟨rfl, same_account_does_not_identify_incarnation 5 17 1 2 (by decide)⟩

theorem repeated_ensure_preserves_incarnation :
    ensured.1 = first.1 ∧ ensured.2 = first.2 := by
  simp [ensured, first, initial, Registry.ensure, Registry.rotate]

end Controls

#print axioms Registry.empty_lawful
#print axioms Registry.empty_unique
#print axioms Registry.rotate_current
#print axioms Registry.ensure_current
#print axioms Registry.ensure_existing
#print axioms Registry.ensure_missing
#print axioms Registry.rotate_lawful
#print axioms Registry.rotate_unique
#print axioms Registry.ensure_lawful
#print axioms Registry.ensure_unique
#print axioms Registry.current_generation_identifies_account
#print axioms Registry.rotate_preserves_other
#print axioms Registry.rotate_invalidates_prior
#print axioms same_account_does_not_identify_incarnation
#print axioms Controls.first_rotation_is_current_and_lawful
#print axioms Controls.first_rotation_is_unique
#print axioms Controls.second_rotation_invalidates_first
#print axioms Controls.account_value_alone_is_unchanged
#print axioms Controls.repeated_ensure_preserves_incarnation

end PrincipalIncarnation

namespace CheckedGrant

open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

/-- A retained operation requires an authority resource at one exact provider,
resource and generation.  `Handle` is the existing nominal foreign-resource
identity; this interface does not introduce another capability identity. -/
structure Requirement (Provider Resource Authority : Type) where
  handle : Handle Provider Resource
  required : Authority

/-- A current grant view joins the exact live handle to the authority available
at it.  Authentic construction of this view remains a native monitor duty. -/
structure View (Provider Resource Authority : Type) where
  handle : Handle Provider Resource
  available : Authority

/-- The retained requirement is current exactly when both its nominal
generation and its required frame-preserving authority remain current. -/
def Requirement.Current
    {Provider Resource Authority : Type}
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (requirement : Requirement Provider Resource Authority)
    (view : View Provider Resource Authority) : Prop :=
  requirement.handle = view.handle ∧ FrameUpdate view.available requirement.required

theorem Requirement.current_iff
    {Provider Resource Authority : Type}
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (requirement : Requirement Provider Resource Authority)
    (view : View Provider Resource Authority) :
    requirement.Current view ↔
      requirement.handle = view.handle ∧ FrameUpdate view.available requirement.required :=
  Iff.rfl

/-- Replacing a grant with a distinct generation cannot revive a requirement
issued for the old generation, even when its rights spelling is restored. -/
theorem Requirement.not_current_of_generation_ne
    {Provider Resource Authority : Type}
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (requirement : Requirement Provider Resource Authority)
    (view : View Provider Resource Authority)
    (different : requirement.handle.generation ≠ view.handle.generation) :
    ¬ requirement.Current view := by
  intro current
  exact different (congrArg Handle.generation current.1)

end CheckedGrant

namespace CheckedDecision

/-- A durable decision keeps the exact grant requirement even when its full
reply has left the bounded reply cache.  `none` is an explicit retired reply,
not absence of a decision. -/
structure Decision (Provider Resource Authority Reply : Type) where
  requirement : CheckedGrant.Requirement Provider Resource Authority
  reply : Option Reply

/-- Retire only the bounded reply payload.  The durable decision and its exact
grant requirement remain available for retry classification and historical
observations. -/
def Decision.retireReply
    {Provider Resource Authority Reply : Type}
    (decision : Decision Provider Resource Authority Reply) :
    Decision Provider Resource Authority Reply :=
  { decision with reply := none }

/-- Retrying a request is distinct from observing a cached reply, a known
decision whose reply was retired, or a decision whose authority is stale. -/
inductive RetryResult (Reply : Type) where
  | execute
  | cached (reply : Reply)
  | unknown
  | refused
  deriving DecidableEq, Repr

def retry
    {Provider Resource Authority Reply : Type}
    [DecidableEq Provider] [DecidableEq Resource]
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (permission : ∀ current required : Authority, Decidable (FrameUpdate current required))
    (view : CheckedGrant.View Provider Resource Authority)
    (decision : Option (Decision Provider Resource Authority Reply)) : RetryResult Reply :=
  match decision with
  | none => .execute
  | some decision =>
      if decision.requirement.handle = view.handle then
        if FrameUpdate view.available decision.requirement.required then
          match decision.reply with
          | some reply => .cached reply
          | none => .unknown
        else .refused
      else .refused

@[simp] theorem retry_missing
    {Provider Resource Authority Reply : Type}
    [DecidableEq Provider] [DecidableEq Resource]
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (permission : ∀ current required : Authority, Decidable (FrameUpdate current required))
    (view : CheckedGrant.View Provider Resource Authority) :
    retry permission view (none : Option (Decision Provider Resource Authority Reply)) = .execute :=
  rfl

theorem retry_current
    {Provider Resource Authority Reply : Type}
    [DecidableEq Provider] [DecidableEq Resource]
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (permission : ∀ current required : Authority, Decidable (FrameUpdate current required))
    (view : CheckedGrant.View Provider Resource Authority)
    (decision : Decision Provider Resource Authority Reply)
    (current : decision.requirement.Current view) :
    retry permission view (some decision) =
      match decision.reply with
      | some reply => .cached reply
      | none => .unknown := by
  simp [retry, current.1, current.2]

theorem retry_stale_generation
    {Provider Resource Authority Reply : Type}
    [DecidableEq Provider] [DecidableEq Resource]
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (permission : ∀ current required : Authority, Decidable (FrameUpdate current required))
    (view : CheckedGrant.View Provider Resource Authority)
    (decision : Decision Provider Resource Authority Reply)
    (stale : decision.requirement.handle.generation ≠ view.handle.generation) :
    retry permission view (some decision) = .refused := by
  have different : decision.requirement.handle ≠ view.handle := by
    intro same
    exact stale (congrArg (fun handle => handle.generation) same)
  simp [retry, different]

theorem retry_authority_refused
    {Provider Resource Authority Reply : Type}
    [DecidableEq Provider] [DecidableEq Resource]
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (permission : ∀ current required : Authority, Decidable (FrameUpdate current required))
    (view : CheckedGrant.View Provider Resource Authority)
    (decision : Decision Provider Resource Authority Reply)
    (same : decision.requirement.handle = view.handle)
    (refused : ¬FrameUpdate view.available decision.requirement.required) :
    retry permission view (some decision) = .refused := by
  simp [retry, same, refused]

/-- A known decision never re-enters execution.  A retired reply becomes
explicitly unknown, and stale authority becomes refused. -/
theorem retry_existing_ne_execute
    {Provider Resource Authority Reply : Type}
    [DecidableEq Provider] [DecidableEq Resource]
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (permission : ∀ current required : Authority, Decidable (FrameUpdate current required))
    (view : CheckedGrant.View Provider Resource Authority)
    (decision : Decision Provider Resource Authority Reply) :
    retry permission view (some decision) ≠ .execute := by
  by_cases same : decision.requirement.handle = view.handle
  · by_cases allowed : FrameUpdate view.available decision.requirement.required
    · cases reply : decision.reply <;> simp [retry, same, allowed, reply]
    · simp [retry, same, allowed]
  · simp [retry, same]

theorem retry_eq_execute_iff
    {Provider Resource Authority Reply : Type}
    [DecidableEq Provider] [DecidableEq Resource]
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (permission : ∀ current required : Authority, Decidable (FrameUpdate current required))
    (view : CheckedGrant.View Provider Resource Authority)
    (decision : Option (Decision Provider Resource Authority Reply)) :
    retry permission view decision = .execute ↔ decision = none := by
  cases decision with
  | none => simp [retry]
  | some decision =>
      constructor
      · intro executes
        exact (retry_existing_ne_execute permission view decision executes).elim
      · intro impossible
        cases impossible

/-! ### Historical account origin

An account-origin reference is copyable evidence, not authority.  Its
protection comes from lookup in the service-private durable decision table;
constructing the record below is therefore a native issuance obligation.  The
observation deliberately omits the cached reply and any claimed agent label.
-/

namespace AccountOrigin

structure Reference (Service Principal Request Nonce : Type) where
  service : Service
  principal : Principal
  request : Request
  nonce : Nonce
  deriving DecidableEq, Repr

structure Record (Provider Resource Authority Reply Service Principal Request Nonce Digest : Type)
    where
  reference : Reference Service Principal Request Nonce
  decision : CheckedDecision.Decision Provider Resource Authority Reply
  effectDigest : Digest

structure Observation (Provider Resource Authority Service Principal Request Nonce Digest : Type)
    where
  reference : Reference Service Principal Request Nonce
  requirement : CheckedGrant.Requirement Provider Resource Authority
  effectDigest : Digest

def Record.observe
    {Provider Resource Authority Reply Service Principal Request Nonce Digest : Type}
    (record : Record Provider Resource Authority Reply Service Principal Request Nonce Digest) :
    Observation Provider Resource Authority Service Principal Request Nonce Digest :=
  ⟨record.reference, record.decision.requirement, record.effectDigest⟩

/-- Reply-cache retirement changes only the decision's optional reply.  The
historical origin record remains the same observation. -/
def Record.retireReply
    {Provider Resource Authority Reply Service Principal Request Nonce Digest : Type}
    (record : Record Provider Resource Authority Reply Service Principal Request Nonce Digest) :
    Record Provider Resource Authority Reply Service Principal Request Nonce Digest :=
  { record with decision := record.decision.retireReply }

/-- Full reply retention and historical origin have independent lifetimes. -/
theorem observe_reply_irrelevant
    {Provider Resource Authority Reply Service Principal Request Nonce Digest : Type}
    (reference : Reference Service Principal Request Nonce)
    (requirement : CheckedGrant.Requirement Provider Resource Authority)
    (first second : Option Reply) (digest : Digest) :
    (⟨reference, ⟨requirement, first⟩, digest⟩ :
      Record Provider Resource Authority Reply Service Principal Request Nonce Digest).observe =
    (⟨reference, ⟨requirement, second⟩, digest⟩ :
      Record Provider Resource Authority Reply Service Principal Request Nonce Digest).observe :=
  rfl

/-- Inspecting historical origin checks the current service and either the
authenticated originating account or the service owner.  It never checks or
restores current mutation authority. -/
def inspect
    {Provider Resource Authority Reply Service Principal Request Nonce Digest : Type}
    [DecidableEq Service] [DecidableEq Principal] [DecidableEq Request] [DecidableEq Nonce]
    (service : Service) (requester : Principal) (owner : Bool)
    (reference : Reference Service Principal Request Nonce)
    (stored : Option
      (Record Provider Resource Authority Reply Service Principal Request Nonce Digest)) :
    Option (Observation Provider Resource Authority Service Principal Request Nonce Digest) :=
  match stored with
  | none => none
  | some record =>
      if service = record.reference.service ∧ reference = record.reference ∧
          (owner = true ∨ requester = record.reference.principal) then
        some record.observe
      else none

@[simp] theorem inspect_missing
    {Provider Resource Authority Reply Service Principal Request Nonce Digest : Type}
    [DecidableEq Service] [DecidableEq Principal] [DecidableEq Request] [DecidableEq Nonce]
    (service : Service) (requester : Principal) (owner : Bool)
    (reference : Reference Service Principal Request Nonce) :
    inspect (Provider := Provider) (Resource := Resource) (Authority := Authority) (Reply := Reply)
      (Digest := Digest) service requester owner reference none = none :=
  rfl

theorem inspect_owner
    {Provider Resource Authority Reply Service Principal Request Nonce Digest : Type}
    [DecidableEq Service] [DecidableEq Principal] [DecidableEq Request] [DecidableEq Nonce]
    (requester : Principal)
    (record : Record Provider Resource Authority Reply Service Principal Request Nonce Digest) :
    inspect record.reference.service requester true record.reference (some record) =
      some record.observe := by
  simp [inspect]

theorem inspect_originating_account
    {Provider Resource Authority Reply Service Principal Request Nonce Digest : Type}
    [DecidableEq Service] [DecidableEq Principal] [DecidableEq Request] [DecidableEq Nonce]
    (record : Record Provider Resource Authority Reply Service Principal Request Nonce Digest) :
    inspect record.reference.service record.reference.principal false record.reference
      (some record) = some record.observe := by
  simp [inspect]

theorem inspect_other_account_refused
    {Provider Resource Authority Reply Service Principal Request Nonce Digest : Type}
    [DecidableEq Service] [DecidableEq Principal] [DecidableEq Request] [DecidableEq Nonce]
    (requester : Principal)
    (record : Record Provider Resource Authority Reply Service Principal Request Nonce Digest)
    (other : requester ≠ record.reference.principal) :
    inspect record.reference.service requester false record.reference (some record) = none := by
  simp [inspect, other]

theorem inspect_forged_reference_refused
    {Provider Resource Authority Reply Service Principal Request Nonce Digest : Type}
    [DecidableEq Service] [DecidableEq Principal] [DecidableEq Request] [DecidableEq Nonce]
    (requester : Principal) (owner : Bool)
    (reference : Reference Service Principal Request Nonce)
    (record : Record Provider Resource Authority Reply Service Principal Request Nonce Digest)
    (forged : reference ≠ record.reference) :
    inspect record.reference.service requester owner reference (some record) = none := by
  simp [inspect, forged]

/-- Evicting a current decision's bounded reply makes retry explicitly
unknown, while the originating account still observes the same historical
origin. -/
theorem retired_reply_unknown_and_origin_preserved
    {Provider Resource Authority Reply Service Principal Request Nonce Digest : Type}
    [DecidableEq Provider] [DecidableEq Resource]
    [DecidableEq Service] [DecidableEq Principal] [DecidableEq Request] [DecidableEq Nonce]
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (permission : ∀ current required : Authority, Decidable (FrameUpdate current required))
    (view : CheckedGrant.View Provider Resource Authority)
    (record : Record Provider Resource Authority Reply Service Principal Request Nonce Digest)
    (current : record.decision.requirement.Current view) :
    retry permission view (some record.retireReply.decision) = .unknown ∧
      inspect record.reference.service record.reference.principal false record.reference
        (some record.retireReply) = some record.observe := by
  constructor
  · simp [retry, Record.retireReply, Decision.retireReply, current.1, current.2]
  · simp [inspect, Record.retireReply, Decision.retireReply, Record.observe]

/-- Replacing a grant generation refuses retry but does not rewrite historical
origin.  The reference remains readable by the originating account. -/
theorem stale_generation_refused_and_origin_preserved
    {Provider Resource Authority Reply Service Principal Request Nonce Digest : Type}
    [DecidableEq Provider] [DecidableEq Resource]
    [DecidableEq Service] [DecidableEq Principal] [DecidableEq Request] [DecidableEq Nonce]
    [Zero Authority] [Add Authority] [Mettapedia.GSLT.SeparationAlgebra.SepAlgebra Authority]
    (permission : ∀ current required : Authority, Decidable (FrameUpdate current required))
    (view : CheckedGrant.View Provider Resource Authority)
    (record : Record Provider Resource Authority Reply Service Principal Request Nonce Digest)
    (stale : record.decision.requirement.handle.generation ≠ view.handle.generation) :
    retry permission view (some record.decision) = .refused ∧
      inspect record.reference.service record.reference.principal false record.reference
        (some record) = some record.observe := by
  exact ⟨retry_stale_generation permission view record.decision stale,
    inspect_originating_account record⟩

namespace Controls

def requirement : CheckedGrant.Requirement Nat Nat Nat := ⟨⟨3, 7, 11⟩, 1⟩
def decision : CheckedDecision.Decision Nat Nat Nat Nat := ⟨requirement, some 99⟩
def reference : Reference Nat Nat Nat Nat := ⟨5, 17, 23, 29⟩
def record : Record Nat Nat Nat Nat Nat Nat Nat Nat Nat := ⟨reference, decision, 31⟩

abbrev Incarnation := ForeignCapabilityLightcone.Handle Nat Nat
def incarnationReference : Reference Nat Incarnation Nat Nat :=
  ⟨5, PrincipalIncarnation.Controls.first.1, 23, 29⟩
def incarnationRecord : Record Nat Nat Nat Nat Nat Incarnation Nat Nat Nat :=
  ⟨incarnationReference, decision, 31⟩

theorem owner_reads_historical_origin :
    inspect 5 999 true reference (some record) = some record.observe := by
  exact inspect_owner 999 record

theorem originating_account_reads_historical_origin :
    inspect 5 17 false reference (some record) = some record.observe := by
  exact inspect_originating_account record

theorem another_account_cannot_read_origin :
    inspect 5 18 false reference (some record) = none := by
  exact inspect_other_account_refused 18 record (by decide)

theorem changed_nonce_is_not_the_origin :
    inspect 5 17 false { reference with nonce := 30 } (some record) = none := by
  exact inspect_forged_reference_refused 17 false { reference with nonce := 30 } record (by decide)

theorem rotated_same_account_cannot_read_prior_origin :
    inspect 5 PrincipalIncarnation.Controls.second.1 false incarnationReference
      (some incarnationRecord) = none := by
  have different : PrincipalIncarnation.Controls.second.1 ≠
      PrincipalIncarnation.Controls.first.1 :=
    Ne.symm PrincipalIncarnation.Controls.account_value_alone_is_unchanged.2
  simpa [incarnationRecord, incarnationReference] using
    (inspect_other_account_refused PrincipalIncarnation.Controls.second.1
      incarnationRecord different)

theorem owner_still_reads_prior_incarnation_origin :
    inspect 5 PrincipalIncarnation.Controls.second.1 true incarnationReference
      (some incarnationRecord) = some incarnationRecord.observe := by
  exact inspect_owner PrincipalIncarnation.Controls.second.1 incarnationRecord

end Controls

#print axioms inspect_missing
#print axioms observe_reply_irrelevant
#print axioms inspect_owner
#print axioms inspect_originating_account
#print axioms inspect_other_account_refused
#print axioms inspect_forged_reference_refused
#print axioms retired_reply_unknown_and_origin_preserved
#print axioms stale_generation_refused_and_origin_preserved
#print axioms Controls.owner_reads_historical_origin
#print axioms Controls.originating_account_reads_historical_origin
#print axioms Controls.another_account_cannot_read_origin
#print axioms Controls.changed_nonce_is_not_the_origin
#print axioms Controls.rotated_same_account_cannot_read_prior_origin
#print axioms Controls.owner_still_reads_prior_incarnation_origin

end AccountOrigin

end CheckedDecision

/-- Programmable publication keeps current-authority refusal, dependency
conflict and accepted commitment distinct.  Both retry cases return the exact
invocation and ordered native poll history.  A committed result omits the
invocation from this interface; external delivery and crash recovery are later
services over the committed state, not part of this transition. -/
inductive Invocation.PublicationResult (base : Base) where
  | authorityRefused (reason : Denied)
      (held : Invocation (Key := Key) (Value := Value)
        source gate profiles replay invoice reader notice base)
      (history : NativePoll.History)
  | dependencyConflict
      (held : Invocation (Key := Key) (Value := Value)
        source gate profiles replay invoice reader notice base)
      (history : NativePoll.History)
  | committed (next : Key → Value) (history : NativePoll.History)

/-- Invoke the later delivery handler only from a committed publication.
Authority refusal and dependency conflict cannot send.  The committed store is
not revalidated here: durable delivery and its receipt policy are a separate
service boundary. -/
def Invocation.PublicationResult.deliver
    {DeliveryKey Payload : Type} [DecidableEq DeliveryKey] [DecidableEq Payload]
    {base : Base}
    (publication : Invocation.PublicationResult (Key := Key) (Value := Value)
      (source := source) (gate := gate) (profiles := profiles) (replay := replay)
      (invoice := invoice) (reader := reader) (notice := notice) base)
    (policy : DeliveryRecovery.Policy) (acknowledged : Bool)
    (state : DeliveryRecovery.State DeliveryKey Payload)
    (receipt : NativePoll.Receipt) (key : DeliveryKey) (payload : Payload) :
    Option (DeliveryRecovery.Result DeliveryKey Payload) :=
  match publication with
  | .committed _ history =>
      some (DeliveryRecovery.attempt policy acknowledged state history receipt key payload)
  | .authorityRefused _ _ _ | .dependencyConflict _ _ => none

/-- Recheck current world-indexed authority, then use the existing validated
commit.  No application or policy callback occurs between those model
boundaries.  The ordered poll history is transported unchanged rather than
reconstructed from aggregate counters. -/
def Invocation.publishCurrent
    [DecidableEq Key] [DecidableEq Value]
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld] {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (_ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (history : NativePoll.History)
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [Decidable (FrameUpdate point.authority required)] (denied : Denied)
    (current : Key → Value) :
    Invocation.PublicationResult (Key := Key) (Value := Value)
      (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) base :=
  if FrameUpdate point.authority required then
    match ValidatedCommit.commit current
      (ValidatedCommit.propose held.submission.1 held.submission.2) with
    | none => .dependencyConflict held history
    | some next => .committed next history
  else .authorityRefused denied held history

/-- Recheck the exact generation-bearing grant before the existing current
world authority and dependency checks.  A stale handle returns the same retry
residual and history; a matching handle delegates to `publishCurrent`. -/
def Invocation.publishCheckedGrant
    [DecidableEq Key] [DecidableEq Value]
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {Provider Resource : Type} [DecidableEq Provider] [DecidableEq Resource]
    {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (history : NativePoll.History)
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (currentHandle : Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone.Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)] (denied : Denied)
    (current : Key → Value) :
    Invocation.PublicationResult (Key := Key) (Value := Value)
      (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) base :=
  if requirement.handle = currentHandle then
    held.publishCurrent source gate profiles replay invoice reader notice writes ready history
      authority point requirement.required denied current
  else .authorityRefused denied held history

theorem Invocation.publishCheckedGrant_stale
    [DecidableEq Key] [DecidableEq Value]
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {Provider Resource : Type} [DecidableEq Provider] [DecidableEq Resource]
    {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (history : NativePoll.History)
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (currentHandle : Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone.Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)] (denied : Denied)
    (current : Key → Value) (stale : requirement.handle ≠ currentHandle) :
    held.publishCheckedGrant source gate profiles replay invoice reader notice writes ready history
      authority point requirement currentHandle denied current =
        .authorityRefused denied held history := by
  simp [Invocation.publishCheckedGrant, stale]

theorem Invocation.publishCheckedGrant_current
    [DecidableEq Key] [DecidableEq Value]
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {Provider Resource : Type} [DecidableEq Provider] [DecidableEq Resource]
    {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (history : NativePoll.History)
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (currentHandle : Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone.Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)] (denied : Denied)
    (current : Key → Value) (same : requirement.handle = currentHandle) :
    held.publishCheckedGrant source gate profiles replay invoice reader notice writes ready history
      authority point requirement currentHandle denied current =
    held.publishCurrent source gate profiles replay invoice reader notice writes ready history
      authority point requirement.required denied current := by
  simp [Invocation.publishCheckedGrant, same]

theorem Invocation.publishCurrent_authorityRefused
    [DecidableEq Key] [DecidableEq Value]
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld] {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (history : NativePoll.History)
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [Decidable (FrameUpdate point.authority required)] (denied : Denied)
    (current : Key → Value) (refused : ¬ FrameUpdate point.authority required) :
    held.publishCurrent source gate profiles replay invoice reader notice writes ready history
      authority point required denied current =
        .authorityRefused denied held history := by
  simp [Invocation.publishCurrent, refused]

theorem Invocation.publishCurrent_dependencyConflict
    [DecidableEq Key] [DecidableEq Value]
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld] {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (history : NativePoll.History)
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [Decidable (FrameUpdate point.authority required)] (denied : Denied)
    (current : Key → Value) (permitted : FrameUpdate point.authority required)
    (changed : ¬ ReadOnlyQuery.Agrees current held.reads) :
    held.publishCurrent source gate profiles replay invoice reader notice writes ready history
      authority point required denied current = .dependencyConflict held history := by
  have commitRefused : ValidatedCommit.commit current
      (ValidatedCommit.propose held.submission.1 held.submission.2) = none :=
    (ValidatedCommit.commit_refused_iff held.submission.1 current held.submission.2).2 changed
  simp [Invocation.publishCurrent, permitted, commitRefused]

/-- Accepted current-authority publication is the independently rerun current
transaction, and its terminal value realizes those writes.  Ordered poll
history coverage is preserved as a separately stated native premise. -/
theorem Invocation.publishCurrent_fresh
    [DecidableEq Key] [DecidableEq Value]
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld] {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (history : NativePoll.History)
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [Decidable (FrameUpdate point.authority required)] (denied : Denied)
    (current next : Key → Value)
    (accepted : held.publishCurrent source gate profiles replay invoice reader notice writes ready history
      authority point required denied current = .committed next history) :
    FrameUpdate point.authority required ∧
      next = ValidatedCommit.write current
        (ReadOnlyQuery.run current held.submission.2).answer ∧
      ∃ index : Index base, ∃ value : Return base index,
        ∃ state : source.State base index × Account,
          held.outcome = Cursor.Outcome.done ⟨index, .inl value, state⟩ ∧
            writes value = (ReadOnlyQuery.run current held.submission.2).answer := by
  unfold Invocation.publishCurrent at accepted
  split at accepted
  · rename_i permitted
    cases committed : ValidatedCommit.commit current
        (ValidatedCommit.propose held.submission.1 held.submission.2) with
    | none =>
        rw [committed] at accepted
        cases accepted
    | some actual =>
        rw [committed] at accepted
        cases accepted
        have fresh := ValidatedCommit.commit_fresh held.submission.1 current held.submission.2 next committed
        have valid : ReadOnlyQuery.checkReads current
            (ReadOnlyQuery.run held.submission.1 held.submission.2).reads = true := by
          unfold ValidatedCommit.commit ValidatedCommit.propose at committed
          split at committed
          · assumption
          · contradiction
        have sameAnswer := ReadOnlyQuery.validated_answer held.submission.1 current
          held.submission.2 valid
        obtain ⟨index, value, state, terminal, realizes⟩ := ready
        exact ⟨permitted, fresh, index, value, state, terminal,
          realizes.trans sameAnswer.symm⟩
  · cases accepted

/-- Accepted generation-checked publication carries both the exact current
grant identity and all existing current-authority/fresh-commit conclusions. -/
theorem Invocation.publishCheckedGrant_fresh
    [DecidableEq Key] [DecidableEq Value]
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {Provider Resource : Type} [DecidableEq Provider] [DecidableEq Resource]
    {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (history : NativePoll.History)
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (currentHandle : Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone.Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)] (denied : Denied)
    (current next : Key → Value)
    (accepted : held.publishCheckedGrant source gate profiles replay invoice reader notice
      writes ready history authority point requirement currentHandle denied current =
        .committed next history) :
    requirement.handle = currentHandle ∧
      FrameUpdate point.authority requirement.required ∧
      next = ValidatedCommit.write current
        (ReadOnlyQuery.run current held.submission.2).answer ∧
      ∃ index : Index base, ∃ value : Return base index,
        ∃ state : source.State base index × Account,
          held.outcome = Cursor.Outcome.done ⟨index, .inl value, state⟩ ∧
            writes value = (ReadOnlyQuery.run current held.submission.2).answer := by
  unfold Invocation.publishCheckedGrant at accepted
  split at accepted
  · rename_i same
    exact ⟨same, Invocation.publishCurrent_fresh source gate profiles replay invoice reader notice
      writes held ready history authority point requirement.required denied current next accepted⟩
  · cases accepted


/-- Publish a genuinely ready invocation.  Authority refusal and dependency
refusal remain different branches.  The invocation itself is immutable and
can be retained by the caller on either refusal. -/
def Invocation.publish
    [DecidableEq Key] [DecidableEq Value]
    {Authority : Type} {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (_ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (permission : Authority → Except Denied Unit) (currentAuthority : Authority)
    (current : Key → Value) :
    Except Denied (Option (Key → Value)) :=
  match permission currentAuthority with
  | .error reason => .error reason
  | .ok _ => .ok (ValidatedCommit.commit current
      (ValidatedCommit.propose held.submission.1 held.submission.2))

theorem Invocation.publish_denied
    [DecidableEq Key] [DecidableEq Value]
    {Authority : Type} {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (permission : Authority → Except Denied Unit) (currentAuthority : Authority)
    (reason : Denied) (denied : permission currentAuthority = .error reason)
    (current : Key → Value) :
    Invocation.publish (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice)
      writes held ready permission currentAuthority current = Except.error reason := by
  simp [Invocation.publish, denied]

/-- A permitted publication is refused exactly when a dependency in the
retained source submission has changed. -/
theorem Invocation.publish_refused_iff
    [DecidableEq Key] [DecidableEq Value]
    {Authority : Type} {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (permission : Authority → Except Denied Unit) (currentAuthority : Authority)
    (permitted : permission currentAuthority = .ok ()) (current : Key → Value) :
    Invocation.publish (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice)
      writes held ready permission currentAuthority current = Except.ok none ↔
      ¬ ReadOnlyQuery.Agrees current held.reads := by
  simp only [Invocation.publish, permitted, Invocation.reads, Except.ok.injEq]
  exact ValidatedCommit.commit_refused_iff held.submission.1 current held.submission.2

/-- Accepted publication equals running the retained transaction afresh on
the store at the commit boundary. -/
theorem Invocation.publish_fresh
    [DecidableEq Key] [DecidableEq Value]
    {Authority : Type} {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice) writes held)
    (permission : Authority → Except Denied Unit) (currentAuthority : Authority)
    (current next : Key → Value)
    (accepted : Invocation.publish (source := source) (gate := gate) (profiles := profiles)
      (replay := replay) (invoice := invoice) (reader := reader) (notice := notice)
      writes held ready permission currentAuthority current = Except.ok (some next)) :
    next = ValidatedCommit.write current
        (ReadOnlyQuery.run current held.submission.2).answer ∧
      ∃ index : Index base, ∃ value : Return base index,
        ∃ state : source.State base index × Account,
          held.outcome = Cursor.Outcome.done ⟨index, .inl value, state⟩ ∧
            writes value = (ReadOnlyQuery.run current held.submission.2).answer := by
  cases checked : permission currentAuthority with
  | error reason => simp [Invocation.publish, checked] at accepted
  | ok unitValue =>
    cases unitValue
    simp only [Invocation.publish, checked] at accepted
    have committed := Except.ok.inj accepted
    have fresh := ValidatedCommit.commit_fresh held.submission.1 current held.submission.2 next committed
    have valid : ReadOnlyQuery.checkReads current
        (ReadOnlyQuery.run held.submission.1 held.submission.2).reads = true := by
      unfold ValidatedCommit.commit ValidatedCommit.propose at committed
      split at committed
      · assumption
      · contradiction
    have sameAnswer := ReadOnlyQuery.validated_answer held.submission.1 current held.submission.2 valid
    obtain ⟨index, value, state, terminal, realizes⟩ := ready
    exact ⟨fresh, index, value, state, terminal, realizes.trans sameAnswer.symm⟩

/-- Batches of retained submissions inherit the existing serializability
theorem.  Authority admission remains a separate current-world premise used to
select the submitted invocations; this theorem concerns their dependency-
validated commit order. -/
theorem Invocation.commitAll_serial {base : Base} (store : Key → Value)
    [DecidableEq Key] [DecidableEq Value]
    (held : List (Invocation (Key := Key) (Value := Value)
      source gate profiles replay invoice reader notice base)) :
    let submissions := held.map Invocation.submission
    (ValidatedCommit.commitAll store submissions).1 =
      ValidatedCommit.serial store (ValidatedCommit.commitAll store submissions).2 :=
  ValidatedCommit.commitAll_serial store (held.map Invocation.submission)

/-! ### Substitution of a realized indexed handler

The local representation map below reuses `Cursor.Hom`.  Its additional laws
concern the four inputs to admission at each actual request, rather than
assuming equivalence of complete executions.  Exact invoice equality retains
event identities and order.  It concerns the declared semantic account;
different physical implementations need not have equal instruction counts or
elapsed costs.

The lift constructs the homomorphism of the decorated providers.  Bounded
execution and retained resumption then use the generic cursor theorems, with
no second runner or invocation semantics. -/

structure HandlerHom (source target : Cursor.Provider P)
    (sourceGate : Gate (Denied := Denied) source)
    (targetGate : Gate (Denied := Denied) target)
    (sourceProfiles targetProfiles :
      {base : Base} → {index : Index base} → P.Shape base index → Profile)
    (sourceReplay targetReplay :
      {base : Base} → {index : Index base} → P.Shape base index → Bool)
    (sourceInvoice : Invoice source) (targetInvoice : Invoice target) where
  representation : Cursor.Hom source target
  gate_eq : ∀ {base index} (state : source.State base index) (request : P.Shape base index),
    sourceGate state request = targetGate (representation.map state) request
  profiles_eq : ∀ {base index} (request : P.Shape base index),
    sourceProfiles request = targetProfiles request
  replay_eq : ∀ {base index} (request : P.Shape base index),
    sourceReplay request = targetReplay request
  invoice_eq : ∀ {base index} (state : source.State base index) (request : P.Shape base index),
    sourceInvoice state request = targetInvoice (representation.map state) request

namespace HandlerHom

variable {source target : Cursor.Provider P}
  {sourceGate : Gate (Denied := Denied) source}
  {targetGate : Gate (Denied := Denied) target}
  {sourceProfiles targetProfiles :
    {base : Base} → {index : Index base} → P.Shape base index → Profile}
  {sourceReplay targetReplay :
    {base : Base} → {index : Index base} → P.Shape base index → Bool}
  {sourceInvoice : Invoice source} {targetInvoice : Invoice target}
  (h : HandlerHom source target sourceGate targetGate sourceProfiles targetProfiles
    sourceReplay targetReplay sourceInvoice targetInvoice)

theorem admit_eq {base : Base} {index : Index base}
    (state : source.State base index) (request : P.Shape base index) (account : Account) :
    admit source sourceGate sourceProfiles sourceReplay sourceInvoice state request account =
      admit target targetGate targetProfiles targetReplay targetInvoice
        (h.representation.map state) request account := by
  dsimp only [admit]
  rw [h.gate_eq, h.profiles_eq, h.replay_eq, h.invoice_eq]

/-- The original step law and request-level admission laws construct a real
homomorphism after authority, replay and account decoration.  Refusal maps the
unchanged private state; an accepted reply maps its actual successor. -/
def lift : Cursor.Hom
    (provider source sourceGate sourceProfiles sourceReplay sourceInvoice)
    (provider target targetGate targetProfiles targetReplay targetInvoice) where
  map state := (h.representation.map state.1, state.2)
  step state request := by
    dsimp only [provider]
    rw [← h.admit_eq]
    cases admitted : admit source sourceGate sourceProfiles sourceReplay sourceInvoice
        state.1 request state.2 with
    | error reason => rfl
    | ok account =>
        rw [← h.representation.step state.1 request]

theorem charge_eq {base : Base} {index : Index base}
    (state : source.State base index × Account) (request : P.Shape base index) :
    charge source sourceGate sourceProfiles sourceReplay sourceInvoice state request =
      charge target targetGate targetProfiles targetReplay targetInvoice (h.lift.map state) request := by
  dsimp only [charge, lift]
  rw [← h.admit_eq, h.invoice_eq]

variable (reader : Cursor.Client (P := P) (Return := Return)) (notice : Notice P Denied)

def mapOutcome {base : Base}
    (outcome : Outcome source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base) :
    Outcome target targetGate targetProfiles targetReplay targetInvoice reader notice base :=
  h.lift.outcome (client reader notice) outcome

theorem mapOutcome_account {base : Base}
    (outcome : Outcome source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base) :
    accountOf target targetGate targetProfiles targetReplay targetInvoice reader notice
      (h.mapOutcome reader notice outcome) =
        accountOf source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice outcome := by
  cases outcome with
  | paused packet => rcases packet with ⟨index, control, state⟩; rfl
  | done result => rcases result with ⟨index, value, state⟩; rfl

/-- Rearming transports only the refusal notice.  The retained reply-selected
continuation and its already paid account are the same on both sides. -/
theorem mapOutcome_retry {base : Base}
    (outcome : Outcome source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base) :
    h.mapOutcome reader notice
      (retry source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice outcome) =
        retry target targetGate targetProfiles targetReplay targetInvoice reader notice
          (h.mapOutcome reader notice outcome) := by
  cases outcome with
  | paused packet => rcases packet with ⟨index, control, state⟩; rfl
  | done result => rcases result with ⟨index, value, state⟩; cases value <;> rfl

theorem run (fuel : Nat) {base : Base}
    (packet : Cursor.Packet
      (provider source sourceGate sourceProfiles sourceReplay sourceInvoice)
      (client (Denied := Denied) reader notice) base) :
    ((Indexed.run source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice fuel packet).1,
      h.mapOutcome reader notice
        (Indexed.run source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice fuel packet).2) =
      Indexed.run target targetGate targetProfiles targetReplay targetInvoice reader notice fuel
        (h.lift.packet (client reader notice) packet) :=
  h.lift.advance_account (client reader notice)
    (charge source sourceGate sourceProfiles sourceReplay sourceInvoice)
    (charge target targetGate targetProfiles targetReplay targetInvoice)
    h.charge_eq fuel packet

theorem resume (fuel : Nat) {base : Base}
    (previous : Nat × Outcome source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base) :
    ((Indexed.resume source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice fuel previous).1,
      h.mapOutcome reader notice
        (Indexed.resume source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice fuel previous).2) =
      Indexed.resume target targetGate targetProfiles targetReplay targetInvoice reader notice fuel
        (previous.1, h.mapOutcome reader notice previous.2) :=
  h.lift.resume_account (client reader notice)
    (charge source sourceGate sourceProfiles sourceReplay sourceInvoice)
    (charge target targetGate targetProfiles targetReplay targetInvoice)
    h.charge_eq fuel previous

/-- Replacing the current permission test requires a new local agreement law;
the old permission is not retained as authority inside the mapped state. -/
def withGates (nextSource : Gate (Denied := Denied) source)
    (nextTarget : Gate (Denied := Denied) target)
    (agrees : ∀ {base index} (state : source.State base index) (request : P.Shape base index),
      nextSource state request = nextTarget (h.representation.map state) request) :
    HandlerHom source target nextSource nextTarget sourceProfiles targetProfiles
      sourceReplay targetReplay sourceInvoice targetInvoice where
  representation := h.representation
  gate_eq := agrees
  profiles_eq := h.profiles_eq
  replay_eq := h.replay_eq
  invoice_eq := h.invoice_eq

theorem mapOutcome_replaceGate (nextSource : Gate (Denied := Denied) source)
    (nextTarget : Gate (Denied := Denied) target)
    (agrees : ∀ {base index} (state : source.State base index) (request : P.Shape base index),
      nextSource state request = nextTarget (h.representation.map state) request)
    {base : Base}
    (previous : Outcome source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base) :
    (h.withGates nextSource nextTarget agrees).mapOutcome reader notice
      (replaceGate source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice nextSource previous) =
      replaceGate target targetGate targetProfiles targetReplay targetInvoice reader notice nextTarget
        (h.mapOutcome reader notice previous) := by
  cases previous with
  | paused packet => rcases packet with ⟨index, control, state⟩; rfl
  | done result => rcases result with ⟨index, value, state⟩; rfl

/-- Local handler substitutions compose through the actual intermediate
representation.  The composed decorator still checks the current target gate
and retains exactly the source's ordered semantic invoice. -/
def comp {third : Cursor.Provider P}
    {thirdGate : Gate (Denied := Denied) third}
    {thirdProfiles : {base : Base} → {index : Index base} → P.Shape base index → Profile}
    {thirdReplay : {base : Base} → {index : Index base} → P.Shape base index → Bool}
    {thirdInvoice : Invoice third}
    (next : HandlerHom target third targetGate thirdGate targetProfiles thirdProfiles
      targetReplay thirdReplay targetInvoice thirdInvoice) :
    HandlerHom source third sourceGate thirdGate sourceProfiles thirdProfiles
      sourceReplay thirdReplay sourceInvoice thirdInvoice where
  representation := h.representation.comp next.representation
  gate_eq state request := (h.gate_eq state request).trans (next.gate_eq _ request)
  profiles_eq request := (h.profiles_eq request).trans (next.profiles_eq request)
  replay_eq request := (h.replay_eq request).trans (next.replay_eq request)
  invoice_eq state request := (h.invoice_eq state request).trans (next.invoice_eq _ request)

theorem lift_comp {third : Cursor.Provider P}
    {thirdGate : Gate (Denied := Denied) third}
    {thirdProfiles : {base : Base} → {index : Index base} → P.Shape base index → Profile}
    {thirdReplay : {base : Base} → {index : Index base} → P.Shape base index → Bool}
    {thirdInvoice : Invoice third}
    (next : HandlerHom target third targetGate thirdGate targetProfiles thirdProfiles
      targetReplay thirdReplay targetInvoice thirdInvoice) :
    (h.comp next).lift = h.lift.comp next.lift := rfl

/-- Transport the existing invocation without re-running its submission,
prefix, or transaction.  Only the provider's private representation changes. -/
def invocation {Key Value : Type} {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base) :
    Invocation (Key := Key) (Value := Value)
      target targetGate targetProfiles targetReplay targetInvoice reader notice base where
  submission := held.submission
  spent := held.spent
  outcome := h.mapOutcome reader notice held.outcome

@[simp] theorem invocation_submission {Key Value : Type} {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base) :
    (h.invocation reader notice held).submission = held.submission := rfl

@[simp] theorem invocation_reads {Key Value : Type} {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base) :
    (h.invocation reader notice held).reads = held.reads := rfl

@[simp] theorem invocation_spent {Key Value : Type} {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base) :
    (h.invocation reader notice held).spent = held.spent := rfl

theorem invocation_account {Key Value : Type} {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base) :
    (h.invocation reader notice held).account = held.account :=
  h.mapOutcome_account reader notice held.outcome

theorem invocation_history_iff {Key Value : Type} {base : Base}
    (held : Invocation (Key := Key) (Value := Value)
      source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base)
    (history : NativePoll.History) :
    Invocation.PollHistoryCovers (source := target) (gate := targetGate) (profiles := targetProfiles)
      (replay := targetReplay) (invoice := targetInvoice) (reader := reader) (notice := notice)
      (h.invocation reader notice held) history ↔
    Invocation.PollHistoryCovers (source := source) (gate := sourceGate) (profiles := sourceProfiles)
      (replay := sourceReplay) (invoice := sourceInvoice) (reader := reader) (notice := notice)
      held history := by
  unfold Invocation.PollHistoryCovers
  rw [h.invocation_account]

/-- Readiness is witnessed by the same actual terminal reply and writes, at
its reply-selected index; it is never inferred merely from a copied payload. -/
theorem invocation_ready {Key Value : Type} {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := sourceGate) (profiles := sourceProfiles)
      (replay := sourceReplay) (invoice := sourceInvoice) (reader := reader) (notice := notice) writes held) :
    Invocation.Ready (source := target) (gate := targetGate) (profiles := targetProfiles)
      (replay := targetReplay) (invoice := targetInvoice) (reader := reader) (notice := notice)
      writes (h.invocation reader notice held) := by
  obtain ⟨index, value, state, terminal, realizes⟩ := ready
  refine ⟨index, value, h.lift.map state, ?_, realizes⟩
  change h.mapOutcome reader notice held.outcome = _
  rw [terminal]
  rfl

/-- Handler replacement and installing current permission commute with actual
retained retry/resumption.  The already paid prefix is transported, not run
again, and the next source and target gates govern all new requests. -/
theorem invocation_resumeWith {Key Value : Type} {base : Base}
    (nextSource : Gate (Denied := Denied) source)
    (nextTarget : Gate (Denied := Denied) target)
    (agrees : ∀ {base index} (state : source.State base index) (request : P.Shape base index),
      nextSource state request = nextTarget (h.representation.map state) request)
    (fuel : Nat)
    (held : Invocation (Key := Key) (Value := Value)
      source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base) :
    (h.withGates nextSource nextTarget agrees).invocation reader notice
      (held.resumeWith source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice nextSource fuel) =
      (h.invocation reader notice held).resumeWith
        target targetGate targetProfiles targetReplay targetInvoice reader notice nextTarget fuel := by
  have transported := (h.withGates nextSource nextTarget agrees).resume reader notice fuel
    (held.spent, retry source nextSource sourceProfiles sourceReplay sourceInvoice reader notice
      (replaceGate source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice
        nextSource held.outcome))
  rw [mapOutcome_retry, h.mapOutcome_replaceGate reader notice nextSource nextTarget agrees] at transported
  exact congrArg
    (fun result : Nat × Outcome target nextTarget targetProfiles targetReplay targetInvoice reader notice base =>
      (⟨held.submission, result.1, result.2⟩ : Invocation (Key := Key) (Value := Value)
        target nextTarget targetProfiles targetReplay targetInvoice reader notice base)) transported

/-- Retry branches retain the transported invocation and exact history;
committed branches retain the same resulting shared store and history. -/
def publication {Key Value : Type} {base : Base} :
    Invocation.PublicationResult (Key := Key) (Value := Value)
      (source := source) (gate := sourceGate) (profiles := sourceProfiles)
      (replay := sourceReplay) (invoice := sourceInvoice) (reader := reader) (notice := notice) base →
    Invocation.PublicationResult (Key := Key) (Value := Value)
      (source := target) (gate := targetGate) (profiles := targetProfiles)
      (replay := targetReplay) (invoice := targetInvoice) (reader := reader) (notice := notice) base
  | .authorityRefused reason held history => .authorityRefused reason (h.invocation reader notice held) history
  | .dependencyConflict held history => .dependencyConflict (h.invocation reader notice held) history
  | .committed next history => .committed next history

/-- A representation substitution preserves the current-authority and
dependency-validation decision, including the complete retained retry branch.
The authority input is supplied now, independently of the phase handler. -/
theorem publishCurrent {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld] {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := sourceGate) (profiles := sourceProfiles)
      (replay := sourceReplay) (invoice := sourceInvoice) (reader := reader) (notice := notice) writes held)
    (history : NativePoll.History)
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority) (required : authority.Fibre point.world)
    [Decidable (FrameUpdate point.authority required)] (denied : Denied)
    (current : Key → Value) :
    h.publication reader notice
      (held.publishCurrent source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice
        writes ready history authority point required denied current) =
      (h.invocation reader notice held).publishCurrent
        target targetGate targetProfiles targetReplay targetInvoice reader notice writes
        (h.invocation_ready reader notice writes held ready) history authority point required denied current := by
  dsimp only [Invocation.publishCurrent, invocation]
  split
  · cases ValidatedCommit.commit current
      (ValidatedCommit.propose held.submission.1 held.submission.2) <;> rfl
  · rfl

/-- The full generation-bearing handle is a current publication input on both
representations.  Substitution cannot revive an earlier grant incarnation. -/
theorem publishCheckedGrant {Key Value : Type} [DecidableEq Key] [DecidableEq Value]
    {AuthorityWorld : Type} [Category.{0} AuthorityWorld]
    {Provider Resource : Type} [DecidableEq Provider] [DecidableEq Resource]
    {base : Base}
    (writes : {index : Index base} → Return base index → ValidatedCommit.Writes Key Value)
    (held : Invocation (Key := Key) (Value := Value)
      source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice base)
    (ready : Invocation.Ready (source := source) (gate := sourceGate) (profiles := sourceProfiles)
      (replay := sourceReplay) (invoice := sourceInvoice) (reader := reader) (notice := notice) writes held)
    (history : NativePoll.History)
    (authority : IndexedAuthority.{0, 0, 0} AuthorityWorld)
    (point : IndexedAuthority.Point authority)
    (requirement : CheckedGrant.Requirement Provider Resource (authority.Fibre point.world))
    (currentHandle : ForeignCapabilityLightcone.Handle Provider Resource)
    [Decidable (FrameUpdate point.authority requirement.required)] (denied : Denied)
    (current : Key → Value) :
    h.publication reader notice
      (held.publishCheckedGrant source sourceGate sourceProfiles sourceReplay sourceInvoice reader notice
        writes ready history authority point requirement currentHandle denied current) =
      (h.invocation reader notice held).publishCheckedGrant
        target targetGate targetProfiles targetReplay targetInvoice reader notice writes
        (h.invocation_ready reader notice writes held ready) history authority point requirement
        currentHandle denied current := by
  dsimp only [Invocation.publishCheckedGrant]
  split
  · exact h.publishCurrent reader notice writes held ready history authority point requirement.required denied current
  · rfl

end HandlerHom

#print axioms HandlerHom.admit_eq
#print axioms HandlerHom.lift
#print axioms HandlerHom.charge_eq
#print axioms HandlerHom.run
#print axioms HandlerHom.resume
#print axioms HandlerHom.mapOutcome_account
#print axioms HandlerHom.mapOutcome_retry
#print axioms HandlerHom.mapOutcome_replaceGate
#print axioms HandlerHom.lift_comp
#print axioms HandlerHom.invocation_account
#print axioms HandlerHom.invocation_history_iff
#print axioms HandlerHom.invocation_ready
#print axioms HandlerHom.invocation_resumeWith
#print axioms HandlerHom.publishCurrent
#print axioms HandlerHom.publishCheckedGrant

#print axioms currentGate_ok_iff
#print axioms step_account
#print axioms advance_account
#print axioms replaceGate_roundtrip
#print axioms replaceGate_preserves_account
#print axioms pre_call_refusal_retains_pending_phase
#print axioms post_reply_refusal_retains_selected_phase
#print axioms run_account
#print axioms run_ledger
#print axioms resume_account
#print axioms Invocation.replaceGate_account
#print axioms Invocation.resumeWith_account
#print axioms CheckedGrant.Requirement.current_iff
#print axioms CheckedGrant.Requirement.not_current_of_generation_ne
#print axioms CheckedDecision.retry_missing
#print axioms CheckedDecision.retry_current
#print axioms CheckedDecision.retry_stale_generation
#print axioms CheckedDecision.retry_authority_refused
#print axioms CheckedDecision.retry_existing_ne_execute
#print axioms CheckedDecision.retry_eq_execute_iff
#print axioms Invocation.publishCheckedGrant_stale
#print axioms Invocation.publishCheckedGrant_current
#print axioms Invocation.publishCheckedGrant_fresh
#print axioms Invocation.publishCurrent_authorityRefused
#print axioms Invocation.publishCurrent_dependencyConflict
#print axioms Invocation.publishCurrent_fresh
#print axioms Invocation.publish_denied
#print axioms Invocation.publish_refused_iff
#print axioms Invocation.publish_fresh
#print axioms Invocation.commitAll_serial

end Mettapedia.GSLT.LanguageDef.OperationCostProtocol.Indexed
