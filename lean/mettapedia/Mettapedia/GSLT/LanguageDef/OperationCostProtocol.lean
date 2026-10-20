import Mettapedia.GSLT.LanguageDef.OperationContracts
import Mettapedia.Machines.NativeCostLedger
import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Machines.ValidatedCommit
import Mettapedia.GSLT.Contracts.IndexedAuthority

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

end Controls

#print axioms run_complete
#print axioms complete_agrees
#print axioms Controls.complete_capture_detects_selected_change
#print axioms Controls.may_read_placement_does_not_capture_a_missing_read

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
#print axioms Invocation.publish_denied
#print axioms Invocation.publish_refused_iff
#print axioms Invocation.publish_fresh
#print axioms Invocation.commitAll_serial

end Mettapedia.GSLT.LanguageDef.OperationCostProtocol.Indexed
