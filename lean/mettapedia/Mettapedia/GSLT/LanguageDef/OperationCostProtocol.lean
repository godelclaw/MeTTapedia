import Mettapedia.GSLT.LanguageDef.OperationContracts
import Mettapedia.Machines.NativeCostLedger
import Mettapedia.Machines.Cursor.Protocol

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
