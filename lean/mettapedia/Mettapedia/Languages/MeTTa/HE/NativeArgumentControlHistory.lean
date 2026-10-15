import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlMachine
import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlEncoding
import Mettapedia.Machines.RevisionDependencySet

/-!
# Ordered reply history and retained phase invariants

An admitted protocol state records strictly increasing consumed serials.
Only its first frame may await a service; that pending serial follows all
consumed serials and precedes the next fresh serial. Independent phase and
reply rules preserve this invariant. This is an ordered control invariant,
not historical-proof validation or native resource ownership. The checked
reply boundary additionally joins the existing issued-return registry and
captured-read validation for profiles which explicitly capture a read view.
It consumes one issued authority only when a reply
fits the complete saved configuration and all consulted dependencies remain
current. Native owner discovery and effect execution remain separate contracts.
Independent issued replies commute at their captured consumer endpoints and
remaining authority when world changes preserve the other consumer's consulted
support. Physical registry order, scan cost and external-effect order are
separate observations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.NativeArgumentControlHistory

open NativeArgumentControl NativeArgumentControlMachine
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def Plain : Frame → Prop
  | .waiting _ _ => False
  | _ => True

def PlainFrames (frames : List Frame) : Prop := ∀ frame ∈ frames, Plain frame

structure HistoryInv (state : Configuration) : Prop where
  ordered : state.replyHistory.Pairwise (· < ·)
  beforeNext : ∀ serial ∈ state.replyHistory, serial < state.nextTicket
  tailPlain : PlainFrames state.frames.tail
  pendingFresh : ∀ service ticket rest, state.frames = .waiting service ticket :: rest →
    ticket < state.nextTicket ∧ ∀ serial ∈ state.replyHistory, serial < ticket

theorem plain_cons (frame : Frame) (first : Plain frame) {rest : List Frame}
    (remaining : PlainFrames rest) : PlainFrames (frame :: rest) := by
  intro other member
  rcases List.mem_cons.mp member with same | later
  · subst other
    exact first
  · exact remaining other later

theorem parent_plain (parent : Parent) : Plain parent.frame := by cases parent <;> trivial

theorem history_empty (frames : List Frame) (plain : PlainFrames frames) (episode : Nat) :
    HistoryInv ⟨frames, [], episode, 0, [], 0⟩ := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · intro frame member
    exact plain frame (List.mem_of_mem_tail member)
  · intro service ticket rest pending
    have head := plain (.waiting service ticket) (by change frames = _ at pending; rw [pending]; simp)
    exact head.elim

theorem rest_plain {state : Configuration} {frame : Frame} {rest : List Frame}
    (admitted : HistoryInv state) (frames : state.frames = frame :: rest) : PlainFrames rest := by
  have plain := admitted.tailPlain
  simpa only [frames, List.tail_cons] using plain

theorem replace_plain {state : Configuration} (admitted : HistoryInv state)
    (frames : List Frame) (plain : PlainFrames frames) : HistoryInv (replace state frames) := by
  refine ⟨admitted.ordered, admitted.beforeNext, ?_, ?_⟩
  · intro frame member
    exact plain frame (List.mem_of_mem_tail member)
  · intro service ticket rest pending
    have equal : frames = .waiting service ticket :: rest := pending
    have head := plain (.waiting service ticket) (by rw [equal]; simp)
    exact head.elim

theorem publish_plain {state : Configuration} (admitted : HistoryInv state)
    (frames : List Frame) (plain : PlainFrames frames) (result : ResultPair) :
    HistoryInv {state with frames := frames, emitted := state.emitted ++ [result]} := by
  have changed : HistoryInv {state with emitted := state.emitted ++ [result]} :=
    ⟨admitted.ordered, admitted.beforeNext, admitted.tailPlain, admitted.pendingFresh⟩
  exact replace_plain changed frames plain

theorem issue_history {state : Configuration} (admitted : HistoryInv state)
    (rest : List Frame) (plain : PlainFrames rest) (service : Waiting) :
    HistoryInv (issue state rest service) := by
  refine ⟨admitted.ordered, ?_, plain, ?_⟩
  · intro serial member
    have below := admitted.beforeNext serial member
    change serial < state.nextTicket + 1
    omega
  · intro other ticket tail pending
    have exactFields : (service = other ∧ state.nextTicket = ticket) ∧ rest = tail := by
      simpa only [issue, List.cons.injEq, Frame.waiting.injEq] using pending
    have equal : ticket = state.nextTicket := exactFields.1.2.symm
    subst ticket
    exact ⟨Nat.lt_succ_self _, admitted.beforeNext⟩

private theorem ordered_append (serials : List Nat) (ticket : Nat)
    (ordered : serials.Pairwise (· < ·)) (later : ∀ serial ∈ serials, serial < ticket) :
    (serials ++ [ticket]).Pairwise (· < ·) := by
  induction serials with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨before, restOrdered⟩ := List.pairwise_cons.mp ordered
    rw [List.cons_append, List.pairwise_cons]
    refine ⟨?_, ih restOrdered (fun serial member => later serial (List.mem_cons_of_mem _ member))⟩
    intro serial member
    rcases List.mem_append.mp member with old | last
    · exact before serial old
    · have same : serial = ticket := by simpa using last
      subst serial
      exact later first (List.mem_cons_self)

inductive ReplyShape (ticket : Nat) : List Frame → Prop where
  | plain (frames) : PlainFrames frames → ReplyShape ticket frames
  | waiting (service) : ReplyShape ticket [.waiting service ticket]

theorem response_shape {service : Waiting} {value : ReplyValue} {events : ResultList} {frames : List Frame}
    (related : ResponseRel service value events frames) (ticket : Nat) :
    ReplyShape ticket (reticket ticket frames) := by
  cases related with
  | error => exact .plain _ (by simp [reticket, PlainFrames])
  | ordinary related =>
    cases related <;> first
      | exact .waiting _
      | (apply ReplyShape.plain; simp [reticket, PlainFrames, Plain])
    case entered child parent =>
      cases parent <;> simp [Parent.frame]
    case cancelled child parent =>
      cases parent <;> simp [Parent.frame]

private theorem received_history {state : Configuration} (admitted : HistoryInv state)
    (service : Waiting) (ticket : Nat) (rest : List Frame)
    (returned : List Frame) (emitted : ResultList) (work : Nat)
    (pending : state.frames = .waiting service ticket :: rest)
    (shape : ReplyShape state.nextTicket returned) :
    HistoryInv ⟨returned ++ rest, emitted, state.episode, state.nextTicket + 1,
      state.replyHistory ++ [ticket], work⟩ := by
  obtain ⟨ticketBefore, fresh⟩ := admitted.pendingFresh service ticket rest pending
  have restPlain := rest_plain admitted pending
  have ordered := ordered_append state.replyHistory ticket admitted.ordered fresh
  have beforeNext : ∀ serial ∈ state.replyHistory ++ [ticket], serial < state.nextTicket + 1 := by
    intro serial member
    rcases List.mem_append.mp member with old | last
    · have below := admitted.beforeNext serial old
      omega
    · have same : serial = ticket := by simpa using last
      omega
  cases shape with
  | plain returned allPlain =>
    have entirelyPlain : PlainFrames (returned ++ rest) := by
      intro frame member
      rcases List.mem_append.mp member with first | last
      · exact allPlain frame first
      · exact restPlain frame last
    refine ⟨ordered, beforeNext, ?_, ?_⟩
    · intro frame member
      exact entirelyPlain frame (List.mem_of_mem_tail member)
    · intro nextService nextTicket nextRest nextPending
      have equal : returned ++ rest = .waiting nextService nextTicket :: nextRest := nextPending
      have impossible : False := entirelyPlain (.waiting nextService nextTicket) (by rw [equal]; simp)
      exact impossible.elim
  | waiting waitingService =>
    refine ⟨ordered, beforeNext, ?_, ?_⟩
    · exact restPlain
    · intro nextService nextTicket nextRest nextPending
      have exactFields : (waitingService = nextService ∧ state.nextTicket = nextTicket) ∧ rest = nextRest := by
        simpa only [List.singleton_append, List.cons.injEq, Frame.waiting.injEq] using nextPending
      rw [← exactFields.1.2]
      refine ⟨Nat.lt_succ_self _, ?_⟩
      intro serial member
      rcases List.mem_append.mp member with old | last
      · exact admitted.beforeNext serial old
      · have same : serial = ticket := by simpa using last
        simpa [same] using ticketBefore

theorem replied_history {state : Configuration} (admitted : HistoryInv state)
    (service : Waiting) (ticket : Nat) (rest : List Frame) (reply : Reply)
    (events : ResultList) (frames : List Frame)
    (pending : state.frames = .waiting service ticket :: rest)
    (shape : ReplyShape state.nextTicket (reticket state.nextTicket frames)) :
    HistoryInv (replied {state with emitted := state.emitted ++ events} rest reply frames) := by
  have consumedTicket : pendingTicket {state with emitted := state.emitted ++ events} = ticket := by
    simp [pendingTicket, pending]
  simpa only [replied, consumedTicket] using received_history admitted service ticket rest
    (reticket state.nextTicket frames) (state.emitted ++ events) (state.externalWork + reply.charge) pending shape

theorem delivery_preserves_history {state after : Configuration} {reply : Reply}
    (admitted : HistoryInv state) (accepted : deliver state reply = .accepted after) : HistoryInv after := by
  cases (deliver_iff _ _ _).mp accepted with
  | accepted service ticket rest events frames pending endpoint body =>
    exact replied_history admitted service ticket rest reply events frames pending (response_shape body _)

def RetainsHistory (transition : Advance) : Prop :=
  match transition with
  | .silent state | .publish _ state | .finish state | .call _ state => HistoryInv state
  | .fail _ => True

theorem advance_preserves_history (operations : Operations) (state : Configuration) (transition : Advance)
    (admitted : HistoryInv state) (related : AdvanceRel operations state transition) : RetainsHistory transition := by
  cases related
  case finished => exact admitted
  case invalid => trivial
  case completed arguments rest frames valid completed =>
    exact publish_plain admitted rest (rest_plain admitted frames) _
  case preparation arguments rest frames valid incomplete =>
    exact issue_history admitted rest (rest_plain admitted frames) _
  case transformed arguments prepared rest frames raw transform =>
    exact issue_history admitted rest (rest_plain admitted frames) _
  case raw arguments prepared rest frames raw transform =>
    exact replace_plain admitted _ (plain_cons _ (by trivial) (rest_plain admitted frames))
  case evaluation arguments prepared rest frames notRaw =>
    exact issue_history admitted rest (rest_plain admitted frames) _
  case rawFailed arguments prepared value rest frames failed =>
    exact replace_plain admitted _ (rest_plain admitted frames)
  case rawChild arguments prepared value rest bindings frames extended =>
    exact issue_history admitted rest (rest_plain admitted frames) _
  case consume snapshot prepared rest action frames related =>
    cases related
    case exhausted => exact replace_plain admitted _ (rest_plain admitted frames)
    case mergeFailed => exact replace_plain admitted _ (plain_cons _ (by trivial) (rest_plain admitted frames))
    case error => exact publish_plain admitted _ (plain_cons _ (by trivial) (rest_plain admitted frames)) _
    case binderFailed => exact replace_plain admitted _ (plain_cons _ (by trivial) (rest_plain admitted frames))
    case selected => exact issue_history admitted rest (rest_plain admitted frames) _
  case returned snapshot prepared rest saved frames returned =>
    exact replace_plain admitted _ (plain_cons _ (by trivial) (rest_plain admitted frames))
  case invalidReturn => trivial
  case onlyReturned arguments prepared value bindings rest frames =>
    exact replace_plain admitted _ (rest_plain admitted frames)
  case awaiting => exact admitted

theorem inspect_preserves_history (operations : Operations) (state : Configuration)
    (admitted : HistoryInv state) : RetainsHistory (inspect operations state) :=
  advance_preserves_history operations state _ admitted (inspect_sound operations state)

theorem consumed_serial_cannot_be_pending {state : Configuration}
    (admitted : HistoryInv state) (service : Waiting) (ticket : Nat) (rest : List Frame)
    (pending : state.frames = .waiting service ticket :: rest) : ticket ∉ state.replyHistory := by
  intro consumed
  have before := (admitted.pendingFresh service ticket rest pending).2 ticket consumed
  omega

/-! ## Issued reply authority and captured-world validation -/

namespace OwnedReplyBoundary

open Mettapedia.Machines
open Mettapedia.Machines.Cursor.OwnedLifecycle
open NativeArgumentControlEncoding

variable {Key Revision : Type} [DecidableEq Key] [DecidableEq Revision]

/-- The existing captured-read frame carries the complete retained controller. -/
abbrev Capture (Key Revision : Type) := CapturedReadFrame Nat Key Revision Configuration

abbrev Registry := IssuedReturn.Registry Mettapedia.Languages.MeTTa.OSLFCore.Atom Nat
abbrev Handle := IssuedReturn.Handle Mettapedia.Languages.MeTTa.OSLFCore.Atom Nat

/-- Parent lineage, provider identity and exact retained payload are distinct
checks. Registry membership alone does not authenticate a parent. -/
def Matches (capture : Capture Key Revision) (handle : Handle) : Prop :=
  handle.parent = capture.capture.episode ∧
    handle.row.provider = capture.source ∧
    handle.row.payload = configurationData capture.capture

instance (capture : Capture Key Revision) (handle : Handle) : Decidable (Matches capture handle) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

inductive Refusal where
  | ownerMismatch
  | staleDependencies
  | unissued
  | protocol (reason : Rejection)
  deriving Repr, DecidableEq

/-- A refused attempt has no new controller or registry to publish. Validation
still returns its sticky read view and authentication its actual visited cost. -/
abbrev Result (Key Revision : Type) :=
  Except Refusal (Configuration × Registry) × CapturedReadView Key Revision × Nat

def deliverChecked (registry : Registry) (live : RevisionEnvironment Key Revision)
    (capture : Capture Key Revision) (handle : Handle) (reply : Reply) : Result Key Revision :=
  let checked := capture.view.validate live
  if Matches capture handle then
    if checked.accepted then
      let released := IssuedReturn.releaseIssued registry handle
      match released.1 with
      | none => (.error .unissued, checked, released.2)
      | some (next, _) =>
        match deliver capture.capture reply with
        | .rejected reason => (.error (.protocol reason), checked, released.2)
        | .accepted after => (.ok (after, next), checked, released.2)
    else (.error .staleDependencies, checked, 0)
  else (.error .ownerMismatch, checked, 0)

/-- Executable admission agrees with independent controller reply rules,
captured dependency validity, and exact physical release of the issued row. -/
theorem deliverChecked_iff (registry : Registry) (live : RevisionEnvironment Key Revision)
    (capture : Capture Key Revision) (handle : Handle) (reply : Reply)
    (after : Configuration) (next : Registry) :
    (deliverChecked registry live capture handle reply).1 = .ok (after, next) ↔
      Matches capture handle ∧ capture.view.CanPublish live ∧
      DeliveryRel capture.capture reply after ∧
      ∃ cleared, (IssuedReturn.releaseIssued registry handle).1 = some (next, cleared) := by
  rw [← CapturedReadView.validate_accepted_iff_canPublish,
    ← deliver_iff]
  by_cases fits : Matches capture handle
  · cases current : (capture.view.validate live).accepted with
    | false => simp [deliverChecked, fits, current]
    | true =>
      cases released : (IssuedReturn.releaseIssued registry handle).1 with
      | none => simp [deliverChecked, fits, current, released]
      | some pair =>
        obtain ⟨remaining, cleared⟩ := pair
        cases delivered : deliver capture.capture reply with
        | rejected reason => simp [deliverChecked, fits, current, released, delivered]
        | accepted returned =>
          simp [deliverChecked, fits, current, released, delivered,
            and_comm]
  · simp [deliverChecked, fits]

/-- Successful delivery exists exactly under these three independent contracts.
The release algorithm constructs its residual registry; no release witness is
assumed by this admission theorem. -/
theorem accepts_iff (registry : Registry) (live : RevisionEnvironment Key Revision)
    (capture : Capture Key Revision) (handle : Handle) (reply : Reply) :
    (∃ after next, (deliverChecked registry live capture handle reply).1 = .ok (after, next)) ↔
      Matches capture handle ∧ capture.view.CanPublish live ∧
      IssuedReturn.Authenticated registry handle ∧
      ∃ after, DeliveryRel capture.capture reply after := by
  constructor
  · rintro ⟨after, next, admitted⟩
    obtain ⟨fits, current, body, cleared, released⟩ := (deliverChecked_iff _ _ _ _ _ _ _).mp admitted
    exact ⟨fits, current,
      (IssuedReturn.releaseIssued_exists_iff registry handle).mp ⟨next, cleared, released⟩,
      after, body⟩
  · rintro ⟨fits, current, authorized, after, body⟩
    obtain ⟨next, cleared, released⟩ :=
      (IssuedReturn.releaseIssued_exists_iff registry handle).mpr authorized
    exact ⟨after, next, (deliverChecked_iff _ _ _ _ _ _ _).mpr
      ⟨fits, current, body, cleared, released⟩⟩

omit [DecidableEq Key] in
theorem retains_validation (registry : Registry) (live : RevisionEnvironment Key Revision)
    (capture : Capture Key Revision) (handle : Handle) (reply : Reply) :
    (deliverChecked registry live capture handle reply).2.1 = capture.view.validate live := by
  by_cases fits : Matches capture handle
  · cases current : (capture.view.validate live).accepted with
    | false => simp [deliverChecked, fits, current]
    | true =>
      cases released : (IssuedReturn.releaseIssued registry handle).1 with
      | none => simp [deliverChecked, fits, current, released]
      | some pair =>
        obtain ⟨next, cleared⟩ := pair
        cases delivered : deliver capture.capture reply <;>
          simp [deliverChecked, fits, current, released, delivered]
  · simp [deliverChecked, fits]

omit [DecidableEq Key] in
/-- Read validation never rebases captured values, including captured absence. -/
theorem retains_captured_world (registry : Registry) (live : RevisionEnvironment Key Revision)
    (capture : Capture Key Revision) (handle : Handle) (reply : Reply) :
    (deliverChecked registry live capture handle reply).2.1.captured = capture.view.captured := by
  rw [retains_validation]
  rfl

/-- Invalidated captured reads refuse before any issued row is consumed. -/
theorem stale_refused (registry : Registry) (live : RevisionEnvironment Key Revision)
    (capture : Capture Key Revision) (handle : Handle) (reply : Reply)
    (fits : Matches capture handle) (stale : ¬ capture.view.CanPublish live) :
    (deliverChecked registry live capture handle reply).1 = .error .staleDependencies := by
  have refused : (capture.view.validate live).accepted = false := by
    apply Bool.eq_false_iff.mpr
    intro accepted
    exact stale ((CapturedReadView.validate_accepted_iff_canPublish capture.view live).mp accepted)
  simp [deliverChecked, fits, refused]

theorem accepted_history {registry next : Registry} {live : RevisionEnvironment Key Revision}
    {capture : Capture Key Revision} {handle : Handle} {reply : Reply} {after : Configuration}
    (history : HistoryInv capture.capture)
    (admitted : (deliverChecked registry live capture handle reply).1 = .ok (after, next)) :
    HistoryInv after :=
  delivery_preserves_history history ((deliver_iff _ _ _).mpr
    ((deliverChecked_iff _ _ _ _ _ _ _).mp admitted).2.2.1)

theorem accepted_prefix_and_accounts {registry next : Registry}
    {live : RevisionEnvironment Key Revision} {capture : Capture Key Revision}
    {handle : Handle} {reply : Reply} {after : Configuration}
    (admitted : (deliverChecked registry live capture handle reply).1 = .ok (after, next)) :
    (∃ added, after.emitted = capture.capture.emitted ++ added) ∧
      after.replyHistory = capture.capture.replyHistory ++ [pendingTicket capture.capture] ∧
      after.externalWork = capture.capture.externalWork + reply.charge := by
  have delivered := (deliver_iff _ _ _).mpr
    ((deliverChecked_iff _ _ _ _ _ _ _).mp admitted).2.2.1
  have accounts := delivery_accounts delivered
  exact ⟨delivery_preserves_emitted_prefix delivered, accounts.2.1, accounts.2.2.1⟩

/-- Consuming an issued row revokes every alias of that handle, including an
unchanged copy of the complete pre-reply configuration. The latest registry
must be shared by attempts; copying it would copy authority as well as data. -/
theorem copied_pending_reply_cannot_be_accepted {registry next : Registry}
    {live : RevisionEnvironment Key Revision} {capture : Capture Key Revision}
    {handle : Handle} {reply : Reply} {after : Configuration}
    (valid : registry.Valid)
    (admitted : (deliverChecked registry live capture handle reply).1 = .ok (after, next))
    (otherLive : RevisionEnvironment Key Revision) (other : Capture Key Revision)
    (second : Reply) (returned : Configuration) (remaining : Registry) :
    (deliverChecked next otherLive other handle second).1 ≠ .ok (returned, remaining) := by
  obtain ⟨_, _, _, cleared, released⟩ := (deliverChecked_iff _ _ _ _ _ _ _).mp admitted
  have retired := IssuedReturn.releaseIssued_revokes_old_and_cleared registry handle next cleared
    (IssuedReturn.releaseIssued registry handle).2 valid (Prod.ext released rfl)
  intro repeated
  have again := (accepts_iff next otherLive other handle second).mp ⟨returned, remaining, repeated⟩
  exact retired.1 again.2.2.1

/-- Different issued occurrences survive this delivery. Equal payloads alone
do not identify them or authorize suppressing a duplicate answer. -/
theorem accepted_keeps_other_authority {registry next : Registry}
    {live : RevisionEnvironment Key Revision} {capture : Capture Key Revision}
    {handle : Handle} {reply : Reply} {after : Configuration}
    (admitted : (deliverChecked registry live capture handle reply).1 = .ok (after, next))
    (other : Handle) (different : other.row ≠ handle.row) :
    IssuedReturn.Authenticated next other ↔ IssuedReturn.Authenticated registry other := by
  obtain ⟨_, _, _, cleared, released⟩ := (deliverChecked_iff _ _ _ _ _ _ _).mp admitted
  exact IssuedReturn.releaseIssued_keeps_other registry handle other next cleared
    (IssuedReturn.releaseIssued registry handle).2 (Prod.ext released rfl) different

/-- Exact accepted controller and registry results depend on the consulted
world support. This does not identify the complete validation receipts of
refused attempts in two worlds. -/
theorem deliverChecked_world_iff (registry : Registry)
    (left right : RevisionEnvironment Key Revision) (capture : Capture Key Revision)
    (handle : Handle) (reply : Reply) (after : Configuration) (next : Registry)
    (agrees : RevisionEnvironment.AgreesOn capture.view.consulted.toFinset left right) :
    (deliverChecked registry left capture handle reply).1 = .ok (after, next) ↔
      (deliverChecked registry right capture handle reply).1 = .ok (after, next) := by
  rw [deliverChecked_iff, deliverChecked_iff,
    CapturedReadView.canPublish_iff_of_agreesOn capture.view left right agrees]

/-- A world edit outside the consulted support changes neither admission nor
the complete reply's independent controller meaning. -/
theorem accepts_unrelated_update_iff (registry : Registry)
    (live : RevisionEnvironment Key Revision) (capture : Capture Key Revision)
    (handle : Handle) (reply : Reply) (key : Key) (value : Revision)
    (outside : key ∉ capture.view.consulted) :
    (∃ after next, (deliverChecked registry (live.update key value) capture handle reply).1 =
        .ok (after, next)) ↔
      ∃ after next, (deliverChecked registry live capture handle reply).1 = .ok (after, next) := by
  rw [accepts_iff, accepts_iff,
    CapturedReadView.canPublish_update_iff_of_not_consulted capture.view live key value outside]

/-- Stateful dependency observations justify admission at their actual final
world. Truthful replies alone are insufficient: every observer must preserve
the entire consulted support, including keys sampled earlier. -/
theorem observed_admission_iff {State : Type} (registry : Registry)
    (capture : Capture Key Revision) (handle : Handle) (reply : Reply)
    (projection : State → RevisionEnvironment Key Revision)
    (observe : Key → State → Revision × State)
    (complete : capture.view.captureComplete = true)
    (unpoisoned : capture.view.firstMismatch = none)
    (truthful : ∀ key ∈ capture.view.consulted.toFinset, ∀ state,
      (observe key state).1 = (projection state).current key)
    (stable : ∀ key ∈ capture.view.consulted.toFinset, ∀ state,
      RevisionEnvironment.AgreesOn capture.view.consulted.toFinset
        (projection (observe key state).2) (projection state)) (state : State) :
    (∃ after next, (deliverChecked registry
      (projection (RevisionEnvironment.checkObserved capture.view.captured observe
        capture.view.consulted state).2) capture handle reply).1 = .ok (after, next)) ↔
      Matches capture handle ∧
      (RevisionEnvironment.checkObserved capture.view.captured observe
        capture.view.consulted state).1 = true ∧
      IssuedReturn.Authenticated registry handle ∧
      ∃ after, DeliveryRel capture.capture reply after := by
  rw [accepts_iff, ← CapturedReadView.checkObserved_canPublish capture.view projection observe
    complete unpoisoned truthful stable state]

/-- Two admitted replies to distinct issued rows can be delivered in either
sequence. Each consumer keeps its own captured configuration and the latest
shared registry. This law concerns admission and endpoints, not scan cost or
effects that change the other's consulted world. -/
theorem independent_reply_survives {registry next : Registry}
    {live : RevisionEnvironment Key Revision} {capture other : Capture Key Revision}
    {handle second : Handle} {reply secondReply : Reply} {after otherAfter : Configuration}
    {otherNext : Registry}
    (firstAccepted : (deliverChecked registry live capture handle reply).1 = .ok (after, next))
    (secondAccepted : (deliverChecked registry live other second secondReply).1 = .ok (otherAfter, otherNext))
    (different : second.row ≠ handle.row) :
    ∃ remaining, (deliverChecked next live other second secondReply).1 = .ok (otherAfter, remaining) := by
  obtain ⟨fits, current, body, cleared, released⟩ :=
    (deliverChecked_iff _ _ _ _ _ _ _).mp secondAccepted
  have original := (IssuedReturn.releaseIssued_exists_iff registry second).mp
    ⟨otherNext, cleared, released⟩
  have retained := (accepted_keeps_other_authority firstAccepted second different).mpr original
  obtain ⟨remaining, cleared, released⟩ :=
    (IssuedReturn.releaseIssued_exists_iff next second).mpr retained
  exact ⟨remaining, (deliverChecked_iff _ _ _ _ _ _ _).mpr
    ⟨fits, current, body, cleared, released⟩⟩

/-- Construct both delivery orders from independently admitted, distinct issued
rows. Each consumer retains its exact endpoint; remaining authority agrees
with multiplicity. Changed worlds must preserve the other consumer's complete
consulted support, including absence reads. This does not equate those worlds
or license reordering their external effects. -/
theorem independent_replies_commute {registry next otherNext : Registry}
    {live afterFirstWorld afterSecondWorld : RevisionEnvironment Key Revision}
    {capture other : Capture Key Revision} {handle second : Handle}
    {reply secondReply : Reply} {after otherAfter : Configuration}
    (firstAccepted : (deliverChecked registry live capture handle reply).1 = .ok (after, next))
    (secondAccepted : (deliverChecked registry live other second secondReply).1 =
      .ok (otherAfter, otherNext))
    (different : second.row ≠ handle.row)
    (otherStable : RevisionEnvironment.AgreesOn other.view.consulted.toFinset afterFirstWorld live)
    (firstStable : RevisionEnvironment.AgreesOn capture.view.consulted.toFinset afterSecondWorld live) :
    ∃ finalFirst finalSecond,
      (deliverChecked next afterFirstWorld other second secondReply).1 = .ok (otherAfter, finalFirst) ∧
      (deliverChecked otherNext afterSecondWorld capture handle reply).1 = .ok (after, finalSecond) ∧
      finalFirst.identity = finalSecond.identity ∧ finalFirst.rows.Perm finalSecond.rows ∧
      ∀ survivor, IssuedReturn.Authenticated finalFirst survivor ↔
        IssuedReturn.Authenticated finalSecond survivor := by
  obtain ⟨finalFirst, secondAfter⟩ :=
    independent_reply_survives firstAccepted secondAccepted different
  obtain ⟨finalSecond, firstAfter⟩ :=
    independent_reply_survives secondAccepted firstAccepted (Ne.symm different)
  obtain ⟨clearedFirst, releasedFirst⟩ :=
    ((deliverChecked_iff _ _ _ _ _ _ _).mp firstAccepted).2.2.2
  obtain ⟨clearedSecond, releasedSecond⟩ :=
    ((deliverChecked_iff _ _ _ _ _ _ _).mp secondAccepted).2.2.2
  obtain ⟨clearedAfterFirst, releasedAfterFirst⟩ :=
    ((deliverChecked_iff _ _ _ _ _ _ _).mp secondAfter).2.2.2
  obtain ⟨clearedAfterSecond, releasedAfterSecond⟩ :=
    ((deliverChecked_iff _ _ _ _ _ _ _).mp firstAfter).2.2.2
  obtain ⟨identity, rows⟩ := IssuedReturn.releaseIssued_commute registry next otherNext
    finalFirst finalSecond handle second clearedFirst clearedSecond clearedAfterFirst clearedAfterSecond
    releasedFirst releasedSecond releasedAfterFirst releasedAfterSecond
  refine ⟨finalFirst, finalSecond, ?_, ?_, identity, rows, ?_⟩
  · exact (deliverChecked_world_iff _ _ _ _ _ _ _ _ otherStable).mpr secondAfter
  · exact (deliverChecked_world_iff _ _ _ _ _ _ _ _ firstStable).mpr firstAfter
  · exact IssuedReturn.authentication_of_rows_perm finalFirst finalSecond identity rows

/-- Independently admitted issued replies join the existing binding-publication
algorithm. Disjoint write sets make the final binding maps agree; each write
set must also avoid the other capture's consulted reads. Complete controller
endpoints and remaining issued authority are retained in both orders. Other
world metadata and ordered external traces need their own compatibility laws. -/
theorem independent_replies_with_binding_publication {Value : Type} [DecidableEq Value]
    {registry next otherNext : Registry}
    {live : RevisionEnvironment Key (Option Value)}
    {capture other : Capture Key (Option Value)} {handle second : Handle}
    {reply secondReply : Reply} {after otherAfter : Configuration}
    (firstWrites secondWrites : List (Key × Value))
    (firstAccepted : (deliverChecked registry live capture handle reply).1 = .ok (after, next))
    (secondAccepted : (deliverChecked registry live other second secondReply).1 =
      .ok (otherAfter, otherNext))
    (different : second.row ≠ handle.row)
    (otherReads : List.Disjoint other.view.consulted (firstWrites.map Prod.fst))
    (firstReads : List.Disjoint capture.view.consulted (secondWrites.map Prod.fst))
    (writes : List.Disjoint (firstWrites.map Prod.fst) (secondWrites.map Prod.fst)) :
    ∃ finalFirst finalSecond,
      (deliverChecked next ⟨BindingPublication.applyWrites live.current firstWrites⟩
        other second secondReply).1 = .ok (otherAfter, finalFirst) ∧
      (deliverChecked otherNext ⟨BindingPublication.applyWrites live.current secondWrites⟩
        capture handle reply).1 = .ok (after, finalSecond) ∧
      finalFirst.identity = finalSecond.identity ∧ finalFirst.rows.Perm finalSecond.rows ∧
      BindingPublication.applyWrites (BindingPublication.applyWrites live.current firstWrites)
        secondWrites =
          BindingPublication.applyWrites (BindingPublication.applyWrites live.current secondWrites)
            firstWrites ∧
      ∀ survivor, IssuedReturn.Authenticated finalFirst survivor ↔
        IssuedReturn.Authenticated finalSecond survivor := by
  obtain ⟨finalFirst, finalSecond, acceptedSecond, acceptedFirst, identity, rows, authority⟩ :=
    independent_replies_commute firstAccepted secondAccepted different
      (RevisionEnvironment.agreesOn_applyWrites live firstWrites other.view.consulted otherReads)
      (RevisionEnvironment.agreesOn_applyWrites live secondWrites capture.view.consulted firstReads)
  exact ⟨finalFirst, finalSecond, acceptedSecond, acceptedFirst, identity, rows,
    BindingPublication.applyWrites_commute live.current firstWrites secondWrites writes, authority⟩

/-- Cancellation only retires the issued permission. It neither evaluates the
saved controller nor alters its captured world, answer prefix or work account. -/
def cancel (registry : Registry) (capture : Capture Key Revision) (handle : Handle) :
    Option (Registry × Capture Key Revision) × Nat :=
  if Matches capture handle then
    ((IssuedReturn.releaseIssued registry handle).1.map fun released => (released.1, capture),
      (IssuedReturn.releaseIssued registry handle).2)
  else (none, 0)

omit [DecidableEq Key] [DecidableEq Revision] in
theorem cancellation_keeps_complete_capture (registry : Registry)
    (capture : Capture Key Revision) (handle : Handle) (next : Registry)
    (retained : Capture Key Revision) (cancelled : (cancel registry capture handle).1 = some (next, retained)) :
    retained = capture := by
  by_cases fits : Matches capture handle
  · simp only [cancel, fits, ↓reduceIte] at cancelled
    obtain ⟨released, _, same⟩ := Option.map_eq_some_iff.mp cancelled
    exact (congrArg Prod.snd same).symm
  · simp [cancel, fits] at cancelled

end OwnedReplyBoundary

end Mettapedia.Languages.MeTTa.HE.NativeArgumentControlHistory
