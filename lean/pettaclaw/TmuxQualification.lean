import OperatorRevocation

/-!
# A qualification boundary for terminal effects

This file does not place terminal policy in the process kernel. It specifies a
small capability protocol which an external effect broker can implement and a
replaceable agent policy can use.

An exact target contains session, window, and pane identity. Observation
returns that target together with a revision. Submission succeeds only if the
same target is still live at the same revision. Thus the broker—not a sleep in
the model's plan—closes the check/use interval. Partial addresses are rejected,
and a successful send cannot perturb another target.

Window lifetime is a separate concern. A shell-owned window survives guest
exit; a guest-owned window does not. This distinction was operationally
relevant in the failed Claude/tmux episode.
-/

namespace PettaClaw.TmuxQualification

structure Target where
  session : Nat
  window : Nat
  pane : Nat
deriving Repr, DecidableEq

structure WindowAddress where
  session : Nat
  window : Nat
deriving Repr, DecidableEq

def Target.windowAddress (target : Target) : WindowAddress :=
  ⟨target.session, target.window⟩

/-- A window-only address is not an exact effect capability: two distinct
panes can have the same projection. -/
theorem window_address_is_not_injective :
    let first : Target := ⟨1, 7, 0⟩
    let second : Target := ⟨1, 7, 1⟩
    first ≠ second ∧ first.windowAddress = second.windowAddress := by
  decide

inductive Address where
  | exact (target : Target)
  | windowOnly (address : WindowAddress)
  | bareName (name : String)
deriving Repr, DecidableEq

/-- The effect broker accepts only a complete target. Resolution of friendly
names remains a replaceable discovery process which must end in an exact
capability before dispatch. -/
def exactTarget : Address → Option Target
  | .exact target => some target
  | .windowOnly _ => none
  | .bareName _ => none

theorem partial_addresses_are_not_effect_capabilities
    (address : WindowAddress) (name : String) :
    exactTarget (.windowOnly address) = none ∧
      exactTarget (.bareName name) = none := by
  constructor <;> rfl

structure PaneState where
  revision : Nat
  shellAlive : Bool
  transcript : List String
deriving Repr, DecidableEq

abbrev World := Target → PaneState

structure Observation where
  target : Target
  revision : Nat
deriving Repr, DecidableEq

def updateTarget (target : Target) (next : PaneState) (world : World) : World :=
  fun candidate => if candidate = target then next else world candidate

/-- Compare-and-send is one broker transition. A changed revision or dead
shell produces no physical successor. -/
def guardedSend (observed : Observation) (text : String)
    (world : World) : Option World :=
  if (world observed.target).revision = observed.revision ∧
      (world observed.target).shellAlive = true then
    let pane := world observed.target
    some (updateTarget observed.target
      { pane with
        revision := pane.revision + 1
        transcript := pane.transcript ++ [text] }
      world)
  else
    none

theorem stale_observation_cannot_send
    (world : World) (observed : Observation) (text : String)
    (changed : (world observed.target).revision ≠ observed.revision) :
    guardedSend observed text world = none := by
  simp [guardedSend, changed]

theorem dead_shell_cannot_receive
    (world : World) (observed : Observation) (text : String)
    (dead : (world observed.target).shellAlive = false) :
    guardedSend observed text world = none := by
  simp [guardedSend, dead]

/-- A successful exact-target effect leaves every other pane unchanged. -/
theorem guarded_send_noninterference
    (world next : World) (observed : Observation) (text : String)
    (sent : guardedSend observed text world = some next)
    (other : Target) (distinct : other ≠ observed.target) :
    next other = world other := by
  unfold guardedSend at sent
  split at sent
  · simp only [Option.some.injEq] at sent
    subst next
    simp [updateTarget, distinct]
  · contradiction

inductive WindowOwner where
  | shell
  | guest
deriving Repr, DecidableEq

structure HostedWindow where
  owner : WindowOwner
  windowAlive : Bool
  shellAlive : Bool
  guestAlive : Bool
deriving Repr, DecidableEq

/-- Exiting a guest only closes the window when that guest was installed as
the window-owning process. -/
def exitGuest (window : HostedWindow) : HostedWindow :=
  match window.owner with
  | .shell => { window with guestAlive := false }
  | .guest =>
      { window with
        windowAlive := false
        shellAlive := false
        guestAlive := false }

theorem shell_owned_window_survives_guest_exit
    (shellAlive : Bool) :
    let before : HostedWindow := ⟨.shell, true, shellAlive, true⟩
    (exitGuest before).windowAlive = true ∧
      (exitGuest before).shellAlive = shellAlive ∧
      (exitGuest before).guestAlive = false := by
  cases shellAlive <;> decide

theorem guest_owned_window_dies_with_guest :
    let before : HostedWindow := ⟨.guest, true, false, true⟩
    (exitGuest before).windowAlive = false ∧
      (exitGuest before).guestAlive = false := by
  decide

/-- The protocol is policy-neutral: any chooser may select an exact observed
target and text. Authority and staleness remain broker checks. -/
def brokeredChoice
    (choose : List Observation → Option (Observation × String))
    (observations : List Observation) (world : World) : Option World :=
  match choose observations with
  | none => none
  | some (observed, text) => guardedSend observed text world

/-! ## A replaceable commitment-phase projection

The broker protocol prevents stale and misdirected effects, but it does not
tell a model whether a multi-step task is already complete. Append-only screen
history is insufficient when old prompt markers remain visible. A small
receipt-derived phase is a replaceable world-state projection, not a new
kernel transition.
-/

inductive TaskPhase where
  | needCreate
  | needLaunch
  | needTrust
  | needServer
  | goalSatisfied
deriving Repr, DecidableEq

inductive TaskReceipt where
  | windowCreated
  | guestLaunched
  | trustAnswered
  | serverAnswered
  | unrelated
deriving Repr, DecidableEq

/-- Only the receipt expected by the current phase advances the commitment.
Once satisfied, accidental duplicate receipts cannot reopen it. -/
def advancePhase : TaskPhase → TaskReceipt → TaskPhase
  | .needCreate, .windowCreated => .needLaunch
  | .needLaunch, .guestLaunched => .needTrust
  | .needTrust, .trustAnswered => .needServer
  | .needServer, .serverAnswered => .goalSatisfied
  | phase, _ => phase

theorem satisfied_phase_is_absorbing (receipt : TaskReceipt) :
    advancePhase .goalSatisfied receipt = .goalSatisfied := by
  cases receipt <;> rfl

theorem verified_receipt_sequence_reaches_satisfaction :
    advancePhase
      (advancePhase
        (advancePhase
          (advancePhase .needCreate .windowCreated)
          .guestLaunched)
        .trustAnswered)
      .serverAnswered = .goalSatisfied := by
  rfl

inductive Marker where
  | trust
  | server
  | idle
deriving Repr, DecidableEq, BEq

structure ScreenHistory where
  phase : TaskPhase
  markers : List Marker
deriving Repr, DecidableEq

/-- A common but lossy terminal summary remembers whether a marker appeared,
not which occurrence is currently awaiting input. -/
def markerPresence (history : ScreenHistory) : Bool × Bool × Bool :=
  (history.markers.contains .trust,
    history.markers.contains .server,
    history.markers.contains .idle)

/-- A completed dialogue and a relaunched dialogue waiting at the trust prompt
have identical marker-presence summaries. Therefore marker presence cannot be
a complete view of current task phase. -/
theorem marker_presence_cannot_determine_current_phase :
    let completed : ScreenHistory :=
      ⟨.goalSatisfied, [.trust, .server, .idle]⟩
    let relaunched : ScreenHistory :=
      ⟨.needTrust, [.trust, .server, .idle, .trust]⟩
    completed.phase ≠ relaunched.phase ∧
      markerPresence completed = markerPresence relaunched := by
  decide

inductive PhaseAction where
  | create
  | launch
  | answerTrust
  | selectServer
  | finish
deriving Repr, DecidableEq

def requiredAction : TaskPhase → PhaseAction
  | .needCreate => .create
  | .needLaunch => .launch
  | .needTrust => .answerTrust
  | .needServer => .selectServer
  | .goalSatisfied => .finish

/-- The operational consequence of the collision above: no deterministic
policy which sees only marker presence can choose correctly both after genuine
completion and after a relaunch whose new trust prompt sits below old markers.
The missing information is not model intelligence; it is absent from the
policy's observation. -/
theorem no_marker_only_policy_handles_completion_and_relaunch :
    let completed : ScreenHistory :=
      ⟨.goalSatisfied, [.trust, .server, .idle]⟩
    let relaunched : ScreenHistory :=
      ⟨.needTrust, [.trust, .server, .idle, .trust]⟩
    ¬ ∃ choose : (Bool × Bool × Bool) → PhaseAction,
      choose (markerPresence completed) = .finish ∧
        choose (markerPresence relaunched) = .answerTrust := by
  dsimp [markerPresence]
  rintro ⟨choose, finished, relaunched⟩
  have impossible : PhaseAction.finish = PhaseAction.answerTrust :=
    finished.symm.trans relaunched
  cases impossible

/-- Adding the receipt-derived phase is sufficient for the two states which
the raw marker view conflates. The projection informs policy without fixing a
specific model or placing task semantics in the process kernel. -/
theorem phase_projection_handles_completion_and_relaunch :
    requiredAction .goalSatisfied = .finish ∧
      requiredAction .needTrust = .answerTrust := by
  exact ⟨rfl, rfl⟩

theorem witnessed_satisfaction_requires_finish :
    requiredAction .goalSatisfied = .finish := by
  rfl

end PettaClaw.TmuxQualification

#print axioms PettaClaw.TmuxQualification.window_address_is_not_injective
#print axioms PettaClaw.TmuxQualification.stale_observation_cannot_send
#print axioms PettaClaw.TmuxQualification.dead_shell_cannot_receive
#print axioms PettaClaw.TmuxQualification.guarded_send_noninterference
#print axioms PettaClaw.TmuxQualification.shell_owned_window_survives_guest_exit
#print axioms PettaClaw.TmuxQualification.guest_owned_window_dies_with_guest
#print axioms PettaClaw.TmuxQualification.satisfied_phase_is_absorbing
#print axioms PettaClaw.TmuxQualification.verified_receipt_sequence_reaches_satisfaction
#print axioms PettaClaw.TmuxQualification.marker_presence_cannot_determine_current_phase
#print axioms PettaClaw.TmuxQualification.no_marker_only_policy_handles_completion_and_relaunch
#print axioms PettaClaw.TmuxQualification.phase_projection_handles_completion_and_relaunch
#print axioms PettaClaw.TmuxQualification.witnessed_satisfaction_requires_finish
