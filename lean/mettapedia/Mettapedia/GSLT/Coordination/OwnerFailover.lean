import Mettapedia.GSLT.Coordination.MajorityEpochs
import Mettapedia.GSLT.Coordination.HomeLocation

/-!
# Owner failover: majority epochs, state transfer and fencing

A region's owner is the location that runs its commits (`HomeLocation`). When the owner may fail
and the region must stay available, the owner's state is kept by a group of **acceptors**, and any
**candidate** may become the owner of a new **epoch**. This module gives the full protocol and
proves its safety for every failure pattern.

## The protocol

The owner's state is a **log** of commands. An acceptor keeps the highest epoch it has promised,
and the log it last accepted with that log's epoch. Messages are never lost from the record of
what was sent (`State.sent`); a delivery is an event that reads a sent message, so messages may be
delayed, duplicated, reordered or never delivered.

1. **start** `who e`: a candidate starts an epoch above every epoch it started before, and asks
   for promises.
2. **promise** `a who e`: an acceptor that has promised only lower epochs promises `e` to `who`,
   reporting the log it last accepted and that log's epoch. An acceptor promises each epoch to one
   candidate at most.
3. **elect** `who Q ae al`: with promises from a quorum `Q`, the candidate becomes the owner of its
   epoch. **State transfer**: it adopts the reported log of the highest epoch, the longest among
   those (`ae`, `al`), and asks the acceptors to accept it at the new epoch.
4. **propose** `who c`: the owner appends a command its state admits (`valid`) and asks the
   acceptors to accept the longer log.
5. **accept** `a who e log`: an acceptor accepts a log of epoch `e` unless it has promised a higher
   epoch (**fencing**), and unless it holds a longer log of the same epoch.

A log is **chosen** at an epoch when every acceptor of a quorum has accepted, at that epoch, a log
that extends it (`Chosen`). The owner acknowledges a command only once a log containing it is
chosen.

## Safety, for every sequence of events

Quorums are a parameter; the theorems need only that two quorums meet (`QuorumSystem`), which
majorities do (`majority_quorumSystem`).

* **One owner per epoch** (`one_owner_per_epoch`): two candidates that send logs at one epoch are
  the same candidate.
* **State transfer is complete** (`chosen_extends`): every log chosen at an epoch is a prefix of
  every log sent at any higher epoch. So **every new owner's log extends everything chosen before
  its epoch** (`owner_extends_chosen`): nothing committed is lost across failover.
* **Chosen logs form one history** (`chosen_comparable`): of two chosen logs, one extends the other.
* **Chosen logs are admissible** (`chosen_admissible`): every command was admitted by the owner's
  state after the commands before it.
* **Fencing** (`stale_accept_refused`): an acceptor that has promised a higher epoch refuses the
  stale owner's logs. This is the step the proofs use to keep reports complete.

## Over K's commits

With commands read as commits of an occurrence store, and an owner that admits a commit when it is
enabled after the log and makes identities never seen before (`commitValid`):

* **every chosen log is a run of the atomic semantics** (`chosen_legal`);
* **no occurrence is taken twice in the committed history** (`chosen_takes_once`), however many
  owners and epochs it spans.

## Controls

* `Controls.minority_double_take`: with quorums of one acceptor out of three, two owners are
  elected in one epoch and each gets a log chosen that takes the same token.
* `Controls.unfenced_double_take`: with majorities but acceptors that do not fence by promised
  epoch, a stale owner's log is chosen at its old epoch after the new owner was elected without it;
  the two chosen logs both take the token.
* `Controls.fenced_refuses_stale`: in the same run with fencing, the stale owner's log is refused.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.OwnerFailover

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Coordination.ReplicaMerge
open Mettapedia.GSLT.Coordination.MajorityEpochs

universe u v w

/-! ## Admissible logs -/

section Logs

variable {C : Type w}

/-- A log is admissible when each command was valid after the commands before it. -/
inductive Admissible (valid : List C → C → Prop) : List C → Prop
  | nil : Admissible valid []
  | snoc {log : List C} {c : C} : Admissible valid log → valid log c → Admissible valid (log ++ [c])

/-- Admissible logs are closed under prefixes. -/
theorem Admissible.prefix {valid : List C → C → Prop} {log : List C} (admissible : Admissible valid log) :
    ∀ {pre : List C}, pre <+: log → Admissible valid pre := by
  induction admissible with
  | nil => intro pre isPrefix; rw [List.prefix_nil.mp isPrefix]; exact .nil
  | snoc rest ok ih =>
      intro pre isPrefix
      rcases List.prefix_concat_iff.mp isPrefix with same | shorter
      · rw [same]; exact .snoc rest ok
      · exact ih shorter

/-- A log extended by one command is admissible exactly when the log is and the command was valid
after it. -/
theorem Admissible.snoc_iff {valid : List C → C → Prop} {log : List C} {c : C} :
    Admissible valid (log ++ [c]) ↔ Admissible valid log ∧ valid log c := by
  constructor
  · intro h
    generalize hl : log ++ [c] = l at h
    cases h with
    | nil => simp at hl
    | @snoc log' c' rest ok =>
        obtain ⟨hlog, hc⟩ := List.append_inj' hl rfl
        simp only [List.cons.injEq, and_true] at hc
        subst hlog hc
        exact ⟨rest, ok⟩
  · rintro ⟨h, ok⟩
    exact .snoc h ok

end Logs

/-! ## States, messages, events -/

/-- An acceptor: the highest epoch it promised, and the log it last accepted with its epoch. -/
structure Acceptor (C : Type w) where
  promised : ℕ
  acceptedEpoch : ℕ
  log : List C
  deriving DecidableEq

/-- What a candidate is doing at its current epoch. -/
inductive Phase (C : Type w) where
  | idle
  | electing
  | owner (log : List C)
  deriving DecidableEq

/-- A candidate: the highest epoch it started (kept durably), and its phase there. -/
structure Candidate (C : Type w) where
  epoch : ℕ
  phase : Phase C
  deriving DecidableEq

/-- The messages of the protocol. -/
inductive Msg (V : Type u) (P : Type v) (C : Type w) where
  | prepare (who : P) (epoch : ℕ)
  | promise (acceptor : V) (who : P) (epoch acceptedEpoch : ℕ) (log : List C)
  | accept (who : P) (epoch : ℕ) (log : List C)
  | accepted (acceptor : V) (epoch : ℕ) (log : List C)
  deriving DecidableEq

/-- The global state: acceptors, candidates, and every message ever sent. -/
structure State (V : Type u) (P : Type v) (C : Type w) where
  acc : V → Acceptor C
  cand : P → Candidate C
  sent : List (Msg V P C)

/-- The events. A delivery of a message is the event of its receiver that reads it. -/
inductive Event (V : Type u) (P : Type v) (C : Type w) where
  | start (who : P) (epoch : ℕ)
  | promise (acceptor : V) (who : P) (epoch : ℕ)
  | elect (who : P) (quorum : Finset V) (acceptedEpoch : ℕ) (log : List C)
  | propose (who : P) (command : C)
  | accept (acceptor : V) (who : P) (epoch : ℕ) (log : List C)

variable {V : Type u} [DecidableEq V] {P : Type v} [DecidableEq P] {C : Type w} [DecidableEq C]

/-- The initial state: nothing promised, accepted, started or sent. -/
def State.init : State V P C := ⟨fun _ => ⟨0, 0, []⟩, fun _ => ⟨0, .idle⟩, []⟩

namespace Msg

/-- A promise from `a` to `who` for epoch `e`. -/
def IsPromiseFor (a : V) (who : P) (e : ℕ) : Msg V P C → Prop
  | .promise a' w e' _ _ => a' = a ∧ w = who ∧ e' = e
  | _ => False

/-- A promise from `a` to `who` for `e` reports nothing above `(ae, al)`. -/
def BelowReport (a : V) (who : P) (e ae : ℕ) (al : List C) : Msg V P C → Prop
  | .promise a' w e' ae' al' => a' = a → w = who → e' = e → ae' < ae ∨ (ae' = ae ∧ al'.length ≤ al.length)
  | _ => True

instance (a : V) (who : P) (e : ℕ) (m : Msg V P C) : Decidable (m.IsPromiseFor a who e) := by
  cases m <;> unfold IsPromiseFor <;> infer_instance

instance (a : V) (who : P) (e ae : ℕ) (al : List C) (m : Msg V P C) :
    Decidable (m.BelowReport a who e ae al) := by
  cases m <;> unfold BelowReport <;> infer_instance

omit [DecidableEq V] [DecidableEq P] [DecidableEq C] in
theorem isPromiseFor_iff {a : V} {who : P} {e : ℕ} {m : Msg V P C} :
    m.IsPromiseFor a who e ↔ ∃ ae al, m = .promise a who e ae al := by
  cases m with
  | promise a' w e' ae al =>
      simp only [IsPromiseFor, promise.injEq]
      constructor
      · rintro ⟨rfl, rfl, rfl⟩; exact ⟨ae, al, by simp⟩
      · rintro ⟨_, _, rfl, rfl, rfl, _, _⟩; exact ⟨rfl, rfl, rfl⟩
  | prepare => simp [IsPromiseFor]
  | accept => simp [IsPromiseFor]
  | accepted => simp [IsPromiseFor]

end Msg

variable (quorum : Finset V → Prop) [DecidablePred quorum] (fenced : Bool)
variable (valid : List C → C → Prop) [∀ log c, Decidable (valid log c)]

/-- The guard of an election: the candidate is electing, `Q` is a quorum, every member of `Q` has
promised the candidate's epoch, and `(ae, al)` is a report of a member of `Q` that no member's
report exceeds. -/
def ElectOK (s : State V P C) (who : P) (Q : Finset V) (ae : ℕ) (al : List C) : Prop :=
  (s.cand who).phase = .electing ∧ quorum Q ∧
    (∀ a ∈ Q, ∃ m ∈ s.sent, m.IsPromiseFor a who (s.cand who).epoch) ∧
    (∃ a ∈ Q, Msg.promise a who (s.cand who).epoch ae al ∈ s.sent) ∧
    ∀ a ∈ Q, ∀ m ∈ s.sent, m.BelowReport a who (s.cand who).epoch ae al

instance (s : State V P C) (who : P) (Q : Finset V) (ae : ℕ) (al : List C) :
    Decidable (ElectOK quorum s who Q ae al) := by
  unfold ElectOK; infer_instance

/-- The guard of an acceptance. -/
def AcceptOK (s : State V P C) (a : V) (who : P) (e : ℕ) (log : List C) : Prop :=
  Msg.accept who e log ∈ s.sent ∧ (fenced = true → (s.acc a).promised ≤ e) ∧
    ((s.acc a).acceptedEpoch < e ∨ ((s.acc a).acceptedEpoch = e ∧ (s.acc a).log <+: log))

instance (s : State V P C) (a : V) (who : P) (e : ℕ) (log : List C) :
    Decidable (AcceptOK fenced s a who e log) := by
  unfold AcceptOK; infer_instance

/-- One event. An event whose guard fails changes nothing. -/
def apply (s : State V P C) : Event V P C → State V P C
  | .start who e =>
      if (s.cand who).epoch < e then
        { s with cand := Function.update s.cand who ⟨e, .electing⟩, sent := .prepare who e :: s.sent }
      else s
  | .promise a who e =>
      if Msg.prepare who e ∈ s.sent ∧ (s.acc a).promised < e then
        { s with acc := Function.update s.acc a ⟨e, (s.acc a).acceptedEpoch, (s.acc a).log⟩
                 sent := .promise a who e (s.acc a).acceptedEpoch (s.acc a).log :: s.sent }
      else s
  | .elect who Q ae al =>
      if ElectOK quorum s who Q ae al then
        { s with cand := Function.update s.cand who ⟨(s.cand who).epoch, .owner al⟩
                 sent := .accept who (s.cand who).epoch al :: s.sent }
      else s
  | .propose who c =>
      match (s.cand who).phase with
      | .owner log =>
          if valid log c then
            { s with cand := Function.update s.cand who ⟨(s.cand who).epoch, .owner (log ++ [c])⟩
                     sent := .accept who (s.cand who).epoch (log ++ [c]) :: s.sent }
          else s
      | _ => s
  | .accept a who e log =>
      if AcceptOK fenced s a who e log then
        { s with acc := Function.update s.acc a ⟨max (s.acc a).promised e, e, log⟩
                 sent := .accepted a e log :: s.sent }
      else s

/-- A run of events. -/
def run (s : State V P C) : List (Event V P C) → State V P C
  | [] => s
  | e :: es => run (apply quorum fenced valid s e) es

/-- A log is **chosen** at an epoch: every acceptor of a quorum accepted, at that epoch, a log that
extends it. -/
def Chosen (s : State V P C) (e : ℕ) (L : List C) : Prop :=
  ∃ Q, quorum Q ∧ ∀ a ∈ Q, ∃ L', Msg.accepted a e L' ∈ s.sent ∧ L <+: L'

/-- Two quorums always meet. -/
def QuorumSystem : Prop := ∀ Q Q', quorum Q → quorum Q' → ∃ a, a ∈ Q ∧ a ∈ Q'

omit [DecidableEq V] in
/-- **Majorities form a quorum system.** -/
theorem majority_quorumSystem [Fintype V] [DecidableEq V] :
    QuorumSystem (IsMajority (V := V)) := fun _ _ first second => quorums_intersect first second

/-! ## The invariant -/

variable {quorum fenced valid}

/-- The facts every reachable state satisfies. -/
structure Inv (s : State V P C) : Prop where
  acc_le : ∀ a, (s.acc a).acceptedEpoch ≤ (s.acc a).promised
  acc_dom : ∀ a e L, Msg.accepted a e L ∈ s.sent →
    e ≤ (s.acc a).acceptedEpoch ∧ (e = (s.acc a).acceptedEpoch → L <+: (s.acc a).log)
  acc_cur : ∀ a, ((s.acc a).acceptedEpoch = 0 ∧ (s.acc a).log = []) ∨
    Msg.accepted a (s.acc a).acceptedEpoch (s.acc a).log ∈ s.sent
  promise_le : ∀ a who e ae al, Msg.promise a who e ae al ∈ s.sent → e ≤ (s.acc a).promised
  promise_report : ∀ a who e ae al, Msg.promise a who e ae al ∈ s.sent →
    ae < e ∧ ((ae = 0 ∧ al = []) ∨ Msg.accepted a ae al ∈ s.sent) ∧
      ∀ e' L', Msg.accepted a e' L' ∈ s.sent → e' < e → e' ≤ ae ∧ (e' = ae → L' <+: al)
  promise_unique : ∀ a who who' e ae ae' al al', Msg.promise a who e ae al ∈ s.sent →
    Msg.promise a who' e ae' al' ∈ s.sent → who = who' ∧ ae = ae' ∧ al = al'
  accepted_src : ∀ a e L, Msg.accepted a e L ∈ s.sent → ∃ who, Msg.accept who e L ∈ s.sent
  prepare_le : ∀ who e, Msg.prepare who e ∈ s.sent → e ≤ (s.cand who).epoch
  promise_src : ∀ a who e ae al, Msg.promise a who e ae al ∈ s.sent → Msg.prepare who e ∈ s.sent
  accept_le : ∀ who e L, Msg.accept who e L ∈ s.sent → 1 ≤ e ∧ e ≤ (s.cand who).epoch
  cand_pos : ∀ who, (s.cand who).phase ≠ .idle → 1 ≤ (s.cand who).epoch
  electing_silent : ∀ who, (s.cand who).phase = .electing →
    ∀ L, Msg.accept who (s.cand who).epoch L ∉ s.sent
  owner_max : ∀ who log, (s.cand who).phase = .owner log →
    Msg.accept who (s.cand who).epoch log ∈ s.sent ∧
      ∀ L, Msg.accept who (s.cand who).epoch L ∈ s.sent → L <+: log
  accept_chain : ∀ who e L L', Msg.accept who e L ∈ s.sent → Msg.accept who e L' ∈ s.sent →
    L <+: L' ∨ L' <+: L
  accept_elected : ∀ who e L, Msg.accept who e L ∈ s.sent → ∃ Q ae al, quorum Q ∧
    (∀ a ∈ Q, ∃ ae' al', Msg.promise a who e ae' al' ∈ s.sent ∧
      (ae' < ae ∨ (ae' = ae ∧ al'.length ≤ al.length))) ∧
    (∃ a ∈ Q, Msg.promise a who e ae al ∈ s.sent) ∧ al <+: L
  accept_admissible : ∀ who e L, Msg.accept who e L ∈ s.sent → Admissible valid L

omit [DecidableEq V] [DecidableEq P] [DecidableEq C] [DecidablePred quorum] [(log : List C) → (c : C) → Decidable (valid log c)] in
theorem inv_init : Inv (quorum := quorum) (valid := valid) (State.init : State V P C) where
  acc_le _ := le_rfl
  acc_dom _ _ _ h := by simp [State.init] at h
  acc_cur _ := Or.inl ⟨rfl, rfl⟩
  promise_le _ _ _ _ _ h := by simp [State.init] at h
  promise_report _ _ _ _ _ h := by simp [State.init] at h
  promise_unique _ _ _ _ _ _ _ _ h := by simp [State.init] at h
  accepted_src _ _ _ h := by simp [State.init] at h
  prepare_le _ _ h := by simp [State.init] at h
  promise_src _ _ _ _ _ h := by simp [State.init] at h
  accept_le _ _ _ h := by simp [State.init] at h
  cand_pos _ h := by simp [State.init] at h
  electing_silent _ h := by simp [State.init] at h
  owner_max _ _ h := by simp [State.init] at h
  accept_chain _ _ _ _ h := by simp [State.init] at h
  accept_elected _ _ _ h := by simp [State.init] at h
  accept_admissible _ _ _ h := by simp [State.init] at h

/-! ### Preservation, event by event -/

section Preservation

variable {s : State V P C}

theorem inv_start (inv : Inv (quorum := quorum) (valid := valid) s) (who : P) (e : ℕ) :
    Inv (quorum := quorum) (valid := valid) (apply quorum fenced valid s (.start who e)) := by
  simp only [apply]
  split_ifs with higher
  · have epochGe : ∀ w, (s.cand w).epoch ≤ (Function.update s.cand who ⟨e, .electing⟩ w).epoch := by
      intro w
      by_cases same : w = who
      · subst same; simp only [Function.update_self]; exact higher.le
      · rw [Function.update_of_ne same]
    refine ⟨inv.acc_le, fun a e' L h => ?_, fun a => ?_, fun a w e' ae al h => ?_,
      fun a w e' ae al h => ?_, fun a w w' e' ae ae' al al' h h' => ?_, fun a e' L h => ?_,
      fun w e' h => ?_, fun a w e' ae al h => ?_, fun w e' L h => ?_, fun w ph => ?_,
      fun w ph L h => ?_, fun w log ph => ?_, fun w e' L L' h h' => ?_, fun w e' L h => ?_,
      fun w e' L h => ?_⟩
    all_goals simp only [List.mem_cons, reduceCtorEq, false_or] at *
    · exact inv.acc_dom a e' L h
    · exact inv.acc_cur a
    · exact inv.promise_le a w e' ae al h
    · exact inv.promise_report a w e' ae al h
    · exact inv.promise_unique a w w' e' ae ae' al al' h h'
    · exact inv.accepted_src a e' L h
    · rcases h with ⟨rfl, rfl⟩ | h
      · simp
      · exact (inv.prepare_le w e' h).trans (epochGe w)
    · exact Or.inr (inv.promise_src a w e' ae al h)
    · obtain ⟨pos, le⟩ := inv.accept_le w e' L h
      exact ⟨pos, le.trans (epochGe w)⟩
    · by_cases same : w = who
      · subst same; simp only [Function.update_self]; omega
      · rw [Function.update_of_ne same] at ph ⊢; exact inv.cand_pos w ph
    · by_cases same : w = who
      · subst same
        simp only [Function.update_self] at h
        have := (inv.accept_le _ _ L h).2
        omega
      · rw [Function.update_of_ne same] at ph h; exact inv.electing_silent w ph L h
    · by_cases same : w = who
      · subst same; simp only [Function.update_self, reduceCtorEq] at ph
      · rw [Function.update_of_ne same] at ph ⊢; exact inv.owner_max w log ph
    · exact inv.accept_chain w e' L L' h h'
    · exact inv.accept_elected w e' L h
    · exact inv.accept_admissible w e' L h
  · exact inv

theorem inv_promise (inv : Inv (quorum := quorum) (valid := valid) s) (a : V) (who : P) (e : ℕ) :
    Inv (quorum := quorum) (valid := valid) (apply quorum fenced valid s (.promise a who e)) := by
  simp only [apply]
  split_ifs with guard
  · obtain ⟨prepared, below⟩ := guard
    set A := Function.update s.acc a ⟨e, (s.acc a).acceptedEpoch, (s.acc a).log⟩
    have epochSame : ∀ b, (A b).acceptedEpoch = (s.acc b).acceptedEpoch := by
      intro b; by_cases same : b = a
      · subst same; simp [A]
      · simp [A, Function.update_of_ne same]
    have logSame : ∀ b, (A b).log = (s.acc b).log := by
      intro b; by_cases same : b = a
      · subst same; simp [A]
      · simp [A, Function.update_of_ne same]
    have promisedGe : ∀ b, (s.acc b).promised ≤ (A b).promised := by
      intro b; by_cases same : b = a
      · subst same; simp only [A, Function.update_self]; exact below.le
      · simp [A, Function.update_of_ne same]
    refine ⟨fun b => ?_, fun b e' L h => ?_, fun b => ?_, fun b w e' ae al h => ?_,
      fun b w e' ae al h => ?_, fun b w w' e' ae ae' al al' h h' => ?_, fun b e' L h => ?_,
      fun w e' h => ?_, fun b w e' ae al h => ?_, fun w e' L h => ?_, fun w ph => ?_,
      fun w ph L h => ?_, fun w log ph => ?_, fun w e' L L' h h' => ?_, fun w e' L h => ?_,
      fun w e' L h => ?_⟩
    all_goals simp only [List.mem_cons, reduceCtorEq, false_or, Msg.promise.injEq] at *
    · rw [epochSame]; exact (inv.acc_le b).trans (promisedGe b)
    · rw [epochSame, logSame]; exact inv.acc_dom b e' L h
    · rw [epochSame, logSame]; exact inv.acc_cur b
    · rcases h with ⟨h₁, h₂, h₃, h₄, h₅⟩ | h <;> subst_vars
      · simp [A]
      · exact (inv.promise_le b w e' ae al h).trans (promisedGe b)
    · rcases h with ⟨h₁, h₂, h₃, h₄, h₅⟩ | h <;> subst_vars
      · refine ⟨lt_of_le_of_lt (inv.acc_le b) below, inv.acc_cur b, fun e'' L'' h'' _ => ?_⟩
        exact inv.acc_dom b e'' L'' h''
      · exact inv.promise_report b w e' ae al h
    · rcases h with ⟨h₁, h₂, h₃, h₄, h₅⟩ | h <;> rcases h' with ⟨h₁', h₂', h₃', h₄', h₅'⟩ | h' <;> subst_vars
      · exact ⟨rfl, rfl, rfl⟩
      · have := inv.promise_le b w' e' ae' al' h'; omega
      · have := inv.promise_le b w e' ae al h; omega
      · exact inv.promise_unique b w w' e' ae ae' al al' h h'
    · exact inv.accepted_src b e' L h
    · exact inv.prepare_le w e' h
    · rcases h with ⟨h₁, h₂, h₃, h₄, h₅⟩ | h <;> subst_vars
      · exact prepared
      · exact inv.promise_src b w e' ae al h
    · exact inv.accept_le w e' L h
    · exact inv.cand_pos w ph
    · exact inv.electing_silent w ph L h
    · exact inv.owner_max w log ph
    · exact inv.accept_chain w e' L L' h h'
    · obtain ⟨Q, ae, al, isQ, reports, best, pre⟩ := inv.accept_elected w e' L h
      refine ⟨Q, ae, al, isQ, fun b member => ?_, ?_, pre⟩
      · obtain ⟨ae', al', h', dom⟩ := reports b member
        exact ⟨ae', al', Or.inr h', dom⟩
      · obtain ⟨b, member, h'⟩ := best
        exact ⟨b, member, Or.inr h'⟩
    · exact inv.accept_admissible w e' L h
  · exact inv

theorem inv_elect (inv : Inv (quorum := quorum) (valid := valid) s) (who : P) (Q : Finset V)
    (ae : ℕ) (al : List C) :
    Inv (quorum := quorum) (valid := valid) (apply quorum fenced valid s (.elect who Q ae al)) := by
  simp only [apply]
  split_ifs with guard
  · obtain ⟨electing, isQ, promised, ⟨b₀, inQ₀, reported⟩, below⟩ := guard
    set e := (s.cand who).epoch
    set K := Function.update s.cand who ⟨e, .owner al⟩ with hK
    have epochSame : ∀ w, (K w).epoch = (s.cand w).epoch := by
      intro w; by_cases same : w = who
      · subst same; simp [K, e]
      · simp [K, Function.update_of_ne same]
    have pos : 1 ≤ e := inv.cand_pos who (by rw [electing]; exact fun h => by cases h)
    refine ⟨inv.acc_le, fun b e' L h => ?_, fun b => ?_, fun b w e' ae' al' h => ?_,
      fun b w e' ae' al' h => ?_, fun b w w' e' ae₁ ae₂ al₁ al₂ h h' => ?_, fun b e' L h => ?_,
      fun w e' h => ?_, fun b w e' ae' al' h => ?_, fun w e' L h => ?_, fun w ph => ?_,
      fun w ph L h => ?_, fun w log ph => ?_, fun w e' L L' h h' => ?_, fun w e' L h => ?_,
      fun w e' L h => ?_⟩
    all_goals simp only [List.mem_cons, reduceCtorEq, false_or, Msg.accept.injEq] at *
    · exact inv.acc_dom b e' L h
    · exact inv.acc_cur b
    · exact inv.promise_le b w e' ae' al' h
    · exact inv.promise_report b w e' ae' al' h
    · exact inv.promise_unique b w w' e' ae₁ ae₂ al₁ al₂ h h'
    · obtain ⟨w, hw⟩ := inv.accepted_src b e' L h
      exact ⟨w, Or.inr hw⟩
    · rw [epochSame]; exact inv.prepare_le w e' h
    · exact inv.promise_src b w e' ae' al' h
    · rw [epochSame]
      rcases h with ⟨h₁, h₂, h₃⟩ | h <;> subst_vars
      · exact ⟨pos, le_rfl⟩
      · exact inv.accept_le w e' L h
    · rw [epochSame]
      by_cases same : w = who
      · subst same; exact pos
      · rw [hK, Function.update_of_ne same] at ph; exact inv.cand_pos w ph
    · by_cases same : w = who
      · subst same; simp [K] at ph
      · rw [hK, Function.update_of_ne same] at ph h
        rcases h with ⟨rfl, _, _⟩ | h
        · exact absurd rfl same
        · exact inv.electing_silent w ph L h
    · by_cases same : w = who
      · subst same
        simp only [K, Function.update_self, Phase.owner.injEq] at ph ⊢
        subst ph
        refine ⟨Or.inl (by simp), fun L h => ?_⟩
        rcases h with ⟨_, _, rfl⟩ | h
        · exact List.prefix_refl _
        · exact absurd h (inv.electing_silent _ electing L)
      · rw [hK, Function.update_of_ne same] at ph ⊢
        obtain ⟨present, maximal⟩ := inv.owner_max w log ph
        refine ⟨Or.inr present, fun L h => ?_⟩
        rcases h with ⟨rfl, _, _⟩ | h
        · exact absurd rfl same
        · exact maximal L h
    · rcases h with ⟨h₁, h₂, h₃⟩ | h <;> rcases h' with ⟨h₁', h₂', h₃'⟩ | h' <;> subst_vars
      · exact Or.inl (List.prefix_refl _)
      · exact absurd h' (inv.electing_silent _ electing L')
      · exact absurd h (inv.electing_silent _ electing L)
      · exact inv.accept_chain w e' L L' h h'
    · rcases h with ⟨h₁, h₂, h₃⟩ | h <;> subst_vars
      · refine ⟨Q, ae, _, isQ, fun b member => ?_, ⟨b₀, inQ₀, reported⟩, List.prefix_refl _⟩
        obtain ⟨m, inSent, isPromise⟩ := promised b member
        obtain ⟨ae', al', rfl⟩ := Msg.isPromiseFor_iff.mp isPromise
        exact ⟨ae', al', inSent, below b member _ inSent rfl rfl rfl⟩
      · exact inv.accept_elected w e' L h
    · rcases h with ⟨h₁, h₂, h₃⟩ | h <;> subst_vars
      · rcases (inv.promise_report b₀ _ _ _ _ reported).2.1 with ⟨_, rfl⟩ | acceptedThere
        · exact .nil
        · obtain ⟨w', hw'⟩ := inv.accepted_src b₀ _ _ acceptedThere
          exact inv.accept_admissible w' _ _ hw'
      · exact inv.accept_admissible w e' L h
  · exact inv

theorem inv_propose (inv : Inv (quorum := quorum) (valid := valid) s) (who : P) (c : C) :
    Inv (quorum := quorum) (valid := valid) (apply quorum fenced valid s (.propose who c)) := by
  simp only [apply]
  rcases phaseIs : (s.cand who).phase with _ | _ | log
  · exact inv
  · exact inv
  · simp only
    split_ifs with ok
    · set e := (s.cand who).epoch
      set K := Function.update s.cand who ⟨e, .owner (log ++ [c])⟩ with hK
      have epochSame : ∀ w, (K w).epoch = (s.cand w).epoch := by
        intro w; by_cases same : w = who
        · subst same; simp [K, e]
        · simp [K, Function.update_of_ne same]
      have pos : 1 ≤ e := inv.cand_pos who (by rw [phaseIs]; exact fun h => by cases h)
      obtain ⟨present, maximal⟩ := inv.owner_max who log phaseIs
      refine ⟨inv.acc_le, fun b e' L h => ?_, fun b => ?_, fun b w e' ae' al' h => ?_,
        fun b w e' ae' al' h => ?_, fun b w w' e' ae₁ ae₂ al₁ al₂ h h' => ?_, fun b e' L h => ?_,
        fun w e' h => ?_, fun b w e' ae' al' h => ?_, fun w e' L h => ?_, fun w ph => ?_,
        fun w ph L h => ?_, fun w log' ph => ?_, fun w e' L L' h h' => ?_, fun w e' L h => ?_,
        fun w e' L h => ?_⟩
      all_goals simp only [List.mem_cons, reduceCtorEq, false_or, Msg.accept.injEq] at *
      · exact inv.acc_dom b e' L h
      · exact inv.acc_cur b
      · exact inv.promise_le b w e' ae' al' h
      · exact inv.promise_report b w e' ae' al' h
      · exact inv.promise_unique b w w' e' ae₁ ae₂ al₁ al₂ h h'
      · obtain ⟨w, hw⟩ := inv.accepted_src b e' L h
        exact ⟨w, Or.inr hw⟩
      · rw [epochSame]; exact inv.prepare_le w e' h
      · exact inv.promise_src b w e' ae' al' h
      · rw [epochSame]
        rcases h with ⟨h₁, h₂, h₃⟩ | h <;> subst_vars
        · exact ⟨pos, le_rfl⟩
        · exact inv.accept_le w e' L h
      · rw [epochSame]
        by_cases same : w = who
        · subst same; exact pos
        · rw [hK, Function.update_of_ne same] at ph; exact inv.cand_pos w ph
      · by_cases same : w = who
        · subst same; simp [K] at ph
        · rw [hK, Function.update_of_ne same] at ph h
          rcases h with ⟨rfl, _, _⟩ | h
          · exact absurd rfl same
          · exact inv.electing_silent w ph L h
      · by_cases same : w = who
        · subst same
          simp only [K, Function.update_self, Phase.owner.injEq] at ph ⊢
          subst ph
          refine ⟨Or.inl (by simp), fun L h => ?_⟩
          rcases h with ⟨_, _, rfl⟩ | h
          · exact List.prefix_refl _
          · exact (maximal L h).trans (List.prefix_append _ _)
        · rw [hK, Function.update_of_ne same] at ph ⊢
          obtain ⟨present', maximal'⟩ := inv.owner_max w log' ph
          refine ⟨Or.inr present', fun L h => ?_⟩
          rcases h with ⟨rfl, _, _⟩ | h
          · exact absurd rfl same
          · exact maximal' L h
      · rcases h with ⟨h₁, h₂, h₃⟩ | h <;> rcases h' with ⟨h₁', h₂', h₃'⟩ | h' <;> subst_vars
        · exact Or.inl (List.prefix_refl _)
        · exact Or.inr ((maximal L' h').trans (List.prefix_append _ _))
        · exact Or.inl ((maximal L h).trans (List.prefix_append _ _))
        · exact inv.accept_chain w e' L L' h h'
      · rcases h with ⟨h₁, h₂, h₃⟩ | h <;> subst_vars
        · obtain ⟨Q, ae, al, isQ, reports, best, pre⟩ := inv.accept_elected _ _ log present
          exact ⟨Q, ae, al, isQ, reports, best, pre.trans (List.prefix_append _ _)⟩
        · exact inv.accept_elected w e' L h
      · rcases h with ⟨h₁, h₂, h₃⟩ | h <;> subst_vars
        · exact .snoc (inv.accept_admissible _ _ log present) ok
        · exact inv.accept_admissible w e' L h
    · exact inv

theorem inv_accept (fencedOn : fenced = true) (inv : Inv (quorum := quorum) (valid := valid) s)
    (a : V) (who : P) (e : ℕ) (log : List C) :
    Inv (quorum := quorum) (valid := valid) (apply quorum fenced valid s (.accept a who e log)) := by
  simp only [apply]
  split_ifs with guard
  · obtain ⟨sentAccept, fence, fresher⟩ := guard
    have notAbove := fence fencedOn
    set A := Function.update s.acc a ⟨max (s.acc a).promised e, e, log⟩
    have atA : A a = ⟨max (s.acc a).promised e, e, log⟩ := by simp [A]
    have other : ∀ b, b ≠ a → A b = s.acc b := fun b h => by simp [A, Function.update_of_ne h]
    have promisedGe : ∀ b, (s.acc b).promised ≤ (A b).promised := by
      intro b; by_cases same : b = a
      · subst same; simp only [atA]; exact le_max_left _ _
      · rw [other b same]
    refine ⟨fun b => ?_, fun b e' L h => ?_, fun b => ?_, fun b w e' ae al h => ?_,
      fun b w e' ae al h => ?_, fun b w w' e' ae ae' al al' h h' => ?_, fun b e' L h => ?_,
      fun w e' h => ?_, fun b w e' ae al h => ?_, fun w e' L h => ?_, fun w ph => ?_,
      fun w ph L h => ?_, fun w log' ph => ?_, fun w e' L L' h h' => ?_, fun w e' L h => ?_,
      fun w e' L h => ?_⟩
    all_goals simp only [List.mem_cons, reduceCtorEq, false_or, Msg.accepted.injEq] at *
    · by_cases same : b = a
      · subst same; simp only [atA]; exact le_max_right _ _
      · rw [other b same]; exact inv.acc_le b
    · by_cases same : b = a
      · subst same
        simp only [atA]
        rcases h with ⟨_, rfl, rfl⟩ | h
        · exact ⟨le_rfl, fun _ => List.prefix_refl _⟩
        · obtain ⟨le, sameLog⟩ := inv.acc_dom b e' L h
          rcases fresher with lt | ⟨eq, pre⟩
          · exact ⟨by omega, fun h' => by omega⟩
          · exact ⟨by omega, fun h' => (sameLog (by omega)).trans pre⟩
      · rw [other b same]
        rcases h with ⟨rfl, _, _⟩ | h
        · exact absurd rfl same
        · exact inv.acc_dom b e' L h
    · by_cases same : b = a
      · subst same; simp only [atA]; exact Or.inr (Or.inl (by simp))
      · rw [other b same]
        rcases inv.acc_cur b with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    · exact (inv.promise_le b w e' ae al h).trans (promisedGe b)
    · obtain ⟨lt, cur, earlier⟩ := inv.promise_report b w e' ae al h
      refine ⟨lt, cur.imp_right Or.inr, fun e'' L'' h'' below => ?_⟩
      rcases h'' with ⟨rfl, rfl, rfl⟩ | h''
      · have := inv.promise_le b w e' ae al h
        omega
      · exact earlier e'' L'' h'' below
    · exact inv.promise_unique b w w' e' ae ae' al al' h h'
    · rcases h with ⟨_, rfl, rfl⟩ | h
      · exact ⟨who, sentAccept⟩
      · exact inv.accepted_src b e' L h
    · exact inv.prepare_le w e' h
    · exact inv.promise_src b w e' ae al h
    · exact inv.accept_le w e' L h
    · exact inv.cand_pos w ph
    · exact inv.electing_silent w ph L h
    · exact inv.owner_max w log' ph
    · exact inv.accept_chain w e' L L' h h'
    · exact inv.accept_elected w e' L h
    · exact inv.accept_admissible w e' L h
  · exact inv

/-- **Every event keeps the invariant**, when acceptors fence. -/
theorem inv_apply (fencedOn : fenced = true) (inv : Inv (quorum := quorum) (valid := valid) s)
    (ev : Event V P C) : Inv (quorum := quorum) (valid := valid) (apply quorum fenced valid s ev) := by
  cases ev with
  | start who e => exact inv_start inv who e
  | promise a who e => exact inv_promise inv a who e
  | elect who Q ae al => exact inv_elect inv who Q ae al
  | propose who c => exact inv_propose inv who c
  | accept a who e log => exact inv_accept fencedOn inv a who e log

end Preservation

/-! ## Reachable states -/

variable (quorum fenced valid) in
/-- A state reachable from the initial one by some sequence of events. -/
def Reachable (s : State V P C) : Prop := ∃ events, s = run quorum fenced valid State.init events

theorem run_append (s : State V P C) (first second : List (Event V P C)) :
    run quorum fenced valid s (first ++ second) =
      run quorum fenced valid (run quorum fenced valid s first) second := by
  induction first generalizing s with
  | nil => rfl
  | cons ev rest ih => exact ih _

theorem inv_run (fencedOn : fenced = true) :
    ∀ (events : List (Event V P C)) (s : State V P C), Inv (quorum := quorum) (valid := valid) s →
      Inv (quorum := quorum) (valid := valid) (run quorum fenced valid s events) := by
  intro events
  induction events with
  | nil => exact fun _ inv => inv
  | cons ev rest ih => exact fun s inv => ih _ (inv_apply fencedOn inv ev)

/-- **Every reachable state satisfies the invariant**, for every sequence of events: any crash,
loss, delay, duplication or reordering of messages. -/
theorem inv_reachable (fencedOn : fenced = true) {s : State V P C}
    (reach : Reachable quorum fenced valid s) : Inv (quorum := quorum) (valid := valid) s := by
  obtain ⟨events, rfl⟩ := reach
  exact inv_run fencedOn events _ inv_init

/-! ## Safety -/

section Safety

variable {s : State V P C} (system : QuorumSystem quorum)
include system

omit [DecidableEq V] [DecidableEq P] [DecidableEq C] [DecidablePred quorum] [(log : List C) → (c : C) → Decidable (valid log c)] in
/-- **One owner per epoch**: two candidates that send logs at one epoch are the same. -/
theorem one_owner_per_epoch (inv : Inv (quorum := quorum) (valid := valid) s) {who who' : P} {e : ℕ}
    {L L' : List C} (h : Msg.accept who e L ∈ s.sent) (h' : Msg.accept who' e L' ∈ s.sent) :
    who = who' := by
  obtain ⟨Q, _, _, isQ, reports, _, _⟩ := inv.accept_elected who e L h
  obtain ⟨Q', _, _, isQ', reports', _, _⟩ := inv.accept_elected who' e L' h'
  obtain ⟨a, inQ, inQ'⟩ := system Q Q' isQ isQ'
  obtain ⟨x, y, hx, -⟩ := reports a inQ
  obtain ⟨x', y', hx', -⟩ := reports' a inQ'
  exact (inv.promise_unique a who who' e x x' y y' hx hx').1

omit [DecidableEq V] [DecidableEq P] [DecidableEq C] [DecidablePred quorum] [(log : List C) → (c : C) → Decidable (valid log c)] in
/-- The logs sent at one epoch form a chain. -/
theorem accepts_comparable (inv : Inv (quorum := quorum) (valid := valid) s) {who who' : P} {e : ℕ}
    {L L' : List C} (h : Msg.accept who e L ∈ s.sent) (h' : Msg.accept who' e L' ∈ s.sent) :
    L <+: L' ∨ L' <+: L := by
  obtain rfl := one_owner_per_epoch system inv h h'
  exact inv.accept_chain who e L L' h h'

omit [DecidableEq V] [DecidableEq P] [DecidablePred quorum] [(log : List C) → (c : C) → Decidable (valid log c)] in
/-- **State transfer is complete**: a log chosen at an epoch is a prefix of every log sent at a
higher epoch. -/
theorem chosen_extends (inv : Inv (quorum := quorum) (valid := valid) s) :
    ∀ e', ∀ who L', Msg.accept who e' L' ∈ s.sent → ∀ e L, Chosen quorum s e L → e < e' → L <+: L' := by
  intro e'
  induction e' using Nat.strong_induction_on with
  | _ e' ih =>
    intro who L' h e L chosen lt
    obtain ⟨Q', ae, al, isQ', reports, ⟨b, _, reportedB⟩, pre⟩ := inv.accept_elected who e' L' h
    obtain ⟨Q, isQ, accepts⟩ := chosen
    obtain ⟨a, inQ, inQ'⟩ := system Q Q' isQ isQ'
    obtain ⟨La, acceptedA, preA⟩ := accepts a inQ
    obtain ⟨aeA, alA, promiseA, dom⟩ := reports a inQ'
    obtain ⟨_, curA, earlier⟩ := inv.promise_report a who e' aeA alA promiseA
    obtain ⟨geA, sameA⟩ := earlier e La acceptedA lt
    obtain ⟨ltB, curB, -⟩ := inv.promise_report b who e' ae al reportedB
    obtain ⟨w₀, srcA⟩ := inv.accepted_src a e La acceptedA
    have posE := (inv.accept_le w₀ e La srcA).1
    have geAdopted : e ≤ ae := by rcases dom with h | ⟨h, _⟩ <;> omega
    rcases Nat.lt_or_ge e ae with above | atMost
    · rcases curB with ⟨zero, _⟩ | acceptedB
      · omega
      · obtain ⟨w₁, srcB⟩ := inv.accepted_src b ae al acceptedB
        exact (ih ae ltB w₁ al srcB e L ⟨Q, isQ, accepts⟩ above).trans pre
    · have eqAe : ae = e := le_antisymm atMost geAdopted
      have aeAeq : aeA = e := by rcases dom with h | ⟨h, _⟩ <;> omega
      have lenA : alA.length ≤ al.length := by
        rcases dom with h | ⟨_, h⟩
        · omega
        · exact h
      have preLa : La <+: alA := sameA aeAeq.symm
      rcases curA with ⟨zero, _⟩ | acceptedAlA
      · omega
      · rcases curB with ⟨zero, _⟩ | acceptedB
        · omega
        · obtain ⟨w₂, srcAlA⟩ := inv.accepted_src a aeA alA acceptedAlA
          obtain ⟨w₁, srcB⟩ := inv.accepted_src b ae al acceptedB
          rw [aeAeq] at srcAlA
          rw [eqAe] at srcB
          have alAal : alA <+: al := by
            rcases accepts_comparable system inv srcAlA srcB with h | h
            · exact h
            · exact List.prefix_of_prefix_length_le (List.prefix_refl alA) h lenA
          exact preA.trans (preLa.trans (alAal.trans pre))

omit [DecidableEq V] [DecidableEq P] [DecidablePred quorum] [(log : List C) → (c : C) → Decidable (valid log c)] in
/-- **Every new owner's log extends everything chosen at or before its epoch**: nothing committed
is lost across failover. -/
theorem owner_extends_chosen (inv : Inv (quorum := quorum) (valid := valid) s) {who : P}
    {log : List C} (owner : (s.cand who).phase = .owner log) {e : ℕ} {L : List C}
    (chosen : Chosen quorum s e L) (atOrBefore : e ≤ (s.cand who).epoch) : L <+: log := by
  obtain ⟨present, maximal⟩ := inv.owner_max who log owner
  rcases Nat.lt_or_ge e (s.cand who).epoch with lt | ge
  · exact chosen_extends system inv _ who log present e L chosen lt
  · have eq : e = (s.cand who).epoch := le_antisymm atOrBefore ge
    obtain ⟨Q, isQ, accepts⟩ := chosen
    obtain ⟨a, inQ, -⟩ := system Q Q isQ isQ
    obtain ⟨L', acceptedL', pre⟩ := accepts a inQ
    obtain ⟨w, src⟩ := inv.accepted_src a e L' acceptedL'
    rw [eq] at src
    obtain rfl := one_owner_per_epoch system inv src present
    exact pre.trans (maximal L' src)

omit [DecidableEq V] [DecidableEq P] [DecidablePred quorum] [(log : List C) → (c : C) → Decidable (valid log c)] in
/-- **Chosen logs form one history**: of two chosen logs, one extends the other. -/
theorem chosen_comparable (inv : Inv (quorum := quorum) (valid := valid) s) {e₁ e₂ : ℕ}
    {L₁ L₂ : List C} (chosen₁ : Chosen quorum s e₁ L₁) (chosen₂ : Chosen quorum s e₂ L₂) :
    L₁ <+: L₂ ∨ L₂ <+: L₁ := by
  have witness : ∀ {e L}, Chosen quorum s e L → ∃ who L', Msg.accept who e L' ∈ s.sent ∧ L <+: L' := by
    intro e L chosen
    obtain ⟨Q, isQ, accepts⟩ := chosen
    obtain ⟨a, inQ, -⟩ := system Q Q isQ isQ
    obtain ⟨L', acceptedL', pre⟩ := accepts a inQ
    obtain ⟨w, src⟩ := inv.accepted_src a e L' acceptedL'
    exact ⟨w, L', src, pre⟩
  obtain ⟨w₁, L₁', src₁, pre₁⟩ := witness chosen₁
  obtain ⟨w₂, L₂', src₂, pre₂⟩ := witness chosen₂
  rcases lt_trichotomy e₁ e₂ with lt | rfl | gt
  · exact List.prefix_or_prefix_of_prefix (chosen_extends system inv e₂ w₂ L₂' src₂ e₁ L₁ chosen₁ lt) pre₂
  · rcases accepts_comparable system inv src₁ src₂ with h | h
    · exact List.prefix_or_prefix_of_prefix (pre₁.trans h) pre₂
    · exact List.prefix_or_prefix_of_prefix pre₁ (pre₂.trans h)
  · exact (List.prefix_or_prefix_of_prefix (chosen_extends system inv e₁ w₁ L₁' src₁ e₂ L₂ chosen₂ gt)
      pre₁).symm

omit [DecidableEq V] [DecidableEq P] [DecidableEq C] [DecidablePred quorum] [(log : List C) → (c : C) → Decidable (valid log c)] in
/-- **Chosen logs are admissible.** -/
theorem chosen_admissible (inv : Inv (quorum := quorum) (valid := valid) s) {e : ℕ} {L : List C}
    (chosen : Chosen quorum s e L) : Admissible valid L := by
  obtain ⟨Q, isQ, accepts⟩ := chosen
  obtain ⟨a, inQ, -⟩ := system Q Q isQ isQ
  obtain ⟨L', acceptedL', pre⟩ := accepts a inQ
  obtain ⟨w, src⟩ := inv.accepted_src a e L' acceptedL'
  exact (inv.accept_admissible w e L' src).prefix pre

end Safety

/-- **Fencing**: an acceptor that has promised a higher epoch refuses a stale owner's log. -/
theorem stale_accept_refused (fencedOn : fenced = true) (s : State V P C) {a : V} {who : P} {e : ℕ}
    {log : List C} (stale : e < (s.acc a).promised) :
    apply quorum fenced valid s (.accept a who e log) = s := by
  simp only [apply]
  rw [if_neg fun guard => by have := guard.2.1 fencedOn; omega]

/-! ### What is sent stays sent -/

theorem sent_apply (s : State V P C) (ev : Event V P C) :
    ∀ m ∈ s.sent, m ∈ (apply quorum fenced valid s ev).sent := by
  intro m member
  cases ev with
  | start who e => simp only [apply]; split_ifs <;> simp [member]
  | promise a who e => simp only [apply]; split_ifs <;> simp [member]
  | elect who Q ae al => simp only [apply]; split_ifs <;> simp [member]
  | propose who c =>
      simp only [apply]
      rcases (s.cand who).phase with _ | _ | log
      · exact member
      · exact member
      · simp only; split_ifs <;> simp [member]
  | accept a who e log => simp only [apply]; split_ifs <;> simp [member]

theorem sent_run (s : State V P C) :
    ∀ (events : List (Event V P C)), ∀ m ∈ s.sent, m ∈ (run quorum fenced valid s events).sent := by
  intro events
  induction events generalizing s with
  | nil => exact fun _ h => h
  | cons ev rest ih => exact fun m h => ih _ m (sent_apply s ev m h)

/-- **What is chosen stays chosen.** -/
theorem chosen_run {s : State V P C} {e : ℕ} {L : List C} (chosen : Chosen quorum s e L)
    (events : List (Event V P C)) : Chosen quorum (run quorum fenced valid s events) e L := by
  obtain ⟨Q, isQ, accepts⟩ := chosen
  refine ⟨Q, isQ, fun a inQ => ?_⟩
  obtain ⟨L', h, pre⟩ := accepts a inQ
  exact ⟨L', sent_run s events _ h, pre⟩

/-- **A committed log survives every later failover**: in every continuation, every owner of an
epoch at or after the commit extends it. -/
theorem committed_survives (fencedOn : fenced = true) (system : QuorumSystem quorum) {s : State V P C}
    (reach : Reachable quorum fenced valid s) {e : ℕ} {L : List C} (chosen : Chosen quorum s e L)
    (events : List (Event V P C)) {who : P} {log : List C}
    (owner : ((run quorum fenced valid s events).cand who).phase = .owner log)
    (later : e ≤ ((run quorum fenced valid s events).cand who).epoch) : L <+: log := by
  obtain ⟨before, rfl⟩ := reach
  have reach' : Reachable quorum fenced valid
      (run quorum fenced valid (run quorum fenced valid State.init before) events) :=
    ⟨before ++ events, (run_append _ before events).symm⟩
  exact owner_extends_chosen system (inv_reachable fencedOn reach') owner (chosen_run chosen events) later

/-! ## Over K's commits -/

section Commits

variable {O : Type*} [DecidableEq O] {R : Type*}
variable (label : O → R) (init : Finset O) (meaning : C → Commit O R)

/-- The store after a log. -/
def storeOf (log : List C) : Finset O := fireList init (log.map meaning)

/-- Every identity a log has used: the initial store and everything it made. -/
def bornOf (log : List C) : Finset O := init ∪ madeOf (log.map meaning)

/-- Everything a log has taken. -/
def takenOf : List C → Finset O
  | [] => ∅
  | c :: rest => (meaning c).taken ∪ takenOf rest

/-- **The owner admits a commit** when it is enabled at the store the log reaches and makes only
identities the log never used. -/
def commitValid (log : List C) (c : C) : Prop :=
  Enabled label (storeOf init meaning log) (meaning c) ∧ Disjoint (meaning c).made (bornOf init meaning log)

instance (log : List C) (c : C) : Decidable (commitValid label init meaning log c) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {label init meaning}

omit [DecidableEq C] in
theorem storeOf_snoc (log : List C) (c : C) :
    storeOf init meaning (log ++ [c]) = fire (storeOf init meaning log) (meaning c) := by
  simp [storeOf, fireList_append]

omit [DecidableEq C] in
theorem bornOf_snoc (log : List C) (c : C) :
    bornOf init meaning (log ++ [c]) = bornOf init meaning log ∪ (meaning c).made := by
  simp [bornOf, madeOf_append, madeOf, Finset.union_assoc]

omit [DecidableEq C] in
theorem takenOf_snoc (log : List C) (c : C) :
    takenOf meaning (log ++ [c]) = takenOf meaning log ∪ (meaning c).taken := by
  induction log with
  | nil => simp [takenOf]
  | cons d rest ih => simp [takenOf, ih, Finset.union_assoc]

omit [DecidableEq C] in
theorem mem_takenOf {log : List C} {o : O} : o ∈ takenOf meaning log ↔ ∃ c ∈ log, o ∈ (meaning c).taken := by
  induction log with
  | nil => simp [takenOf]
  | cons d rest ih => simp [takenOf, ih]

omit [DecidableEq C] in
/-- What a log takes is what its commits take (`OccurrenceCommits.takenOf`). -/
theorem takenOf_eq_map (log : List C) :
    takenOf meaning log = Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.takenOf
      (log.map meaning) := by
  induction log with
  | nil => rfl
  | cons d rest ih =>
      simp only [takenOf, List.map_cons, ih]
      rfl

omit [DecidableEq C] in
/-- **An admissible log is a run of the atomic semantics.** -/
theorem executable_of_admissible {log : List C} (admissible : Admissible (commitValid label init meaning) log) :
    Executable label init (log.map meaning) := by
  induction admissible with
  | nil => exact Executable.nil _
  | snoc _ ok ih =>
      rw [List.map_append, List.map_singleton, executable_snoc_iff]
      exact ⟨ih, ok.1⟩

omit [DecidableEq C] in
/-- What an admissible log keeps: its store and what it took are among the identities it used, and
nothing taken is in its store. -/
theorem admissible_bookkeeping {log : List C} (admissible : Admissible (commitValid label init meaning) log) :
    storeOf init meaning log ⊆ bornOf init meaning log ∧ takenOf meaning log ⊆ bornOf init meaning log ∧
      Disjoint (storeOf init meaning log) (takenOf meaning log) ∧
        (log.map fun c => (meaning c).taken).Pairwise Disjoint := by
  induction admissible with
  | nil =>
      refine ⟨Finset.subset_union_left, by simp [takenOf], by simp [takenOf], List.Pairwise.nil⟩
  | @snoc log c _ ok ih =>
      obtain ⟨storeBorn, takenBorn, apart, pairwise⟩ := ih
      obtain ⟨enabled, fresh⟩ := ok
      rw [storeOf_snoc, bornOf_snoc, takenOf_snoc]
      refine ⟨fun o member => ?_, fun o member => ?_, ?_, ?_⟩
      · rcases mem_fire.mp member with ⟨inStore, _⟩ | made
        · exact Finset.mem_union_left _ (storeBorn inStore)
        · exact Finset.mem_union_right _ made
      · rcases Finset.mem_union.mp member with old | new
        · exact Finset.mem_union_left _ (takenBorn old)
        · exact Finset.mem_union_left _ (storeBorn (enabled.taken_subset new))
      · refine Finset.disjoint_left.mpr fun o inStore inTaken => ?_
        rcases mem_fire.mp inStore with ⟨inOld, notNow⟩ | made
        · rcases Finset.mem_union.mp inTaken with old | new
          · exact Finset.disjoint_left.mp apart inOld old
          · exact notNow new
        · rcases Finset.mem_union.mp inTaken with old | new
          · exact Finset.disjoint_left.mp fresh made (takenBorn old)
          · exact Finset.disjoint_left.mp enabled.fresh made (enabled.taken_subset new)
      · rw [List.map_append, List.map_singleton, List.pairwise_append]
        refine ⟨pairwise, List.pairwise_singleton _ _, fun x inX y inY => ?_⟩
        rw [List.mem_singleton] at inY
        subst inY
        obtain ⟨d, inLog, rfl⟩ := List.mem_map.mp inX
        refine Finset.disjoint_left.mpr fun o inD inC => ?_
        exact Finset.disjoint_left.mp apart (enabled.taken_subset inC)
          (mem_takenOf.mpr ⟨d, inLog, inD⟩)

omit [DecidableEq C] in
/-- **No occurrence is taken twice in an admissible log.** -/
theorem takes_once {log : List C} (admissible : Admissible (commitValid label init meaning) log) :
    (log.map fun c => (meaning c).taken).Pairwise Disjoint :=
  (admissible_bookkeeping admissible).2.2.2

/-- **Every chosen log is a run of the atomic semantics**, in every reachable state of the failover
protocol over K's commits. -/
theorem chosen_legal (fencedOn : fenced = true) (system : QuorumSystem quorum) {s : State V P C}
    (reach : Reachable quorum fenced (commitValid label init meaning) s) {e : ℕ} {L : List C}
    (chosen : Chosen quorum s e L) : Executable label init (L.map meaning) :=
  executable_of_admissible (chosen_admissible system (inv_reachable fencedOn reach) chosen)

/-- **No occurrence is taken twice in the committed history**, across every failover. -/
theorem chosen_takes_once (fencedOn : fenced = true) (system : QuorumSystem quorum) {s : State V P C}
    (reach : Reachable quorum fenced (commitValid label init meaning) s) {e : ℕ} {L : List C}
    (chosen : Chosen quorum s e L) : (L.map fun c => (meaning c).taken).Pairwise Disjoint :=
  takes_once (chosen_admissible system (inv_reachable fencedOn reach) chosen)

end Commits

/-! ## Controls -/

namespace Controls

/-- Two commands over a one-token store: both take token `0`; one makes `1`, the other `2`. -/
def meaning : Bool → Commit ℕ ℕ
  | true => ⟨{0}, ∅, {1}, []⟩
  | false => ⟨{0}, ∅, {2}, []⟩

/-- The owner admits a command when its commit is enabled after the log. -/
abbrev admits : List Bool → Bool → Prop := commitValid id {0} meaning

/-- Quorums of one acceptor out of three: a minority suffices. -/
def minority (Q : Finset (Fin 3)) : Prop := 1 ≤ Q.card

instance : DecidablePred minority := fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- Two candidates each elected by a minority at epoch `1`, each committing a take of the token. -/
def minorityRun : List (Event (Fin 3) Bool Bool) :=
  [.start true 1, .start false 1, .promise 0 true 1, .promise 2 false 1,
    .elect true {0} 0 [], .elect false {2} 0 [], .propose true true, .propose false false,
    .accept 0 true 1 [true], .accept 2 false 1 [false]]

theorem minorityRun_sent :
    Msg.accepted 0 1 [true] ∈ (run minority true admits State.init minorityRun).sent ∧
      Msg.accepted 2 1 [false] ∈ (run minority true admits State.init minorityRun).sent := by
  decide

/-- **Minority owners take one token twice**: with quorums of one acceptor, two owners are elected
in one epoch, each gets its log chosen, the two chosen logs are not one history, and both take
token `0`. -/
theorem minority_double_take :
    Chosen minority (run minority true admits State.init minorityRun) 1 [true] ∧
      Chosen minority (run minority true admits State.init minorityRun) 1 [false] ∧
      ¬ ([true] <+: [false] ∨ [false] <+: [true]) ∧
      0 ∈ (meaning true).taken ∧ 0 ∈ (meaning false).taken := by
  refine ⟨⟨{0}, by decide, fun a inQ => ⟨[true], ?_, List.prefix_refl _⟩⟩,
    ⟨{2}, by decide, fun a inQ => ⟨[false], ?_, List.prefix_refl _⟩⟩, by decide, by decide, by decide⟩
  · rw [Finset.mem_singleton.mp inQ]; exact minorityRun_sent.1
  · rw [Finset.mem_singleton.mp inQ]; exact minorityRun_sent.2

theorem minority_not_quorumSystem : ¬ QuorumSystem minority := by
  intro system
  obtain ⟨a, inFirst, inSecond⟩ := system {0} {2} (by decide) (by decide)
  rw [Finset.mem_singleton.mp inFirst] at inSecond
  exact absurd inSecond (by decide)

/-- A stale owner and a new one. Candidate `true` owns epoch `1`; candidate `false` is elected at
epoch `2` by acceptors `1` and `2` before they hear of `true`'s log. Then `true` proposes and
acceptors `0` and `1` accept its log at epoch `1`, although `1` has promised epoch `2`; then
`false` proposes and acceptors `1` and `2` accept its log at epoch `2`. -/
def staleRun : List (Event (Fin 3) Bool Bool) :=
  [.start true 1, .promise 0 true 1, .promise 1 true 1, .elect true {0, 1} 0 [],
    .start false 2, .promise 1 false 2, .promise 2 false 2, .elect false {1, 2} 0 [],
    .propose true true, .accept 0 true 1 [true], .accept 1 true 1 [true],
    .propose false false, .accept 1 false 2 [false], .accept 2 false 2 [false]]

theorem staleRun_unfenced_sent :
    Msg.accepted 0 1 [true] ∈ (run (IsMajority (V := Fin 3)) false admits State.init staleRun).sent ∧
      Msg.accepted 1 1 [true] ∈ (run (IsMajority (V := Fin 3)) false admits State.init staleRun).sent ∧
      Msg.accepted 1 2 [false] ∈ (run (IsMajority (V := Fin 3)) false admits State.init staleRun).sent ∧
      Msg.accepted 2 2 [false] ∈ (run (IsMajority (V := Fin 3)) false admits State.init staleRun).sent := by
  decide

/-- **A stale owner without fencing takes the token twice**: with majorities but acceptors that do
not fence by promised epoch, the stale owner's log is chosen at epoch `1` and the new owner's log at
epoch `2`; they are not one history, and both take token `0`. -/
theorem unfenced_double_take :
    Chosen IsMajority (run (IsMajority (V := Fin 3)) false admits State.init staleRun) 1 [true] ∧
      Chosen IsMajority (run (IsMajority (V := Fin 3)) false admits State.init staleRun) 2 [false] ∧
      ¬ ([true] <+: [false] ∨ [false] <+: [true]) ∧
      0 ∈ (meaning true).taken ∧ 0 ∈ (meaning false).taken := by
  obtain ⟨h₀, h₁, h₁', h₂⟩ := staleRun_unfenced_sent
  refine ⟨⟨{0, 1}, by decide, fun a inQ => ⟨[true], ?_, List.prefix_refl _⟩⟩,
    ⟨{1, 2}, by decide, fun a inQ => ⟨[false], ?_, List.prefix_refl _⟩⟩, by decide, by decide,
    by decide⟩
  · rcases Finset.mem_insert.mp inQ with rfl | inQ
    · exact h₀
    · rw [Finset.mem_singleton.mp inQ]; exact h₁
  · rcases Finset.mem_insert.mp inQ with rfl | inQ
    · exact h₁'
    · rw [Finset.mem_singleton.mp inQ]; exact h₂

/-- **With fencing the stale log is refused**: in the same run, acceptor `1`, which promised epoch
`2`, does not accept the stale owner's log; the new owner's log is chosen. -/
theorem fenced_refuses_stale :
    Msg.accepted 1 1 [true] ∉ (run (IsMajority (V := Fin 3)) true admits State.init staleRun).sent ∧
      Msg.accepted 1 2 [false] ∈ (run (IsMajority (V := Fin 3)) true admits State.init staleRun).sent ∧
      Msg.accepted 2 2 [false] ∈ (run (IsMajority (V := Fin 3)) true admits State.init staleRun).sent := by
  decide

/-- **Quorum system, positive**: the majorities of three acceptors pairwise meet.
(`minority_not_quorumSystem` is the negative control.) -/
theorem majorities_quorumSystem : QuorumSystem (IsMajority (V := Fin 3)) := majority_quorumSystem

/-! ### Messages, guards, logs and states -/

/-- A promise from acceptor `0` to candidate `true` at epoch `1` is one; a prepare is not. -/
theorem isPromiseFor_controls :
    (Msg.promise 0 true 1 0 [] : Msg (Fin 3) Bool Bool).IsPromiseFor 0 true 1 ∧
      ¬ (Msg.prepare true 1 : Msg (Fin 3) Bool Bool).IsPromiseFor 0 true 1 := by
  decide

/-- A promise reporting nothing accepted is below the empty report; one reporting epoch `2` is not
below a report of epoch `1`. -/
theorem belowReport_controls :
    (Msg.promise 0 true 1 0 [] : Msg (Fin 3) Bool Bool).BelowReport 0 true 1 0 [] ∧
      ¬ (Msg.promise 0 true 1 2 [] : Msg (Fin 3) Bool Bool).BelowReport 0 true 1 1 [] := by
  decide

/-- Candidate `true` has started epoch `1`, and acceptors `0` and `1` promised it. -/
def promisedTwo : State (Fin 3) Bool Bool :=
  run (IsMajority (V := Fin 3)) true admits State.init
    [.start true 1, .promise 0 true 1, .promise 1 true 1]

/-- **Elections**: the two acceptors that promised elect the candidate; one alone is not a
majority, and all three include one that has not promised. -/
theorem electOK_controls :
    ElectOK IsMajority promisedTwo true {0, 1} 0 [] ∧
      ¬ ElectOK IsMajority promisedTwo true {0} 0 [] ∧
      ¬ ElectOK IsMajority promisedTwo true Finset.univ 0 [] := by
  decide

/-- The stale run up to the stale owner's proposal. -/
def beforeStaleAccepts (fenced : Bool) : State (Fin 3) Bool Bool :=
  run (IsMajority (V := Fin 3)) fenced admits State.init (staleRun.take 9)

/-- **Acceptances**: acceptor `0` may accept the stale owner's log; acceptor `1`, which promised
epoch `2`, may not when acceptors fence, and may when they do not. -/
theorem acceptOK_controls :
    AcceptOK true (beforeStaleAccepts true) 0 true 1 [true] ∧
      ¬ AcceptOK true (beforeStaleAccepts true) 1 true 1 [true] ∧
      AcceptOK false (beforeStaleAccepts false) 1 true 1 [true] := by
  decide

/-- **The owner admits** the first take of the token, and not a second. -/
theorem commitValid_controls : admits [] true ∧ ¬ admits [true] false := by decide

/-- **Admissible logs**: one take of the token is; two are not. -/
theorem admissible_controls : Admissible admits [true] ∧ ¬ Admissible admits [true, false] := by
  refine ⟨.snoc (log := []) .nil (by decide), fun h => ?_⟩
  exact (by decide : ¬ admits [true] false) ((Admissible.snoc_iff (log := [true])).mp h).2

/-- A state holding an acceptance that no owner sent. -/
def forged : State (Fin 3) Bool Bool := { State.init with sent := [.accepted 0 1 [true]] }

/-- **Reachable states and the invariant**: the fenced stale run reaches a state, and that state
satisfies the invariant; a state holding an acceptance no owner sent satisfies neither. -/
theorem reachable_inv_controls :
    Reachable IsMajority true admits (run (IsMajority (V := Fin 3)) true admits State.init staleRun) ∧
      Inv (quorum := IsMajority) (valid := admits)
        (run (IsMajority (V := Fin 3)) true admits State.init staleRun) ∧
      ¬ Inv (quorum := IsMajority (V := Fin 3)) (valid := admits) forged ∧
      ¬ Reachable IsMajority true admits forged := by
  have notInv : ¬ Inv (quorum := IsMajority (V := Fin 3)) (valid := admits) forged := fun inv => by
    obtain ⟨who, sent⟩ := inv.accepted_src 0 1 [true] (by simp [forged])
    simp [forged] at sent
  exact ⟨⟨staleRun, rfl⟩, inv_reachable rfl ⟨staleRun, rfl⟩, notInv,
    fun reach => notInv (inv_reachable rfl reach)⟩

end Controls

end Mettapedia.GSLT.Coordination.OwnerFailover
