/-!
# Replyable messages and retained ask continuations

The interface creates one identity for the outgoing question and its receive.
The native receive retains the task and continuation note. A matching first
reply fills that receive; unrelated replies and later duplicates leave it alone.
Repeating a saved ask observes it and emits no publication.

This specifies matching and recovery data, not filesystem durability, foreign
implementation refinement, sender authentication or the truth of message bodies.
Native integration fixtures check registration before immediate publication,
restart, duplicate delivery, failed publication and return routing separately.
-/

namespace PettaClaw.ReplyableMailbox

structure Frame where
  identity : Nat
  task : Nat
  note : String
  deriving DecidableEq, Repr

structure Message where
  identity : Nat
  correlation : Nat
  sender : Nat
  returnAddress : Option Nat
  body : String
  deriving DecidableEq, Repr

inductive Publication where
  | published | failed | unknown
  deriving DecidableEq, Repr

structure Ask where
  frame : Frame
  publication : Publication
  reply : Option Message := none
  deriving DecidableEq, Repr

/-- The model supplies task and note; one created identity serves both ends. -/
def register (identity task : Nat) (note : String) : Ask :=
  ⟨⟨identity, task, note⟩, .unknown, none⟩

/-- Publication state is evidence, not permission to retry. -/
def publicationResult (a : Ask) (p : Publication) : Ask :=
  { a with publication := p }

/-- A first matching response preserves the exact frame captured at request. -/
def receive (a : Ask) (m : Message) : Ask :=
  if a.reply.isNone && (m.correlation == a.frame.identity) then
    { a with reply := some m }
  else a

def resume (a : Ask) : Option (Frame × Message) :=
  a.reply.map (fun m => (a.frame, m))

/-- Return routing uses the stored message header, never body prose. -/
def replyAddress (m : Message) : Option Nat := m.returnAddress

/-- Restoring a checkpoint retains the complete ask, including unknown state. -/
structure Checkpoint where
  asks : List Ask

def restore (s : Checkpoint) : List Ask := s.asks

/-- Reissuing an existing handle is inspection. A new handle is a new request. -/
def repeatAsk (a : Ask) : Ask × List Nat := (a, [])

theorem registered_matching_identity (identity task : Nat) (note : String) :
    (register identity task note).frame.identity = identity := rfl

theorem receive_preserves_frame (a : Ask) (m : Message) :
    (receive a m).frame = a.frame := by
  unfold receive
  split <;> rfl

theorem publication_preserves_continuation (a : Ask) (p : Publication) :
    (publicationResult a p).frame = a.frame := rfl

theorem unrelated_reply_leaves_ask (a : Ask) (m : Message)
    (different : m.correlation ≠ a.frame.identity) : receive a m = a := by
  simp [receive, different]

theorem first_matching_reply (a : Ask) (m : Message)
    (empty : a.reply = none) (matching : m.correlation = a.frame.identity) :
    resume (receive a m) = some (a.frame, m) := by
  simp [receive, resume, empty, matching]

theorem received_reply_is_stable (a : Ask) (m prior : Message)
    (filled : a.reply = some prior) : receive a m = a := by
  simp [receive, filled]

theorem duplicate_reply_is_idempotent (a : Ask) (m : Message) :
    receive (receive a m) m = receive a m := by
  unfold receive
  split <;> simp_all

theorem unrelated_requests_unchanged (asks : List Ask) (m : Message)
    (different : ∀ a ∈ asks, m.correlation ≠ a.frame.identity) :
    asks.map (fun a => receive a m) = asks := by
  induction asks with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons]
    rw [unrelated_reply_leaves_ask a m (different a (by simp))]
    rw [ih (fun b hb => different b (by simp [hb]))]

theorem repeated_ask_does_not_publish (a : Ask) : (repeatAsk a).2 = [] := rfl

theorem restart_retains_all_asks (s : Checkpoint) : restore s = s.asks := rfl

theorem return_route_ignores_body (m : Message) (body : String) :
    replyAddress { m with body := body } = replyAddress m := rfl

#print axioms receive_preserves_frame
#print axioms unrelated_reply_leaves_ask
#print axioms first_matching_reply
#print axioms duplicate_reply_is_idempotent
#print axioms unrelated_requests_unchanged

end PettaClaw.ReplyableMailbox
