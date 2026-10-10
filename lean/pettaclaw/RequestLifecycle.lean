import Init

/-!
# Delivery lifecycle and retained work

The original protected strategy models task fulfillment. This separate layer
models message processing and agent workflow dispositions, which are not
fulfillment certificates. Input settlement requires a successful provider
turn, durable history and durable handover. Issued effects remain in the
separate action ledger. Bounded views retain their underlying records.

The draining theorem is conditional on successful durable boundaries, no
additional arrivals, and service of the queued heads. It is not a theorem
that arbitrary tasks terminate or that network delivery is guaranteed.
-/
namespace RequestLifecycle

inductive Kind where
  | message | notification | task | goal | autonomous
deriving Repr, DecidableEq

inductive Status where
  | active | processed | waitingUser | deferred | addressed | achieved | cancelled
deriving Repr, DecidableEq

structure Request where
  id : Nat
  content : Nat
  kind : Kind
  status : Status := .active
  processed : Bool := false
  certified : Bool := false
deriving Repr, DecidableEq

structure Boundary where
  providerSucceeded : Bool
  historyDurable : Bool
  handoverDurable : Bool
deriving Repr, DecidableEq

def complete (b : Boundary) : Bool :=
  b.providerSucceeded && b.historyDurable && b.handoverDurable

def settleInput (r : Request) (b : Boundary) : Request :=
  if complete b && (r.kind == .message || r.kind == .notification) then
    { r with processed := true, status := if r.status == .active then .processed else r.status }
  else r

def workflow (r : Request) (status : Status) : Request :=
  if status ∈ [Status.active, .waitingUser, .deferred, .addressed] then
    { r with status := status }
  else r

theorem processing_is_not_certification (r : Request) (b : Boundary) :
    (settleInput r b).certified = r.certified := by
  simp only [settleInput]; split <;> rfl

theorem processing_preserves_identity (r : Request) (b : Boundary) :
    (settleInput r b).id = r.id := by simp only [settleInput]; split <;> rfl

theorem processing_preserves_content (r : Request) (b : Boundary) :
    (settleInput r b).content = r.content := by simp only [settleInput]; split <;> rfl

theorem incomplete_boundary_stutters (r : Request) (b : Boundary)
    (h : complete b = false) : settleInput r b = r := by simp [settleInput, h]

theorem task_is_not_settled_as_input (r : Request) (b : Boundary)
    (h : r.kind = .task) : settleInput r b = r := by simp [settleInput, h]

theorem workflow_does_not_certify (r : Request) (status : Status) :
    (workflow r status).certified = r.certified := by
  simp only [workflow]; split <;> rfl

theorem workflow_cannot_claim_achievement (r : Request) :
    workflow r .achieved = r := by simp [workflow]

def activeView (records : List Request) (limit : Nat) : List Request := records.take limit

theorem bounded_view (records : List Request) (limit : Nat) :
    (activeView records limit).length ≤ limit := by
  exact List.length_take_le _ _

theorem view_and_remainder_reconstruct (records : List Request) (limit : Nat) :
    activeView records limit ++ records.drop limit = records := by
  exact List.take_append_drop _ _

structure Queue where
  pending : List Nat
  retained : List Request
deriving Repr, DecidableEq

def acknowledgeHead (q : Queue) (durable : Bool) : Queue :=
  if durable then { q with pending := q.pending.tail } else q

def serve (fuel : Nat) (q : Queue) (durable : Bool) : Queue :=
  match fuel with
  | 0 => q
  | n + 1 => serve n (acknowledgeHead q durable) durable

theorem handover_preserves_retained_work (q : Queue) (durable : Bool) :
    (acknowledgeHead q durable).retained = q.retained := by
  simp only [acknowledgeHead]; split <;> rfl

theorem successful_heads_eventually_drain (pending : List Nat) (records : List Request) :
    (serve pending.length ⟨pending, records⟩ true).pending = [] := by
  induction pending with
  | nil => rfl
  | cons head tail ih => simpa [serve, acknowledgeHead] using ih

theorem no_durable_progress_keeps_queue (fuel : Nat) (q : Queue) :
    serve fuel q false = q := by
  induction fuel with
  | zero => rfl
  | succ n ih => simpa [serve, acknowledgeHead] using ih

example : complete ⟨true, false, true⟩ = false := rfl
example : workflow { id := 1, content := 2, kind := .task } .achieved =
    { id := 1, content := 2, kind := .task } := by decide

end RequestLifecycle
