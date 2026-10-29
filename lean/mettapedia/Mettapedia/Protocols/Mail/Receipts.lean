import Mettapedia.Protocols.Mail.Mailbox

/-!
# Receipts: none for a receipt, one for each fact

Two kinds of receipt report what became of a message: delivery status
notifications (DSNs, RFC 3461 and RFC 3464), here only the success DSN with the
action `delivered`, and message disposition notifications (MDNs, RFC 8098).
The rules that bound them:
- RFC 3461 §4.1: a success DSN is issued on successful delivery, when the
  sender asked for one (`NOTIFY=SUCCESS`).
- RFC 8098 §2.1: a user agent issues at most one MDN for each recipient, even
  if another disposition is performed on the message.
- No receipt requests one. A DSN is sent with the null reverse-path, and with
  `NOTIFY=NEVER` if it carries `NOTIFY` at all (RFC 3461 §6.1). An MDN is sent
  with the null reverse-path and without `Disposition-Notification-To`, and no
  MDN is generated in response to an MDN (RFC 8098 §2.1, §3).

The model: the recipient runs a `Mail.Mailbox`. Filing a message is
`Mailbox.deliver`, and disposing of it (RFC 8098 §3.2.6.2: displayed, deleted,
dispatched, processed) is `Mailbox.ack`. A message that requested receipts
draws a delivery receipt when it is first filed and a disposition receipt when
it is first disposed of.

The theorems:
- `deliveries_le_one`, `dispositions_le_one`, `receipts_le_two`: over any
  sequence of filings and dispositions, repeats included, a message draws at
  most one receipt of each kind, so at most two.
- `unrequested_none`: a message that requested none draws none.
- `generation_ends`: since receipts request none, the receipts started by one
  message are its two, and the next generation is empty.
- Mutants: a recipient that does not remember what it reported answers every
  disposition (`forgetful_three`), and receipts that request receipts double
  each generation for ever (`sorcerer`).

Not modelled: delays and failures (`DeliveryStatus`), forwarding, the
recipient's consent, and transport.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Mail.Receipts

open Mettapedia.Protocols.Mail

/-- The disposition types of RFC 8098 §3.2.6.2. -/
inductive Disposition
  | displayed
  | deleted
  | dispatched
  | processed
deriving DecidableEq, Repr

/-- What a receipt reports: delivery (a success DSN) or a disposition (an MDN). -/
inductive Fact
  | delivered
  | disposed (d : Disposition)
deriving DecidableEq, Repr

/-- A receipt: the message it is about and the fact it reports. -/
structure Receipt where
  about : MessageId
  fact : Fact
deriving DecidableEq, Repr

/-- A delivery receipt about `id`. -/
def Receipt.deliveryOf (id : MessageId) (r : Receipt) : Bool := r.about == id && r.fact == .delivered

/-- A disposition receipt about `id`. -/
def Receipt.dispositionOf (id : MessageId) (r : Receipt) : Bool := r.about == id && r.fact != .delivered

/-- What the recipient does: file a message, or dispose of a filed one. -/
inductive Op
  | file (m : Message)
  | dispose (id : MessageId) (d : Disposition)

/-- One operation and the receipts it issues; `wants` names the messages that
requested receipts. With `once`, each fact is reported only the first time. -/
def step (once : Bool) (wants : MessageId → Bool) (b : Mailbox) : Op → Mailbox × List Receipt
  | .file m =>
    (b.deliver m, if wants m.id && (!once || decide (m.id ∉ b.ids)) then [⟨m.id, .delivered⟩] else [])
  | .dispose id d =>
    (b.ack id, if wants id && decide (id ∈ b.ids) && (!once || decide (id ∉ b.seen))
      then [⟨id, .disposed d⟩] else [])

/-- A sequence of operations: the final mailbox and every receipt, in order. -/
def run (once : Bool) (wants : MessageId → Bool) : Mailbox → List Op → Mailbox × List Receipt
  | b, [] => (b, [])
  | b, op :: ops =>
    ((run once wants (step once wants b op).1 ops).1,
      (step once wants b op).2 ++ (run once wants (step once wants b op).1 ops).2)

/-! ## The mailbox remembers -/

theorem deliver_seen (b : Mailbox) (m : Message) : (b.deliver m).seen = b.seen := by
  unfold Mailbox.deliver; split <;> rfl

theorem ack_ids (b : Mailbox) (id : MessageId) : (b.ack id).ids = b.ids := by
  simp [Mailbox.ids, Mailbox.ack_stored]

theorem ack_keeps_seen (b : Mailbox) (id : MessageId) {x : MessageId} (h : x ∈ b.seen) :
    x ∈ (b.ack id).seen := by
  unfold Mailbox.ack; split
  · exact List.mem_append_left _ h
  · exact h

theorem ack_seen (b : Mailbox) {id : MessageId} (h : id ∈ b.ids) : id ∈ (b.ack id).seen := by
  unfold Mailbox.ack; split
  · simp
  · next hn =>
    by_contra hs
    exact hn ⟨h, hs⟩

/-! ## At most one receipt for each fact -/

/-- One while the message is not filed, then zero. -/
def unfiled (id : MessageId) (b : Mailbox) : Nat := if id ∈ b.ids then 0 else 1

/-- One while the message is not disposed of, then zero. -/
def undisposed (id : MessageId) (b : Mailbox) : Nat := if id ∈ b.seen then 0 else 1

theorem unfiled_le (id : MessageId) (b : Mailbox) : unfiled id b ≤ 1 := by
  unfold unfiled; split <;> omega

theorem undisposed_le (id : MessageId) (b : Mailbox) : undisposed id b ≤ 1 := by
  unfold undisposed; split <;> omega

theorem singleton_or_nil_le {c : Bool} (r : Receipt) (p : Receipt → Bool) :
    ((if c = true then [r] else []).filter p).length ≤ 1 := by
  split
  · exact le_trans (List.length_filter_le _ _) (by simp)
  · simp

theorem deliveries_step (wants : MessageId → Bool) (id : MessageId) (b : Mailbox) (op : Op) :
    ((step true wants b op).2.filter (Receipt.deliveryOf id)).length +
      unfiled id (step true wants b op).1 ≤ unfiled id b := by
  cases op with
  | file m =>
    show ((if (wants m.id && (!true || decide (m.id ∉ b.ids))) = true
        then [(⟨m.id, .delivered⟩ : Receipt)] else []).filter (Receipt.deliveryOf id)).length +
      unfiled id (b.deliver m) ≤ unfiled id b
    have hle := singleton_or_nil_le (c := wants m.id && (!true || decide (m.id ∉ b.ids)))
      (⟨m.id, .delivered⟩ : Receipt) (Receipt.deliveryOf id)
    by_cases hm : m.id = id
    · subst hm
      have h1 : m.id ∈ (b.deliver m).ids := Mailbox.deliver_holds b m
      by_cases hb : m.id ∈ b.ids
      · simp [unfiled, hb, h1]
      · rw [show unfiled m.id (b.deliver m) = 0 by simp [unfiled, h1],
          show unfiled m.id b = 1 by simp [unfiled, hb]]
        omega
    · have h0 : ((if (wants m.id && (!true || decide (m.id ∉ b.ids))) = true
          then [(⟨m.id, .delivered⟩ : Receipt)] else []).filter (Receipt.deliveryOf id)) = [] := by
        split <;> simp [Receipt.deliveryOf, hm]
      rw [h0]
      by_cases hb : id ∈ b.ids
      · simp [unfiled, hb, Mailbox.deliver_keeps b m hb]
      · simpa [unfiled, hb] using unfiled_le id (b.deliver m)
  | dispose x d =>
    show ((if (wants x && decide (x ∈ b.ids) && (!true || decide (x ∉ b.seen))) = true
        then [(⟨x, .disposed d⟩ : Receipt)] else []).filter (Receipt.deliveryOf id)).length +
      unfiled id (b.ack x) ≤ unfiled id b
    have h0 : ((if (wants x && decide (x ∈ b.ids) && (!true || decide (x ∉ b.seen))) = true
        then [(⟨x, .disposed d⟩ : Receipt)] else []).filter (Receipt.deliveryOf id)) = [] := by
      split <;> simp [Receipt.deliveryOf]
    rw [h0]
    simp [unfiled, ack_ids]

theorem dispositions_step (wants : MessageId → Bool) (id : MessageId) (b : Mailbox) (op : Op) :
    ((step true wants b op).2.filter (Receipt.dispositionOf id)).length +
      undisposed id (step true wants b op).1 ≤ undisposed id b := by
  cases op with
  | file m =>
    show ((if (wants m.id && (!true || decide (m.id ∉ b.ids))) = true
        then [(⟨m.id, .delivered⟩ : Receipt)] else []).filter (Receipt.dispositionOf id)).length +
      undisposed id (b.deliver m) ≤ undisposed id b
    have h0 : ((if (wants m.id && (!true || decide (m.id ∉ b.ids))) = true
        then [(⟨m.id, .delivered⟩ : Receipt)] else []).filter (Receipt.dispositionOf id)) = [] := by
      split <;> simp [Receipt.dispositionOf]
    rw [h0]
    simp [undisposed, deliver_seen]
  | dispose x d =>
    show ((if (wants x && decide (x ∈ b.ids) && (!true || decide (x ∉ b.seen))) = true
        then [(⟨x, .disposed d⟩ : Receipt)] else []).filter (Receipt.dispositionOf id)).length +
      undisposed id (b.ack x) ≤ undisposed id b
    have hle := singleton_or_nil_le (c := wants x && decide (x ∈ b.ids) && (!true || decide (x ∉ b.seen)))
      (⟨x, .disposed d⟩ : Receipt) (Receipt.dispositionOf id)
    by_cases hx : x = id
    · subst hx
      by_cases hs : x ∈ b.seen
      · simp [undisposed, hs, ack_keeps_seen b x hs]
      · by_cases hi : x ∈ b.ids
        · rw [show undisposed x (b.ack x) = 0 by simp [undisposed, ack_seen b hi],
            show undisposed x b = 1 by simp [undisposed, hs]]
          omega
        · have hb : b.ack x = b := by unfold Mailbox.ack; simp [hi]
          simp [undisposed, hs, hi, hb]
    · have h0 : ((if (wants x && decide (x ∈ b.ids) && (!true || decide (x ∉ b.seen))) = true
          then [(⟨x, .disposed d⟩ : Receipt)] else []).filter (Receipt.dispositionOf id)) = [] := by
        split <;> simp [Receipt.dispositionOf, hx]
      rw [h0]
      by_cases hs : id ∈ b.seen
      · simp [undisposed, hs, ack_keeps_seen b x hs]
      · simpa [undisposed, hs] using undisposed_le id (b.ack x)

/-- Over any sequence of operations, a message draws at most one delivery
receipt, and none once it is filed. -/
theorem deliveries_le_one (wants : MessageId → Bool) (id : MessageId) :
    ∀ (ops : List Op) (b : Mailbox),
      ((run true wants b ops).2.filter (Receipt.deliveryOf id)).length ≤ unfiled id b
  | [], b => by simp [run]
  | op :: ops, b => by
    have ih := deliveries_le_one wants id ops (step true wants b op).1
    have hs := deliveries_step wants id b op
    simp only [run, List.filter_append, List.length_append]
    omega

/-- Over any sequence of operations, a message draws at most one disposition
receipt, whatever dispositions follow (RFC 8098 §2.1). -/
theorem dispositions_le_one (wants : MessageId → Bool) (id : MessageId) :
    ∀ (ops : List Op) (b : Mailbox),
      ((run true wants b ops).2.filter (Receipt.dispositionOf id)).length ≤ undisposed id b
  | [], b => by simp [run]
  | op :: ops, b => by
    have ih := dispositions_le_one wants id ops (step true wants b op).1
    have hs := dispositions_step wants id b op
    simp only [run, List.filter_append, List.length_append]
    omega

theorem filter_about (id : MessageId) (rs : List Receipt) :
    (rs.filter (·.about == id)).length =
      (rs.filter (Receipt.deliveryOf id)).length + (rs.filter (Receipt.dispositionOf id)).length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.filter_cons, Receipt.deliveryOf, Receipt.dispositionOf] at ih ⊢
    by_cases ha : r.about = id <;> by_cases hf : r.fact = .delivered <;> simp_all <;> omega

/-- **At most two receipts per message**: one delivery, one disposition. -/
theorem receipts_le_two (wants : MessageId → Bool) (id : MessageId) (ops : List Op) (b : Mailbox) :
    ((run true wants b ops).2.filter (·.about == id)).length ≤ 2 := by
  rw [filter_about]
  have h1 := deliveries_le_one wants id ops b
  have h2 := dispositions_le_one wants id ops b
  have := unfiled_le id b
  have := undisposed_le id b
  omega

/-- A message that requested no receipts draws none. -/
theorem unrequested_none {wants : MessageId → Bool} {id : MessageId} (h : wants id = false) :
    ∀ (ops : List Op) (b : Mailbox), (run true wants b ops).2.filter (·.about == id) = []
  | [], _ => rfl
  | op :: ops, b => by
    simp only [run, List.filter_append, unrequested_none h ops, List.append_nil]
    cases op with
    | file m =>
      simp only [step]
      split
      · next hw =>
        have : m.id ≠ id := fun e => by rw [e, h] at hw; simp at hw
        simp [this]
      · rfl
    | dispose x d =>
      simp only [step]
      split
      · next hw =>
        have : x ≠ id := fun e => by rw [e, h] at hw; simp at hw
        simp [this]
      · rfl

/-! ## Examples -/

/-- A message from `a` to `b`. -/
def hello : Message := ⟨"m", "a", ["b"], 0, "", [], [], ""⟩

/-- Filed three times and disposed of three ways, a message that asked for
receipts draws exactly its two: the bound is met. -/
example : (run true (fun _ => true) Mailbox.empty
    [.file hello, .dispose "m" .displayed, .file hello, .dispose "m" .deleted, .file hello,
      .dispose "m" .processed]).2 = [⟨"m", .delivered⟩, ⟨"m", .disposed .displayed⟩] := by decide

/-- A message that requested none draws none, filed and disposed of: the
hypothesis of `unrequested_none` meets. -/
example : (run true (fun _ => false) Mailbox.empty [.file hello, .dispose "m" .displayed]).2 = [] := by
  decide

/-- A recipient that does not remember what it reported answers every
disposition: three receipts where the rule allows one. -/
theorem forgetful_three : ((run false (fun _ => true) Mailbox.empty
    [.file hello, .dispose "m" .displayed, .dispose "m" .deleted, .dispose "m" .processed]).2.filter
      (·.about == "m")).length = 4 := by decide

/-! ## Generations of receipts -/

/-- A note in an exchange: an original message, or a receipt about a note. -/
inductive Note
  | original
  | receipt (about : Note) (fact : Fact)
deriving DecidableEq, Repr

/-- The rule: the original may request receipts, a receipt requests none. -/
def rules : Note → Bool
  | .original => true
  | .receipt _ _ => false

/-- What a note draws from a recipient that files it and displays it: its two
receipts, when it requested receipts. -/
def draws (wants : Note → Bool) (n : Note) : List Note :=
  if wants n then [.receipt n .delivered, .receipt n (.disposed .displayed)] else []

/-- The notes of the `k`-th generation started by one message. -/
def generation (wants : Note → Bool) : Nat → List Note
  | 0 => [.original]
  | k + 1 => (generation wants k).flatMap (draws wants)

/-- `draws` is what the recipient's run issues for a message filed and then
displayed. -/
example : (run true (fun _ => true) Mailbox.empty [.file hello, .dispose "m" .displayed]).2.length =
    (draws rules .original).length := by decide

/-- **Generation ends**: one message draws its two receipts, and they draw
nothing. -/
theorem generation_ends : (generation rules 1).length = 2 ∧ ∀ k, 2 ≤ k → generation rules k = [] := by
  refine ⟨by decide, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  induction j with
  | zero => decide
  | succ j ih =>
    show (generation rules (j + 2)).flatMap (draws rules) = []
    rw [ih (by omega)]
    rfl

/-- **Sorcerer's apprentice** (RFC 3834 §1): receipts that request receipts
double each generation, so generation never ends. -/
theorem sorcerer (k : Nat) : (generation (fun _ => true) k).length = 2 ^ k := by
  have double : ∀ l : List Note, (l.flatMap (draws fun _ => true)).length = 2 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons n l ih => simp [List.flatMap_cons, draws, ih]; omega
  induction k with
  | zero => rfl
  | succ k ih =>
    show ((generation (fun _ => true) k).flatMap (draws fun _ => true)).length = 2 ^ (k + 1)
    rw [double, ih, Nat.pow_succ, Nat.mul_comm]

end Mettapedia.Protocols.Mail.Receipts
