import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded

/-!
# Mail messages and threads (RFC 5322)

An internet message as RFC 5322 §3.6 shapes its header: a unique message
identifier, the originator, the recipients, a date, a subject, and the
identification fields `In-Reply-To` and `References` that thread replies. Only
the semantic content is modelled, not the field grammar, folding or encoded
words. That is enough to read other agent mail systems as mail: claw-mail's
space records and Nostr's signed events both map onto these fields.

The theorem is about threads. RFC 5322 §3.6.4 requires message identifiers to
be unique. When, in addition, every message names as parents only messages
delivered before it, the reply relation is well founded: threads form a forest
and no reply chain loops. Uniqueness within a log is an explicit hypothesis
here, since a log may receive the same message twice; deduplication is the
mailbox's job (`Mail.Mailbox`).
-/

namespace Mettapedia.Protocols.Mail

/-- The mailbox part of an RFC 5322 `addr-spec`; a display name is presentation. -/
abbrev Address := String

/-- The content of a `msg-id`. -/
abbrev MessageId := String

/-- An internet message, by the meaning of its header fields. -/
structure Message where
  id : MessageId
  originator : Address
  recipients : List Address
  /-- The `Date:` field, in seconds since the epoch. -/
  date : Nat
  subject : String
  inReplyTo : List MessageId
  references : List MessageId
  body : String
deriving DecidableEq, Repr

/-- The parents a message names: `In-Reply-To` together with `References`. -/
def Message.parents (m : Message) : List MessageId := m.inReplyTo ++ m.references

/-- A log of messages in delivery order, oldest first. -/
abbrev Log := List Message

/-- Every parent a message names was delivered earlier in the log. -/
def Causal (log : Log) : Prop :=
  ∀ (i : Fin log.length), ∀ p ∈ (log.get i).parents,
    ∃ j : Fin log.length, j < i ∧ (log.get j).id = p

/-- Message `j` is a parent of message `i` in the log. -/
def ReplyTo (log : Log) (j i : Fin log.length) : Prop :=
  (log.get j).id ∈ (log.get i).parents

/-- Distinct positions of a log with unique identifiers hold distinct identifiers. -/
theorem eq_of_id_eq {log : Log} (unique : (log.map Message.id).Nodup)
    {j k : Fin log.length} (h : (log.get j).id = (log.get k).id) : j = k := by
  have hj : j.val < (log.map Message.id).length := by simp
  have hk : k.val < (log.map Message.id).length := by simp
  have := (List.Nodup.getElem_inj_iff unique (i := j.val) (j := k.val) (hi := hj) (hj := hk)).mp
    (by simpa using h)
  exact Fin.ext this

/-- In a causal log with unique identifiers, a parent comes before its reply. -/
theorem replyTo_lt {log : Log} (causal : Causal log) (unique : (log.map Message.id).Nodup)
    {j i : Fin log.length} (h : ReplyTo log j i) : j < i := by
  obtain ⟨j', earlier, same⟩ := causal i _ h
  have : j' = j := eq_of_id_eq unique same
  exact this ▸ earlier

/-- Threads form a forest: the reply relation of a causal log with unique
identifiers is well founded. -/
theorem replyTo_wellFounded {log : Log} (causal : Causal log)
    (unique : (log.map Message.id).Nodup) : WellFounded (ReplyTo log) :=
  Subrelation.wf (fun h => replyTo_lt causal unique h) (InvImage.wf (fun i : Fin log.length => i.val)
    Nat.lt_wfRel.wf)

/-- No message is its own ancestor. -/
theorem no_reply_cycle {log : Log} (causal : Causal log) (unique : (log.map Message.id).Nodup)
    (i : Fin log.length) : ¬ Relation.TransGen (ReplyTo log) i i := by
  intro cycle
  have lt : ∀ {a b}, Relation.TransGen (ReplyTo log) a b → a.val < b.val := by
    intro a b h
    induction h with
    | single h => exact replyTo_lt causal unique h
    | tail _ h ih => exact Nat.lt_trans ih (replyTo_lt causal unique h)
  exact Nat.lt_irrefl _ (lt cycle)

/-- Uniqueness is needed: two copies of one identifier let a message reply to a
later copy of itself. -/
example : ∃ log : Log, Causal log ∧ ¬ (log.map Message.id).Nodup ∧
    ∃ i : Fin log.length, ReplyTo log i i := by
  let m : Message := ⟨"a", "x", [], 0, "", ["a"], [], ""⟩
  let first : Message := { m with inReplyTo := [] }
  refine ⟨[first, m], ?_, by decide, ⟨⟨1, by decide⟩, ?_⟩⟩
  · rintro ⟨_ | _ | n, hi⟩ p hp
    · simp [first, m, Message.parents] at hp
    · refine ⟨⟨0, by decide⟩, Fin.mk_lt_mk.mpr (by omega), ?_⟩
      simp [first, m, Message.parents] at hp ⊢
      exact hp.symm
    · exact absurd hi (by simp)
  · simp [ReplyTo, m, Message.parents]

end Mettapedia.Protocols.Mail
