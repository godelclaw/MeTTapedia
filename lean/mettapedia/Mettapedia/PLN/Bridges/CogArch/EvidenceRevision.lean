import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Evidence-bearing memory: truth values as views of evidence

Three upstream designs attach PLN/NAL truth values to long-term memories:

* `patham9/mettaclaw` branch `neoclaw` (head `2af37c3`): `support` and
  `contradict` link an episode to a memory and revise its `(stv s c)` with
  `Truth_Revision` against `(stv 1 0.5)` or `(stv 0 0.5)`; `unlink` removes the
  link; `update` and `forget` address memories by creation timestamp.
* `patham9/iter` branch `omega` (`3e376bb`, also merged into `erayindex`): the
  same revision in Python tools that address memories by UUID, refuse a
  support or contradiction from an episode already linked, and add a
  `confidence_boost` tool that supports a memory with the transcript episode
  nearest to its creation time.
* `bgoertzel-sing/iter` WMTM (`3399366`, live branch `4564185`): noisy-OR
  evidence aggregation over working-memory items. On `3399366`, PLN truth
  values were computed from attention (`confidence = sti / (1 + sti)`).

`Truth_Revision` (`lib_pln.metta`) converts confidence to evidence weight
`w = c / (1 - c)`, adds weights and converts back with `c = w / (w + 1)`.
`revise_tv` proves the algebraic identity between revision and pooling
nonnegative evidence weights, with positive incoming total weight. It does not
establish source disjointness or statistical independence. The ledger below
models episode identity explicitly; the controls show how repeated support
can overcount the same episode.

Results:
* `revise_tv`: revision of evidence-derived truth values is addition of
  evidence. `revise_self_overcounts`: revising a truth value with itself
  raises its confidence, so revision is not idempotent.
* `Ledger`: evidence as two finite sets of episodes. The raw carrier does not
  enforce disjoint polarities; `Ledger.ev` counts each polarized membership.
  `support_idem`,
  `unlink_support_fresh` and `support_comm` make support idempotent,
  retractable for a previously unlinked episode, and order-independent.
  `tv_support_fresh` shows that the ledger
  reproduces the upstream arithmetic exactly when the episode is new.
* Counterexamples to the upstream state: `neoclaw_double_support` (the same
  episode counted twice), `neoclaw_unlink_keeps_evidence` (unlinking leaves
  the episode's evidence in the truth value), `iter_relink_double_counts`
  (the duplicate check is bypassed by unlinking and linking again), and
  `default_is_phantom_evidence` (the default `(stv 1 0.5)` is one positive
  observation that no episode supplied).
* `self_support_counted` and `origin_support_noop`: a confidence boost from
  the episode in which a memory was created raises confidence upstream; when
  the origin is recorded in the evidential base, the same boost changes
  nothing.
* `update_by_time_loses_memory`: timestamps are not identities. Two memories
  created in the same second are both deleted by one `update`, and one of them
  is lost. `update_by_id_preserves_others` is the identity-keyed alternative.
* `noisy_or_self_inflates` and `noisyOrSet_insert_mem`: noisy-OR over items
  counts restatements of one observation as independent; over a set of
  sources it is idempotent.
* `rehearsal_raises_confidence`: a confidence computed from attention rises
  with rehearsal alone.

The truth value of a claim should therefore be a view computed from the
evidence atoms that support or contradict it, each naming its episode. Adding
an atom twice changes nothing. Unlinking a newly linked episode restores the
earlier view under the freshness hypotheses of `unlink_support_fresh`; this
does not undo a change from contradiction to support. The claim's origin
episode belongs to its evidential base.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.CogArch.EvidenceRevision

/-! ## Simple truth values and revision -/

/-- A simple truth value `(stv f c)`. -/
structure STV where
  f : ℚ
  c : ℚ
  deriving DecidableEq

/-- Confidence to evidence weight with horizon 1 (`Truth_c2w`). -/
def c2w (c : ℚ) : ℚ := c / (1 - c)

/-- Evidence weight to confidence with horizon 1 (`Truth_w2c`). -/
def w2c (w : ℚ) : ℚ := w / (w + 1)

/-- `Truth_Revision` from `lib_pln.metta`. Its clamps (`min 1 f` and
`max c c1 c2`) never bind on truth values computed from evidence, so they are
omitted. -/
def revise (t u : STV) : STV :=
  ⟨(c2w t.c * t.f + c2w u.c * u.f) / (c2w t.c + c2w u.c), w2c (c2w t.c + c2w u.c)⟩

/-- Positive and negative evidence weight. -/
structure Ev where
  pos : ℚ
  neg : ℚ
  deriving DecidableEq

/-- Total evidence weight. -/
def Ev.total (e : Ev) : ℚ := e.pos + e.neg

/-- Pooling two bodies of evidence. -/
def Ev.add (a b : Ev) : Ev := ⟨a.pos + b.pos, a.neg + b.neg⟩

/-- The truth value of a body of evidence. -/
def tv (e : Ev) : STV := ⟨e.pos / e.total, w2c e.total⟩

/-- Nonnegative evidence. -/
def Ev.Valid (e : Ev) : Prop := 0 ≤ e.pos ∧ 0 ≤ e.neg

theorem c2w_w2c {w : ℚ} (hw : 0 ≤ w) : c2w (w2c w) = w := by
  unfold c2w w2c
  have h : w + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- One support from an episode: one unit of positive evidence. -/
def positive : STV := ⟨1, 1 / 2⟩

/-- One contradiction from an episode: one unit of negative evidence. -/
def negative : STV := ⟨0, 1 / 2⟩

theorem positive_eq : positive = tv ⟨1, 0⟩ := by
  simp [positive, tv, Ev.total, w2c]
  norm_num

theorem negative_eq : negative = tv ⟨0, 1⟩ := by
  simp [negative, tv, Ev.total, w2c]
  norm_num

/-- Revision of evidence-derived truth values equals pooling nonnegative
weights, with positive incoming total weight. Source independence and
disjointness are not established by this algebraic identity. -/
theorem revise_tv (a b : Ev) (ha : a.Valid) (hb : b.Valid) (hb0 : 0 < b.total) :
    revise (tv a) (tv b) = tv (a.add b) := by
  obtain ⟨hap, han⟩ := ha
  obtain ⟨hbp, hbn⟩ := hb
  have hta : 0 ≤ a.total := by unfold Ev.total; linarith
  have htb : 0 ≤ b.total := hb0.le
  simp only [revise, tv, c2w_w2c hta, c2w_w2c htb]
  have hsum : (a.add b).total = a.total + b.total := by
    simp [Ev.add, Ev.total]; ring
  rw [hsum]
  congr 1
  rcases hta.eq_or_lt with h0 | hpos
  · -- no prior evidence
    have hp : a.pos = 0 := by unfold Ev.total at h0; linarith
    rw [← h0]
    simp only [zero_mul, zero_add]
    have : b.total ≠ 0 := hb0.ne'
    field_simp
    simp [Ev.add, hp]
  · have h1 : a.total ≠ 0 := hpos.ne'
    have h2 : b.total ≠ 0 := hb0.ne'
    have h3 : a.total + b.total ≠ 0 := by positivity
    field_simp
    simp [Ev.add]

/-- Revision is not idempotent: revising a truth value with itself pretends that
its evidence was observed twice. -/
theorem revise_self_overcounts (e : Ev) (he : e.Valid) (h0 : 0 < e.total) :
    revise (tv e) (tv e) = tv (e.add e) ∧ (tv e).c < (revise (tv e) (tv e)).c := by
  refine ⟨revise_tv e e he he h0, ?_⟩
  rw [revise_tv e e he he h0]
  have hsum : (e.add e).total = 2 * e.total := by simp [Ev.add, Ev.total]; ring
  simp only [tv, hsum, w2c]
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-! ## Evidence as sets of episodes -/

section Ledger

variable {E : Type*} [DecidableEq E]

/-- The evidence for one claim: the episodes that support it and the episodes
that contradict it. The raw carrier does not require these sets to be disjoint. -/
structure Ledger (E : Type*) where
  sup : Finset E
  con : Finset E
  deriving DecidableEq

/-- An episode supports the claim (it no longer contradicts it). -/
def Ledger.support (e : E) (L : Ledger E) : Ledger E := ⟨insert e L.sup, L.con.erase e⟩

/-- An episode contradicts the claim (it no longer supports it). -/
def Ledger.contradict (e : E) (L : Ledger E) : Ledger E := ⟨L.sup.erase e, insert e L.con⟩

/-- An episode is no longer evidence for or against the claim. -/
def Ledger.unlink (e : E) (L : Ledger E) : Ledger E := ⟨L.sup.erase e, L.con.erase e⟩

/-- One unit per polarized membership. An episode in both sets counts once
in each coordinate; no disjointness invariant is imposed on this raw carrier. -/
def Ledger.ev (L : Ledger E) : Ev := ⟨L.sup.card, L.con.card⟩

/-- The truth value is a view of the ledger. -/
def Ledger.tv (L : Ledger E) : STV := Mettapedia.PLN.Bridges.CogArch.EvidenceRevision.tv L.ev

omit [DecidableEq E] in
theorem Ledger.ev_valid (L : Ledger E) : L.ev.Valid := by
  constructor <;> simp [Ledger.ev]

/-- Support by an episode is idempotent. -/
theorem support_idem (e : E) (L : Ledger E) :
    (L.support e).support e = L.support e := by
  simp [Ledger.support]

/-- Contradiction by an episode is idempotent. -/
theorem contradict_idem (e : E) (L : Ledger E) :
    (L.contradict e).contradict e = L.contradict e := by
  simp [Ledger.contradict]

/-- Unlinking a newly linked episode restores the ledger exactly, and with it
the truth value. -/
theorem unlink_support_fresh (e : E) (L : Ledger E) (hs : e ∉ L.sup) (hc : e ∉ L.con) :
    (L.support e).unlink e = L := by
  simp [Ledger.support, Ledger.unlink, Finset.erase_insert hs, Finset.erase_eq_of_notMem hc]

/-- Supports commute. -/
theorem support_comm (e e' : E) (L : Ledger E) :
    (L.support e).support e' = (L.support e').support e := by
  simp only [Ledger.support, Ledger.mk.injEq]
  exact ⟨Finset.insert_comm e' e L.sup, Finset.erase_right_comm⟩

/-- Support from a new episode is exactly the upstream revision step. -/
theorem tv_support_fresh (e : E) (L : Ledger E) (hs : e ∉ L.sup) (hc : e ∉ L.con) :
    (L.support e).tv = revise L.tv positive := by
  have hev : (L.support e).ev = L.ev.add ⟨1, 0⟩ := by
    simp [Ledger.ev, Ledger.support, Finset.card_insert_of_notMem hs,
      Finset.erase_eq_of_notMem hc, Ev.add]
  rw [positive_eq]
  simp only [Ledger.tv]
  rw [revise_tv L.ev ⟨1, 0⟩ L.ev_valid (by constructor <;> norm_num) (by simp [Ev.total]), hev]

/-- Contradiction from a new episode is exactly the upstream revision step. -/
theorem tv_contradict_fresh (e : E) (L : Ledger E) (hs : e ∉ L.sup) (hc : e ∉ L.con) :
    (L.contradict e).tv = revise L.tv negative := by
  have hev : (L.contradict e).ev = L.ev.add ⟨0, 1⟩ := by
    simp [Ledger.ev, Ledger.contradict, Finset.card_insert_of_notMem hc,
      Finset.erase_eq_of_notMem hs, Ev.add]
  rw [negative_eq]
  simp only [Ledger.tv]
  rw [revise_tv L.ev ⟨0, 1⟩ L.ev_valid (by constructor <;> norm_num) (by simp [Ev.total]), hev]

end Ledger

/-! ## The upstream record: an accumulated truth value and a list of links -/

/-- A memory as the upstream tools store it: a truth value and linked episodes. -/
structure Record where
  stv : STV
  links : List ℕ
  deriving DecidableEq

/-- `neoclaw` `support`: link the episode and revise with positive evidence. -/
def supportNeo (e : ℕ) (r : Record) : Record := ⟨revise r.stv positive, e :: r.links⟩

/-- `neoclaw` and Iter `unlink`: remove the link; the truth value is unchanged. -/
def unlinkLink (e : ℕ) (r : Record) : Record := ⟨r.stv, r.links.erase e⟩

/-- Iter `support`: refuse an episode that is already linked. -/
def supportIter (e : ℕ) (r : Record) : Record :=
  if e ∈ r.links then r else ⟨revise r.stv positive, e :: r.links⟩

/-- A new memory: both upstream tools read a missing truth value as
`(stv 1 0.5)`. -/
def fresh : Record := ⟨positive, []⟩

/-- The default truth value is one unit of positive evidence that no episode
supplied. -/
theorem default_is_phantom_evidence : fresh.stv = tv ⟨1, 0⟩ ∧ fresh.links = [] :=
  ⟨positive_eq, rfl⟩

/-- `neoclaw` counts the same episode twice: two supports from one episode
reach confidence `3/4`, while the ledger of that one episode has `1/2`. -/
theorem neoclaw_double_support :
    (supportNeo 7 (supportNeo 7 fresh)).stv = ⟨1, 3 / 4⟩ ∧
      (Ledger.support 7 (⟨∅, ∅⟩ : Ledger ℕ)).tv = ⟨1, 1 / 2⟩ := by
  constructor
  · simp [supportNeo, fresh, revise, positive, c2w, w2c]
    norm_num
  · simp [Ledger.support, Ledger.tv, Ledger.ev, tv, Ev.total, w2c]
    norm_num

/-- Unlinking does not remove the episode's evidence from the stored truth value. -/
theorem neoclaw_unlink_keeps_evidence :
    (unlinkLink 7 (supportNeo 7 fresh)).links = fresh.links ∧
      (unlinkLink 7 (supportNeo 7 fresh)).stv ≠ fresh.stv := by
  constructor
  · simp [unlinkLink, supportNeo, fresh]
  · simp [unlinkLink, supportNeo, fresh, revise, positive, c2w, w2c]
    norm_num

/-- Iter refuses a duplicate support, but unlinking and supporting again counts
the episode a second time: one linked episode, confidence `3/4`. -/
theorem iter_relink_double_counts :
    supportIter 7 (supportIter 7 fresh) = supportIter 7 fresh ∧
      (supportIter 7 (unlinkLink 7 (supportIter 7 fresh))).links = [7] ∧
      (supportIter 7 (unlinkLink 7 (supportIter 7 fresh))).stv = ⟨1, 3 / 4⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · simp [supportIter, fresh]
  · simp [supportIter, unlinkLink, fresh]
  · simp [supportIter, unlinkLink, fresh, revise, positive, c2w, w2c]
    norm_num

/-! ## The origin of a memory belongs to its evidential base -/

/-- Iter's `confidence_boost` supports a memory with the transcript episode
nearest to its creation time. A new memory has no links, so the episode in
which it was created is accepted as independent support. -/
theorem self_support_counted (origin : ℕ) :
    (supportIter origin fresh).stv.c = 2 / 3 := by
  simp [supportIter, fresh, revise, positive, c2w, w2c]
  norm_num

/-- When creation records the origin episode as the claim's first evidence,
the same boost changes nothing. -/
theorem origin_support_noop (origin : ℕ) :
    let created : Ledger ℕ := ⟨{origin}, ∅⟩
    created.support origin = created ∧ created.tv = ⟨1, 1 / 2⟩ := by
  constructor
  · simp [Ledger.support]
  · simp [Ledger.tv, Ledger.ev, tv, Ev.total, w2c]
    norm_num

/-! ## Timestamps are not identities -/

/-- A stored memory: identity, creation second and content. -/
structure Mem where
  id : ℕ
  time : ℕ
  content : ℕ
  deriving DecidableEq

/-- `neoclaw` `forget`: delete every memory created in second `t`. -/
def forgetByTime (t : ℕ) (s : List Mem) : List Mem := s.filter (fun m => m.time ≠ t)

/-- `neoclaw` `update`: create the new memory, then forget every memory created
in second `t`. -/
def updateByTime (t now newId c : ℕ) (s : List Mem) : List Mem :=
  ⟨newId, now, c⟩ :: forgetByTime t s

/-- Identity-keyed update: replace the content of one memory. -/
def updateById (i c : ℕ) (s : List Mem) : List Mem :=
  s.map (fun m => if m.id = i then { m with content := c } else m)

/-- Two memories remembered in one command batch share their creation second.
Updating the first deletes both, so the second memory's content is lost. -/
theorem update_by_time_loses_memory :
    let s : List Mem := [⟨1, 100, 10⟩, ⟨2, 100, 20⟩]
    (updateByTime 100 105 3 11 s).map Mem.content = [11] ∧
      20 ∈ s.map Mem.content ∧ 20 ∉ (updateByTime 100 105 3 11 s).map Mem.content := by
  decide

/-- An identity-keyed update keeps every other memory unchanged. -/
theorem update_by_id_preserves_others (i c : ℕ) (s : List Mem) (m : Mem) (hm : m ∈ s)
    (hne : m.id ≠ i) : m ∈ updateById i c s := by
  simp only [updateById, List.mem_map]
  exact ⟨m, hm, by simp [hne]⟩

/-! ## Noisy-OR aggregation -/

/-- Noisy-OR over a list of confidences, as in the WMTM and PLN aggregators. -/
def noisyOr (cs : List ℚ) : ℚ := 1 - (cs.map (fun c => 1 - c)).prod

/-- Aggregating an item with its own restatement raises the combined value,
although no new evidence arrived. -/
theorem noisy_or_self_inflates (c : ℚ) (h0 : 0 < c) (h1 : c < 1) :
    noisyOr [c] < noisyOr [c, c] := by
  simp only [noisyOr, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  nlinarith

/-- With WMTM's base strength `0.7`, an observation and its restatement aggregate
to `0.91`. -/
theorem wmtm_aggregate_restatement : noisyOr [7 / 10, 7 / 10] = 91 / 100 := by
  simp [noisyOr]
  norm_num

/-- Noisy-OR over a set of sources: counting a source again changes nothing. -/
def noisyOrSet {ι : Type*} [DecidableEq ι] (src : Finset ι) (conf : ι → ℚ) : ℚ :=
  1 - ∏ i ∈ src, (1 - conf i)

theorem noisyOrSet_insert_mem {ι : Type*} [DecidableEq ι] (src : Finset ι) (conf : ι → ℚ)
    (i : ι) (hi : i ∈ src) : noisyOrSet (insert i src) conf = noisyOrSet src conf := by
  simp [noisyOrSet, Finset.insert_eq_of_mem hi]

/-! ## Attention is not evidence -/

/-- The confidence that the WMTM PLN bridge computed from attention on
`3399366`. -/
def attentionConfidence (sti : ℚ) : ℚ := sti / (1 + sti)

/-- Rehearsal alone raises such a confidence: two items with the same evidence
and different attention receive different truth values. -/
theorem rehearsal_raises_confidence (a b : ℚ) (ha : 0 ≤ a) (hab : a < b) :
    attentionConfidence a < attentionConfidence b := by
  unfold attentionConfidence
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end Mettapedia.PLN.Bridges.CogArch.EvidenceRevision
