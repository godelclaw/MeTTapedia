import Mathlib.Data.List.Basic

/-!
# Acknowledgement counters and stream resumption (XEP-0198)

XMPP stream management counts stanzas.
- §4: each side keeps `h`, the number of stanzas it has handled. It starts at
  zero when stream management is enabled and grows by one per handled stanza.
  An `<a h='…'/>` tells the sender how many of its stanzas were handled; the
  rest stay its responsibility.
- §5: after a broken connection, `<resume h='…'/>` and `<resumed h='…'/>`
  carry each side's count. The counts carry over to the new stream, and each
  side re-sends the stanzas the other has not handled. The exchange tells
  definitively which stanzas need retransmission, eliminating duplication
  through replay.
- §4: without resumption, re-sent stanzas may arrive twice, and stanza ids can
  help the recipient weed out duplicates.

The model: one direction of one stream, over connections that keep order
(TCP) and lose whatever is in flight when they break. The sender keeps every
stanza it sent and the last count it heard. The receiver handles the stanza
whose position equals its count, or with `dedup` off, every stanza that
arrives. At a resumption the sender re-sends from the receiver's count, or
with `resumeH` off, from the last count it heard.

The theorems:
- `run_inv`, `handled_prefix`: with either mechanism, and with both, after any
  sequence of sends, deliveries, acknowledgements, breaks and resumptions, the
  receiver has handled a prefix of the stream, each stanza once and in order.
- `resume_resends_rest`: a resumption re-sends exactly the stanzas the
  receiver has not handled.
- `quiet_complete`: when the stream is up and nothing is in flight, the
  receiver has handled the whole stream.
- Mutants: with neither mechanism a stanza is handled twice
  (`neither_duplicates`); a resumption that re-sends nothing loses a stanza
  (`no_resend_loses`).

Not modelled: the 2^32 wrap of `h`, both directions at once, timeouts that
discard the session, and stanza content.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Mail.Resumption

variable {α : Type}

/-- Stanzas with their positions, from `n`. -/
def indexed : List α → Nat → List (Nat × α)
  | [], _ => []
  | x :: xs, n => (n, x) :: indexed xs (n + 1)

/-- The sender's stream, the last count it heard, what is in flight, whether
the connection is up, and what the receiver has handled. -/
structure World (α : Type) where
  stream : List α
  acked : Nat
  wire : List (Nat × α)
  up : Bool
  handled : List α

/-- A fresh stream. -/
def World.start : World α := ⟨[], 0, [], true, []⟩

/-- What happens next. -/
inductive Ev (α : Type)
  | send (x : α)
  | deliver
  | ack
  | drop
  | resume

/-- The two mechanisms: count-based dedup at the receiver, and resumption from
the receiver's count. -/
structure Mechanisms where
  dedup : Bool := true
  resumeH : Bool := true

/-- One event. -/
def step (m : Mechanisms) (w : World α) : Ev α → World α
  | .send x =>
    if w.up then { w with stream := w.stream ++ [x], wire := w.wire ++ [(w.stream.length, x)] } else w
  | .deliver =>
    match w.up, w.wire with
    | true, (i, x) :: rest =>
      if !m.dedup || i = w.handled.length then { w with wire := rest, handled := w.handled ++ [x] }
      else { w with wire := rest }
    | _, _ => w
  | .ack => { w with acked := w.handled.length }
  | .drop => { w with up := false, wire := [] }
  | .resume =>
    if w.up then w
    else
      let h := if m.resumeH then w.handled.length else w.acked
      { w with up := true, acked := h, wire := indexed (w.stream.drop h) h }

/-- Events in order. -/
def run (m : Mechanisms) (w : World α) (es : List (Ev α)) : World α := es.foldl (step m) w

/-- The invariant: the receiver has handled a prefix of the stream; the sender's
count is no ahead of it; and while up, what is in flight is the stream from a
position at or before the receiver's count, that position being the count
itself without dedup. -/
def Inv (m : Mechanisms) (w : World α) : Prop :=
  w.handled = w.stream.take w.handled.length ∧ w.handled.length ≤ w.stream.length ∧
    w.acked ≤ w.handled.length ∧
    (w.up = true → ∃ lo, lo ≤ w.handled.length ∧ (m.dedup = false → lo = w.handled.length) ∧
      w.wire = indexed (w.stream.drop lo) lo) ∧
    (w.up = false → w.wire = [])

theorem indexed_append (l : List α) (x : α) (n : Nat) :
    indexed (l ++ [x]) n = indexed l n ++ [(n + l.length, x)] := by
  induction l generalizing n with
  | nil => simp [indexed]
  | cons y ys ih => simp [indexed, ih]; omega

theorem start_inv (m : Mechanisms) : Inv m (World.start : World α) :=
  ⟨rfl, Nat.le_refl _, Nat.le_refl _, fun _ => ⟨0, Nat.le_refl _, fun _ => rfl, rfl⟩, fun h => by cases h⟩

theorem step_inv (m : Mechanisms) (hm : (m.dedup || m.resumeH) = true) {w : World α} (hw : Inv m w)
    (e : Ev α) : Inv m (step m w e) := by
  obtain ⟨hpre, hlen, hack, hup, hdown⟩ := hw
  cases e with
  | send x =>
    by_cases hu : w.up = true
    · have hs : step m w (.send x) =
          { w with stream := w.stream ++ [x], wire := w.wire ++ [(w.stream.length, x)] } := by
        simp [step, hu]
      rw [hs]
      obtain ⟨lo, hlo, hlo', hwire⟩ := hup hu
      refine ⟨?_, ?_, hack, fun _ => ⟨lo, hlo, hlo', ?_⟩,
        fun h => absurd ((h : w.up = false).symm.trans hu) Bool.false_ne_true⟩
      · show w.handled = (w.stream ++ [x]).take w.handled.length
        rw [List.take_append_of_le_length hlen]; exact hpre
      · show w.handled.length ≤ (w.stream ++ [x]).length
        simp only [List.length_append, List.length_singleton]; omega
      · show w.wire ++ [(w.stream.length, x)] = indexed ((w.stream ++ [x]).drop lo) lo
        rw [hwire, List.drop_append_of_le_length (by omega), indexed_append, List.length_drop]
        congr 3
        omega
    · have hs : step m w (.send x) = w := by simp [step, hu]
      rw [hs]; exact ⟨hpre, hlen, hack, hup, hdown⟩
  | deliver =>
    cases hu : w.up with
    | false =>
      have hs : step m w .deliver = w := by simp [step, hu]
      rw [hs]; exact ⟨hpre, hlen, hack, hup, hdown⟩
    | true =>
      obtain ⟨lo, hlo, hlo', hwire⟩ := hup hu
      cases hwr : w.wire with
      | nil =>
        have hs : step m w .deliver = w := by simp [step, hu, hwr]
        rw [hs]; exact ⟨hpre, hlen, hack, hup, hdown⟩
      | cons p rest =>
        obtain ⟨i, x⟩ := p
        rw [hwr] at hwire
        -- the head of the wire is the stanza at `lo`
        have hd1 : w.stream.drop lo = x :: w.stream.drop (lo + 1) ∧ i = lo := by
          cases hd : w.stream.drop lo with
          | nil => rw [hd] at hwire; simp [indexed] at hwire
          | cons y ys =>
            rw [hd] at hwire
            simp only [indexed, List.cons.injEq, Prod.mk.injEq] at hwire
            obtain ⟨⟨rfl, rfl⟩, -⟩ := hwire
            refine ⟨?_, rfl⟩
            have : w.stream.drop (i + 1) = ys := by
              rw [← List.drop_drop, hd]; rfl
            rw [this]
        obtain ⟨hd1, rfl⟩ := hd1
        have hrest : rest = indexed (w.stream.drop (i + 1)) (i + 1) := by
          rw [hd1] at hwire; simp only [indexed, List.cons.injEq] at hwire; exact hwire.2
        by_cases hc : (!m.dedup || decide (i = w.handled.length)) = true
        · have hs : step m w .deliver = { w with wire := rest, handled := w.handled ++ [x] } := by
            simp only [step, hu, hwr]; rw [if_pos hc]
          rw [hs]
          have hi : i = w.handled.length := by
            cases hdd : m.dedup
            · exact hlo' hdd
            · simpa [hdd] using hc
          subst hi
          have hx : w.stream[w.handled.length]? = some x := by
            rw [← List.head?_drop, hd1]; rfl
          refine ⟨?_, ?_, ?_, fun _ => ⟨w.handled.length + 1, ?_, fun _ => ?_, ?_⟩,
            fun h => absurd ((h : w.up = false).symm.trans hu) Bool.false_ne_true⟩
          · show w.handled ++ [x] = w.stream.take (w.handled ++ [x]).length
            rw [List.length_append, List.length_singleton, List.take_add_one, hx, ← hpre]; rfl
          · show (w.handled ++ [x]).length ≤ w.stream.length
            have : w.handled.length < w.stream.length := by
              by_contra hc'
              rw [List.drop_eq_nil_of_le (by omega)] at hd1
              cases hd1
            simp only [List.length_append, List.length_singleton]; omega
          · show w.acked ≤ (w.handled ++ [x]).length
            simp only [List.length_append, List.length_singleton]; omega
          · simp
          · simp
          · simpa using hrest
        · have hs : step m w .deliver = { w with wire := rest } := by
            simp only [step, hu, hwr]; rw [if_neg hc]
          rw [hs]
          have hne : i ≠ w.handled.length := fun h => hc (by simp [h])
          refine ⟨hpre, hlen, hack, fun _ => ⟨i + 1, show i + 1 ≤ w.handled.length by omega,
            fun hdd => ?_, hrest⟩, fun h => absurd ((h : w.up = false).symm.trans hu) Bool.false_ne_true⟩
          simp [hdd] at hc
  | ack =>
    have hs : step m w .ack = { w with acked := w.handled.length } := rfl
    rw [hs]; exact ⟨hpre, hlen, Nat.le_refl _, hup, hdown⟩
  | drop =>
    have hs : step m w .drop = { w with up := false, wire := [] } := rfl
    rw [hs]; exact ⟨hpre, hlen, hack, fun h => Bool.noConfusion h, fun _ => rfl⟩
  | resume =>
    by_cases hu : w.up = true
    · have hs : step m w .resume = w := by simp [step, hu]
      rw [hs]; exact ⟨hpre, hlen, hack, hup, hdown⟩
    · have hs : step m w .resume =
          { w with up := true, acked := if m.resumeH then w.handled.length else w.acked,
                   wire := indexed (w.stream.drop (if m.resumeH then w.handled.length else w.acked))
                     (if m.resumeH then w.handled.length else w.acked) } := by
        simp [step, hu]
      rw [hs]
      refine ⟨hpre, hlen, ?_, fun _ => ⟨if m.resumeH then w.handled.length else w.acked, ?_, ?_, rfl⟩,
        fun h => Bool.noConfusion h⟩
      · show (if m.resumeH then w.handled.length else w.acked) ≤ w.handled.length
        split <;> omega
      · show (if m.resumeH then w.handled.length else w.acked) ≤ w.handled.length
        split <;> omega
      · intro hd
        have : m.resumeH = true := by simpa [hd] using hm
        simp [this]

/-- The invariant holds after any sequence of events. -/
theorem run_inv (m : Mechanisms) (hm : (m.dedup || m.resumeH) = true) :
    ∀ (es : List (Ev α)) (w : World α), Inv m w → Inv m (run m w es)
  | [], _, hw => hw
  | e :: es, _, hw => run_inv m hm es _ (step_inv m hm hw e)

/-- **Exactly once, in order**: whatever happens, the receiver has handled a
prefix of the stream. -/
theorem handled_prefix (m : Mechanisms) (hm : (m.dedup || m.resumeH) = true) (es : List (Ev α)) :
    let w := run m World.start es
    w.handled = w.stream.take w.handled.length :=
  (run_inv m hm es _ (start_inv m)).1

/-- A resumption re-sends exactly the stanzas the receiver has not handled. -/
theorem resume_resends_rest (w : World α) (hdown : w.up = false) :
    ((step {} w .resume).wire.map Prod.snd) = w.stream.drop w.handled.length := by
  simp only [step, hdown, Bool.false_eq_true, if_false, if_true]
  generalize w.stream.drop w.handled.length = l
  generalize w.handled.length = n
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih => simp [indexed, ih]

/-- **Complete when quiet**: with the stream up and nothing in flight, the
receiver has handled all of it. -/
theorem quiet_complete (m : Mechanisms) (hm : (m.dedup || m.resumeH) = true) (es : List (Ev α))
    (hup : (run m World.start es).up = true) (hq : (run m World.start es).wire = []) :
    (run m World.start es).handled = (run m World.start es).stream := by
  obtain ⟨hpre, hlen, -, hu, -⟩ := run_inv m hm es _ (start_inv m)
  obtain ⟨lo, hlo, -, hwire⟩ := hu hup
  rw [hq] at hwire
  have : (run m World.start es).stream.drop lo = [] := by
    cases hd : (run m World.start es).stream.drop lo with
    | nil => rfl
    | cons y ys => rw [hd] at hwire; simp [indexed] at hwire
  have hle : (run m World.start es).stream.length ≤ lo := List.drop_eq_nil_iff.mp this
  rw [hpre, List.take_of_length_le (by omega)]

/-! ## Examples and mutants -/

/-- Three stanzas; the second is in flight when the connection breaks, and the
sender's count lags the receiver's. -/
def outage : List (Ev String) :=
  [.send "a", .send "b", .deliver, .drop, .resume, .send "c", .deliver, .deliver, .deliver]

/-- With both mechanisms, and with either alone, each stanza is handled once;
the run ends up and quiet, as `quiet_complete` assumes. -/
example : (run {} World.start outage).up = true ∧ (run {} World.start outage).wire = [] ∧
    (run {} World.start outage).handled = ["a", "b", "c"] ∧
    (run { dedup := false } World.start outage).handled = ["a", "b", "c"] ∧
    (run { resumeH := false } World.start outage).handled = ["a", "b", "c"] := by decide

/-- With neither, the stanza handled before the break is handled again. -/
theorem neither_duplicates :
    (run { dedup := false, resumeH := false } World.start outage).handled = ["a", "a", "b", "c"] := by
  decide

/-- A resumption that re-sends nothing. -/
def resumeBare (w : World α) : World α := if w.up then w else { w with up := true }

/-- It loses the stanza that was in flight: the stream is up and quiet, and the
receiver lacks `b`. -/
theorem no_resend_loses :
    let w := (resumeBare (run {} World.start [.send "a", .send "b", .deliver, .drop])).wire
    w = [] ∧ (run {} World.start [.send "a", .send "b", .deliver, .drop]).handled = ["a"] ∧
      (run {} World.start [.send "a", .send "b", .deliver, .drop]).stream = ["a", "b"] := by decide

end Mettapedia.Protocols.Mail.Resumption
