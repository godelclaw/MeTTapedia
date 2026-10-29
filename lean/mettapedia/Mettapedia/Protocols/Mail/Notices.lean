import Mathlib.Data.List.Basic

/-!
# Notices of failure: each reason at most once per period

A gateway tells a sender that a request was refused; a mail watcher sends a
bounce for mail it refuses. An agent may answer each notice with a new request
that is refused again, as in `AutoReply.alternating_loops`, and each notice costs
the agent a turn. RFC 3834 §2 bounds a personal responder to one response to a
sender within a period. Here the period is kept per sender and per reason: a
sender is told each reason at most once per period, and a new reason at once.

The theorems:
- `notices_spaced`: two notices to one sender for one reason are at least a
  period apart, so within any period a sender gets at most one notice per reason.
- `told_within`: nothing is withheld. For failures in time order, each failure's
  sender was told its reason within the period before it.
- Necessity: changing one part of the rule refutes one of the two.
  - Without memory (`period = 0`), two notices for one reason come a second apart
    (`forgetful_unspaced`), so an agent that answers notices keeps the exchange
    going (`AutoReply.alternating_loops`).
  - Keyed by thread as well, an agent that starts a fresh thread for each attempt
    draws a notice each time (`by_thread_unspaced`).
  - Keyed by the sender alone, a new reason inside the period goes untold
    (`by_sender_withholds`).

The model takes failures in the order the gateway or watcher sees them, with
times in seconds. Not modelled: clocks that go backwards, and memory lost on a
restart. The memory has to survive restarts for the bound to hold across them.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Mail.Notices

/-- A refused request: its sender, the reason, its thread, and the time, in
seconds. -/
structure Failure (S R : Type) where
  sender : S
  reason : R
  thread : Nat
  time : Nat
deriving DecidableEq, Repr

section Rule

variable {S R K : Type} [DecidableEq K]

/-- A notice `n` covers the failure `f` for `key` when it went to the same key
less than `period` seconds before `f`. -/
def covers (key : Failure S R → K) (period : Nat) (f n : Failure S R) : Bool :=
  key n == key f && decide (f.time < n.time + period)

/-- The notices sent, newest first: a failure draws a notice unless one already
sent covers it. -/
def notify (key : Failure S R → K) (period : Nat) :
    List (Failure S R) → List (Failure S R) → List (Failure S R)
  | sent, [] => sent
  | sent, f :: fs => notify key period (if sent.any (covers key period f) then sent else f :: sent) fs

theorem mem_notify_of_mem (key : Failure S R → K) (period : Nat) :
    ∀ (sent fs : List (Failure S R)) (n : Failure S R), n ∈ sent → n ∈ notify key period sent fs
  | _, [], _, h => h
  | sent, f :: fs, n, h => by
    unfold notify
    apply mem_notify_of_mem
    split
    · exact h
    · exact List.mem_cons_of_mem _ h

/-- Notices to one key, newest first, at least a period apart. -/
abbrev Spaced (key : Failure S R → K) (period : Nat) (l : List (Failure S R)) : Prop :=
  l.Pairwise fun later earlier => key later = key earlier → earlier.time + period ≤ later.time

theorem notify_spaced (key : Failure S R → K) (period : Nat) :
    ∀ (sent fs : List (Failure S R)), Spaced key period sent → Spaced key period (notify key period sent fs)
  | _, [], h => h
  | sent, f :: fs, h => by
    unfold notify
    apply notify_spaced
    split
    · exact h
    · next hc =>
      refine List.pairwise_cons.mpr ⟨fun n hn hk => ?_, h⟩
      have hn' : covers key period f n = false := by
        cases hcn : covers key period f n with
        | false => rfl
        | true => exact absurd (List.any_eq_true.mpr ⟨n, hn, hcn⟩) hc
      simp only [covers, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
        decide_eq_false_iff_not, Nat.not_lt] at hn'
      rcases hn' with h1 | h1
      · exact absurd hk.symm h1
      · exact h1

theorem notify_told (key : Failure S R → K) {period : Nat} (hp : 0 < period) :
    ∀ (sent fs : List (Failure S R)), (∀ n ∈ sent, ∀ f ∈ fs, n.time ≤ f.time) →
      fs.Pairwise (fun a b => a.time ≤ b.time) →
      ∀ f ∈ fs, ∃ n ∈ notify key period sent fs,
        key n = key f ∧ n.time ≤ f.time ∧ f.time < n.time + period
  | _, [], _, _, _, hf => by simp at hf
  | sent, g :: fs, hle, hsort, f, hf => by
    rw [List.pairwise_cons] at hsort
    have hle' : ∀ n ∈ (if sent.any (covers key period g) then sent else g :: sent),
        ∀ f ∈ fs, n.time ≤ f.time := by
      intro n hn x hx
      split at hn
      · exact hle n hn x (List.mem_cons_of_mem _ hx)
      · rcases List.mem_cons.mp hn with rfl | hn
        · exact hsort.1 x hx
        · exact hle n hn x (List.mem_cons_of_mem _ hx)
    unfold notify
    rcases List.mem_cons.mp hf with rfl | hf
    · by_cases hc : sent.any (covers key period f) = true
      · obtain ⟨n, hn, hcov⟩ := List.any_eq_true.mp hc
        simp only [covers, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcov
        refine ⟨n, ?_, hcov.1, hle n hn f (List.mem_cons_self ..), hcov.2⟩
        rw [if_pos hc]
        exact mem_notify_of_mem key period sent fs n hn
      · refine ⟨f, ?_, rfl, Nat.le_refl _, by omega⟩
        rw [if_neg hc]
        exact mem_notify_of_mem key period _ fs f (List.mem_cons_self ..)
    · exact notify_told key hp _ fs hle' hsort.2 f hf

end Rule

section TheRule

variable {S R : Type} [DecidableEq S] [DecidableEq R]

/-- The rule's key: the sender and the reason. -/
def bySenderReason (f : Failure S R) : S × R := (f.sender, f.reason)

/-- The notices of the rule, newest first. -/
def notices (period : Nat) (fs : List (Failure S R)) : List (Failure S R) :=
  notify bySenderReason period [] fs

/-- **At most once per period.** Two notices to one sender for one reason are at
least a period apart. -/
theorem notices_spaced (period : Nat) (fs : List (Failure S R)) :
    Spaced bySenderReason period (notices period fs) :=
  notify_spaced _ _ [] fs List.Pairwise.nil

/-- **Nothing withheld.** For failures in time order, each failure's sender was
told its reason within the period before it. -/
theorem told_within {period : Nat} (hp : 0 < period) {fs : List (Failure S R)}
    (hsort : fs.Pairwise (fun a b => a.time ≤ b.time)) :
    ∀ f ∈ fs, ∃ n ∈ notices period fs, n.sender = f.sender ∧ n.reason = f.reason ∧
      n.time ≤ f.time ∧ f.time < n.time + period := by
  intro f hf
  obtain ⟨n, hn, hk, h1, h2⟩ := notify_told bySenderReason hp [] fs (by simp) hsort f hf
  simp only [bySenderReason, Prod.mk.injEq] at hk
  exact ⟨n, hn, hk.1, hk.2, h1, h2⟩

end TheRule

/-! ## The hypotheses meet, and the rule at work -/

/-- One sender's failures: `r1` at 0 and 3 seconds, `r2` at 5, `r1` again at 12. -/
def sample : List (Failure String String) :=
  [⟨"b", "r1", 0, 0⟩, ⟨"b", "r1", 0, 3⟩, ⟨"b", "r2", 0, 5⟩, ⟨"b", "r1", 0, 12⟩]

/-- The failures are in time order, and with a period of ten seconds the repeat
at 3 is not told again, the new reason at 5 is, and `r1` is told again at 12. -/
example : sample.Pairwise (fun a b => a.time ≤ b.time) ∧
    notices 10 sample = [⟨"b", "r1", 0, 12⟩, ⟨"b", "r2", 0, 5⟩, ⟨"b", "r1", 0, 0⟩] := by
  decide

/-! ## Necessity: each part of the rule is needed -/

/-- A day, in seconds. -/
def day : Nat := 86400

/-- An agent's two attempts a second apart, refused for the same reason, in two
threads. -/
def twoAttempts : List (Failure String String) := [⟨"b", "no headers", 0, 0⟩, ⟨"b", "no headers", 1, 1⟩]

/-- Without memory, both attempts draw a notice, a second apart. -/
theorem forgetful_unspaced : ¬ Spaced bySenderReason day (notices 0 twoAttempts) := by
  decide

/-- Keyed by thread as well, the second thread draws a notice a second after the
first. -/
theorem by_thread_unspaced :
    ¬ Spaced bySenderReason day
      (notify (fun f : Failure String String => (f.sender, f.reason, f.thread)) day [] twoAttempts) := by
  decide

/-- Two failures a second apart, for two reasons. -/
def twoReasons : List (Failure String String) := [⟨"b", "no headers", 0, 0⟩, ⟨"b", "too long", 0, 1⟩]

/-- The rule tells both reasons. -/
example : notices day twoReasons = [⟨"b", "too long", 0, 1⟩, ⟨"b", "no headers", 0, 0⟩] := by
  decide

/-- Keyed by the sender alone, the second reason is never told: `told_within`
fails for it. -/
theorem by_sender_withholds :
    ¬ ∃ n ∈ notify (fun f : Failure String String => f.sender) day [] twoReasons,
      n.reason = "too long" := by
  decide

end Mettapedia.Protocols.Mail.Notices
