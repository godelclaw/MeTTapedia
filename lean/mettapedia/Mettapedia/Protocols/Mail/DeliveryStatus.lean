import Mathlib.Data.List.Basic

/-!
# Delivery status: one final state per recipient, and bounded warnings

RFC 3464 §2.3.3 reports what a mail system did for each recipient of a message:
- `delivered`: a terminal state; no further DSN for this recipient.
- `failed`: the reporting MTA has abandoned delivery; no further notifications.
- `relayed`: relayed or gatewayed into an environment that does not generate
  DSNs on successful delivery. The model treats it as final.
- `delayed`: a warning; the MTA keeps trying, and more notifications may follow.
- `expanded` (delivery to an alias with several recipients) is not modelled.

The MTA retries until the message is transmitted or it gives up (RFC 5321
§4.5.4.1). A delayed DSN may carry `Will-Retry-Until`, the date after which the
MTA expects to abandon delivery (RFC 3464 §2.3.9). The model makes that a
policy: a temporary failure at or after the give-up time is final, and the MTA
warns at most a fixed number of times.

The model: one recipient. Attempts come from an oracle, any number, each with a
time and an outcome: accepted, refused permanently, refused for now, or handed
to a system that will not report.

The theorems:
- `finals_le_one`: whatever the oracle, at most one final notice.
- `final_last`: every notice before the last is a warning.
- `warnings_le`: at most the policy's number of warnings.
- `exactly_one_final`: an attempt at or after the give-up time, or one that is
  not a temporary failure, leaves exactly one final notice.
- Mutants, each refuting a conclusion: a system that never gives up reaches no
  final state (`no_giveup_no_final`); one that warns on every temporary failure
  warns without bound (`uncapped_warnings`); one that keeps attempting after a
  final state reports two finals (`reopened_two_finals`).

Not modelled: the content of notices, several recipients (each has its own
state), and the sender's request for notices (RFC 3461 `NOTIFY`).
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Mail.DeliveryStatus

/-- The outcome of one delivery attempt. -/
inductive Outcome
  | accepted
  | permanent
  | temporary
  | handedOff
deriving DecidableEq, Repr

/-- The RFC 3464 action values modelled. -/
inductive Action
  | failed
  | delayed
  | delivered
  | relayed
deriving DecidableEq, Repr

/-- Everything but `delayed` is final. -/
def Action.final : Action → Bool
  | .delayed => false
  | _ => true

/-- The recipient's state: queued, with the warnings issued so far, or done with
its final action. -/
inductive State
  | queued (warned : Nat)
  | done (a : Action)
deriving DecidableEq, Repr

/-- When the MTA gives up, and how many warnings it issues at most. -/
structure Policy where
  giveUp : Nat
  maxWarnings : Nat

/-- Variants of the MTA: `sticky` stops at a final state, `capped` limits the
warnings, `givesUp` makes a late temporary failure final. RFC 3464 and RFC 5321
have all three. -/
structure Variant where
  sticky : Bool := true
  capped : Bool := true
  givesUp : Bool := true

/-- A temporary failure at time `t` while queued with `w` warnings. -/
def onTemporary (v : Variant) (p : Policy) (w t : Nat) : State × Option Action :=
  if v.givesUp && decide (p.giveUp ≤ t) then (.done .failed, some .failed)
  else if !v.capped || decide (w < p.maxWarnings) then (.queued (w + 1), some .delayed)
  else (.queued w, none)

/-- One attempt: the new state and the notice issued, if any. -/
def attempt (v : Variant) (p : Policy) (s : State) (x : Nat × Outcome) : State × Option Action :=
  match s, x.2 with
  | .done a, _ => if v.sticky then (.done a, none) else attempt' x.2
  | .queued w, .temporary => onTemporary v p w x.1
  | .queued _, o => attempt' o
where
  /-- The final state an outcome other than a temporary failure leads to. -/
  attempt' : Outcome → State × Option Action
    | .accepted => (.done .delivered, some .delivered)
    | .permanent => (.done .failed, some .failed)
    | .handedOff => (.done .relayed, some .relayed)
    | .temporary => (.queued 0, some .delayed)

/-- Attempts in order: the final state and the notices. -/
def run (v : Variant) (p : Policy) : State → List (Nat × Outcome) → State × List Action
  | s, [] => (s, [])
  | s, x :: xs =>
    ((run v p (attempt v p s x).1 xs).1, (attempt v p s x).2.toList ++ (run v p (attempt v p s x).1 xs).2)

/-- RFC 3464 and RFC 5321 as modelled. -/
def rfc : Variant := {}

@[simp] theorem rfc_sticky : rfc.sticky = true := rfl
@[simp] theorem rfc_capped : rfc.capped = true := rfl
@[simp] theorem rfc_givesUp : rfc.givesUp = true := rfl

/-! ## The theorems -/

variable (p : Policy)

theorem attempt_done (a : Action) (x : Nat × Outcome) : attempt rfc p (.done a) x = (.done a, none) := by
  simp [attempt]

theorem run_done (a : Action) : ∀ xs, run rfc p (.done a) xs = (.done a, [])
  | [] => rfl
  | x :: xs => by simp only [run, attempt_done, run_done a xs]; rfl

theorem attempt_queued_or_done (w : Nat) (x : Nat × Outcome) :
    (∃ w', (attempt rfc p (.queued w) x) = (.queued w', none) ∨
      (attempt rfc p (.queued w) x) = (.queued w', some .delayed)) ∨
    ∃ a, a.final = true ∧ (attempt rfc p (.queued w) x) = (.done a, some a) := by
  rcases x with ⟨t, o⟩
  cases o <;> simp [attempt, attempt.attempt', onTemporary, Action.final]
  split
  · simp
  · split <;> simp

/-- Whatever the oracle, at most one final notice; none once done. -/
theorem finals_le_one : ∀ (xs : List (Nat × Outcome)) (s : State),
    ((run rfc p s xs).2.filter Action.final).length ≤ (match s with | .queued _ => 1 | .done _ => 0)
  | [], s => by cases s <;> simp [run]
  | x :: xs, .done a => by simp [run_done]
  | x :: xs, .queued w => by
    simp only [run, List.filter_append, List.length_append]
    rcases attempt_queued_or_done p w x with ⟨w', h | h⟩ | ⟨a, ha, h⟩
    · rw [h]; simpa using finals_le_one xs (.queued w')
    · rw [h]; simpa [Action.final] using finals_le_one xs (.queued w')
    · rw [h, run_done]; simp [ha]

/-- Every notice before the last is a warning: the final notice, if any, comes last. -/
theorem final_last : ∀ (xs : List (Nat × Outcome)) (s : State),
    ∀ a ∈ (run rfc p s xs).2.dropLast, a = .delayed
  | [], s => by simp [run]
  | x :: xs, .done a => by simp [run_done]
  | x :: xs, .queued w => by
    intro a ha
    simp only [run] at ha
    rcases attempt_queued_or_done p w x with ⟨w', h | h⟩ | ⟨b, hb, h⟩
    · rw [h] at ha; simpa using final_last xs (.queued w') a (by simpa using ha)
    · rw [h] at ha
      cases hr : (run rfc p (.queued w') xs).2 with
      | nil => rw [hr] at ha; simp at ha
      | cons c cs =>
        rw [hr] at ha
        simp only [Option.toList_some, List.cons_append, List.nil_append] at ha
        rw [List.dropLast_cons_of_ne_nil (by simp)] at ha
        rcases List.mem_cons.mp ha with rfl | ha
        · rfl
        · exact final_last xs (.queued w') a (by rw [hr]; exact ha)
    · rw [h, run_done] at ha; simp at ha

/-- At most the policy's number of warnings. -/
theorem warnings_le : ∀ (xs : List (Nat × Outcome)) (w : Nat), w ≤ p.maxWarnings →
    ((run rfc p (.queued w) xs).2.filter (· == .delayed)).length + w ≤ p.maxWarnings
  | [], w, hw => by simpa [run] using hw
  | x :: xs, w, hw => by
    simp only [run, List.filter_append, List.length_append]
    rcases x with ⟨t, o⟩
    cases o with
    | temporary =>
      simp only [attempt, onTemporary, rfc_givesUp, rfc_capped]
      by_cases hg : p.giveUp ≤ t
      · simp [hg, run_done]; omega
      · by_cases hc : w < p.maxWarnings
        · have := warnings_le xs (w + 1) (by omega)
          simp [hg, hc] at this ⊢; omega
        · have := warnings_le xs w hw
          simp [hg, hc] at this ⊢; omega
    | accepted => simp [attempt, attempt.attempt', run_done]; omega
    | permanent => simp [attempt, attempt.attempt', run_done]; omega
    | handedOff => simp [attempt, attempt.attempt', run_done]; omega

/-- A final state is reached by an attempt at or after the give-up time, or by an
outcome other than a temporary failure. -/
def Decisive (p : Policy) (x : Nat × Outcome) : Prop := p.giveUp ≤ x.1 ∨ x.2 ≠ .temporary

theorem reaches_done : ∀ (xs : List (Nat × Outcome)) (w : Nat), (∃ x ∈ xs, Decisive p x) →
    ∃ a, (run rfc p (.queued w) xs).1 = .done a ∧ ((run rfc p (.queued w) xs).2.filter Action.final).length = 1
  | [], _, ⟨_, hx, _⟩ => by simp at hx
  | x :: xs, w, ⟨y, hy, hd⟩ => by
    rcases attempt_queued_or_done p w x with ⟨w', h | h⟩ | ⟨a, ha, h⟩
    · have hy' : y ∈ xs := by
        rcases List.mem_cons.mp hy with rfl | hy
        · exfalso
          rcases y with ⟨t, o⟩
          cases o <;> simp [attempt, attempt.attempt', onTemporary, Decisive] at h hd
          split at h <;> simp_all
        · exact hy
      obtain ⟨a, h1, h2⟩ := reaches_done xs w' ⟨y, hy', hd⟩
      exact ⟨a, by simp [run, h, h1], by simpa [run, h] using h2⟩
    · have hy' : y ∈ xs := by
        rcases List.mem_cons.mp hy with rfl | hy
        · exfalso
          rcases y with ⟨t, o⟩
          cases o <;> simp [attempt, attempt.attempt', onTemporary, Decisive] at h hd
          split at h <;> simp_all
        · exact hy
      obtain ⟨a, h1, h2⟩ := reaches_done xs w' ⟨y, hy', hd⟩
      exact ⟨a, by simp [run, h, h1], by simpa [run, h, Action.final] using h2⟩
    · exact ⟨a, by simp [run, h, run_done], by simp [run, h, run_done, ha]⟩

/-- **Exactly one final state**: with a decisive attempt, the recipient ends
done and exactly one final notice was issued. -/
theorem exactly_one_final (xs : List (Nat × Outcome)) (h : ∃ x ∈ xs, Decisive p x) :
    ∃ a, (run rfc p (.queued 0) xs).1 = .done a ∧
      ((run rfc p (.queued 0) xs).2.filter Action.final).length = 1 :=
  reaches_done p xs 0 h

/-! ## Examples and mutants -/

/-- Give up at time 100; warn at most twice. -/
def policy : Policy := ⟨100, 2⟩

/-- Five temporary failures, the last after the give-up time: two warnings, then
one failure. The hypotheses of `exactly_one_final` meet. -/
example : (∃ x ∈ [(10, Outcome.temporary), (20, .temporary), (30, .temporary), (40, .temporary),
      (100, .temporary)], Decisive policy x) ∧
    (run rfc policy (.queued 0) [(10, .temporary), (20, .temporary), (30, .temporary), (40, .temporary),
      (100, .temporary)]).2 = [.delayed, .delayed, .failed] := by
  refine ⟨⟨(100, .temporary), by simp, Or.inl (by decide)⟩, by decide⟩

/-- A system that never gives up reaches no final state, however late it tries. -/
theorem no_giveup_no_final (n : Nat) :
    ((run { givesUp := false } policy (.queued 0) ((List.range n).map fun t => (t, .temporary))).2.filter
      Action.final).length = 0 := by
  have : ∀ (ts : List Nat) (w : Nat),
      ((run { givesUp := false } policy (.queued w) (ts.map fun t => (t, .temporary))).2.filter
        Action.final).length = 0 ∧
      ∃ w', (run { givesUp := false } policy (.queued w) (ts.map fun t => (t, .temporary))).1 = .queued w' := by
    intro ts
    induction ts with
    | nil => intro w; simp [run]
    | cons t ts ih =>
      intro w
      simp only [List.map_cons, run, attempt, onTemporary, Bool.false_and, Bool.false_eq_true,
        if_false]
      split
      · obtain ⟨h1, h2⟩ := ih (w + 1)
        exact ⟨by simpa [Action.final] using h1, h2⟩
      · obtain ⟨h1, h2⟩ := ih w
        exact ⟨by simpa using h1, h2⟩
  exact (this _ 0).1

/-- Temporary failures every 25 seconds reach the give-up time, and under the
rule they end in failure. -/
example : (run rfc policy (.queued 0) ((List.range 5).map fun t => (25 * t, .temporary))).1 =
    .done .failed := by
  decide

/-- A system that warns on every temporary failure: five warnings where the
policy allows two. -/
theorem uncapped_warnings :
    ((run { capped := false } policy (.queued 0) [(10, .temporary), (20, .temporary), (30, .temporary),
      (40, .temporary), (50, .temporary)]).2.filter (· == .delayed)).length = 5 := by decide

/-- A system that keeps attempting after a final state reports a failure and
then a delivery for the same recipient. -/
theorem reopened_two_finals :
    (run { sticky := false } policy (.queued 0) [(10, .permanent), (20, .accepted)]).2 =
      [.failed, .delivered] := by decide

end Mettapedia.Protocols.Mail.DeliveryStatus
