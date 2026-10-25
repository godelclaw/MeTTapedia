import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Retrying a model request

A failed model request is retried, held, or reconciled, depending on what the
failure says.

* A **transient** failure (overload, a dropped stream, a timeout before
  sending) is retried after a delay that grows exponentially up to a cap and
  never undercuts a delay the server stated.
* A **rejection** of the request as such (it is too large, or malformed)
  fails again if resent unchanged. It is held until something changes.
* An **uncertain** outcome (the request may have taken effect) is reconciled,
  never replayed.

Proved:

* the policy never resends after a rejection, never replays an uncertain
  outcome, and honours a stated delay (`policy_rejected`, `policy_uncertain`,
  `policy_wait_honours`);
* with delays of at least one tick and at most a cap, an outage of any length
  is survived: the first attempt after the outage ends comes less than one cap
  after its end (`first_success_within_cap`);
* a policy that gives up after a fixed number of attempts fails every outage
  longer than its total wait (`bounded_gives_up`). For an interactive agent a
  failed turn returns control to the user; for an autonomous one it loses the
  turn, so an autonomous agent retries without an attempt limit and relies on
  the cap for its request rate.

Times are natural numbers in any unit.
-/

set_option autoImplicit false

namespace Mettapedia.CogArch.Agent.CodingAgent.Retry

/-! ## The policy -/

/-- What a request attempt came back with. -/
inductive Outcome where
  | ok
  | transient (stated : Option ℕ)
  | rejected
  | uncertain

/-- What the client does next. -/
inductive Next where
  | done
  | wait (delay : ℕ)
  | hold
  | reconcile
  | giveUp
  deriving DecidableEq

/-- Exponential backoff from `base`, capped at `cap`. -/
def backoff (base cap n : ℕ) : ℕ := min cap (base * 2 ^ n)

/-- The policy after attempt `n`, with an optional attempt limit. -/
def policy (base cap : ℕ) (limit : Option ℕ) (n : ℕ) : Outcome → Next
  | Outcome.ok => Next.done
  | Outcome.transient stated =>
    if limit = some n then Next.giveUp else Next.wait (max (backoff base cap n) (stated.getD 0))
  | Outcome.rejected => Next.hold
  | Outcome.uncertain => Next.reconcile

theorem policy_rejected (base cap : ℕ) (limit : Option ℕ) (n : ℕ) :
    policy base cap limit n Outcome.rejected = Next.hold := rfl

theorem policy_uncertain (base cap : ℕ) (limit : Option ℕ) (n : ℕ) :
    policy base cap limit n Outcome.uncertain = Next.reconcile := rfl

/-- A stated delay is never undercut. -/
theorem policy_wait_honours (base cap : ℕ) (limit : Option ℕ) (n stated d : ℕ)
    (h : policy base cap limit n (Outcome.transient (some stated)) = Next.wait d) :
    stated ≤ d := by
  simp only [policy, Option.getD_some] at h
  split at h
  · cases h
  · injection h with h
    rw [← h]
    exact le_max_right _ _

theorem backoff_le_cap (base cap n : ℕ) : backoff base cap n ≤ cap := min_le_left _ _

/-! ## Outages -/

/-- When attempt `n` is sent, if every earlier attempt failed and attempt `k`
waited `delay k`. -/
def sendTime (delay : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sendTime delay n + delay n

theorem sendTime_ge (delay : ℕ → ℕ) (hpos : ∀ n, 1 ≤ delay n) (n : ℕ) : n ≤ sendTime delay n := by
  induction n with
  | zero => simp [sendTime]
  | succ n ih => have := hpos n; simp only [sendTime]; omega

theorem sendTime_mono (delay : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    sendTime delay m ≤ sendTime delay n := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => simp only [sendTime]; omega

/-- **Outages are survived.** With every delay at least one tick and at most
`cap`, and an outage in which attempts before time `T` fail, some attempt is
sent at or after `T` and less than `cap` after it. -/
theorem first_success_within_cap (delay : ℕ → ℕ) (cap T : ℕ) (hcap : 1 ≤ cap)
    (hpos : ∀ n, 1 ≤ delay n) (hle : ∀ n, delay n ≤ cap) :
    ∃ n, T ≤ sendTime delay n ∧ sendTime delay n < T + cap := by
  classical
  have hex : ∃ n, T ≤ sendTime delay n := ⟨T, sendTime_ge delay hpos T⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  cases hfind : Nat.find hex with
  | zero =>
    have h0 := Nat.find_spec hex
    rw [hfind] at h0
    simp only [sendTime] at h0 ⊢
    omega
  | succ m =>
    have hlt : sendTime delay m < T := by
      have := Nat.find_min hex (show m < Nat.find hex by omega)
      omega
    simp only [sendTime]
    have := hle m
    omega

/-- **A bounded policy gives up on long outages.** If the attempts are limited
to `limit + 1` and the outage outlasts the last of them, every attempt fails. -/
theorem bounded_gives_up (delay : ℕ → ℕ) (limit T : ℕ)
    (hT : sendTime delay limit < T) : ∀ n ≤ limit, sendTime delay n < T := by
  intro n hn
  exact lt_of_le_of_lt (sendTime_mono delay hn) hT

/-- With waits of 200, 400, 800 and 1600 time units and no further attempt,
an outage longer than 3000 units fails the turn. -/
example : sendTime (fun n => 200 * 2 ^ n) 4 = 3000 := by decide

/-- With waits of 2, 4, 8 and 16 capped at 30 and five retries, the client
gives up on outages longer than 60 units. -/
example : sendTime (fun n => min 30 (2 * 2 ^ n)) 5 = 60 := by decide

end Mettapedia.CogArch.Agent.CodingAgent.Retry
