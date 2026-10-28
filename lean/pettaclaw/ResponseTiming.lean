import EventPump

/-!
# Local responsiveness, provider completion, and periodic work

`EventPump` already bounds local service in wall time, conditional on the
duration of the entire scheduling slot. This file separates that bound from
external provider completion and checks the additional deadline condition for
periodic work. Times use one common unit and one monotone clock.

The answer model assumes local dispatch and an independent provider readiness
time, followed by bounded delivery work. Real providers and remote delivery
need their own bounds; none is inferred from cooperative fairness. For a
provider submitted only after dispatch, its ready time includes that delay.
The periodic handler cost includes the local work whose deadline is claimed.
It does not imply that a remote chat service receives the message on time.

These are integration obligations, not a proof of the live host scheduler.
-/

namespace ResponseTiming

def answerTime (localReady providerReady deliveryCost : Nat) : Nat :=
  max localReady providerReady + deliveryCost

theorem answer_requires_provider (localReady providerReady deliveryCost : Nat) :
    providerReady ≤ answerTime localReady providerReady deliveryCost := by
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_right _ _)

/-- An arbitrarily responsive dispatcher supplies no uniform answer deadline
when provider readiness is unbounded. -/
theorem local_service_does_not_bound_answer (bound : Nat) :
    ∃ localReady providerReady,
      localReady ≤ bound ∧ answerTime localReady providerReady 0 > bound := by
  refine ⟨0, bound + 1, Nat.zero_le _, ?_⟩
  simp [answerTime]

theorem answer_bound_needs_external_bounds
    (localReady providerReady deliveryCost localBound providerBound deliveryBound : Nat)
    (localBounded : localReady ≤ localBound) (provider : providerReady ≤ providerBound)
    (delivery : deliveryCost ≤ deliveryBound) :
    answerTime localReady providerReady deliveryCost ≤
      max localBound providerBound + deliveryBound := by
  have ready : max localReady providerReady ≤ max localBound providerBound :=
    Nat.max_le.mpr
      ⟨Nat.le_trans localBounded (Nat.le_max_left _ _),
       Nat.le_trans provider (Nat.le_max_right _ _)⟩
  exact Nat.add_le_add ready delivery

/-- The pump bound can be extended to a delivered notice only when the
outbound work is bounded too. Durations include store and evaluator overhead. -/
theorem notice_bound_includes_outbound
    (durations : List Nat) (capacity quantum intake outbound outboundBound : Nat)
    (count : durations.length ≤ capacity)
    (slots : ∀ duration ∈ durations, duration ≤ quantum)
    (delivery : outbound ≤ outboundBound) :
    intake + durations.sum + outbound ≤
      intake + capacity * quantum + outboundBound := by
  have total := EventPump.bounded_slot_time durations quantum slots
  have queued := Nat.le_trans total (Nat.mul_le_mul_right quantum count)
  exact Nat.add_le_add (Nat.add_le_add_left queued intake) delivery

def release (iteration period : Nat) : Nat := iteration * period

/-- Absolute timer releases meet the next release's deadline if the full
dispatch delay and handler cost fit inside one period. -/
theorem periodic_deadline_from_slot_bounds
    (iteration period intake capacity quantum handler : Nat)
    (durations : List Nat)
    (count : durations.length ≤ capacity)
    (slots : ∀ duration ∈ durations, duration ≤ quantum)
    (fits : intake + capacity * quantum + handler ≤ period) :
    release iteration period + intake + durations.sum + handler ≤
      release (iteration + 1) period := by
  have total := EventPump.bounded_slot_time durations quantum slots
  have queued := Nat.le_trans total (Nat.mul_le_mul_right quantum count)
  have budget : intake + durations.sum + handler ≤ period :=
    Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_left queued intake) handler) fits
  simpa [release, Nat.add_mul, Nat.add_assoc] using
    Nat.add_le_add_left budget (iteration * period)

/-- Sleeping for the period after each handler accumulates handler cost.
Absolute release times avoid this arithmetic drift; they do not remove jitter. -/
theorem fixed_delay_accumulates_handler_cost (iteration period handler : Nat) :
    iteration * (period + handler) = release iteration period + iteration * handler := by
  simp [release, Nat.mul_add]

end ResponseTiming
