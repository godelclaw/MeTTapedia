import Std

/-!
# Cooperative service with continuing arrivals

A retained task rotates behind the current queue and ahead of newly arriving
work. This policy supplies logical service; bounded native slot durations are
a separate implementation obligation. Extracted from the event-pump contract
at godelclaw/MeTTapedia commit 562e3c8af4be9f2984bf7783eb71771ce9417d2a.
-/

namespace Mettapedia.Machines.CooperativeQueue

universe u

/-- A concrete fair policy; this does not claim Tokio uses round-robin. Each
successful slot pops one task, requeues its continuation, then appends arrivals.
Waiting tasks are omitted from this runnable queue and retain their own state. -/
def services {α : Type u} : Nat → (Nat → List α) → List α → List α
  | 0, _, _ => []
  | n + 1, arrivals, [] => services n (fun i => arrivals (i + 1)) (arrivals 0)
  | n + 1, arrivals, head :: tail =>
      head :: services n (fun i => arrivals (i + 1)) (tail ++ [head] ++ arrivals 0)

/-- A visit can retire its head after service. New arrivals remain behind
the old waiting prefix. Imported from the ready-order contract at
godelclaw/MeTTapedia commit 262e6f38993617ba8a438432299e658d3988fe21. -/
def servicesRetiring {α : Type u} : Nat → (Nat → Bool) → (Nat → List α) → List α → List α
  | 0, _, _, _ => []
  | n + 1, keep, arrivals, [] =>
      servicesRetiring n (fun i => keep (i + 1)) (fun i => arrivals (i + 1)) (arrivals 0)
  | n + 1, keep, arrivals, head :: tail =>
      head :: servicesRetiring n (fun i => keep (i + 1)) (fun i => arrivals (i + 1))
        (tail ++ (if keep 0 then [head] else []) ++ arrivals 0)

theorem servicesRetiring_retained {α : Type u} (n : Nat)
    (arrivals : Nat → List α) (queue : List α) :
    servicesRetiring n (fun _ => true) arrivals queue = services n arrivals queue := by
  induction n generalizing arrivals queue with
  | zero => rfl
  | succ n ih => cases queue <;> simp [servicesRetiring, services, ih]

theorem prefix_served_despite_retirement_and_arrivals {α : Type u}
    (before suffix : List α) (target : α) (keep : Nat → Bool) (arrivals : Nat → List α) :
    target ∈ servicesRetiring (before.length + 1) keep arrivals (before ++ target :: suffix) := by
  induction before generalizing suffix keep arrivals with
  | nil => simp [servicesRetiring]
  | cons head before ih =>
    simp only [List.length_cons, List.cons_append, servicesRetiring]
    apply List.mem_cons_of_mem
    simpa only [List.append_assoc, List.cons_append] using
      ih (suffix ++ (if keep 0 then [head] else []) ++ arrivals 0)
        (fun i => keep (i + 1)) (fun i => arrivals (i + 1))

theorem queued_task_gets_bounded_service_with_retirement {α : Type u} (queue : List α) (target : α)
    (keep : Nat → Bool) (arrivals : Nat → List α) (member : target ∈ queue) :
    ∃ slots ≤ queue.length, target ∈ servicesRetiring slots keep arrivals queue := by
  obtain ⟨before, suffix, rfl⟩ := List.mem_iff_append.mp member
  refine ⟨before.length + 1, ?_,
    prefix_served_despite_retirement_and_arrivals before suffix target keep arrivals⟩
  simp

/-- Arbitrarily continuing arrivals cannot jump ahead of a queued prefix. -/
theorem prefix_served_despite_arrivals {α : Type u} (before suffix : List α)
    (target : α) (arrivals : Nat → List α) :
    target ∈ services (before.length + 1) arrivals (before ++ target :: suffix) := by
  simpa only [servicesRetiring_retained] using
    prefix_served_despite_retirement_and_arrivals before suffix target (fun _ => true) arrivals

theorem queued_task_gets_bounded_service {α : Type u} (queue : List α) (target : α)
    (arrivals : Nat → List α) (member : target ∈ queue) :
    ∃ slots ≤ queue.length, target ∈ services slots arrivals queue := by
  obtain ⟨before, suffix, rfl⟩ := List.mem_iff_append.mp member
  refine ⟨before.length + 1, ?_, prefix_served_despite_arrivals before suffix target arrivals⟩
  simp

/-- The next queue retains the dispatched task. This policy applies while a
task stays runnable; completion and blocking require explicit removal. -/
def rotate {α : Type u} (arrivals queue : List α) : List α :=
  match queue with
  | [] => arrivals
  | head :: tail => tail ++ [head] ++ arrivals

/-- Preserve the complete queue across a bounded slice, including arrivals. -/
def remaining {α : Type u} : Nat → (Nat → List α) → List α → List α
  | 0, _, queue => queue
  | n + 1, arrivals, queue =>
      remaining n (fun i => arrivals (i + 1)) (rotate (arrivals 0) queue)

theorem rotate_preserves_member {α : Type u} (arrivals queue : List α) (target : α)
    (member : target ∈ queue) : target ∈ rotate arrivals queue := by
  cases queue with
  | nil => simp at member
  | cons head tail =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp [rotate]
      · simp [rotate, member]

theorem remaining_preserves_member {α : Type u} (slots : Nat)
    (arrivals : Nat → List α) (queue : List α) (target : α)
    (member : target ∈ queue) : target ∈ remaining slots arrivals queue := by
  induction slots generalizing arrivals queue with
  | zero => exact member
  | succ slots ih =>
      exact ih _ _ (rotate_preserves_member (arrivals 0) queue target member)

/-- Finite slicing neither repeats a service nor loses the residual queue. -/
theorem services_add {α : Type u} (first second : Nat)
    (arrivals : Nat → List α) (queue : List α) :
    services (first + second) arrivals queue = services first arrivals queue ++
      services second (fun i => arrivals (i + first)) (remaining first arrivals queue) := by
  induction first generalizing arrivals queue with
  | zero => simp [services, remaining]
  | succ first ih =>
      cases queue with
      | nil =>
          simpa only [Nat.succ_add, Nat.zero_add, services, remaining, rotate, Nat.add_assoc,
            Nat.add_comm first 1] using ih (fun i => arrivals (i + 1)) (arrivals 0)
      | cons head tail =>
          simp only [Nat.succ_add, services, remaining, rotate, List.cons_append]
          congr 1
          simpa only [Nat.add_assoc, Nat.add_comm first 1] using
            ih (fun i => arrivals (i + 1)) (tail ++ [head] ++ arrivals 0)

/-- A continuously queued task receives every finite demand, even with
unboundedly growing queues. No bound on queue growth or task termination is
assumed, so this is an existence theorem rather than a uniform latency bound. -/
theorem unbounded_service {α : Type u} [DecidableEq α] (demand : Nat)
    (arrivals : Nat → List α) (queue : List α) (target : α)
    (member : target ∈ queue) :
    ∃ slots, demand ≤ (services slots arrivals queue).count target := by
  induction demand generalizing arrivals queue with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ demand ih =>
      obtain ⟨first, _, served⟩ := queued_task_gets_bounded_service queue target arrivals member
      obtain ⟨second, enough⟩ := ih (fun i => arrivals (i + first))
        (remaining first arrivals queue) (remaining_preserves_member first arrivals queue target member)
      refine ⟨first + second, ?_⟩
      rw [services_add, List.count_append]
      have positive : 0 < (services first arrivals queue).count target :=
        List.count_pos_iff.mpr served
      omega

/-- Residual of the existing retiring service policy. A completed head is
removed before arrivals join the tail. -/
def rotateRetiring {α : Type u} (keep : Bool) (arrivals queue : List α) : List α :=
  match queue with
  | [] => arrivals
  | head :: tail => tail ++ (if keep then [head] else []) ++ arrivals

/-- Retain the whole queue across the same retiring slots. -/
def remainingRetiring {α : Type u} : Nat → (Nat → Bool) → (Nat → List α) → List α → List α
  | 0, _, _, queue => queue
  | n + 1, keep, arrivals, queue =>
      remainingRetiring n (fun i => keep (i + 1)) (fun i => arrivals (i + 1))
        (rotateRetiring (keep 0) (arrivals 0) queue)

theorem retiring_services_add {α : Type u} (first second : Nat)
    (keep : Nat → Bool) (arrivals : Nat → List α) (queue : List α) :
    servicesRetiring (first + second) keep arrivals queue =
      servicesRetiring first keep arrivals queue ++
        servicesRetiring second (fun i => keep (i + first)) (fun i => arrivals (i + first))
          (remainingRetiring first keep arrivals queue) := by
  induction first generalizing keep arrivals queue with
  | zero => simp [servicesRetiring, remainingRetiring]
  | succ first ih =>
      cases queue with
      | nil =>
          simpa only [Nat.succ_add, Nat.zero_add, servicesRetiring, remainingRetiring, rotateRetiring,
            Nat.add_assoc, Nat.add_comm first 1] using
              ih (fun i => keep (i + 1)) (fun i => arrivals (i + 1)) (arrivals 0)
      | cons head tail =>
          simp only [Nat.succ_add, servicesRetiring, remainingRetiring, rotateRetiring, List.cons_append]
          congr 1
          simpa only [Nat.add_assoc, Nat.add_comm first 1] using
            ih (fun i => keep (i + 1)) (fun i => arrivals (i + 1))
              (tail ++ (if keep 0 then [head] else []) ++ arrivals 0)

theorem retiring_remaining_add {α : Type u} (first second : Nat)
    (keep : Nat → Bool) (arrivals : Nat → List α) (queue : List α) :
    remainingRetiring (first + second) keep arrivals queue =
      remainingRetiring second (fun i => keep (i + first)) (fun i => arrivals (i + first))
        (remainingRetiring first keep arrivals queue) := by
  induction first generalizing keep arrivals queue with
  | zero => simp [remainingRetiring]
  | succ first ih =>
      simpa only [Nat.succ_add, Nat.zero_add, remainingRetiring, Nat.add_assoc, Nat.add_comm first 1] using
        ih (fun i => keep (i + 1)) (fun i => arrivals (i + 1)) (rotateRetiring (keep 0) (arrivals 0) queue)

#print axioms retiring_services_add
#print axioms retiring_remaining_add

end Mettapedia.Machines.CooperativeQueue
