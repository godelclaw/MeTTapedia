import Mettapedia.Machines.Cursor.Scheduling

/-!
# State-dependent budgets for retained cursor execution

A policy sees its own memory, the complete retained computation, and prior
rounds. It proposes a natural-valued inspection budget and updated policy
memory. The scheduler applies only `Cursor.resume`: the policy has no operation
for replacing the residual, inventing an answer, or silently discarding one.

After finitely many rounds, the actual packet/outcome and operation receipt
equal uninterrupted execution at the sum of the budgets actually chosen.
Policies need not be fixed, positive, geometric, monotone, or independent of
observed answers. A learned cost model or history-dependent controller can
supply this policy without acquiring semantic authority over the computation.

The history is newest-first and retains exact post-round states. This is a
mathematical record, not a prescribed runtime logging representation. Budgets
count protocol inspections. Receipts retain the realization's declared charge;
neither quantity is automatically CPU time or the cost of deciding the policy.
An opaque provider transition has no internal scheduling points here. Progress
requires enough cumulative budget; it does not follow merely from having a
policy. No search optimality or physical-time fairness claim is made.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.AdaptiveBudget

open Mettapedia.TypeTheory

universe u v w

variable {Base : Type u} {Index : Base → Type u}
variable {P : IndexedPolynomial.{u,u,u,u} Base Index}
variable {Return : (base : Base) → Index base → Type u}
variable (M : Provider P) (C : Client (P := P) (Return := Return))

structure Round (base : Base) where
  budget : Nat
  after : Scheduling.Cell M C base

structure State (Memory : Type v) (base : Base) where
  memory : Memory
  history : List (Round M C base)
  current : Scheduling.Cell M C base

/-- Policy output contains a budget and policy memory, never a cursor packet. -/
abbrev Policy (Memory : Type v) (base : Base) :=
  State M C Memory base → Nat × Memory

variable (charge : Charge M)
variable {Memory : Type v} {base : Base}

def step (policy : Policy M C Memory base) (state : State M C Memory base) :
    State M C Memory base :=
  let choice := policy state
  let next := resume M C charge choice.1 state.current
  ⟨choice.2, ⟨choice.1, next⟩ :: state.history, next⟩

/-- Iterate the common resumption operation; no alternate evaluator is used. -/
def run (policy : Policy M C Memory base) : Nat → State M C Memory base → State M C Memory base
  | 0, state => state
  | rounds + 1, state => step M C charge policy (run policy rounds state)

/-- Only budgets chosen in this run are counted; preexisting history remains
available to the policy but is not charged again. Order is newest-first. -/
def chosenBudgets (policy : Policy M C Memory base) (rounds : Nat)
    (initial : State M C Memory base) : List Nat :=
  ((run M C charge policy rounds initial).history.take rounds).map Round.budget

def allocation (policy : Policy M C Memory base) (rounds : Nat)
    (initial : State M C Memory base) : Nat :=
  (chosenBudgets M C charge policy rounds initial).sum

theorem chosenBudgets_succ (policy : Policy M C Memory base) (rounds : Nat)
    (initial : State M C Memory base) :
    chosenBudgets M C charge policy (rounds + 1) initial =
      (policy (run M C charge policy rounds initial)).1 ::
        chosenBudgets M C charge policy rounds initial := rfl

theorem allocation_succ (policy : Policy M C Memory base) (rounds : Nat)
    (initial : State M C Memory base) :
    allocation M C charge policy (rounds + 1) initial =
      (policy (run M C charge policy rounds initial)).1 +
        allocation M C charge policy rounds initial := by
  simp only [allocation, chosenBudgets_succ, List.sum_cons]

/-- History cannot be rewritten by the policy. Earlier checkpoints survive. -/
theorem history_suffix (policy : Policy M C Memory base) (rounds : Nat)
    (initial : State M C Memory base) :
    (run M C charge policy rounds initial).history.drop rounds = initial.history := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simpa only [run, step, List.drop_succ_cons] using ih

theorem history_length (policy : Policy M C Memory base) (rounds : Nat)
    (initial : State M C Memory base) :
    (run M C charge policy rounds initial).history.length = rounds + initial.history.length := by
  induction rounds with
  | zero => simp [run]
  | succ rounds ih => simp only [run, step, List.length_cons, ih]; omega

/-- Exact execution for arbitrary adaptive choices. The equality retains the
complete packet/outcome and accumulated operation receipt, not just answers. -/
theorem execution_exact (policy : Policy M C Memory base) (rounds : Nat)
    (initial : State M C Memory base) :
    (run M C charge policy rounds initial).current =
      resume M C charge (allocation M C charge policy rounds initial) initial.current := by
  induction rounds with
  | zero => simp [run, allocation, chosenBudgets]
  | succ rounds ih =>
      change resume M C charge (policy (run M C charge policy rounds initial)).1
        (run M C charge policy rounds initial).current = _
      rw [ih, allocation_succ]
      simpa only [Nat.add_comm] using
        (resume_add M C charge (allocation M C charge policy rounds initial)
          (policy (run M C charge policy rounds initial)).1 initial.current).symm

/-! ## Policies that do not retain decision history

The full policy type permits inspecting prior rounds. Policies constructed
from current memory and the retained cursor instead have a direct loop with
no decision-log field. Its erasure law preserves memory, packet and charge;
the recorded scheduler is a specification, not a runtime prerequisite.
-/

abbrev LocalPolicy (Memory : Type v) (base : Base) :=
  Memory × Scheduling.Cell M C base → Nat × Memory

def forgetDecisions (state : State M C Memory base) :
    Memory × Scheduling.Cell M C base := (state.memory, state.current)

def liftLocal (policy : LocalPolicy M C Memory base) : Policy M C Memory base :=
  fun state => policy (forgetDecisions M C state)

/-- The same `resume` operation, without constructing a history entry. -/
def localStep (policy : LocalPolicy M C Memory base)
    (state : Memory × Scheduling.Cell M C base) : Memory × Scheduling.Cell M C base :=
  let choice := policy state
  (choice.2, resume M C charge choice.1 state.2)

/-- Tail-recursive execution for a policy that does not read prior rounds. -/
def localRun (policy : LocalPolicy M C Memory base) :
    Nat → Memory × Scheduling.Cell M C base → Memory × Scheduling.Cell M C base
  | 0, state => state
  | rounds + 1, state => localRun policy rounds (localStep M C charge policy state)

theorem localRun_succ (policy : LocalPolicy M C Memory base) (rounds : Nat)
    (state : Memory × Scheduling.Cell M C base) :
    localRun M C charge policy (rounds + 1) state =
      localStep M C charge policy (localRun M C charge policy rounds state) := by
  induction rounds generalizing state with
  | zero => rfl
  | succ rounds ih => exact ih (localStep M C charge policy state)

theorem localStep_erasure (policy : LocalPolicy M C Memory base)
    (state : State M C Memory base) :
    forgetDecisions M C (step M C charge (liftLocal M C policy) state) =
      localStep M C charge policy (forgetDecisions M C state) := rfl

/-- The unrecorded loop realizes the projection of recorded execution for
every initial history, number of rounds and current-state policy. -/
theorem localRun_erasure (policy : LocalPolicy M C Memory base) (rounds : Nat)
    (initial : State M C Memory base) :
    forgetDecisions M C (run M C charge (liftLocal M C policy) rounds initial) =
      localRun M C charge policy rounds (forgetDecisions M C initial) := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      rw [run, localStep_erasure, localRun_succ, ih]

theorem local_execution_exact (policy : LocalPolicy M C Memory base) (rounds : Nat)
    (initial : State M C Memory base) :
    (localRun M C charge policy rounds (forgetDecisions M C initial)).2 =
      resume M C charge (allocation M C charge (liftLocal M C policy) rounds initial)
        initial.current := by
  rw [← localRun_erasure]
  exact execution_exact M C charge (liftLocal M C policy) rounds initial

def start (memory : Memory) (packet : Packet M C base) : State M C Memory base :=
  ⟨memory, [], (0, .paused packet)⟩

/-- Starting with a fresh packet gives uninterrupted `advance` at the actual
sum of the adaptive policy's choices. -/
theorem advance_exact (policy : Policy M C Memory base) (rounds : Nat)
    (memory : Memory) (packet : Packet M C base) :
    (run M C charge policy rounds (start M C memory packet)).current =
      advance M C charge
        (allocation M C charge policy rounds (start M C memory packet)) packet := by
  simpa only [start, resume, Nat.zero_add] using
    execution_exact M C charge policy rounds (start M C memory packet)

/-- Different policy memories and history can choose different rounds. Equal
actual cumulative allocations still give the same complete execution. -/
theorem policies_agree_at_same_allocation {OtherMemory : Type w}
    (left : Policy M C Memory base) (right : Policy M C OtherMemory base)
    (leftRounds rightRounds : Nat) (leftStart : State M C Memory base)
    (rightStart : State M C OtherMemory base)
    (sameStart : leftStart.current = rightStart.current)
    (sameBudget : allocation M C charge left leftRounds leftStart =
      allocation M C charge right rightRounds rightStart) :
    (run M C charge left leftRounds leftStart).current =
      (run M C charge right rightRounds rightStart).current := by
  rw [execution_exact, execution_exact, sameBudget, sameStart]

/-- Once complete, further budget decisions cannot poll the provider again. -/
theorem completed_is_inert (policy : Policy M C Memory base) (rounds : Nat)
    (initial : State M C Memory base) (spent : Nat)
    (result : Finished M (Return := Return) base)
    (completed : initial.current = (spent, .done result)) :
    (run M C charge policy rounds initial).current = (spent, .done result) := by
  rw [execution_exact, completed, resume_done]

theorem completion_of_sufficient_budget (policy : Policy M C Memory base)
    (rounds needed spent : Nat) (initial : State M C Memory base)
    (result : Finished M (Return := Return) base)
    (completed : resume M C charge needed initial.current = (spent, .done result))
    (enough : needed ≤ allocation M C charge policy rounds initial) :
    (run M C charge policy rounds initial).current = (spent, .done result) := by
  rw [execution_exact]
  have split : allocation M C charge policy rounds initial =
      needed + (allocation M C charge policy rounds initial - needed) := by omega
  rw [split, resume_add, completed, resume_done]

/-- Conditional liveness: the computation completes if the chosen budgets
eventually cover a sufficient uninterrupted prefix. Zero-budget rounds remain
allowed. This assumption concerns allocated work, not the desired result. -/
theorem eventually_completes (policy : Policy M C Memory base)
    (needed spent : Nat) (initial : State M C Memory base)
    (result : Finished M (Return := Return) base)
    (completed : resume M C charge needed initial.current = (spent, .done result))
    (eventuallyEnough : ∃ rounds, needed ≤ allocation M C charge policy rounds initial) :
    ∃ rounds, (run M C charge policy rounds initial).current = (spent, .done result) := by
  obtain ⟨rounds, enough⟩ := eventuallyEnough
  exact ⟨rounds, completion_of_sufficient_budget M C charge policy rounds needed spent
    initial result completed enough⟩

def zeroPolicy : Policy M C Memory base := fun state => (0, state.memory)

theorem zero_policy_unchanged (rounds : Nat) (initial : State M C Memory base) :
    (run M C charge (zeroPolicy M C) rounds initial).current = initial.current := by
  induction rounds with
  | zero => rfl
  | succ rounds ih => simpa only [run, step, zeroPolicy, resume_zero] using ih

/-- Stop granting inspections once the retained cumulative charge reaches a
limit. The charge has the selected provider metric; it need not count polls.
This observes between rounds, so an admitted round may cross the limit.
It neither predicts that round's charge nor discards its residual. -/
def stopAtCharge (limit : Nat) (policy : Policy M C Memory base) :
    Policy M C Memory base := fun state =>
  if limit ≤ state.current.1 then (0, state.memory) else policy state

/-- A charge guard preserves the current-state policy boundary. -/
theorem stopAtCharge_liftLocal (limit : Nat) (policy : LocalPolicy M C Memory base) :
    stopAtCharge M C limit (liftLocal M C policy) =
      liftLocal M C (fun state =>
        if limit ≤ state.2.1 then (0, state.1) else policy state) := rfl

theorem stopAtCharge_below (limit : Nat) (policy : Policy M C Memory base)
    (state : State M C Memory base) (below : state.current.1 < limit) :
    stopAtCharge M C limit policy state = policy state :=
  if_neg (Nat.not_le.mpr below)

theorem stopAtCharge_reached (limit : Nat) (policy : Policy M C Memory base)
    (state : State M C Memory base) (reached : limit ≤ state.current.1) :
    stopAtCharge M C limit policy state = (0, state.memory) :=
  if_pos reached

/-- Reaching the limit preserves the exact owned cursor and cumulative paid
charge; no provider poll or replacement packet is introduced. -/
theorem stopped_step_current (limit : Nat) (policy : Policy M C Memory base)
    (state : State M C Memory base) (reached : limit ≤ state.current.1) :
    (step M C charge (stopAtCharge M C limit policy) state).current = state.current := by
  simp only [step, stopAtCharge_reached M C limit policy state reached, resume_zero]

theorem stopped_step_memory (limit : Nat) (policy : Policy M C Memory base)
    (state : State M C Memory base) (reached : limit ≤ state.current.1) :
    (step M C charge (stopAtCharge M C limit policy) state).memory = state.memory := by
  simp only [step, stopAtCharge_reached M C limit policy state reached]

/-- Repeated budget decisions after the stop keep the same residual. Policy
memory and the mathematical decision log cannot restart its computation. -/
theorem stopped_run_current (limit : Nat) (policy : Policy M C Memory base)
    (rounds : Nat) (initial : State M C Memory base)
    (reached : limit ≤ initial.current.1) :
    (run M C charge (stopAtCharge M C limit policy) rounds initial).current =
      initial.current := by
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      change (step M C charge (stopAtCharge M C limit policy)
        (run M C charge (stopAtCharge M C limit policy) rounds initial)).current = _
      rw [stopped_step_current]
      · exact ih
      · simpa only [ih] using reached

namespace Controls

open Scheduling.Controls (provider client receipt)

def initial : State provider client Nat () :=
  ⟨0, [], Scheduling.Controls.initial false⟩

/-- Initial quantum from history; later quanta from actual provider state;
completed computations receive zero. Policy memory records decision count. -/
def adaptive : Policy provider client Nat () := fun state =>
  if state.history.isEmpty then (1, state.memory + 1)
  else match state.current.2 with
    | .paused live => (Nat.succ live.2.2, state.memory + 1)
    | .done _ => (0, state.memory + 1)

theorem first_round_keeps_residual :
    (run provider client receipt adaptive 1 initial).current =
      (2, .paused ⟨(), (([2], 1), (1 : Nat))⟩) := rfl

theorem actual_adaptive_budgets :
    chosenBudgets provider client receipt adaptive 3 initial = [0, 2, 1] ∧
      allocation provider client receipt adaptive 3 initial = 3 ∧
      (run provider client receipt adaptive 3 initial).memory = 3 := by
  constructor
  · rfl
  constructor <;> rfl

theorem adaptive_finishes_without_replay :
    (run provider client receipt adaptive 3 initial).current =
      (5, .done ⟨(), 3, (3 : Nat)⟩) := rfl

/-- Receipt five records operation costs; budget three counts inspections. -/
theorem receipt_is_not_allocated_budget :
    (run provider client receipt adaptive 3 initial).current.1 ≠
      allocation provider client receipt adaptive 3 initial := by decide

theorem charge_limit_keeps_pending_cursor :
    (run provider client receipt (stopAtCharge provider client 2 adaptive) 4 initial).current =
      (run provider client receipt adaptive 1 initial).current := rfl

/-- An inspection can cost more than the threshold. The policy stops before
the next inspection; it does not promise a strict preemptive charge cap. -/
theorem charge_threshold_can_overshoot :
    (run provider client receipt (stopAtCharge provider client 1 adaptive) 1 initial).current.1 = 2 ∧
      (run provider client receipt (stopAtCharge provider client 1 adaptive) 4 initial).current =
        (run provider client receipt adaptive 1 initial).current := by
  constructor <;> rfl

def currentOnly : LocalPolicy provider client Nat () :=
  fun state => (1, state.1 + 1)

theorem local_loop_preserves_completion_and_charge :
    localRun provider client receipt currentOnly 3 (0, initial.current) =
      (3, (5, .done ⟨(), 3, (3 : Nat)⟩)) := rfl

/-- A policy that checks earlier decisions cannot be silently assigned the
current-state interface: identical memory and cursor can choose differently. -/
theorem earlier_decisions_can_change_policy :
    let policy : Policy provider client Nat () := fun state =>
      if state.history.isEmpty then (1, state.memory) else (0, state.memory)
    policy initial ≠ policy { initial with history := [⟨0, initial.current⟩] } := by
  decide

theorem finite_work_can_starve :
    advance provider client receipt 3 (base := ()) ⟨(), (([1, 2], 0), (0 : Nat))⟩ =
      (5, .done ⟨(), 3, (3 : Nat)⟩) ∧
    ∀ rounds, Scheduling.Controls.summary
      (run provider client receipt (zeroPolicy provider client) rounds initial).current =
      (0, none) := by
  constructor
  · rfl
  · intro rounds
    rw [zero_policy_unchanged]
    rfl

/-- Restarting with each individual quantum can fail to finish work that
the same cumulative allocation completes by resumption. -/
theorem restarting_loses_progress :
    Scheduling.Controls.summary
      (advance provider client receipt 2 (base := ()) ⟨(), (([1, 2], 0), (0 : Nat))⟩) ≠
    Scheduling.Controls.summary (run provider client receipt adaptive 2 initial).current := by
  decide

end Controls

#print axioms chosenBudgets_succ
#print axioms allocation_succ
#print axioms history_suffix
#print axioms history_length
#print axioms execution_exact
#print axioms localRun_succ
#print axioms localStep_erasure
#print axioms localRun_erasure
#print axioms local_execution_exact
#print axioms stopAtCharge_liftLocal
#print axioms advance_exact
#print axioms policies_agree_at_same_allocation
#print axioms completed_is_inert
#print axioms completion_of_sufficient_budget
#print axioms eventually_completes
#print axioms zero_policy_unchanged
#print axioms stopAtCharge_below
#print axioms stopAtCharge_reached
#print axioms stopped_step_current
#print axioms stopped_step_memory
#print axioms stopped_run_current
#print axioms Controls.first_round_keeps_residual
#print axioms Controls.actual_adaptive_budgets
#print axioms Controls.adaptive_finishes_without_replay
#print axioms Controls.receipt_is_not_allocated_budget
#print axioms Controls.charge_limit_keeps_pending_cursor
#print axioms Controls.charge_threshold_can_overshoot
#print axioms Controls.local_loop_preserves_completion_and_charge
#print axioms Controls.earlier_decisions_can_change_policy
#print axioms Controls.finite_work_can_starve
#print axioms Controls.restarting_loses_progress

end Mettapedia.Machines.Cursor.AdaptiveBudget
