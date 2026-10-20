import Mettapedia.Machines.EventPump
import Mettapedia.GSLT.Contracts.RunAccounts
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# Bounded native ready order

Executable reference for CeTTa's intrusive ready queue. A task's native link
represents membership; its position is independent of the backing slot. An
admission appends, a visit moves the head to the tail, and removal filters only
the named task. The C trace comparison checks these transitions, not pointer
safety or the C compiler. Durable task identities remain outside this cache.

The service adapter composes those same primitives and proves exact agreement
with the shared `CooperativeQueue` policy, including retirement, duplicate
offers and rejected arrivals. Continuing arrivals cannot overtake the existing
prefix. Bounded slices preserve every visit and the complete residual queue.
A visit is an opportunity, not a successful effect or goal completion; the
host must still execute service slots and bound their complete cost. The costed
service adapter accumulates handling, all arrivals and bookkeeping through the
existing run account, and turns an explicit whole-slot bound into a cumulative
requested-service bound. It establishes no native timing bound by dispatch
count alone. The executable contract originates at godelclaw/MeTTapedia commit
262e6f38993617ba8a438432299e658d3988fe21.
-/

namespace Mettapedia.Machines.ReadyQueue

structure State where
  capacity : Nat
  tasks : List Nat := []
  deriving DecidableEq, Repr

inductive Action where
  | admit (task : Nat)
  | remove (task : Nat)
  | visit
  deriving DecidableEq, Repr

structure Observation where
  status : Nat := 0
  visited : Option Nat := none
  deriving DecidableEq, Repr

def step (state : State) (action : Action) : Observation × State :=
  match action with
  | .admit task =>
    match EventPump.admit state.capacity state.tasks task with
    | none => (⟨2, none⟩, state)
    | some tasks => (⟨if task ∈ state.tasks then 1 else 0, none⟩, { state with tasks })
  | .remove task =>
    (⟨if task ∈ state.tasks then 1 else 0, none⟩,
     { state with tasks := state.tasks.filter (fun other => decide (other ≠ task)) })
  | .visit => (⟨0, state.tasks.head?⟩, { state with tasks := CooperativeQueue.rotate [] state.tasks })

def invariant (state : State) : Prop :=
  state.tasks.Nodup ∧ state.tasks.length ≤ state.capacity

def run : List Action → State → State
  | [], state => state
  | action :: rest, state => run rest (step state action).2

theorem rotation_preserves_membership (tasks : List Nat) (task : Nat) :
    task ∈ CooperativeQueue.rotate [] tasks ↔ task ∈ tasks := by
  cases tasks <;> simp [CooperativeQueue.rotate, or_comm]

theorem rotation_preserves_length (tasks : List Nat) :
    (CooperativeQueue.rotate [] tasks).length = tasks.length := by
  cases tasks <;> simp [CooperativeQueue.rotate]

theorem rotation_preserves_uniqueness (tasks : List Nat) (h : tasks.Nodup) :
    (CooperativeQueue.rotate [] tasks).Nodup := by
  cases tasks with
  | nil => simp [CooperativeQueue.rotate]
  | cons first rest =>
    simp only [CooperativeQueue.rotate, List.append_nil]
    have parts := List.nodup_cons.mp h
    apply List.nodup_append.mpr
    refine ⟨parts.2, by simp, ?_⟩
    intro a member b last equal
    simp only [List.mem_singleton] at last
    exact parts.1 (last ▸ (equal ▸ member))

theorem step_preserves_invariant (state : State) (action : Action)
    (h : invariant state) : invariant (step state action).2 := by
  cases action with
  | admit task =>
    simp only [step]
    split
    · exact h
    · rename_i tasks accepted
      exact ⟨EventPump.admission_preserves_unique_tasks _ _ _ _ h.1 accepted,
        EventPump.admission_preserves_capacity _ _ _ _ accepted⟩
  | remove task =>
    exact ⟨h.1.filter _, Nat.le_trans (List.length_filter_le _ _) h.2⟩
  | visit =>
    exact ⟨rotation_preserves_uniqueness _ h.1,
      by simpa [step, rotation_preserves_length] using h.2⟩

theorem trace_preserves_invariant (actions : List Action) (state : State)
    (h : invariant state) : invariant (run actions state) := by
  induction actions generalizing state with
  | nil => exact h
  | cons action rest ih => exact ih _ (step_preserves_invariant state action h)

theorem rejected_admission_keeps_order (state : State) (task : Nat)
    (full : EventPump.admit state.capacity state.tasks task = none) :
    (step state (.admit task)).2 = state := by simp [step, full]

theorem removal_preserves_other_members (state : State) (task other : Nat)
    (different : other ≠ task) :
    other ∈ (step state (.remove task)).2.tasks ↔ other ∈ state.tasks := by
  simp [step, different]

/-- The native visit followed by retirement is precisely the corresponding
service branch. Duplicates cannot remain because queue membership is unique. -/
theorem visit_then_retire (capacity first : Nat) (rest : List Nat)
    (unique : (first :: rest).Nodup) :
    (step (step ⟨capacity, first :: rest⟩ .visit).2 (.remove first)).2.tasks = rest := by
  have absent := (List.nodup_cons.mp unique).1
  simp only [step, CooperativeQueue.rotate, List.filter_append, List.filter_cons, ne_self_iff_false,
    decide_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
  apply List.filter_eq_self.mpr
  intro other member
  simp only [decide_eq_true_eq]
  intro equal
  exact absent (equal ▸ member)

theorem admission_appends_or_stays (state : State) (task : Nat) :
    ∃ suffix, (step state (.admit task)).2.tasks = state.tasks ++ suffix := by
  simp only [step]
  split
  · exact ⟨[], by simp⟩
  · rename_i tasks accepted
    unfold EventPump.admit at accepted
    split at accepted
    · contradiction
    · split
      · simp_all
      · split at accepted
        · simp_all
        · split at accepted
          · cases accepted; exact ⟨[task], rfl⟩
          · contradiction

theorem admissions_preserve_prefix (offered : List Nat) (state : State) :
    ∃ suffix, (run (offered.map Action.admit) state).tasks = state.tasks ++ suffix := by
  induction offered generalizing state with
  | nil => exact ⟨[], by simp [run]⟩
  | cons task rest ih =>
    obtain ⟨first, firstEq⟩ := admission_appends_or_stays state task
    obtain ⟨later, laterEq⟩ := ih (step state (.admit task)).2
    refine ⟨first ++ later, ?_⟩
    simpa only [List.map_cons, run, firstEq, List.append_assoc] using laterEq

/-- The effective arrivals are the suffix actually admitted by the primitive
queue operations, after duplicate and capacity checks. -/
theorem admissions_equal_prefix_append_drop (offered : List Nat) (state : State) :
    (run (offered.map Action.admit) state).tasks = state.tasks ++
      (run (offered.map Action.admit) state).tasks.drop state.tasks.length := by
  obtain ⟨suffix, equal⟩ := admissions_preserve_prefix offered state
  simp [equal]

/-- One native visit, optionally followed by retirement of that visited head.
No other runnable task may be silently removed by this scheduling adapter. -/
def afterVisit (state : State) (keep : Bool) : State :=
  let visited := step state .visit
  match visited.1.visited with
  | none => visited.2
  | some task => if keep then visited.2 else (step visited.2 (.remove task)).2

theorem afterVisit_preserves_invariant (state : State) (keep : Bool)
    (valid : invariant state) : invariant (afterVisit state keep) := by
  cases visitedEq : (step state .visit).1.visited with
  | none => simpa only [afterVisit, visitedEq] using
      step_preserves_invariant state .visit valid
  | some task =>
    simp only [afterVisit, visitedEq]
    split
    · exact step_preserves_invariant state .visit valid
    · exact step_preserves_invariant _ _ (step_preserves_invariant state .visit valid)

theorem afterVisit_tasks (state : State) (keep : Bool) (valid : invariant state) :
    (afterVisit state keep).tasks = match state.tasks with
      | [] => []
      | head :: tail => tail ++ (if keep then [head] else []) := by
  rcases state with ⟨capacity, tasks⟩
  cases tasks with
  | nil => rfl
  | cons head tail =>
    cases keep with
    | true => simp [afterVisit, step, CooperativeQueue.rotate]
    | false =>
      simpa only [afterVisit, step, Bool.false_eq_true, ↓reduceIte, List.head?_cons,
        List.append_nil] using visit_then_retire capacity head tail valid.1

/-- A service slot is made entirely from the existing visit, remove and admit
primitives. Offered arrivals can include duplicates or exceed capacity. -/
def service (state : State) (keep : Bool) (offered : List Nat) : State :=
  run (offered.map Action.admit) (afterVisit state keep)

theorem service_preserves_invariant (state : State) (keep : Bool) (offered : List Nat)
    (valid : invariant state) : invariant (service state keep offered) :=
  trace_preserves_invariant _ _ (afterVisit_preserves_invariant state keep valid)

def admitted (state : State) (keep : Bool) (offered : List Nat) : List Nat :=
  (service state keep offered).tasks.drop (afterVisit state keep).tasks.length

theorem service_tasks (state : State) (keep : Bool) (offered : List Nat)
    (valid : invariant state) :
    (service state keep offered).tasks =
      (match state.tasks with
       | [] => []
       | head :: tail => tail ++ (if keep then [head] else [])) ++
      admitted state keep offered := by
  have equal := admissions_equal_prefix_append_drop offered (afterVisit state keep)
  change (service state keep offered).tasks =
    (afterVisit state keep).tasks ++ admitted state keep offered at equal
  simpa only [afterVisit_tasks state keep valid] using equal

/-- The visited tasks and complete residual queue after a bounded service
slice. This composes primitive transitions; it does not model task execution. -/
def serviceRun : Nat → (Nat → Bool) → (Nat → List Nat) → State → List Nat × State
  | 0, _, _, state => ([], state)
  | n + 1, keep, offered, state =>
    let rest := serviceRun n (fun i => keep (i + 1)) (fun i => offered (i + 1))
      (service state (keep 0) (offered 0))
    ((step state .visit).1.visited.toList ++ rest.1, rest.2)

/-- Actual accepted suffix at each service slot. Rejected offers never enter
the abstract fairness theorem's arrival sequence. -/
def admittedArrivals (state : State) (keep : Nat → Bool) (offered : Nat → List Nat) :
    Nat → List Nat
  | 0 => admitted state (keep 0) (offered 0)
  | n + 1 => admittedArrivals (service state (keep 0) (offered 0))
      (fun i => keep (i + 1)) (fun i => offered (i + 1)) n

theorem serviceRun_preserves_invariant (slots : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (state : State) (valid : invariant state) :
    invariant (serviceRun slots keep offered state).2 := by
  induction slots generalizing keep offered state with
  | zero => exact valid
  | succ slots ih => exact ih _ _ _ (service_preserves_invariant state _ _ valid)

theorem serviceRun_eq_cooperative (slots : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (state : State) (valid : invariant state) :
    (serviceRun slots keep offered state).1 =
      CooperativeQueue.servicesRetiring slots keep (admittedArrivals state keep offered)
        state.tasks := by
  induction slots generalizing keep offered state with
  | zero => rfl
  | succ slots ih =>
    have nextValid := service_preserves_invariant state (keep 0) (offered 0) valid
    have nextTasks := service_tasks state (keep 0) (offered 0) valid
    simp only [serviceRun, step, ih _ _ _ nextValid]
    cases tasksEq : state.tasks with
    | nil =>
      simp only [tasksEq, CooperativeQueue.servicesRetiring, List.head?_nil,
        Option.toList_none, List.nil_append, admittedArrivals] at *
      rw [nextTasks]
    | cons head tail =>
      simp only [tasksEq, CooperativeQueue.servicesRetiring, List.head?_cons,
        Option.toList_some, List.singleton_append, admittedArrivals] at *
      rw [nextTasks]

theorem queued_task_gets_bounded_service (state : State) (target : Nat)
    (keep : Nat → Bool) (offered : Nat → List Nat) (valid : invariant state)
    (member : target ∈ state.tasks) :
    ∃ slots ≤ state.tasks.length, target ∈ (serviceRun slots keep offered state).1 := by
  obtain ⟨slots, bound, served⟩ :=
    CooperativeQueue.queued_task_gets_bounded_service_with_retirement state.tasks target keep
      (admittedArrivals state keep offered) member
  exact ⟨slots, bound, by simpa only [serviceRun_eq_cooperative slots keep offered state valid]
    using served⟩

/-- A service slice preserves both the observed visits and the whole residual
state, including queue capacity. Arrivals are shifted, never replayed. -/
theorem serviceRun_add (first second : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (state : State) :
    serviceRun (first + second) keep offered state =
      let firstRun := serviceRun first keep offered state
      let suffix := serviceRun second (fun i => keep (i + first))
        (fun i => offered (i + first)) firstRun.2
      (firstRun.1 ++ suffix.1, suffix.2) := by
  induction first generalizing keep offered state with
  | zero => simp [serviceRun]
  | succ first ih =>
    simp only [Nat.succ_add, serviceRun, ih]
    simp only [Nat.add_assoc, Nat.add_comm first 1, List.append_assoc]

/-! ## Whole-slot service accounts

The counter used by `serviceRun` is a count of executed slots. A host cost
profile separately measures the complete slot: handling the visited task,
processing all offers (including rejected offers), and queue bookkeeping.
The costed worker below uses exactly the same transitions and retains the
whole residual state. Its path account is a mathematical reference only;
ordinary service need not construct a path, charge record or execution log.
-/

/-- Three disjoint parts of one complete service slot, in a declared additive
cost profile. Handling may include a native operation; its dispatch count is
not its cost. Empty queues can still incur arrival and bookkeeping costs. -/
structure SlotCharge (Cost : Type*) where
  handling : Cost
  arrivals : Cost
  bookkeeping : Cost
  deriving DecidableEq, Repr

def SlotCharge.total {Cost : Type*} [AddMonoid Cost] (charge : SlotCharge Cost) : Cost :=
  charge.handling + charge.arrivals + charge.bookkeeping

abbrev ServiceMeter (Cost : Type*) := State → Bool → List Nat → SlotCharge Cost

/-- Execute the existing service transition and accumulate its complete
charge. Retired tasks and rejected arrivals follow `service`, not a second
scheduling policy. -/
def costedServiceRun {Cost : Type*} [AddMonoid Cost] (meter : ServiceMeter Cost) :
    Nat → (Nat → Bool) → (Nat → List Nat) → State → (List Nat × State) × Cost
  | 0, _, _, state => (([], state), 0)
  | n + 1, keep, offered, state =>
    let rest := costedServiceRun meter n (fun i => keep (i + 1))
      (fun i => offered (i + 1)) (service state (keep 0) (offered 0))
    (((step state .visit).1.visited.toList ++ rest.1.1, rest.1.2),
      (meter state (keep 0) (offered 0)).total + rest.2)

/-- Cost observation preserves every visit and the complete residual queue. -/
@[simp] theorem costedServiceRun_erases {Cost : Type*} [AddMonoid Cost]
    (meter : ServiceMeter Cost) (slots : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (state : State) :
    (costedServiceRun meter slots keep offered state).1 =
      serviceRun slots keep offered state := by
  induction slots generalizing keep offered state with
  | zero => rfl
  | succ slots ih => simp only [costedServiceRun, serviceRun, ih]

/-- Splitting a costed slice preserves the residual queue and adds the actual
suffix charge. Neither arrivals nor already paid handling are replayed. -/
theorem costedServiceRun_add {Cost : Type*} [AddMonoid Cost]
    (meter : ServiceMeter Cost) (first second : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (state : State) :
    costedServiceRun meter (first + second) keep offered state =
      let firstRun := costedServiceRun meter first keep offered state
      let suffix := costedServiceRun meter second (fun i => keep (i + first))
        (fun i => offered (i + first)) firstRun.1.2
      ((firstRun.1.1 ++ suffix.1.1, suffix.1.2), firstRun.2 + suffix.2) := by
  induction first generalizing keep offered state with
  | zero =>
    simp only [costedServiceRun, List.nil_append, zero_add, Nat.add_zero]
  | succ first ih =>
    simp only [Nat.succ_add, costedServiceRun, ih]
    simp only [Nat.add_comm first 1, List.append_assoc, add_assoc]

/-- Edges are actual applications of `service`, including idle slots. -/
inductive ServiceEdge : State → State → Type where
  | slot (state : State) (keep : Bool) (offered : List Nat) :
      ServiceEdge state (service state keep offered)

abbrev serviceQuiver : Quiver State := ⟨ServiceEdge⟩

/-- The existing general `RunAccount`, labelled by each complete slot. -/
def serviceAccount {Cost : Type*} [AddMonoid Cost] (meter : ServiceMeter Cost) :
    letI := serviceQuiver
    Mettapedia.Effects.RunAccount (_root_.CategoryTheory.Paths State) (Multiplicative Cost) := by
  letI := serviceQuiver
  let label : ∀ {before after : State}, ServiceEdge before after → Multiplicative Cost :=
    fun {before _} edge => by
      cases edge with
      | slot keep offered => exact Multiplicative.ofAdd (meter before keep offered).total
  exact Mettapedia.GSLT.Contracts.Accounts.pathAccount label

/-- A reference path of the uncounted execution; no service driver needs to
allocate this object. -/
def servicePath : (slots : Nat) → (keep : Nat → Bool) → (offered : Nat → List Nat) →
    (state : State) →
    letI := serviceQuiver
    Quiver.Path state (serviceRun slots keep offered state).2
  | 0, _, _, _ => by
    letI := serviceQuiver
    exact .nil
  | n + 1, keep, offered, state => by
    letI := serviceQuiver
    exact (Quiver.Hom.toPath (ServiceEdge.slot state (keep 0) (offered 0))).comp
      (servicePath n (fun i => keep (i + 1)) (fun i => offered (i + 1))
        (service state (keep 0) (offered 0)))

set_option backward.isDefEq.respectTransparency false in
/-- The directly accumulated charge is the independent path account of the
existing uncounted service execution. -/
theorem costedServiceRun_eq_account {Cost : Type*} [AddMonoid Cost]
    (meter : ServiceMeter Cost) (slots : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (state : State) :
    letI := serviceQuiver
    Multiplicative.ofAdd (costedServiceRun meter slots keep offered state).2 =
      (serviceAccount meter).of (servicePath slots keep offered state) := by
  let _ := serviceQuiver
  induction slots generalizing keep offered state with
  | zero => rfl
  | succ slots ih =>
    change Multiplicative.ofAdd ((meter state (keep 0) (offered 0)).total +
      (costedServiceRun meter slots (fun i => keep (i + 1))
        (fun i => offered (i + 1)) (service state (keep 0) (offered 0))).2) = _
    rw [servicePath]
    erw [(serviceAccount meter).of_comp]
    rw [← ih]
    simp [serviceAccount, Quiver.Hom.toPath,
      Mettapedia.GSLT.Contracts.Accounts.pathAccount_cons,
      Mettapedia.GSLT.Contracts.Accounts.pathAccount_nil]

/-- An admission contract on every complete slot actually reached by a
particular service slice. This includes arrival processing and bookkeeping,
not just the task's requested quantum or number of native dispatches. -/
def ServiceCostBound {Cost : Type*} [AddMonoid Cost] [Preorder Cost]
    (meter : ServiceMeter Cost) (bound : Cost) (slots : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (state : State) : Prop :=
  ∀ n, n < slots →
    (meter (serviceRun n keep offered state).2 (keep n) (offered n)).total ≤ bound

theorem SlotCharge.total_le {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost]
    [IsOrderedAddMonoid Cost] (charge : SlotCharge Cost)
    (handling arrivals bookkeeping : Cost)
    (handle : charge.handling ≤ handling) (arrive : charge.arrivals ≤ arrivals)
    (maintain : charge.bookkeeping ≤ bookkeeping) :
    charge.total ≤ handling + arrivals + bookkeeping :=
  add_le_add (add_le_add handle arrive) maintain

/-- Smaller slices inherit the complete-slot admission contract. -/
theorem ServiceCostBound.prefix {Cost : Type*} [AddMonoid Cost] [Preorder Cost]
    {meter : ServiceMeter Cost} {bound : Cost} {first second : Nat}
    {keep : Nat → Bool} {offered : Nat → List Nat} {state : State}
    (admitted : ServiceCostBound meter bound second keep offered state)
    (within : first ≤ second) :
    ServiceCostBound meter bound first keep offered state :=
  fun n before => admitted n (Nat.lt_of_lt_of_le before within)

/-- Component bounds imply whole-slot admission. Arrival and queue costs
cannot disappear into the native handling allowance. -/
theorem ServiceCostBound.of_components {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost]
    [IsOrderedAddMonoid Cost] (meter : ServiceMeter Cost)
    (handling arrivals bookkeeping : Cost) (slots : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (state : State)
    (handle : ∀ n, n < slots →
      (meter (serviceRun n keep offered state).2 (keep n) (offered n)).handling ≤ handling)
    (arrive : ∀ n, n < slots →
      (meter (serviceRun n keep offered state).2 (keep n) (offered n)).arrivals ≤ arrivals)
    (maintain : ∀ n, n < slots →
      (meter (serviceRun n keep offered state).2 (keep n) (offered n)).bookkeeping ≤ bookkeeping) :
    ServiceCostBound meter (handling + arrivals + bookkeeping) slots keep offered state :=
  fun n before => SlotCharge.total_le _ _ _ _
    (handle n before) (arrive n before) (maintain n before)

/-- Whole-slot admission yields a cumulative bound in any ordered additive
cost profile. No conversion from a logical dispatch count to time is assumed. -/
theorem costedServiceRun_cost_le {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost]
    [IsOrderedAddMonoid Cost] (meter : ServiceMeter Cost) (bound : Cost)
    (slots : Nat) (keep : Nat → Bool) (offered : Nat → List Nat) (state : State)
    (admitted : ServiceCostBound meter bound slots keep offered state) :
    (costedServiceRun meter slots keep offered state).2 ≤ slots • bound := by
  induction slots with
  | zero => simp [costedServiceRun]
  | succ slots ih =>
    have earlier := ih (fun n within => admitted n (Nat.lt_trans within (Nat.lt_succ_self slots)))
    have last := admitted slots (Nat.lt_succ_self slots)
    rw [costedServiceRun_add meter slots 1]
    simp only [costedServiceRun, Nat.zero_add, add_zero, costedServiceRun_erases]
    exact (add_le_add earlier last).trans_eq (succ_nsmul bound slots).symm

theorem duplicates_and_full_arrivals_do_not_overtake :
    serviceRun 2 (fun _ => true) (fun _ => [9, 2, 9, 10]) ⟨2, [1, 2]⟩ =
      ([1, 2], ⟨2, [1, 2]⟩) := by decide

theorem retirement_admits_only_the_available_suffix :
    serviceRun 2 (fun _ => false) (fun _ => [9, 9, 10]) ⟨2, [1, 2]⟩ =
      ([1, 2], ⟨2, [9, 10]⟩) := by decide

theorem step_preserves_capacity (state : State) (action : Action) :
    (step state action).2.capacity = state.capacity := by
  cases action with
  | admit task => simp only [step]; split <;> rfl
  | remove _ => rfl
  | visit => rfl

theorem run_preserves_capacity (actions : List Action) (state : State) :
    (run actions state).capacity = state.capacity := by
  induction actions generalizing state with
  | nil => rfl
  | cons action rest ih => simp only [run, ih, step_preserves_capacity]

theorem afterVisit_preserves_capacity (state : State) (keep : Bool) :
    (afterVisit state keep).capacity = state.capacity := by
  cases visitedEq : (step state .visit).1.visited with
  | none => simp only [afterVisit, visitedEq, step_preserves_capacity]
  | some task => cases keep <;> simp [afterVisit, visitedEq, step_preserves_capacity]

theorem serviceRun_preserves_capacity (slots : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (state : State) :
    (serviceRun slots keep offered state).2.capacity = state.capacity := by
  induction slots generalizing keep offered state with
  | zero => rfl
  | succ slots ih =>
    simp only [serviceRun, ih, service, run_preserves_capacity, afterVisit_preserves_capacity]

theorem service_preserves_retained_member (state : State) (target : Nat)
    (keep : Bool) (offered : List Nat) (valid : invariant state)
    (member : target ∈ state.tasks)
    (retained : state.tasks.head? = some target → keep = true) :
    target ∈ (service state keep offered).tasks := by
  rw [service_tasks state keep offered valid]
  apply List.mem_append_left
  cases tasks : state.tasks with
  | nil => simp [tasks] at member
  | cons head tail =>
    simp only [tasks, List.mem_cons] at member
    rcases member with rfl | member
    · have kept := retained (by simp [tasks])
      simp [kept]
    · exact List.mem_append_left _ member

theorem serviceRun_preserves_retained_member (slots : Nat)
    (state : State) (target : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (valid : invariant state)
    (member : target ∈ state.tasks)
    (retained : ∀ n, (serviceRun n keep offered state).2.tasks.head? = some target →
      keep n = true) :
    target ∈ (serviceRun slots keep offered state).2.tasks := by
  induction slots with
  | zero => exact member
  | succ slots ih =>
    have validAt := serviceRun_preserves_invariant slots keep offered state valid
    have keepAt := retained slots
    have next := service_preserves_retained_member _ target (keep slots)
      (offered slots) validAt ih keepAt
    change target ∈ (serviceRun (slots + 1) keep offered state).2.tasks
    rw [serviceRun_add]
    simpa only [serviceRun, Nat.zero_add] using next

theorem serviceRun_visits_prefix {first second : Nat} (within : first ≤ second)
    (keep : Nat → Bool) (offered : Nat → List Nat) (state : State) :
    (serviceRun first keep offered state).1.IsPrefix
      (serviceRun second keep offered state).1 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le within
  rw [serviceRun_add]
  exact List.prefix_append _ _

theorem serviceRun_count_mono {first second : Nat} (within : first ≤ second)
    (state : State) (target : Nat) (keep : Nat → Bool) (offered : Nat → List Nat) :
    (serviceRun first keep offered state).1.count target ≤
      (serviceRun second keep offered state).1.count target := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le within
  rw [serviceRun_add, List.count_append]
  exact Nat.le_add_right _ _

/-- A requested visit cannot disappear by retirement before it is delivered.
The target may retire in the same slot that meets the requested count. -/
theorem serviceRun_preserves_member_until_requested (slots demand : Nat)
    (state : State) (target : Nat) (keep : Nat → Bool) (offered : Nat → List Nat)
    (valid : invariant state) (member : target ∈ state.tasks)
    (retained : ∀ n, (serviceRun (n + 1) keep offered state).1.count target < demand →
      (serviceRun n keep offered state).2.tasks.head? = some target → keep n = true)
    (pending : (serviceRun slots keep offered state).1.count target < demand) :
    target ∈ (serviceRun slots keep offered state).2.tasks := by
  induction slots with
  | zero => exact member
  | succ slots ih =>
    have previous : (serviceRun slots keep offered state).1.count target < demand :=
      Nat.lt_of_le_of_lt (serviceRun_count_mono (Nat.le_succ slots) state target keep offered)
        pending
    have next := service_preserves_retained_member _ target (keep slots) (offered slots)
      (serviceRun_preserves_invariant slots keep offered state valid) (ih previous)
      (retained slots pending)
    change target ∈ (serviceRun (slots + 1) keep offered state).2.tasks
    rw [serviceRun_add]
    simpa only [serviceRun, Nat.zero_add] using next

/-- Requested service is bounded by visits times capacity. The target need
only remain ready until that request is met, while other tasks may retire
and new arrivals may be rejected. This counts executed slots, not time. -/
theorem requested_task_gets_bounded_service (demand : Nat)
    (state : State) (target : Nat) (keep : Nat → Bool) (offered : Nat → List Nat)
    (valid : invariant state) (member : target ∈ state.tasks)
    (retained : ∀ n, (serviceRun (n + 1) keep offered state).1.count target < demand →
      (serviceRun n keep offered state).2.tasks.head? = some target → keep n = true) :
    demand ≤ (serviceRun (demand * state.capacity) keep offered state).1.count target := by
  have byBlocks : ∀ blocks, blocks ≤ demand →
      blocks ≤ (serviceRun (blocks * state.capacity) keep offered state).1.count target := by
    intro blocks
    induction blocks with
    | zero => intro _; exact Nat.zero_le _
    | succ blocks ih =>
      intro within
      have earlier := ih (by omega)
      by_cases served : blocks + 1 ≤
          (serviceRun (blocks * state.capacity) keep offered state).1.count target
      · exact Nat.le_trans served (serviceRun_count_mono (Nat.mul_le_mul_right state.capacity
          (Nat.le_succ blocks)) state target keep offered)
      · have pending : (serviceRun (blocks * state.capacity) keep offered state).1.count
            target < demand := by omega
        have memberAt := serviceRun_preserves_member_until_requested
          (blocks * state.capacity) demand state target keep offered valid member retained pending
        have validAt := serviceRun_preserves_invariant (blocks * state.capacity)
          keep offered state valid
        have capacityAt := serviceRun_preserves_capacity (blocks * state.capacity)
          keep offered state
        obtain ⟨first, bound, found⟩ := queued_task_gets_bounded_service
          (serviceRun (blocks * state.capacity) keep offered state).2 target
          (fun i => keep (i + blocks * state.capacity))
          (fun i => offered (i + blocks * state.capacity)) validAt memberAt
        have bound' : first ≤ state.capacity := by
          have lengthBound := validAt.2
          rw [capacityAt] at lengthBound
          exact Nat.le_trans bound lengthBound
        have foundBlock := (serviceRun_visits_prefix bound'
          (fun i => keep (i + blocks * state.capacity))
          (fun i => offered (i + blocks * state.capacity))
          (serviceRun (blocks * state.capacity) keep offered state).2).subset found
        have positive := List.count_pos_iff.mpr foundBlock
        rw [Nat.succ_mul, serviceRun_add, List.count_append]
        omega
  exact byBlocks demand (Nat.le_refl demand)

/-- A continuously retained task receives any finite number of visits within
that number times queue capacity, despite other tasks retiring and arbitrary
offered arrivals. Each slot must actually execute; this is not a time bound. -/
theorem retained_task_gets_repeated_service (demand : Nat)
    (state : State) (target : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (valid : invariant state)
    (member : target ∈ state.tasks)
    (retained : ∀ n, (serviceRun n keep offered state).2.tasks.head? = some target →
      keep n = true) :
    demand ≤ (serviceRun (demand * state.capacity) keep offered state).1.count target := by
  exact requested_task_gets_bounded_service demand state target keep offered
    valid member (fun n _ atHead => retained n atHead)

/-- The same requested service theorem with the cumulative account of its
actual execution. This bounds a declared cost profile only under the complete
slot admission contract; it does not postulate a wall-clock interpretation. -/
theorem requested_task_gets_bounded_cost {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost]
    [IsOrderedAddMonoid Cost] (meter : ServiceMeter Cost) (bound : Cost) (demand : Nat)
    (state : State) (target : Nat) (keep : Nat → Bool) (offered : Nat → List Nat)
    (valid : invariant state) (member : target ∈ state.tasks)
    (retained : ∀ n, (serviceRun (n + 1) keep offered state).1.count target < demand →
      (serviceRun n keep offered state).2.tasks.head? = some target → keep n = true)
    (admitted : ServiceCostBound meter bound (demand * state.capacity) keep offered state) :
    demand ≤ (costedServiceRun meter (demand * state.capacity) keep offered state).1.1.count target ∧
      (costedServiceRun meter (demand * state.capacity) keep offered state).2 ≤
        (demand * state.capacity) • bound := by
  exact ⟨by simpa only [costedServiceRun_erases] using
      requested_task_gets_bounded_service demand state target keep offered valid member retained,
    costedServiceRun_cost_le meter bound _ keep offered state admitted⟩

/-- A retained task receives every finite request within its cumulative
whole-slot bound. Other tasks can retire, and arrivals can fail admission. -/
theorem retained_task_gets_repeated_bounded_cost {Cost : Type*} [AddCommMonoid Cost]
    [Preorder Cost] [IsOrderedAddMonoid Cost] (meter : ServiceMeter Cost) (bound : Cost)
    (demand : Nat) (state : State) (target : Nat) (keep : Nat → Bool)
    (offered : Nat → List Nat) (valid : invariant state) (member : target ∈ state.tasks)
    (retained : ∀ n, (serviceRun n keep offered state).2.tasks.head? = some target →
      keep n = true)
    (admitted : ServiceCostBound meter bound (demand * state.capacity) keep offered state) :
    demand ≤ (costedServiceRun meter (demand * state.capacity) keep offered state).1.1.count target ∧
      (costedServiceRun meter (demand * state.capacity) keep offered state).2 ≤
        (demand * state.capacity) • bound :=
  requested_task_gets_bounded_cost meter bound demand state target keep offered valid member
    (fun n _ atHead => retained n atHead) admitted

/-- The first requested opportunity already has a cost bound at its actual
prefix, no later than the initial queue length. -/
theorem queued_task_gets_bounded_cost {Cost : Type*} [AddCommMonoid Cost] [Preorder Cost]
    [IsOrderedAddMonoid Cost] (meter : ServiceMeter Cost) (bound : Cost)
    (state : State) (target : Nat) (keep : Nat → Bool) (offered : Nat → List Nat)
    (valid : invariant state) (member : target ∈ state.tasks)
    (admitted : ServiceCostBound meter bound state.tasks.length keep offered state) :
    ∃ slots ≤ state.tasks.length,
      target ∈ (costedServiceRun meter slots keep offered state).1.1 ∧
        (costedServiceRun meter slots keep offered state).2 ≤ slots • bound := by
  obtain ⟨slots, within, served⟩ :=
    queued_task_gets_bounded_service state target keep offered valid member
  exact ⟨slots, within, by simpa only [costedServiceRun_erases] using served,
    costedServiceRun_cost_le meter bound slots keep offered state (admitted.prefix within)⟩

theorem retained_task_survives_retirement_and_rejected_arrivals :
    serviceRun 6 (fun n => decide (n % 2 = 0)) (fun n => [100 + n, 100 + n])
      ⟨2, [1, 2]⟩ = ([1, 2, 1, 101, 1, 103], ⟨2, [1, 105]⟩) := by decide

theorem task_can_retire_after_requested_service :
    serviceRun 6 (fun n => decide (n < 4)) (fun _ => []) ⟨2, [1, 2]⟩ =
      ([1, 2, 1, 2, 1, 2], ⟨2, []⟩) := by decide

theorem retiring_target_prevents_repeated_service :
    (serviceRun 3 (fun _ => false) (fun _ => []) ⟨1, [1]⟩).1.count 1 = 1 ∧
      ¬ 3 ≤ (serviceRun 3 (fun _ => false) (fun _ => []) ⟨1, [1]⟩).1.count 1 := by decide

theorem zero_capacity_accepts_no_offered_task (offered : Nat → List Nat) (slots : Nat)
    (keep : Nat → Bool) : (serviceRun slots keep offered ⟨0, []⟩).2.tasks = [] := by
  have valid := serviceRun_preserves_invariant slots keep offered ⟨0, []⟩ (by simp [invariant])
  have capacity := serviceRun_preserves_capacity slots keep offered ⟨0, []⟩
  have emptyLength : (serviceRun slots keep offered ⟨0, []⟩).2.tasks.length = 0 := by
    have bound := valid.2
    rw [capacity] at bound
    exact Nat.eq_zero_of_le_zero bound
  exact List.length_eq_zero_iff.mp emptyLength

/-- Removing a different task is cancellation, outside retirement of the
visited head. Capacity and uniqueness alone do not prevent starvation. -/
theorem removing_an_unvisited_task_breaks_service :
    (serviceRun 2 (fun _ => true) (fun _ => [])
      (step ⟨2, [1, 2]⟩ (.remove 2)).2).1 = [1, 1] ∧
    2 ∉ (serviceRun 2 (fun _ => true) (fun _ => [])
      (step ⟨2, [1, 2]⟩ (.remove 2)).2).1 := by decide

/-- Admission alone supplies no service. A driver that never visits cannot
derive a progress guarantee from membership and capacity invariants. -/
theorem admissions_alone_can_leave_the_head_waiting (n : Nat) :
    run (List.replicate n (.admit 2)) ⟨2, [1, 2]⟩ = ⟨2, [1, 2]⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, run, step, EventPump.admit] using ih

/-! The following profile is illustrative: a declared per-task handling
charge, one unit per offered arrival and one plus queue length for maintenance.
It is not a measurement model of a particular native implementation. -/

private def controlMeter (native : Nat → Nat) : ServiceMeter Nat :=
  fun state _ offered =>
    ⟨(state.tasks.head?.map native).getD 0, offered.length, state.tasks.length + 1⟩

theorem zero_service_slots_have_no_cost {Cost : Type*} [AddMonoid Cost]
    (meter : ServiceMeter Cost) (keep : Nat → Bool) (offered : Nat → List Nat) (state : State) :
    costedServiceRun meter 0 keep offered state = (([], state), 0) := rfl

/-- Charges use the changing queue: the two visited tasks have different
handling charges, and every offered occurrence is charged even when rejected. -/
theorem costed_retirement_and_rejected_arrivals :
    costedServiceRun (controlMeter id) 2 (fun _ => false) (fun _ => [9, 9, 10])
      ⟨2, [1, 2]⟩ = (([1, 2], ⟨2, [9, 10]⟩), 15) := by decide

/-- A nontrivial whole-slot instance: handling costs at most two, three
arrival occurrences are processed, and capacity two bounds maintenance by
three. Thus every retained request is met within its actual cumulative cost. -/
theorem bounded_native_arrival_and_queue_profile (demand : Nat) :
    demand ≤ (costedServiceRun (controlMeter (fun _ => 2)) (demand * 2)
      (fun _ => true) (fun _ => [9, 9, 10]) ⟨2, [1, 2]⟩).1.1.count 1 ∧
    (costedServiceRun (controlMeter (fun _ => 2)) (demand * 2)
      (fun _ => true) (fun _ => [9, 9, 10]) ⟨2, [1, 2]⟩).2 ≤ (demand * 2) • 8 := by
  apply retained_task_gets_repeated_bounded_cost (controlMeter (fun _ => 2)) 8 demand
    ⟨2, [1, 2]⟩ 1 (fun _ => true) (fun _ => [9, 9, 10]) (by simp [invariant]) (by decide)
    (fun _ _ => rfl)
  apply ServiceCostBound.of_components (controlMeter (fun _ => 2)) 2 3 3
  · intro n _
    change ((serviceRun n (fun _ => true) (fun _ => [9, 9, 10]) ⟨2, [1, 2]⟩).2.tasks.head?.map
      (fun _ => 2)).getD 0 ≤ 2
    cases (serviceRun n (fun _ => true) (fun _ => [9, 9, 10]) ⟨2, [1, 2]⟩).2.tasks.head? <;>
      simp
  · intro n _
    exact Nat.le_refl 3
  · intro n _
    change (serviceRun n (fun _ => true) (fun _ => [9, 9, 10]) ⟨2, [1, 2]⟩).2.tasks.length + 1 ≤ 3
    have valid := serviceRun_preserves_invariant n (fun _ => true)
      (fun _ => [9, 9, 10]) ⟨2, [1, 2]⟩ (by simp [invariant])
    have capacity := serviceRun_preserves_capacity n (fun _ => true)
      (fun _ => [9, 9, 10]) ⟨2, [1, 2]⟩
    have lengthBound := valid.2
    rw [capacity] at lengthBound
    change _ ≤ 2 at lengthBound
    omega

/-- A single native dispatch can exceed every proposed cost bound. Logical
service alone therefore supplies no uniform native-work or elapsed-time bound. -/
theorem one_dispatch_has_arbitrarily_large_cost (budget : Nat) :
    (costedServiceRun (controlMeter (fun _ => budget + 1)) 1 (fun _ => true)
      (fun _ => []) ⟨1, [1]⟩).1.1 = [1] ∧
    budget < (costedServiceRun (controlMeter (fun _ => budget + 1)) 1 (fun _ => true)
      (fun _ => []) ⟨1, [1]⟩).2 := by
  constructor
  · rfl
  · change budget < budget + 1 + 0 + (1 + 1) + 0
    omega

/-- Capacity bounds the ready queue, not the amount of rejected arrival work.
Even a one-task queue can incur arbitrarily large arrival-processing cost. -/
theorem rejected_arrivals_have_arbitrarily_large_cost (offers : Nat) :
    (costedServiceRun (controlMeter (fun _ => 0)) 1 (fun _ => true)
      (fun _ => List.replicate offers 1) ⟨1, [1]⟩).1.1 = [1] ∧
    offers < (costedServiceRun (controlMeter (fun _ => 0)) 1 (fun _ => true)
      (fun _ => List.replicate offers 1) ⟨1, [1]⟩).2 := by
  constructor
  · rfl
  · simp only [costedServiceRun, controlMeter, SlotCharge.total,
      List.head?_cons, Option.map_some, Option.getD_some, List.length_replicate,
      List.length_cons, List.length_nil, zero_add, add_zero]
    omega

/-- Idle slots still pay for rejecting arrivals and maintaining the queue. -/
theorem zero_capacity_still_has_service_cost :
    costedServiceRun (controlMeter (fun _ => 100)) 3 (fun _ => true)
      (fun _ => [9, 9]) ⟨0, []⟩ = (([], ⟨0, []⟩), 9) := by decide

/-- A bound on cost is no substitute for retaining a task until its requested
service is met. This target retires after its first visit. -/
theorem bounded_cost_does_not_restore_a_retired_task :
    (costedServiceRun (controlMeter (fun _ => 1)) 3 (fun _ => false)
      (fun _ => []) ⟨1, [1]⟩).2 = 5 ∧
    ¬ 3 ≤ (costedServiceRun (controlMeter (fun _ => 1)) 3 (fun _ => false)
      (fun _ => []) ⟨1, [1]⟩).1.1.count 1 := by decide

/-- The same worker supports a pair of additive metrics without identifying
them: handling work and the number of offered arrivals. -/
theorem product_cost_profile_keeps_distinct_metrics :
    costedServiceRun (fun state _ offered =>
      (⟨(state.tasks.length, 0), (0, offered.length), (1, 0)⟩ : SlotCharge (Nat × Nat)))
      2 (fun _ => false) (fun _ => [9, 9, 10]) ⟨2, [1, 2]⟩ =
        (([1, 2], ⟨2, [9, 10]⟩), (6, 6)) := by decide

#print axioms costedServiceRun_erases
#print axioms costedServiceRun_add
#print axioms costedServiceRun_eq_account
#print axioms costedServiceRun_cost_le
#print axioms requested_task_gets_bounded_cost
#print axioms retained_task_gets_repeated_bounded_cost
#print axioms bounded_native_arrival_and_queue_profile
#print axioms one_dispatch_has_arbitrarily_large_cost
#print axioms rejected_arrivals_have_arbitrarily_large_cost

/-! Recovery uses an exact journal occurrence cursor. A revision alone cannot
resume a partially discovered batch. The ordered-suffix theorem assumes the
store supplies its documented revision/position order; it does not prove SQL. -/

structure Position where
  revision : Nat
  position : Nat
  deriving DecidableEq, Repr

def before (a b : Position) : Bool :=
  decide (a.revision < b.revision ∨
    (a.revision = b.revision ∧ a.position < b.position))

def pendingFrom (cursor : Position) (records : List Position) : List Position :=
  records.filter (fun record => !before record cursor)

theorem cursor_is_inclusive (cursor : Position) : before cursor cursor = false := by
  simp [before]

theorem same_revision_earlier_position_excluded (revision first next : Nat)
    (h : first < next) :
    pendingFrom ⟨revision, next⟩ [⟨revision, first⟩, ⟨revision, next⟩] =
      [⟨revision, next⟩] := by
  simp [pendingFrom, before, h]

theorem recovered_suffix_exact (cursor : Position) (past suffix : List Position)
    (old : ∀ row ∈ past, before row cursor = true)
    (fresh : ∀ row ∈ suffix, before row cursor = false) :
    pendingFrom cursor (past ++ cursor :: suffix) = cursor :: suffix := by
  have hp : past.filter (fun row => !before row cursor) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro row member
    simp [old row member]
  have hs : suffix.filter (fun row => !before row cursor) = suffix := by
    apply List.filter_eq_self.mpr
    intro row member
    simp [fresh row member]
  simp [pendingFrom, List.filter_append, hp, hs, cursor_is_inclusive]

theorem revision_only_resume_repeats_first_effect :
    ([Position.mk 7 3, Position.mk 7 4].filter (fun row => decide (7 ≤ row.revision))).head? =
      some ⟨7, 3⟩ ∧
    (pendingFrom ⟨7, 4⟩ [⟨7, 3⟩, ⟨7, 4⟩]).head? = some ⟨7, 4⟩ := by
  decide

end Mettapedia.Machines.ReadyQueue
