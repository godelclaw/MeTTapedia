import EventPump

/-!
# Bounded native ready order

Executable reference for CeTTa's intrusive ready queue. A task's native link
represents membership; its position is independent of the backing slot. An
admission appends, a visit moves the head to the tail, and removal filters only
the named task. The C trace comparison checks these transitions, not pointer
safety or the C compiler. Durable task identities remain outside this cache.

The service theorem extends `EventPump` to a visited task that can either
remain queued or retire. Continuing arrivals still cannot overtake an existing
prefix. A visit is an opportunity, not a successful effect or goal completion.
-/

namespace ReadyQueue

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

def rotate : List Nat → List Nat
  | [] => []
  | first :: rest => rest ++ [first]

def step (state : State) (action : Action) : Observation × State :=
  match action with
  | .admit task =>
    match EventPump.admit state.capacity state.tasks task with
    | none => (⟨2, none⟩, state)
    | some tasks => (⟨if task ∈ state.tasks then 1 else 0, none⟩, { state with tasks })
  | .remove task =>
    (⟨if task ∈ state.tasks then 1 else 0, none⟩,
     { state with tasks := state.tasks.filter (fun other => decide (other ≠ task)) })
  | .visit => (⟨0, state.tasks.head?⟩, { state with tasks := rotate state.tasks })

def invariant (state : State) : Prop :=
  state.tasks.Nodup ∧ state.tasks.length ≤ state.capacity

def run : List Action → State → State
  | [], state => state
  | action :: rest, state => run rest (step state action).2

theorem rotation_preserves_membership (tasks : List Nat) (task : Nat) :
    task ∈ rotate tasks ↔ task ∈ tasks := by
  cases tasks <;> simp [rotate, or_comm]

theorem rotation_preserves_length (tasks : List Nat) :
    (rotate tasks).length = tasks.length := by
  cases tasks <;> simp [rotate]

theorem rotation_preserves_uniqueness (tasks : List Nat) (h : tasks.Nodup) :
    (rotate tasks).Nodup := by
  cases tasks with
  | nil => simp [rotate]
  | cons first rest =>
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

def services {α : Type} : Nat → (Nat → Bool) → (Nat → List α) → List α → List α
  | 0, _, _, _ => []
  | n + 1, keep, arrivals, [] =>
      services n (fun i => keep (i + 1)) (fun i => arrivals (i + 1)) (arrivals 0)
  | n + 1, keep, arrivals, head :: tail =>
      head :: services n (fun i => keep (i + 1)) (fun i => arrivals (i + 1))
        (tail ++ (if keep 0 then [head] else []) ++ arrivals 0)

theorem retained_service_is_event_pump_service {α : Type} (n : Nat)
    (arrivals : Nat → List α) (queue : List α) :
    services n (fun _ => true) arrivals queue = EventPump.services n arrivals queue := by
  induction n generalizing arrivals queue with
  | zero => rfl
  | succ n ih => cases queue <;> simp [services, EventPump.services, ih]

theorem prefix_served_despite_retirement_and_arrivals {α : Type}
    (before suffix : List α) (target : α) (keep : Nat → Bool) (arrivals : Nat → List α) :
    target ∈ services (before.length + 1) keep arrivals (before ++ target :: suffix) := by
  induction before generalizing suffix keep arrivals with
  | nil => simp [services]
  | cons head before ih =>
    simp only [List.length_cons, List.cons_append, services]
    apply List.mem_cons_of_mem
    simpa only [List.append_assoc, List.cons_append] using
      ih (suffix ++ (if keep 0 then [head] else []) ++ arrivals 0)
        (fun i => keep (i + 1)) (fun i => arrivals (i + 1))

theorem queued_task_gets_bounded_service {α : Type} (queue : List α) (target : α)
    (keep : Nat → Bool) (arrivals : Nat → List α) (member : target ∈ queue) :
    ∃ slots ≤ queue.length, target ∈ services slots keep arrivals queue := by
  obtain ⟨before, suffix, rfl⟩ := List.mem_iff_append.mp member
  refine ⟨before.length + 1, ?_,
    prefix_served_despite_retirement_and_arrivals before suffix target keep arrivals⟩
  simp

/-- The native visit followed by retirement is precisely the corresponding
service branch. Duplicates cannot remain because queue membership is unique. -/
theorem visit_then_retire (capacity first : Nat) (rest : List Nat)
    (unique : (first :: rest).Nodup) :
    (step (step ⟨capacity, first :: rest⟩ .visit).2 (.remove first)).2.tasks = rest := by
  have absent := (List.nodup_cons.mp unique).1
  simp only [step, rotate, List.filter_append, List.filter_cons, ne_self_iff_false,
    decide_false, Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.append_nil]
  apply List.filter_eq_self.mpr
  intro other member
  simp only [decide_eq_true_eq]
  intro equal
  exact absent (equal ▸ member)

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

end ReadyQueue
