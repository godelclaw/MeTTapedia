import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Recycled producer-dependency edge slots

The counted allocator uses a free slot before extending its initialized
prefix. Capacity doubles only when that prefix fills the buffer. Removing a
live edge returns one slot. Failure preserves the previous edge pool.

These laws account for initialized, live, free and spare slots; they do not
prove the native intrusive adjacency lists or physical allocator behavior.
The caller must remove an actual live edge. Native adjacency, retirement and
failure controls are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProducerDependencyPool

structure Pool where
  initialized : Nat
  live : Nat
  free : Nat
  capacity : Nat
  highWater : Nat
  deriving DecidableEq, Repr

def initial : Pool := ⟨0, 0, 0, 0, 0⟩

def Valid (pool : Pool) : Prop :=
  pool.initialized = pool.live + pool.free ∧
  pool.initialized = pool.highWater ∧
  pool.initialized ≤ pool.capacity ∧
  (pool.capacity = 0 ∨ 16 ≤ pool.capacity) ∧
  pool.capacity ≤ max 16 (2 * pool.highWater)

def allocate (allocated : Bool) (pool : Pool) : Pool × Bool :=
  if 0 < pool.free then
    ({pool with live := pool.live + 1, free := pool.free - 1}, true)
  else if pool.initialized < pool.capacity then
    ({pool with
       initialized := pool.initialized + 1
       live := pool.live + 1
       highWater := max pool.highWater (pool.live + 1)}, true)
  else if allocated then
    ({pool with
       initialized := pool.initialized + 1
       live := pool.live + 1
       capacity := if pool.capacity = 0 then 16 else 2 * pool.capacity
       highWater := max pool.highWater (pool.live + 1)}, true)
  else (pool, false)

def release (pool : Pool) : Pool :=
  if 0 < pool.live then
    {pool with live := pool.live - 1, free := pool.free + 1}
  else pool

theorem initial_valid : Valid initial := by
  simp [Valid, initial]

theorem allocation_preserves_account (allocated : Bool) (pool : Pool)
    (valid : Valid pool) : Valid (allocate allocated pool).1 := by
  unfold Valid at valid ⊢
  by_cases spare : 0 < pool.free
  · simp only [allocate, if_pos spare]
    omega
  · by_cases room : pool.initialized < pool.capacity
    · simp only [allocate, if_neg spare, if_pos room]
      omega
    · cases allocated with
      | false => simpa [allocate, spare, room] using valid
      | true =>
          by_cases empty : pool.capacity = 0
          · simp only [allocate, if_neg spare, if_neg room, if_true, if_pos empty]
            omega
          · simp only [allocate, if_neg spare, if_neg room, if_true, if_neg empty]
            omega

theorem release_preserves_account (pool : Pool) (valid : Valid pool) :
    Valid (release pool) := by
  unfold Valid at valid ⊢
  by_cases occupied : 0 < pool.live
  · simp only [release, if_pos occupied]
    omega
  · simpa [release, occupied] using valid

theorem existing_slot_needs_no_allocation (pool : Pool)
    (available : 0 < pool.free ∨ pool.initialized < pool.capacity) :
    (allocate false pool).2 = true := by
  rcases available with free | room
  · simp [allocate, free]
  · by_cases free : 0 < pool.free <;> simp [allocate, free, room]

theorem failed_growth_preserves_pool (pool : Pool) (full : pool.free = 0)
    (noRoom : pool.capacity ≤ pool.initialized) : allocate false pool = (pool, false) := by
  simp [allocate, full, Nat.not_lt.mpr noRoom]

/-- A reused edge returns to precisely the same pool after removal. -/
theorem reuse_release_exact (pool : Pool) (available : 0 < pool.free) :
    release (allocate false pool).1 = pool := by
  simp only [allocate, if_pos available, release]
  have occupied : 0 < pool.live + 1 := by omega
  simp only [if_pos occupied]
  congr 1
  omega

inductive Event where
  | insert (allocated : Bool)
  | remove

def step (pool : Pool) : Event → Pool
  | .insert allocated => (allocate allocated pool).1
  | .remove => release pool

def run : List Event → Pool → Pool
  | [], pool => pool
  | event :: rest, pool => run rest (step pool event)

theorem step_highWater (event : Event) (pool : Pool) (valid : Valid pool) :
    (step pool event).highWater = max pool.highWater (step pool event).live := by
  unfold Valid at valid
  cases event with
  | insert allocated =>
      by_cases spare : 0 < pool.free
      · simp only [step, allocate, if_pos spare]
        omega
      · by_cases room : pool.initialized < pool.capacity
        · simp only [step, allocate, if_neg spare, if_pos room]
        · cases allocated with
          | false =>
              have water : pool.live ≤ pool.highWater := by omega
              simpa [step, allocate, spare, room] using (max_eq_left water).symm
          | true => simp [step, allocate, spare, room]
  | remove =>
      by_cases occupied : 0 < pool.live <;> simp [step, release, occupied] <;> omega

/-- Largest simultaneously live edge count, including the starting state. -/
def peakLive : List Event → Pool → Nat
  | [], pool => pool.live
  | event :: rest, pool => max pool.live (peakLive rest (step pool event))

theorem run_highWater (events : List Event) (pool : Pool) (valid : Valid pool) :
    (run events pool).highWater = max pool.highWater (peakLive events pool) := by
  induction events generalizing pool with
  | nil => simp only [run, peakLive]; unfold Valid at valid; omega
  | cons event rest ih =>
      have nextValid : Valid (step pool event) := by
        cases event with
        | insert allocated => exact allocation_preserves_account allocated pool valid
        | remove => exact release_preserves_account pool valid
      have later := ih (step pool event) nextValid
      have nextWater := step_highWater event pool valid
      have covers : (step pool event).live ≤ peakLive rest (step pool event) := by
        cases rest <;> simp [peakLive]
      simp only [run, peakLive]
      rw [later, nextWater]
      unfold Valid at valid
      omega

theorem run_preserves_account (events : List Event) (pool : Pool) (valid : Valid pool) :
    Valid (run events pool) := by
  induction events generalizing pool with
  | nil => exact valid
  | cons event rest ih =>
      apply ih
      cases event with
      | insert allocated => exact allocation_preserves_account allocated pool valid
      | remove => exact release_preserves_account pool valid

/-- Retained capacity follows simultaneous live-edge demand, not the number
of insertions and retirements in the execution history. -/
theorem retained_slots_bound (events : List Event) :
    (run events initial).capacity ≤ max 16 (2 * (run events initial).highWater) :=
  (run_preserves_account events initial initial_valid).2.2.2.2

theorem retained_slots_bound_by_live_demand (events : List Event) :
    (run events initial).capacity ≤ max 16 (2 * peakLive events initial) := by
  have bound := retained_slots_bound events
  have peak := run_highWater events initial initial_valid
  rw [peak] at bound
  simpa only [initial, Nat.zero_max] using bound

/-- Failing to return a removed edge to the free pool breaks the account. -/
theorem lost_free_slot_breaks_account (pool : Pool) (valid : Valid pool)
    (occupied : 0 < pool.live) :
    ¬ Valid {pool with live := pool.live - 1} := by
  unfold Valid at valid ⊢
  dsimp
  omega

end Mettapedia.Machines.ProducerDependencyPool
