import Mettapedia.Algebra.WorkSpan
import Mathlib.Data.Nat.Pairing

/-!
# Additive and peak-allocation accounts

Additive resources fit `ConcurrentCostAlgebra`. The declared peak-allocation
model instead reuses storage between sequential phases and adds simultaneous
branch allocations. It satisfies reverse interchange, while forward lax
interchange fails. These are accounting laws, not measured runtime guarantees.

Parallelism can improve span while increasing allocation. A scalar can encode
several resources injectively; choosing which tradeoffs to prefer requires an
additional policy, rather than an impossibility claim about scalar encodings.
-/

namespace Mettapedia.Algebra

/-- Energy, message counts, and similar resources accumulate under both
compositions: two branches running at once spend both their budgets. -/
def additiveAlgebra : ConcurrentCostAlgebra Nat where
  zero := 0
  sequential := (· + ·)
  parallel := (· + ·)
  sequential_zero_left := Nat.zero_add
  sequential_zero_right := Nat.add_zero
  sequential_assoc := fun _ _ _ => Nat.add_assoc _ _ _
  parallel_zero_left := Nat.zero_add
  parallel_zero_right := Nat.add_zero
  parallel_assoc := fun _ _ _ => Nat.add_assoc _ _ _
  parallel_comm := Nat.add_comm
  sequential_mono := fun first second => Nat.add_le_add first second
  parallel_mono := fun first second => Nat.add_le_add first second
  lax_interchange := by
    intro first second third fourth
    omega

/-- Peak concurrently-live storage.  Sequential phases reuse storage, so
the peak is the maximum; independent branches hold their allocations at
the same time, so the peak adds. -/
def peakSequential (first second : Nat) : Nat := max first second

/-- Independent branches coexist, so their peaks add. -/
def peakParallel (left right : Nat) : Nat := left + right

/-- **Peak allocation is not a `ConcurrentCostAlgebra`.**  The lax
interchange law fails: splitting two sequential phases across two branches
can strictly increase the peak, because the phases that would have reused
storage now coexist. -/
theorem peakAllocation_violates_lax_interchange :
    ¬ ∀ first second third fourth : Nat,
      peakParallel (peakSequential first second)
          (peakSequential third fourth) ≤
        peakSequential (peakParallel first third)
          (peakParallel second fourth) := by
  exact fun interchange => by
    simpa [peakSequential, peakParallel] using interchange 1 0 0 1

/-- The witness, stated positively: one unit allocated in the first phase
of one branch and the second phase of the other.  Serialized the peak is
one; run as independent branches it is two. -/
theorem peakAllocation_parallel_strictly_worse :
    peakSequential (peakParallel 1 0) (peakParallel 0 1) <
      peakParallel (peakSequential 1 0) (peakSequential 0 1) := by decide

/-- Parallel execution never increases span but can increase the declared
peak allocation. These are separate coordinates of the resource account. -/
theorem parallelism_improves_span_worsens_allocation :
    (∀ left right : WorkSpan,
      (WorkSpan.parallel left right).span ≤
        (WorkSpan.sequential left right).span) ∧
    (∃ first second : Nat,
      peakSequential first second < peakParallel first second) := by
  exact ⟨fun left right => (WorkSpan.parallel_le_sequential left right).2,
    ⟨1, 1, by decide⟩⟩

/-- Positive allocations make a split strictly larger than sequential reuse.
The positivity guards exclude the zero-allocation equality case. -/
theorem allocationRespecting_scalar_strictMono_at_unitSplit
    (scalar : WorkSpan → Nat → Nat)
    (respectsAllocation : ∀ (value : WorkSpan) (first second : Nat),
      0 < first → 0 < second → scalar value (peakSequential first second) <
        scalar value (peakParallel first second)) :
    ∀ value : WorkSpan, scalar value 1 < scalar value 2 := by
  intro value
  simpa [peakSequential, peakParallel] using respectsAllocation value 1 1 (by decide) (by decide)

/-- Synchronizing phases cannot exceed the sum of the separate branch peaks. -/
theorem peakAllocation_reverse_interchange (first second third fourth : Nat) :
    peakSequential (peakParallel first third) (peakParallel second fourth) ≤
      peakParallel (peakSequential first second) (peakSequential third fourth) :=
  max_add_add_le_max_add_max

/-- The guarded scalar premise is inhabited: simply report allocation. -/
theorem allocation_respects_positive_split (value : WorkSpan) (first second : Nat)
    (firstPositive : 0 < first) (secondPositive : 0 < second) :
    (fun (_ : WorkSpan) allocation => allocation) value (peakSequential first second) <
      (fun (_ : WorkSpan) allocation => allocation) value (peakParallel first second) := by
  simp only [peakSequential, peakParallel]
  omega

/-- An injective scalar encoding preserves all three coordinates, independently
of whether it gives a useful order for optimization. -/
theorem workSpan_allocation_scalar_encoding :
    Function.Injective (fun value : WorkSpan × Nat =>
      Nat.pair (Nat.pair value.1.work value.1.span) value.2) := by
  rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ same
  simpa only [Nat.pair_eq_pair, Prod.mk.injEq, WorkSpan.mk.injEq] using same

end Mettapedia.Algebra
