import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeEventualSupportPeriodicity
import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorTransferMatrix

/-!
# Boolean support stabilizes while exact tube path counts grow

The normalized physical tube has a finite recurrent frontier and eventually
periodic *Boolean* reachability support. Its one-ring relation has exactly two
different successors at every recurrent state. Consequently the number of
exact recurrent transition paths of length `n`, summed over all endpoints,
is `2^n`. Thus Boolean support cannot be substituted for natural-number
transfer counts without an explicit positivity-only argument.

This is a statement about the checked normalized local-ring transfer. It is
not yet an identification of every path with a distinct colouring of an
arbitrary embedded corridor.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeCountGrowth

open GoertzelV24TubeRingTransfer
open GoertzelV24TubeEventualSupportPeriodicity
open GoertzelV24TubeRingSelfLoopCounterexample
open GoertzelV24CorridorTransferMatrix
open GoertzelV24CorridorPumping

noncomputable local instance : DecidableRel RecurrentTubeRingStep :=
  Classical.decRel _

/-- The two exhaustive physical one-ring successor names never coincide. -/
theorem first_ne_second : ∀ source : RecurrentTubeProfile,
    firstFullyRoutedTarget source ≠ secondFullyRoutedTarget source := by
  decide +kernel

/-- The `0/1` matrix recording each physical successor exactly once. -/
def stepMatrix : TransferMatrix RecurrentTubeProfile :=
  fun source target =>
    if target = firstFullyRoutedTarget source ∨
       target = secondFullyRoutedTarget source then 1 else 0

/-- Positivity of the matrix is exactly the *full* physical recurrent
one-ring relation, not a selected deterministic subrelation. -/
theorem stepMatrix_pos_iff (source target : RecurrentTubeProfile) :
    0 < stepMatrix source target ↔ RecurrentTubeRingStep source target := by
  rw [← mem_recurrentNextSet_iff]
  simp only [stepMatrix, recurrentNextSet, Finset.mem_insert,
    Finset.mem_singleton]
  by_cases h : target = firstFullyRoutedTarget source ∨
      target = secondFullyRoutedTarget source <;> simp [h]

theorem stepMatrix_eq_relational :
    stepMatrix = relationalTransferMatrix RecurrentTubeRingStep := by
  funext source target
  have hiff :
      (target = firstFullyRoutedTarget source ∨
        target = secondFullyRoutedTarget source) ↔
        RecurrentTubeRingStep source target := by
    simpa only [recurrentNextSet, Finset.mem_insert,
      Finset.mem_singleton] using
        (mem_recurrentNextSet_iff source target)
  by_cases h : target = firstFullyRoutedTarget source ∨
      target = secondFullyRoutedTarget source
  · have hs := hiff.mp h
    simp [stepMatrix, relationalTransferMatrix, h, hs]
  · have hs : ¬ RecurrentTubeRingStep source target :=
      fun hstep => h (hiff.mpr hstep)
    simp [stepMatrix, relationalTransferMatrix, h, hs]

/-- Positive weighted entries are precisely the genuine physical exact
recurrent transfer paths. -/
theorem transferCount_pos_iff_physical (length : Nat)
    (source target : RecurrentTubeProfile) :
    0 < transferCount stepMatrix length source target ↔
      ExactRelationalTransfer RecurrentTubeRingStep length source target := by
  rw [stepMatrix_eq_relational]
  exact relationalTransferMatrix_pow_pos_iff
    RecurrentTubeRingStep length source target

/-- Sum the natural-number matrix power over every possible terminal
frontier. Matrix multiplication counts distinct intermediate histories. -/
def totalCount (length : Nat) (source : RecurrentTubeProfile) : Nat :=
  ∑ target : RecurrentTubeProfile, transferCount stepMatrix length source target

theorem totalCount_zero (source : RecurrentTubeProfile) :
    totalCount 0 source = 1 := by
  simp [totalCount, transferCount, Matrix.one_apply]

private theorem sum_two_distinct {Q : Type*} [Fintype Q] [DecidableEq Q]
    (first second : Q) (hne : first ≠ second) (f : Q → Nat) :
    (∑ q : Q, if q = first ∨ q = second then f q else 0) =
      f first + f second := by
  calc
    _ = (∑ q : Q, if q = first then f q else 0) +
        (∑ q : Q, if q = second then f q else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      by_cases hfirst : q = first
      · subst q
        simp [hne]
      · by_cases hsecond : q = second
        · subst q
          simp [Ne.symm hne]
        · simp [hfirst, hsecond]
    _ = _ := by simp

private theorem stepMatrix_sum (source : RecurrentTubeProfile)
    (f : RecurrentTubeProfile → Nat) :
    (∑ middle : RecurrentTubeProfile, stepMatrix source middle * f middle) =
      f (firstFullyRoutedTarget source) +
        f (secondFullyRoutedTarget source) := by
  simp only [stepMatrix, ite_mul, one_mul, zero_mul]
  exact sum_two_distinct
    (firstFullyRoutedTarget source) (secondFullyRoutedTarget source)
    (first_ne_second source) f

/-- At each physical ring there are exactly two distinct fully routed
successors. -/
theorem totalCount_succ (length : Nat) (source : RecurrentTubeProfile) :
    totalCount (length + 1) source =
      totalCount length (firstFullyRoutedTarget source) +
        totalCount length (secondFullyRoutedTarget source) := by
  classical
  change (∑ target : RecurrentTubeProfile,
      (stepMatrix ^ (length + 1)) source target) =
    (∑ target : RecurrentTubeProfile,
      (stepMatrix ^ length) (firstFullyRoutedTarget source) target) +
    (∑ target : RecurrentTubeProfile,
      (stepMatrix ^ length) (secondFullyRoutedTarget source) target)
  calc
    _ = ∑ target : RecurrentTubeProfile,
          ∑ middle : RecurrentTubeProfile,
            stepMatrix source middle * (stepMatrix ^ length) middle target := by
      apply Finset.sum_congr rfl
      intro target _
      rw [pow_succ' stepMatrix length, Matrix.mul_apply]
    _ = ∑ middle : RecurrentTubeProfile,
          stepMatrix source middle *
            (∑ target : RecurrentTubeProfile,
              (stepMatrix ^ length) middle target) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = _ := stepMatrix_sum source _

/-- Exact natural-number path mass is unbounded despite finite, eventually
two-periodic endpoint support. -/
theorem totalCount_eq_two_pow (length : Nat) (source : RecurrentTubeProfile) :
    totalCount length source = 2 ^ length := by
  induction length generalizing source with
  | zero => simpa using totalCount_zero source
  | succ length ih =>
      rw [totalCount_succ, ih, ih]
      ring

/-- Support has saturated by ring nine, but exact natural-number path
multiplicity still changes at ring eleven. The distinction is witnessed on
the *same* physical transfer, not on two independently defined evaluators. -/
theorem same_support_different_totalCount (source : RecurrentTubeProfile) :
    (∀ target : RecurrentTubeProfile,
      (0 < transferCount stepMatrix 9 source target) ↔
        (0 < transferCount stepMatrix 11 source target)) ∧
      totalCount 9 source ≠ totalCount 11 source := by
  constructor
  · intro target
    rw [transferCount_pos_iff_physical,
      transferCount_pos_iff_physical]
    exact (recurrentTransfer_period_two_after_nine 0 source target).symm
  · simp [totalCount_eq_two_pow]

/-- There is no uniform natural-number bound on these exact matrix-power
path counts, even though their Boolean support lies in a finite state space. -/
theorem totalCount_unbounded (source : RecurrentTubeProfile) (bound : Nat) :
    ∃ length, bound < totalCount length source := by
  refine ⟨bound + 1, ?_⟩
  rw [totalCount_eq_two_pow]
  exact (Nat.lt_succ_self bound).trans ((bound + 1).lt_two_pow_self)

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeCountGrowth
