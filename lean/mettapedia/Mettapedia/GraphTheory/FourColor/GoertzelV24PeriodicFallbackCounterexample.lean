import Mettapedia.GraphTheory.FourColor.GoertzelV24CorridorTransferMatrix

/-!
# A two-state obstruction to one-step padding from eventual periodicity

The source playbook suggests that eventual periodicity of a finite transfer
supplies a self-looping recurrent state and hence monotonicity of exact-length
acceptance. A two-state alternating transfer refutes both deductions. It is a
generic obstruction to that *fallback*, not a counterexample to the actual
hexagonal Cell-3 transfer, whose local identity support is a separate question.

The corrected general theorem is
`GoertzelV24CorridorPumping.finiteRelationalTransfer_rejectionDescentWithBounds`:
it preserves rejection only in an eventual congruence class. Any physical
splice using it must respect that period.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24PeriodicFallbackCounterexample

open GoertzelV24CorridorPumping GoertzelV24CorridorTransferMatrix

/-- The entire transition graph is a directed two-cycle. -/
def alternating (source target : Bool) : Prop := target = !source

instance : DecidableRel alternating := fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- Both states remain live indefinitely; seriality is not the missing condition. -/
theorem alternating_serial :
    LiveTransferIsSerial (fun _ : Bool => True) alternating := by
  intro source _
  exact ⟨!source, trivial, rfl⟩

/-- Every state recurs after two steps. -/
theorem alternating_return (source : Bool) :
    ExactRelationalTransfer alternating 2 source source := by
  exact ExactRelationalTransfer.succ rfl
    (ExactRelationalTransfer.succ (by cases source <;> decide)
      (ExactRelationalTransfer.zero source))

/-- No recurrent state has the one-step stay transition the playbook asks for. -/
theorem alternating_no_self_loop (source : Bool) :
    ¬ alternating source source := by
  cases source <;> decide

private def initial : Finset Bool := {false}
private def accepting (state : Bool) : Prop := state = true

private instance : DecidablePred accepting := fun _ => inferInstanceAs (Decidable (_ = _))

/-- The exact-length transfer accepts after one slab. -/
theorem accepts_one :
    TransferAcceptsInExactly alternating initial accepting 1 := by
  simp [TransferAcceptsInExactly, reachableProfilesAfter,
    relationalTransferPost, initial, alternating, accepting]

/-- But rejects after two slabs, despite live serial recurrence. -/
theorem rejects_two :
    ¬ TransferAcceptsInExactly alternating initial accepting 2 := by
  simp [TransferAcceptsInExactly, reachableProfilesAfter,
    relationalTransferPost, initial, alternating, accepting,
    Function.iterate_succ_apply]

/-- The source fallback's proposed one-step shortening implication is false
even for a serial transfer in which every state is recurrent. -/
theorem rejection_not_downward_monotone :
    ¬ (¬ TransferAcceptsInExactly alternating initial accepting 2 →
        ¬ TransferAcceptsInExactly alternating initial accepting 1) := by
  intro h
  exact h rejects_two accepts_one

/-- The same obstruction is present in the exact nonnegative Count matrix,
not merely in a Boolean reachability encoding. -/
theorem count_one_positive :
    0 < transferCount (relationalTransferMatrix alternating) 1 false true := by
  exact (relationalTransferMatrix_pow_pos_iff alternating 1 false true).2
    (ExactRelationalTransfer.succ rfl
      (ExactRelationalTransfer.zero true))

theorem count_two_zero :
    transferCount (relationalTransferMatrix alternating) 2 false true = 0 := by
  have h : ¬ ExactRelationalTransfer alternating 2 false true := by
    intro path
    have hp : TransferAcceptsInExactly alternating initial accepting 2 := by
      refine ⟨true, ?_, rfl⟩
      exact (mem_reachableProfilesAfter_iff alternating initial 2 true).2
        ⟨false, by simp [initial], path⟩
    exact rejects_two hp
  have hnot : ¬ 0 < transferCount
      (relationalTransferMatrix alternating) 2 false true := by
    exact fun hp => h ((relationalTransferMatrix_pow_pos_iff
      alternating 2 false true).1 hp)
  omega

end Mettapedia.GraphTheory.FourColor.GoertzelV24PeriodicFallbackCounterexample
