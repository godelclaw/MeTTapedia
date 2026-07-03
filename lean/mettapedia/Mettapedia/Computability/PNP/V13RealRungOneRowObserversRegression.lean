import Mettapedia.Computability.PNP.V13RealRungOneRowObservers

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

#check V13RealLinearRowsBlockTarget
#check v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
#check v13RealLinear_same_rowsTranscript_after_kernel_add
#check v13RealLinear_target_changes_after_kernel_hit
#check v13RealLinear_opposite_targets_same_rowsTranscript_of_not_blocked
#check V13RealLinearFixedRowsTranscriptTargetFiber
#check v13RealLinear_fixedRowsTranscriptTargetFlipEquiv
#check v13RealLinear_fixedRowsTranscriptTargetFiber_card_eq_of_not_blocked

theorem v13RealLinearRowObserversRegression_identity_empty_not_blocked :
    ¬ V13RealLinearRowsBlockTarget
        (v13RealLinearIdentity 2) (∅ : Finset (Fin 2)) 0 := by
  intro hblock
  have hhit :
      v13RealLinearSingleBit (m := 2) 0 0 = 0 :=
    hblock (v13RealLinearSingleBit 0) (by simp)
  simp [v13RealLinearSingleBit] at hhit

theorem v13RealLinearRowObserversRegression_empty_collision :
    ∃ omega₀ omega₁ : V13RealLinearWorld 2,
      v13RealLinearRowsTranscript (∅ : Finset (Fin 2))
          (v13RealLinearPublicInput omega₀) =
        v13RealLinearRowsTranscript (∅ : Finset (Fin 2))
          (v13RealLinearPublicInput omega₁) ∧
      v13RealLinearTarget 0 omega₀ ≠
        v13RealLinearTarget 0 omega₁ := by
  exact
    v13RealLinear_opposite_targets_same_rowsTranscript_of_not_blocked
      (v13RealLinearIdentity 2) (∅ : Finset (Fin 2)) 0
      v13RealLinearRowObserversRegression_identity_empty_not_blocked

#print axioms v13RealLinear_exists_kernel_hit_of_not_rowsBlockTarget
#print axioms v13RealLinear_same_rowsTranscript_after_kernel_add
#print axioms v13RealLinear_target_changes_after_kernel_hit
#print axioms v13RealLinear_opposite_targets_same_rowsTranscript_of_not_blocked
#print axioms v13RealLinear_fixedRowsTranscriptTargetFlipEquiv
#print axioms v13RealLinear_fixedRowsTranscriptTargetFiber_card_eq_of_not_blocked
#print axioms v13RealLinearRowObserversRegression_empty_collision

end Mettapedia.Computability.PNP
