import Mettapedia.Computability.PNP.V13RealRungOneAdaptiveRows

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

#check V13RealLinearAdaptiveRowObserver
#check V13RealLinearAdaptiveBranchCorrect
#check V13RealLinearAdaptiveBranchIncorrect
#check v13RealLinear_adaptive_decide_same_after_kernel_add_on_branch
#check v13RealLinear_adaptiveBranch_correctIncorrectEquiv
#check v13RealLinear_adaptiveBranch_correct_card_eq_incorrect_card_of_kernel_hit
#check v13RealLinear_adaptiveBranch_correct_card_eq_incorrect_card_of_not_blocked

def v13RealLinearAdaptiveRowsRegression_staticConstant :
    V13RealLinearStaticRowObserver 2 0 where
  rows := ∅
  decide := fun _ => 0
  readBudget := by simp
  factorsThroughRows := by
    intro omega₀ omega₁ hsame
    rfl

def v13RealLinearAdaptiveRowsRegression_constantObserver :
    V13RealLinearAdaptiveRowObserver 2 0 where
  Branch := Unit
  branch := fun _ => ()
  staticBranch := fun _ => v13RealLinearAdaptiveRowsRegression_staticConstant
  decide := fun _ => 0
  branchDecision := by
    intro omega
    rfl
  branchStable := by
    intro A x w b hbranch hkernel
    cases b
    rfl

theorem v13RealLinearAdaptiveRowsRegression_empty_correct_eq_incorrect :
    Fintype.card
        (V13RealLinearAdaptiveBranchCorrect
          v13RealLinearAdaptiveRowsRegression_constantObserver
          (v13RealLinearIdentity 2) 0 ()) =
      Fintype.card
        (V13RealLinearAdaptiveBranchIncorrect
          v13RealLinearAdaptiveRowsRegression_constantObserver
          (v13RealLinearIdentity 2) 0 ()) := by
  exact
    v13RealLinear_adaptiveBranch_correct_card_eq_incorrect_card_of_not_blocked
      v13RealLinearAdaptiveRowsRegression_constantObserver
      (v13RealLinearIdentity 2) 0 ()
      (by
        intro hblock
        have hhit :
            v13RealLinearSingleBit (m := 2) 0 0 = 0 :=
          hblock (v13RealLinearSingleBit 0) (by
            intro row hmem
            simp [v13RealLinearAdaptiveRowsRegression_constantObserver,
              v13RealLinearAdaptiveRowsRegression_staticConstant] at hmem)
        simp [v13RealLinearSingleBit] at hhit)

#print axioms v13RealLinear_adaptiveBranch_correctIncorrectEquiv
#print axioms v13RealLinear_adaptiveBranch_correct_card_eq_incorrect_card_of_kernel_hit
#print axioms v13RealLinear_adaptiveBranch_correct_card_eq_incorrect_card_of_not_blocked
#print axioms v13RealLinearAdaptiveRowsRegression_empty_correct_eq_incorrect

end Mettapedia.Computability.PNP
