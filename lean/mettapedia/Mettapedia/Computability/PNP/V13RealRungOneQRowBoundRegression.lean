import Mettapedia.Computability.PNP.V13RealRungOneQRowBound

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

#check V13RealLinearAdaptiveQRowExperiment
#check v13RealLinearAdaptiveQRowSuccess
#check v13RealLinearAdaptiveQRowBlockedMass
#check v13RealLinearAdaptiveQRowGeneratedMass
#check v13RealLinearQRowEpsilon
#check V13RealLinearAdaptiveQRowExperiment.branchRows_card_le
#check V13RealLinearRowCombination
#check v13RealLinearRowCombinationEval
#check V13RealLinearRowsGenerateTarget
#check v13RealLinear_rowCombination_card
#check v13RealLinear_rowCombination_card_le_of_rows_card_le
#check v13RealLinear_rowCombination_card_le_for_branch
#check v13RealLinear_rowsBlockTarget_of_rowsGenerateTarget
#check v13RealLinear_rowsGenerateTarget_of_rowsBlockTarget
#check v13RealLinear_rowsBlockTarget_iff_rowsGenerateTarget
#check V13RealLinearAdaptiveQRowExperiment.blocked_iff_generated
#check v13RealLinearAdaptiveQRowBlockedGeneratedEquiv
#check v13RealLinearAdaptiveQRowBlockedMass_eq_generatedMass
#check V13RealLinearAdaptiveRowSpanCountingBound
#check V13RealLinearUniformInvertibleRowSpanCountingBound
#check v13RealLinearUniformAdaptiveQRowSuccess
#check V13RealLinearAdaptiveKernelFlipSurchargeBound
#check v13RealLinear_adaptiveKernelFlipSurchargeBound
#check v13RealLinear_adaptive_qrow_success_bound_of_spanCounting
#check v13RealLinear_uniform_adaptive_qrow_success_bound_of_spanCounting
#check v13RealLinear_qrow_epsilon_nonnegative

def v13RealLinearQRowBoundRegression_staticConstant :
    V13RealLinearStaticRowObserver 2 0 where
  rows := ∅
  decide := fun _ => 0
  readBudget := by simp
  factorsThroughRows := by
    intro omega₀ omega₁ hsame
    rfl

def v13RealLinearQRowBoundRegression_adaptiveConstant :
    V13RealLinearAdaptiveRowObserver 2 0 where
  Branch := Unit
  branch := fun _ => ()
  staticBranch := fun _ => v13RealLinearQRowBoundRegression_staticConstant
  decide := fun _ => 0
  branchDecision := by
    intro omega
    rfl
  branchStable := by
    intro A x w b hbranch hkernel
    cases b
    rfl

def v13RealLinearQRowBoundRegression_experiment :
    V13RealLinearAdaptiveQRowExperiment 2 0 Unit where
  sampleA := fun _ => v13RealLinearIdentity 2
  observer := v13RealLinearQRowBoundRegression_adaptiveConstant

theorem v13RealLinearQRowBoundRegression_epsilon_nonnegative :
    0 ≤ v13RealLinearQRowEpsilon 0 2 :=
  v13RealLinear_qrow_epsilon_nonnegative 0 2

theorem v13RealLinearQRowBoundRegression_conditional_shape
    (hcount :
      V13RealLinearAdaptiveRowSpanCountingBound
        v13RealLinearQRowBoundRegression_experiment 0) :
    v13RealLinearAdaptiveQRowSuccess
        v13RealLinearQRowBoundRegression_experiment 0 ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 0 2 := by
  exact
    v13RealLinear_adaptive_qrow_success_bound_of_spanCounting
      v13RealLinearQRowBoundRegression_experiment 0 hcount

theorem v13RealLinearQRowBoundRegression_uniform_conditional_shape
    (hcount :
      V13RealLinearUniformInvertibleRowSpanCountingBound
        v13RealLinearQRowBoundRegression_adaptiveConstant 0) :
    v13RealLinearUniformAdaptiveQRowSuccess
        v13RealLinearQRowBoundRegression_adaptiveConstant 0 ≤
      (1 / 2 : Rat) + v13RealLinearQRowEpsilon 0 2 := by
  exact
    v13RealLinear_uniform_adaptive_qrow_success_bound_of_spanCounting
      v13RealLinearQRowBoundRegression_adaptiveConstant 0 hcount

#print axioms v13RealLinear_adaptiveKernelFlipSurchargeBound
#print axioms v13RealLinear_rowCombination_card_le_for_branch
#print axioms v13RealLinear_rowsBlockTarget_of_rowsGenerateTarget
#print axioms v13RealLinear_rowsGenerateTarget_of_rowsBlockTarget
#print axioms v13RealLinear_rowsBlockTarget_iff_rowsGenerateTarget
#print axioms V13RealLinearAdaptiveQRowExperiment.blocked_iff_generated
#print axioms v13RealLinearAdaptiveQRowBlockedMass_eq_generatedMass
#print axioms v13RealLinear_adaptive_qrow_success_bound_of_spanCounting
#print axioms v13RealLinear_uniform_adaptive_qrow_success_bound_of_spanCounting
#print axioms v13RealLinear_qrow_epsilon_nonnegative
#print axioms v13RealLinearQRowBoundRegression_conditional_shape
#print axioms v13RealLinearQRowBoundRegression_uniform_conditional_shape

end Mettapedia.Computability.PNP
