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
#check v13RealLinear_not_rowsGenerateTarget_of_rows_card_zero
#check v13RealLinear_rowCombination_card
#check v13RealLinear_rowCombination_card_le_of_rows_card_le
#check v13RealLinear_rowCombination_card_le_for_branch
#check v13RealLinear_rowsBlockTarget_of_rowsGenerateTarget
#check v13RealLinear_rowsGenerateTarget_of_rowsBlockTarget
#check v13RealLinear_rowsBlockTarget_iff_rowsGenerateTarget
#check v13RealLinear_rowsGenerateTarget_singleton_iff
#check V13RealLinearTargetRows
#check v13RealLinear_mem_targetRows_iff
#check v13RealLinear_targetRows_card_le_one
#check v13RealLinearTargetRowChoice
#check v13RealLinearTargetRowObserver
#check v13RealLinear_targetRowObserver_generated_iff_targetRows_nonempty
#check V13RealLinearAdaptiveQRowExperiment.blocked_iff_generated
#check V13RealLinearAdaptiveQRowExperiment.generated_one_budget_exists_target_row
#check V13RealLinearAdaptiveQRowExperiment.targetRows_nonempty_of_generated_one_budget
#check v13RealLinearAdaptiveQRowBlockedGeneratedEquiv
#check v13RealLinearAdaptiveQRowBlockedMass_eq_generatedMass
#check v13RealLinearAdaptiveQRowGeneratedMass_le_one
#check v13RealLinear_qrow_one_le_epsilon_of_m_le_q
#check v13RealLinearAdaptiveQRowGeneratedMass_eq_zero_of_zero_budget
#check v13RealLinearAdaptiveRowSpanCountingBound_of_m_le_q
#check V13RealLinearAdaptiveRowSpanCountingBound
#check V13RealLinearUniformInvertibleRowSpanCountingBound
#check v13RealLinearUniformInvertibleRowSpanCountingBound_of_zero_budget
#check v13RealLinearUniformInvertibleRowSpanCountingBound_of_m_le_q
#check v13RealLinearUniformAdaptiveQRowSuccess
#check V13RealLinearAdaptiveKernelFlipSurchargeBound
#check v13RealLinear_adaptiveKernelFlipSurchargeBound
#check v13RealLinear_adaptive_qrow_success_bound_of_spanCounting
#check v13RealLinear_uniform_adaptive_qrow_success_bound_of_spanCounting
#check v13RealLinear_uniform_zero_row_success_bound
#check v13RealLinear_uniform_high_budget_success_bound
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
#print axioms v13RealLinear_rowsGenerateTarget_singleton_iff
#print axioms v13RealLinear_targetRows_card_le_one
#print axioms v13RealLinear_targetRowObserver_generated_iff_targetRows_nonempty
#print axioms V13RealLinearAdaptiveQRowExperiment.blocked_iff_generated
#print axioms V13RealLinearAdaptiveQRowExperiment.generated_one_budget_exists_target_row
#print axioms V13RealLinearAdaptiveQRowExperiment.targetRows_nonempty_of_generated_one_budget
#print axioms v13RealLinearAdaptiveQRowBlockedMass_eq_generatedMass
#print axioms v13RealLinearAdaptiveQRowGeneratedMass_le_one
#print axioms v13RealLinear_qrow_one_le_epsilon_of_m_le_q
#print axioms v13RealLinearAdaptiveQRowGeneratedMass_eq_zero_of_zero_budget
#print axioms v13RealLinearUniformInvertibleRowSpanCountingBound_of_zero_budget
#print axioms v13RealLinearAdaptiveRowSpanCountingBound_of_m_le_q
#print axioms v13RealLinearUniformInvertibleRowSpanCountingBound_of_m_le_q
#print axioms v13RealLinear_adaptive_qrow_success_bound_of_spanCounting
#print axioms v13RealLinear_uniform_adaptive_qrow_success_bound_of_spanCounting
#print axioms v13RealLinear_uniform_zero_row_success_bound
#print axioms v13RealLinear_uniform_high_budget_success_bound
#print axioms v13RealLinear_qrow_epsilon_nonnegative
#print axioms v13RealLinearQRowBoundRegression_conditional_shape
#print axioms v13RealLinearQRowBoundRegression_uniform_conditional_shape

end Mettapedia.Computability.PNP
