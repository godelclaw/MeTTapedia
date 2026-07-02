import Mettapedia.Computability.PNP.V13RealRungOneStaticRows

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

#check V13RealLinearStaticRowObserver
#check V13RealLinearFixedCorrect
#check V13RealLinearFixedIncorrect
#check v13RealLinear_staticRows_decide_same_after_kernel_add
#check v13RealLinear_staticRows_correctIncorrectEquiv
#check v13RealLinear_staticRows_correct_card_eq_incorrect_card_of_kernel_hit
#check v13RealLinear_staticRows_correct_card_eq_incorrect_card_of_not_blocked

def v13RealLinearStaticRowsRegression_constantObserver :
    V13RealLinearStaticRowObserver 2 0 where
  rows := ∅
  decide := fun _ => 0
  readBudget := by simp
  factorsThroughRows := by
    intro omega₀ omega₁ hsame
    rfl

theorem v13RealLinearStaticRowsRegression_empty_correct_eq_incorrect :
    Fintype.card
        (V13RealLinearFixedCorrect
          v13RealLinearStaticRowsRegression_constantObserver
          (v13RealLinearIdentity 2) 0) =
      Fintype.card
        (V13RealLinearFixedIncorrect
          v13RealLinearStaticRowsRegression_constantObserver
          (v13RealLinearIdentity 2) 0) := by
  exact
    v13RealLinear_staticRows_correct_card_eq_incorrect_card_of_not_blocked
      v13RealLinearStaticRowsRegression_constantObserver
      (v13RealLinearIdentity 2) 0
      (by
        intro hblock
        have hhit :
            v13RealLinearSingleBit (m := 2) 0 0 = 0 :=
          hblock (v13RealLinearSingleBit 0) (by
            intro row hmem
            simp [v13RealLinearStaticRowsRegression_constantObserver] at hmem)
        simp [v13RealLinearSingleBit] at hhit)

#print axioms v13RealLinear_staticRows_correctIncorrectEquiv
#print axioms v13RealLinear_staticRows_correct_card_eq_incorrect_card_of_kernel_hit
#print axioms v13RealLinear_staticRows_correct_card_eq_incorrect_card_of_not_blocked
#print axioms v13RealLinearStaticRowsRegression_empty_correct_eq_incorrect

end Mettapedia.Computability.PNP
