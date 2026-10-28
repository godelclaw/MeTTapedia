import Mettapedia.Computability.PNP.V13RealRungThreeGaugeSwitch

namespace Mettapedia.Computability.PNP

set_option autoImplicit false

example (observer : V13RealLinearRhsOnlyObserver 2) (i : Fin 2) :
    v13RealLinearRhsOnlySuccess observer i ≤
      (1 / 2 : Rat) + 1 / (2 : Rat) ^ 2 :=
  v13RealLinear_rhsOnly_success_bound observer i

example (observer : V13RealLinearRhsOnlyObserver 3) (i : Fin 3) :
    v13RealLinearRhsOnlySuccess observer i ≤
      (1 / 2 : Rat) + 1 / (2 : Rat) ^ 3 :=
  v13RealLinear_rhsOnly_success_bound observer i

def v13RealLinearRhsCoordinateObserver {m : Nat} (i : Fin m) :
    V13RealLinearRhsOnlyObserver m where
  decide := fun rhs => rhs i

example : V13RealLinearRhsOnlyObserver 2 :=
  v13RealLinearRhsCoordinateObserver 0

def v13RealLinearEmptyColumnSketchObserverTwo :
    V13RealLinearColumnSketchRhsObserver 2 0 where
  cols := ∅
  decide := fun _ rhs => rhs 0
  readBudget := by simp

example (observer : V13RealLinearColumnSketchRhsObserver 3 1)
    (i : Fin 3) :
    v13RealLinearColumnSketchRhsSuccess observer i ≤
      (1 / 2 : Rat) + (2 : Rat) ^ 1 / (2 : Rat) ^ 3 :=
  v13RealLinearColumnSketchRhs_success_bound observer i

end Mettapedia.Computability.PNP
