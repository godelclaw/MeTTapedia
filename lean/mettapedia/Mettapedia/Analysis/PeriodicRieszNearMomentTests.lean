import Mettapedia.Analysis.PeriodicRieszNearMoment

/-! Regression checks for cutoff-uniform near-diagonal moment bounds. -/

open MeasureTheory Mettapedia.Analysis

noncomputable section

namespace Mettapedia.Analysis.PeriodicRieszNearMomentTests

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

example (N : ℕ) :
    (∫ x in Metric.ball (0 : UnitAddTorus (Fin 3)) 0,
      ‖x‖ ^ 2 * ‖PeriodicRieszOperator.kernel N x‖) = 0 := by simp

example (N : ℕ) :
    (∫ x in Metric.ball (0 : UnitAddTorus (Fin 3)) (1 / 2 : ℝ),
      ‖x‖ ^ 2 * ‖PeriodicRieszOperator.kernel N x‖) ≤
        (1 / 2 : ℝ) * PeriodicRieszNearMoment.firstMomentBound 3 :=
  PeriodicRieszNearMoment.nearSecondMoment_le _ (by norm_num) N

#print axioms AnnularRieszKernel.firstMoment_nonneg
#print axioms AnnularRieszKernel.firstMoment_dyadicKernel
#print axioms AnnularRieszKernel.firstMoment_partialKernel_le
#print axioms PeriodicRieszNearMoment.integrable_entryFirstMoment
#print axioms PeriodicRieszNearMoment.entryFirstMoment_le
#print axioms PeriodicRieszNearMoment.firstMomentBound_nonneg
#print axioms PeriodicRieszNearMoment.integrable_rawFirstMoment
#print axioms PeriodicRieszNearMoment.rawFirstMoment_le
#print axioms PeriodicRieszNearMoment.integrable_firstMoment
#print axioms PeriodicRieszNearMoment.firstMoment_le
#print axioms PeriodicRieszNearMoment.nearSecondMoment_le

end Mettapedia.Analysis.PeriodicRieszNearMomentTests
