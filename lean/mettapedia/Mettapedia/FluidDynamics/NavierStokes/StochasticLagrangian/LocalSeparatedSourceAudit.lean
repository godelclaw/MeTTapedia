import Mettapedia.Analysis.PeriodicRieszSeparatedTests
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSeparatedSourceBudget

/-! Audit of separated-source payment and the exact remaining near source. -/

open Mettapedia.FluidDynamics.NavierStokes

example (r L : ℝ) (u : PeriodicFourierTriad.FourierVelocity) :
    VorticitySeparatedSource.farSource r L 0 u = 0 := by
  have hk (h : UnitAddTorus (Fin 3)) : Mettapedia.Analysis.PeriodicRieszOperator.kernel (d := 3) 0 h = 0 := by
    have hz (q : UnitAddTorus (Fin 3)) : Mettapedia.Analysis.PeriodicRieszOperator.rawKernel (d := 3) 0 q = 0 := by
      unfold Mettapedia.Analysis.PeriodicRieszOperator.rawKernel
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      rw [Mettapedia.Analysis.PeriodicRieszKernel.kernel_zero]
      exact zero_smul ℝ (Mettapedia.Analysis.PeriodicRieszOperator.basisOperator (d := 3) i j)
    simp only [Mettapedia.Analysis.PeriodicRieszOperator.kernel, hz, add_zero]
    ext v i
    change (1 / 2 : ℝ) * 0 = 0
    ring
  simp only [VorticitySeparatedSource.farSource, VorticitySeparatedSource.farKernel, hk, ite_self,
    Mettapedia.Analysis.SmoothAmplitudePairing.retainedStretch,
    Mettapedia.Analysis.SignedCrossKernel.pairedStretch, zero_apply,
    inner_zero_right, mul_zero, MeasureTheory.integral_zero]

#print axioms VorticitySeparatedSource.integrable_retained
#print axioms VorticitySeparatedSource.integrable_farDensity
#print axioms VorticitySeparatedSource.retainedSource_eq_near_add_far
#print axioms VorticitySeparatedSource.firstMoment_le_half_one_add_enstrophy
#print axioms VorticitySeparatedSource.exists_uniform_farSource_bound
#print axioms VorticitySeparatedSource.exists_uniform_source_bound
#print axioms LocalSeparatedSourceBudget.growthCoefficient_nonneg
#print axioms LocalSeparatedSourceBudget.continuousOn_growthCoefficient
#print axioms LocalSeparatedSourceBudget.integral_growthCoefficient_le
#print axioms LocalSeparatedSourceBudget.exists_uniform_farSource_growth_budget
