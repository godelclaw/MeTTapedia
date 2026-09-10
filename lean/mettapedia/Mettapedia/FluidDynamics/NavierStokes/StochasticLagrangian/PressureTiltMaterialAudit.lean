import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTiltQuadraticGrowth

/-!
# Regression tests and axiom audit for material quadratic defect generation
-/

open scoped Topology
open Mettapedia.FluidDynamics.NavierStokes
open PressureTiltDatum PressureTiltMaterialEvolution PressureTiltQuadraticGrowth
open PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories

example (nu : ℝ) : quadraticCoefficient 0 nu = 0 := by
  simp [quadraticCoefficient]

example (nu : ℝ) : 0 < quadraticCoefficient 1 nu :=
  quadraticCoefficient_pos 1 nu (by norm_num)

example (epsilon : ℝ) : quadraticCoefficient epsilon 0 =
    (12288 / 25 : ℝ) * Real.pi ^ 5 * epsilon ^ 2 := by
  unfold quadraticCoefficient
  ring

example (nu : ℝ) (hnu : 0 < nu) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (velocity 1) T B,
      ∃ X : ℝ → Fin 3 → ℝ, X 0 = 0 ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          HasDerivWithinAt X (liftedVelocity s t (X t)) (Set.Icc (0 : ℝ) T) t) ∧
        defectAlong s X 0 = 0 ∧ 0 < quadraticCoefficient 1 nu ∧
        Filter.Tendsto (fun t ↦ defectAlong s X t / t ^ 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (quadraticCoefficient 1 nu)) :=
  exists_material_quadratic_growth 1 nu hnu (by norm_num)

#check PressureTiltMaterialEvolution.exists_material_alignment_loss
#check PressureTiltQuadraticGrowth.exists_material_quadratic_growth

#print axioms MaterialInitialGradient.continuousOn_material_eval_closed
#print axioms MaterialInitialGradient.continuous_materialGradientRate_spaceTime
#print axioms MaterialInitialGradient.continuous_velocityGradient_spaceTime
#print axioms MaterialInitialGradient.materialGradientRate_eq_velocityRHS_of_stagnation
#print axioms MaterialInitialGradient.velocityGradient_hasDerivWithinAt_initial
#print axioms PressureTiltMaterialEvolution.defect_initial
#print axioms PressureTiltMaterialEvolution.eventually_defect_pos
#print axioms PressureTiltMaterialEvolution.exists_material_alignment_loss
#print axioms PressureTiltMaterialEvolution.gradient_hasDerivWithinAt_initial
#print axioms PressureTiltMaterialEvolution.residual_hasDerivWithinAt_initial
#print axioms PressureTiltMaterialEvolution.residual_initial
#print axioms PressureTiltMaterialEvolution.strain_initial
#print axioms PressureTiltMaterialEvolution.torusPoint_initial
#print axioms PressureTiltMaterialEvolution.vorticity_initial
#print axioms PressureTiltQuadraticGrowth.exists_material_quadratic_growth
#print axioms PressureTiltQuadraticGrowth.quadraticCoefficient_eq_rate_quotient
#print axioms PressureTiltQuadraticGrowth.quadraticCoefficient_pos
#print axioms PressureTiltQuadraticGrowth.spectralWidth_origin
#print axioms PressureTiltQuadraticGrowth.tendsto_material_defect_div_sq
#print axioms PressureTiltQuadraticGrowth.thirdEigenvalue_origin
#print axioms PressureTiltResidualRate.hasDerivWithinAt_residual_of_rates
#print axioms SpectralDefectAsymptotics.continuous_spectralWidth
#print axioms SpectralDefectAsymptotics.tendsto_defect_div_sq
#print axioms SpectralDefectAsymptotics.tendsto_norm_sq_div_sq
