import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceDecomposition
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergencePhysicalKernel

/-! Boundary and scale checks for the coherent pressure factorization. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceAudit

open MeasureTheory Mettapedia.Analysis.EuclideanCrossProduct
open PressureLowOutputCutoff (ratio receiver)
open PressureLowOutputSymbol (pairEquiv)
open PressureCoherentDivergencePhysicalKernel
open scoped ContDiff SchwartzMap FourierTransform RealInnerProductSpace

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "P" => R3 × R3

example (a : R3) : ContDiff ℝ ∞ (fun x : R3 ↦ cross x (a + x)) := by
  have hm : ContDiff ℝ ∞ (fun x : R3 ↦ (x, a + x)) := by fun_prop
  simpa only [Function.comp_def] using contDiff_cross.comp hm

example (e : R3) (i : Fin 3) :
    PressureCoherentDivergenceKernel.retainedKernel (0, e) i = 0 :=
  PressureCoherentDivergenceKernel.retainedKernel_zero e i

/-- The degenerate physical coordinate change is not invoked at zero ratio. -/
example (e : R3) (i : Fin 3) : physicalKernel (0, e) i = 0 := by
  simp [physicalKernel, ratio]

/-- The cancellation holds without a unit-direction or input-divergence hypothesis. -/
example (t : ℝ) (e : R3) (i : Fin 3) (p : P)
    (h : ⟪p.1, e⟫ + ⟪receiver t p, e⟫ = 0) :
    PressureDyadicSymbol.retained t p *
      CoherentPressurePair.tiltPair e p.1 (receiver t p) e e i = 0 := by
  rw [PressureCoherentDivergenceSymbol.retained_pressure_eq, h, mul_zero]

example (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (i : Fin 3) (ξ : E6) :
    ((PressureDyadicPhysicalKernel.physicalCutoff t (N⁻¹ • ξ) *
        CoherentPressurePair.tiltPair e (pairEquiv ξ).1 (pairEquiv ξ).2 e e i : ℝ) : ℂ) =
      (𝓕 (scaledKernel N hN (t, e) i)) ξ *
        ((N⁻¹ * ⟪(pairEquiv ξ).1 + (pairEquiv ξ).2, e⟫ : ℝ) : ℂ) := by
  simpa only [inner_add_left] using pressure_eq_fourier_scaledKernel_mul N hN (t, e) i ξ

/-- Constants are chosen before the scale, ratio, direction, and output coordinate. -/
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, ∀ hN : 0 < N,
    ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ e : R3, ‖e‖ = 1 → ∀ i : Fin 3,
      (∫ x : E6, ‖scaledKernel N hN (t, e) i x‖) ≤ ratio t * C ∧
      (∫ x : E6, ‖x‖ * ‖scaledKernel N hN (t, e) i x‖) ≤ C / N := by
  obtain ⟨C0, hC0, h0⟩ := exists_uniform_scaled_mass
  obtain ⟨C1, hC1, h1⟩ := exists_uniform_scaled_firstMoment
  refine ⟨max C0 C1, hC0.trans (le_max_left _ _), ?_⟩
  intro N hN t ht e he i
  constructor
  · exact (h0 N hN t ht e he i).trans (mul_le_mul_of_nonneg_left
      (le_max_left _ _) (div_nonneg ht.1 (by norm_num)))
  · exact (h1 N hN t ht e he i).trans (div_le_div_of_nonneg_right (le_max_right _ _) hN.le)

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceAudit

#print axioms Mettapedia.Analysis.EuclideanCrossProduct.contDiff_cross
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceSymbol.retained_pressure_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceSymbol.contDiff_symbol
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceSymbol.tsupport_symbol_subset
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceKernel.exists_uniform_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceKernel.retained_pressure_eq_fourier_mul
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceKernel.moment_retainedKernel
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceKernel.exists_uniform_retained_moment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePhysicalKernel.pressure_eq_fourier_scaledKernel_mul
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePhysicalKernel.exists_uniform_scaled_mass
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergencePhysicalKernel.exists_uniform_scaled_firstMoment
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceDecomposition.retained_pressure_eq_mixed_add_divergence
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceDecomposition.retained_pressure_eq_mixed_sub_transverse_divergence
