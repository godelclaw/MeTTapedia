import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredCoherentProjectionBudget

/-!
# Recombining the complete signed nonlinear projection work

The resolved term and the all-input subgrid term together equal the
pairing with the filtered full inviscid RHS. Only after recombination
can the auxiliary output restriction be removed. Convergence of the
nonlinear fibers is explicit and supplied by the actual local solution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionNonlinearWork

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeHaarTransportRate
open PancakeCoefficientLimitEquation PancakeConvectionFiberIdentity
open PancakeSobolevFiberEnvelope
open PancakeFilteredStrainDynamics InfiniteFilteredEquation PancakeLocalInfiniteVelocity
open LocalLowDiffusionBudget LocalProjectionSourceWork FourierFiniteSupport FiniteVorticityVariation
open FilteredProjectionViscousBalance FilteredProjectionAbsorption FiniteBandProjectionAbsorption

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem nonlinearWork_eq_integral (ν R : ℝ) (hν : 0 < ν) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (u : FourierVelocity)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) :
    nonlinearWork ν R P χ u = ∫ x : T3,
      ⟪correctedGradient (regularization ν R) (normalization R) (filteredVelocity χ u) x,
        fullVorticity (filteredVelocity χ (infiniteVelocityRHS 0 u)) x⟫ := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have he : infiniteVelocityRHS 0 (filteredVelocity χ u) + subgridForce χ u =
      filteredVelocity χ (infiniteVelocityRHS 0 u) := by
    funext q
    exact (filtered_infiniteVelocityRHS χ u C hχ 0 q (hu q)).symm
  unfold nonlinearWork
  rw [← work_add _ _ (regularization_pos ν R hν) P _ _ _ (summable_fourierMoment P _ (hs u) 2), he]
  unfold work
  rw [FilteredProjectionMean.restrictVelocity_eq_self P _ (hs _)]

/-- The support set is bookkeeping, not a hidden part of the nonlinear work. -/
theorem nonlinearWork_support_independent (ν R : ℝ) (hν : 0 < ν) (P Q : Finset Wavevector)
    (χ : Wavevector → ℂ) (hP : ∀ q, q ∉ P → χ q = 0) (hQ : ∀ q, q ∉ Q → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (u : FourierVelocity)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) :
    nonlinearWork ν R P χ u = nonlinearWork ν R Q χ u := by
  rw [nonlinearWork_eq_integral ν R hν P χ hP C hχ u hu,
    nonlinearWork_eq_integral ν R hν Q χ hQ C hχ u hu]

theorem nonlinearWork_solution_eq {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν)
    (R : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    nonlinearWork ν R P χ (s.coefficients t) = ∫ x : T3,
      ⟪correctedGradient (regularization ν R) (normalization R) (filteredVelocity χ (s.coefficients t)) x,
        fullVorticity (filteredVelocity χ (infiniteVelocityRHS 0 (s.coefficients t))) x⟫ :=
  nonlinearWork_eq_integral ν R hν P χ hcut C hχ _ (s.summable_convection t ht)

end Mettapedia.FluidDynamics.NavierStokes.FilteredProjectionNonlinearWork
