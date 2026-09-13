import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularSourceWork

/-!
# Complete signed source of the filtered angular energy

Resolved and subgrid work recombine before taking any absolute values.
Their sum is a pairing with the filtered full inviscid RHS, independently
of the auxiliary support set. The coercive dissipative inequality retains
this actual all-input source. No bound for its time integral is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredAngularSourceBalance

open scoped RealInnerProductSpace
open MeasureTheory
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCoefficientLimitEquation
open PancakeConvectionFiberIdentity PancakeSobolevFiberEnvelope
open PancakeFilteredStrainDynamics InfiniteFilteredEquation PancakeLocalInfiniteVelocity
open PancakeFrequencyProjectorCommutator LocalLowDiffusionBudget LocalVorticityEighthMoment
open FourierFiniteSupport FiniteVorticityVariation FiniteAngularSourceWork
open FilteredAngularViscousBalance FiniteBandAngularEnergy

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Only the output is filtered; the full nonlinear input is retained. -/
def sourceWork (κ : ℝ) (χ : Wavevector → ℂ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ⟪correctedGradient κ (filteredVelocity χ u) x,
    fullVorticity (filteredVelocity χ (infiniteVelocityRHS 0 u)) x⟫

theorem sourceWork_eq_resolved_add_subgrid (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (u : FourierVelocity)
    (hu : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) :
    sourceWork κ χ u = work κ P (filteredVelocity χ u)
        (infiniteVelocityRHS 0 (filteredVelocity χ u)) +
      work κ P (filteredVelocity χ u) (subgridForce χ u) := by
  have hs (v : FourierVelocity) (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ v q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have he : infiniteVelocityRHS 0 (filteredVelocity χ u) + subgridForce χ u =
      filteredVelocity χ (infiniteVelocityRHS 0 u) := by
    funext q
    exact (filtered_infiniteVelocityRHS χ u C hχ 0 q (hu q)).symm
  rw [← work_add κ P _ _ _ (hs u), he, work_eq_pairing κ P _ _ (hs u),
    FilteredProjectionMean.restrictVelocity_eq_self P _ (hs _)]
  rfl

/-- The constant is chosen before viscosity, data, filter and radius. -/
theorem exists_coercive_source_threshold :
    ∃ L : ℝ, 0 < L ∧ ∀ {ν T B : ℝ} {u₀ : FourierVelocity}
      (s : LocalInfiniteVelocitySolution ν u₀ T B), 0 ≤ ν → 0 ≤ B →
      ∀ (κ : ℝ), 0 < κ → ∀ (P : Finset Wavevector) (χ : Wavevector → ℂ),
      (∀ q, q ∉ P → χ q = 0) → ∀ C : ℝ, (∀ q, ‖χ q‖ ≤ C) →
      ∀ R : ℝ, (∀ q ∈ P, ‖frequencyVec q‖ ≤ R) → L * (2 * Real.pi * R) ^ 2 ≤ κ →
      ∀ t ∈ Set.Ioo (0 : ℝ) T,
      (meanEnergy (filteredVelocity χ (s.coefficients t)) / 16 ≤
          correctedEnergy κ (filteredVelocity χ (s.coefficients t)) ∧
        correctedEnergy κ (filteredVelocity χ (s.coefficients t)) ≤
          meanEnergy (filteredVelocity χ (s.coefficients t)) / 8) ∧
      deriv (fun τ ↦ correctedEnergy κ (filteredVelocity χ (s.coefficients τ))) t +
          (ν / 2) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
          6 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) ≤
        sourceWork κ χ (s.coefficients t) := by
  obtain ⟨L, hL, hbound⟩ := exists_coercive_dissipative_threshold
  refine ⟨L, hL, fun s hν hB κ hκ P χ hcut C hχ R hP hscale t ht ↦ ?_⟩
  have h := hbound s hν hB κ hκ P χ hcut C hχ R hP hscale t ht
  rwa [← sourceWork_eq_resolved_add_subgrid κ P χ hcut C hχ _
    (s.summable_convection t (Set.Ioo_subset_Icc_self ht))] at h

end Mettapedia.FluidDynamics.NavierStokes.FilteredAngularSourceBalance
