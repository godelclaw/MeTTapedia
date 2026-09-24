import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredProjectionAbsorption
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRegularizedHelicityBudget

/-!
# Coherent stretching and viscous payment in one filtered budget

The regularized coherent-stretch estimate and the curvature estimate spend
distinct shares of the octic dissipation at the same normalization. Their
combination retains a quarter of weighted palinstrophy and half of radial
dissipation. The complete signed remainder is defined explicitly and is
not bounded here; this is a reduction of the dynamical obligation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FilteredCoherentProjectionBudget

open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity
open LocalVorticityEighthMoment LocalRegularizedHelicityBudget FourierFiniteSupport
open FiniteBandProjectionAbsorption FilteredProjectionAbsorption

/-- The spectral/center remainder and the complete nonlinear source use
exactly the normalization of the corrected energy. -/
def signedWorkRemainder (ν R : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) : ℝ :=
  nonlinearWork ν R P χ u - stretching (filteredVelocity χ u) -
    signedRemainder (regularization ν R) (normalization R) (filteredVelocity χ u) / normalization R

/-- This identity exposes the remaining nonlinear work rather than
asserting that renaming it has paid it. -/
theorem signedWorkRemainder_eq (ν R : ℝ) (hν : 0 < ν) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hd : ∀ q, modeDot q (u q) = 0) :
    signedWorkRemainder ν R P χ u = nonlinearWork ν R P χ u +
      6 / normalization R * LocalVariableHelicityCenter.centeredIntegral
        (LocalVariableHelicityCenter.regularizedCenter (regularization ν R) (filteredVelocity χ u))
        (filteredVelocity χ u) := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ u q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hdχ (q : Wavevector) : modeDot q (filteredVelocity χ u q) = 0 := by
    simp only [filteredVelocity, PancakePeriodicCoherentSplit.modeDot_smul, hd q, mul_zero]
  rw [signedWorkRemainder, signedRemainder_eq _ (regularization_pos ν R hν) _ _
    (summable_fourierMoment P _ hs 4) hdχ]
  have hκ := (normalization_pos R).ne'
  field_simp
  ring

theorem deriv_correctedEnergy_add_dissipation_le {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 < ν) (hB : 0 ≤ B)
    (R : ℝ) (P : Finset Wavevector) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (C : ℝ) (hχ : ∀ q, ‖χ q‖ ≤ C) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    deriv (fun τ ↦ correctedEnergy ν R (filteredVelocity χ (s.coefficients τ))) t +
        (ν / 4) * weightedPalinstrophy (filteredVelocity χ (s.coefficients t)) +
        3 * ν * radialDissipation (filteredVelocity χ (s.coefficients t)) ≤
      signedWorkRemainder ν R P χ (s.coefficients t) := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ (s.coefficients t) q = 0 := by
    simp [filteredVelocity, hcut q hq]
  have hd (q : Wavevector) : modeDot q (filteredVelocity χ (s.coefficients t) q) = 0 := by
    simp only [filteredVelocity, PancakePeriodicCoherentSplit.modeDot_smul, s.transverse t q, mul_zero]
  have h1 := deriv_correctedEnergy_le s hν hB R P hP χ hcut C hχ t ht
  have h2 := stretching_add_remainder_le _ (summable_fourierMoment P _ hs 4) hd
    ν (normalization R) hν (normalization_pos R)
  change stretching _ + signedRemainder (regularization ν R) (normalization R) _ / normalization R ≤ _ at h2
  unfold signedWorkRemainder
  linarith only [h1, h2]

end Mettapedia.FluidDynamics.NavierStokes.FilteredCoherentProjectionBudget
