import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAngularCurlBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteBandProjectionEnergy

/-!
# Finite-band angular correction with a retained radial margin

The angular curl estimate combines with the existing quartic tensor
Bernstein estimate to give `K_ang + 16 R8 <= (8πR)^2 E8`. Subtracting
the angular cost therefore retains an explicit radial term in the
lower bound. This is coercivity, not a bound for its evolving source.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteBandAngularEnergy

open PeriodicFourierTriad PancakePeriodicVorticityEquation FourierFiniteSupport
open PancakeFrequencyProjectorCommutator
open LocalVorticityEighthMoment LocalAngularCurlBudget

theorem angularCurlEnergy_add_radial_le (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R) :
    angularCurlEnergy u + 16 * radialDissipation u ≤ (8 * Real.pi * R) ^ 2 * meanEnergy u := by
  have hu := summable_fourierMoment P u hs 3
  have hK := angularCurlEnergy_le u hu
  have hT := FiniteBandProjectionEnergy.tensorGradientEnergy_le P u hs R hP
  rw [FiniteBandProjectionEnergy.tensorGradientEnergy_eq u hu] at hT
  linarith only [hK, hT]

def correctedEnergy (κ : ℝ) (u : FourierVelocity) : ℝ :=
  meanEnergy u / 8 - 3 / κ * angularCurlEnergy u

/-- The radial margin is retained instead of discarded when proving positivity. -/
theorem correctedEnergy_ge_radial (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (κ : ℝ) (hκ : 0 < κ) (hscale : 48 * (8 * Real.pi * R) ^ 2 ≤ κ) :
    meanEnergy u / 16 + 48 / κ * radialDissipation u ≤ correctedEnergy κ u := by
  have hK := angularCurlEnergy_add_radial_le P u hs R hP
  have hp := mul_le_mul_of_nonneg_right hscale (meanEnergy_nonneg u)
  have h1 := mul_le_mul_of_nonneg_left hK (show 0 ≤ (48 : ℝ) by positivity)
  unfold correctedEnergy
  apply (le_of_mul_le_mul_right (a := κ) ?_ hκ)
  field_simp
  nlinarith only [hp, h1]

theorem correctedEnergy_le (κ : ℝ) (hκ : 0 < κ) (u : FourierVelocity) :
    correctedEnergy κ u ≤ meanEnergy u / 8 :=
  sub_le_self _ (mul_nonneg (by positivity) (angularCurlEnergy_nonneg u))

theorem correctedEnergy_bounds (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (κ : ℝ) (hκ : 0 < κ) (hscale : 48 * (8 * Real.pi * R) ^ 2 ≤ κ) :
    meanEnergy u / 16 ≤ correctedEnergy κ u ∧ correctedEnergy κ u ≤ meanEnergy u / 8 := by
  constructor
  · have h := correctedEnergy_ge_radial P u hs R hP κ hκ hscale
    have hp := mul_nonneg (show 0 ≤ 48 / κ by positivity) (radialDissipation_nonneg u)
    linarith only [h, hp]
  · exact correctedEnergy_le κ hκ u

/-- Filtering does not assert that the retained field solves closed unforced NS. -/
theorem correctedEnergy_filtered_bounds (P : Finset Wavevector) (u : FourierVelocity)
    (χ : Wavevector → ℂ) (hχ : ∀ q, q ∉ P → χ q = 0)
    (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (κ : ℝ) (hκ : 0 < κ) (hscale : 48 * (8 * Real.pi * R) ^ 2 ≤ κ) :
    meanEnergy (PancakeFilteredStrainDynamics.filteredVelocity χ u) / 16 ≤
      correctedEnergy κ (PancakeFilteredStrainDynamics.filteredVelocity χ u) ∧
    correctedEnergy κ (PancakeFilteredStrainDynamics.filteredVelocity χ u) ≤
      meanEnergy (PancakeFilteredStrainDynamics.filteredVelocity χ u) / 8 := by
  apply correctedEnergy_bounds P _ _ R hP κ hκ hscale
  intro q hq
  simp [PancakeFilteredStrainDynamics.filteredVelocity, hχ q hq]

end Mettapedia.FluidDynamics.NavierStokes.FiniteBandAngularEnergy
