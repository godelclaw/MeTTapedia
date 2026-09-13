import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteBandCurvatureCost
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteBandProjectionEnergy

/-!
# Simultaneous coercivity and viscous absorption of the projection correction

A single frequency normalization pays the full curvature cost and keeps
the corrected energy comparable to the eighth vorticity moment. Its
constant is selected from a proved universal estimate, not supplied as
an assumption. Nonlinear work and changes of cutoff are not bounded here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteBandProjectionAbsorption

open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFrequencyProjectorCommutator
open PancakeHaarTransportRate FourierFiniteSupport LocalVorticityEighthMoment
open LocalWeightedProjectionEvolution LocalProjectionCurvatureBudget

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def curvatureConstant : ℝ := FiniteBandCurvatureCost.exists_curvature_constant.choose

theorem curvatureConstant_pos : 0 < curvatureConstant :=
  FiniteBandCurvatureCost.exists_curvature_constant.choose_spec.1

theorem curvatureCost_le (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R) :
    curvatureCost u ≤ curvatureConstant * (2 * Real.pi * R) ^ 2 * weightedPalinstrophy u :=
  FiniteBandCurvatureCost.exists_curvature_constant.choose_spec.2 P u hs R hP

def normalization (R : ℝ) : ℝ :=
  48 * (8 * Real.pi * R) ^ 2 + 12 * curvatureConstant * (2 * Real.pi * R) ^ 2 + 1

theorem normalization_pos (R : ℝ) : 0 < normalization R := by
  have hc := curvatureConstant_pos
  unfold normalization
  positivity

theorem coercivity_scale_le (R : ℝ) : 48 * (8 * Real.pi * R) ^ 2 ≤ normalization R := by
  have h : 0 ≤ 12 * curvatureConstant * (2 * Real.pi * R) ^ 2 :=
    mul_nonneg (by linarith only [curvatureConstant_pos]) (sq_nonneg _)
  unfold normalization
  linarith only [h]

theorem absorption_scale_le (R : ℝ) : 12 * curvatureConstant * (2 * Real.pi * R) ^ 2 ≤ normalization R := by
  unfold normalization
  nlinarith only [sq_nonneg (8 * Real.pi * R)]

def regularization (ν R : ℝ) : ℝ := ν ^ 2 * normalization R ^ 2 / 3

theorem regularization_pos (ν R : ℝ) (hν : 0 < ν) : 0 < regularization ν R := by
  have hκ := normalization_pos R
  unfold regularization
  positivity

def correctedEnergy (ν R : ℝ) (u : FourierVelocity) : ℝ :=
  meanEnergy u / 8 - 3 / normalization R * weightedProjectionEnergy (regularization ν R) u

theorem correctedEnergy_bounds (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (ν : ℝ) (hν : 0 < ν) :
    meanEnergy u / 16 ≤ correctedEnergy ν R u ∧ correctedEnergy ν R u ≤ meanEnergy u / 8 := by
  have hδ := regularization_pos ν R hν
  have hκ := normalization_pos R
  constructor
  · exact FiniteBandProjectionEnergy.correctedEnergy_ge P u hs R hP _ hδ _ hκ (coercivity_scale_le R)
  · have hK : 0 ≤ weightedProjectionEnergy (regularization ν R) u :=
      integral_nonneg (weightedProjectionDensity_nonneg _ hδ.le u)
    exact sub_le_self _ (mul_nonneg (by positivity) hK)

/-- Absorption is valid for every normalization above the explicit threshold. -/
theorem curvature_payment_le (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (ν κ : ℝ) (hν : 0 ≤ ν) (hκ : 0 < κ)
    (hscale : 12 * curvatureConstant * (2 * Real.pi * R) ^ 2 ≤ κ) :
    (3 * ν / κ) * curvatureCost u ≤ ν / 4 * weightedPalinstrophy u := by
  have hcost := curvatureCost_le P u hs R hP
  have h1 := mul_le_mul_of_nonneg_right hscale (weightedPalinstrophy_nonneg u)
  have h2 : 12 * curvatureCost u ≤ κ * weightedPalinstrophy u := by nlinarith only [hcost, h1]
  have h3 := mul_le_mul_of_nonneg_left h2 hν
  apply (le_of_mul_le_mul_right (a := κ) ?_ hκ)
  field_simp
  nlinarith only [h3]

theorem integral_correctedViscousDensity_le (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (R : ℝ) (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R)
    (ν δ : ℝ) (hν : 0 ≤ ν) (hδ : 0 < δ) :
    (∫ x : T3, correctedViscousDensity ν δ (normalization R) u x) ≤
      -(3 * ν / 4) * weightedPalinstrophy u - 6 * ν * radialDissipation u := by
  have h := LocalProjectionCurvatureBudget.integral_correctedViscousDensity_le
    ν δ (normalization R) hν hδ (normalization_pos R) u (summable_fourierMoment P u hs 4)
  have hp := curvature_payment_le P u hs R hP ν (normalization R) hν
    (normalization_pos R) (absorption_scale_le R)
  linarith only [h, hp]

end Mettapedia.FluidDynamics.NavierStokes.FiniteBandProjectionAbsorption
