import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalAdvectionEnstrophy

/-!
# The angular source in the actual regularized helicity-center evolution

The quotient-rule evolution splits into angular forcing, amplitude feedback,
and viscosity. Its sixth-power-weighted angular forcing is bounded without
an inverse regularization constant. The other two terms remain explicit;
the center is not treated as a passive scalar.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalHelicityCenterSourceBudget

open scoped RealInnerProductSpace
open MeasureTheory PeriodicFourierTriad PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeBlockReality PancakeGalerkinKineticEnergy
open LocalLowDiffusionBudget LocalJointDiffusionBudget LocalAlignmentForcing
open LocalVariableHelicityCenter LocalHelicitySourceEvolution
open LocalVorticityEighthMoment HelicityAngularBudget LocalMixedGradientBudget LocalAdvectionEnstrophy
open PancakeLocalInfiniteVelocity PancakeLocalSpatialVelocity PancakeFourierMaterialPaths
open PancakeLocalMaterialTrajectories

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def centerSource (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ⟪fullVorticity u x, source u x⟫ / (δ + ‖fullVorticity u x‖ ^ 2)

def centerStretchFeedback (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  -2 * regularizedCenter δ u x / (δ + ‖fullVorticity u x‖ ^ 2) *
    ⟪fullVorticity u x, fullStrainOperator u x (fullVorticity u x)⟫

def centerViscousRate (δ : ℝ) (u : FourierVelocity) (x : T3) : ℝ :=
  ((⟪fullVorticityLaplacian u x, fullVorticity (fourierCurl u) x⟫ +
      ⟪fullVorticity u x, fullVorticityLaplacian (fourierCurl u) x⟫) *
      (δ + ‖fullVorticity u x‖ ^ 2) -
    2 * ⟪fullVorticity u x, fullVorticity (fourierCurl u) x⟫ *
      ⟪fullVorticity u x, fullVorticityLaplacian u x⟫) /
      (δ + ‖fullVorticity u x‖ ^ 2) ^ 2

theorem centerRate_eq (δ ν : ℝ) (hδ : 0 < δ) (u : FourierVelocity) (x : T3) :
    centerRate δ ν u x = centerSource δ u x + centerStretchFeedback δ u x +
      ν * centerViscousRate δ u x := by
  have hden : δ + ‖fullVorticity u x‖ ^ 2 ≠ 0 := by positivity
  simp only [centerRate, helicityRate, centerSource, centerStretchFeedback,
    centerViscousRate, regularizedCenter, inner_add_right, real_inner_smul_right]
  field_simp
  ring

/-- The checked material derivative retains amplitude feedback and viscosity. -/
theorem hasDerivAt_center_decomposed {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 4 (s.coefficients τ) q ≤ g q)
    (X : ℝ → X3)
    (hX : ∀ τ ∈ Set.Ioo (0 : ℝ) T, HasDerivAt X (liftedVelocity s τ (X τ)) τ)
    (δ : ℝ) (hδ : 0 < δ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ regularizedCenter δ (s.coefficients τ) (torusPoint (X τ)))
      (centerSource δ (s.coefficients t) (torusPoint (X t)) +
        centerStretchFeedback δ (s.coefficients t) (torusPoint (X t)) +
        ν * centerViscousRate δ (s.coefficients t) (torusPoint (X t))) t := by
  simpa only [centerRate_eq δ ν hδ] using hasDerivAt_center_source s g hg hSum hu X hX δ hδ t ht

def weightedCenterSource (δ : ℝ) (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ‖fullVorticity u x‖ ^ 6 * |centerSource δ u x|

theorem weighted_centerSource_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity) (x : T3) :
    ‖fullVorticity u x‖ ^ 6 * |centerSource δ u x| ≤
      ‖fullVorticity u x‖ ^ 4 * |⟪fullVorticity u x, source u x⟫| := by
  have hd : 0 < δ + ‖fullVorticity u x‖ ^ 2 := by positivity
  rw [centerSource, abs_div, abs_of_pos hd, ← mul_div_assoc]
  apply (div_le_iff₀ hd).mpr
  nlinarith only [show 0 ≤ δ * ‖fullVorticity u x‖ ^ 4 *
    |⟪fullVorticity u x, source u x⟫| from by positivity]

theorem continuous_centerSource (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) : Continuous (centerSource δ u) :=
  (continuous_sourcePairing u hu hd hr).div
    (continuous_const.add ((continuous_fullVorticity u (summable_firstMoment_of_second u hu)).norm.pow 2))
    (fun _ ↦ by positivity)

theorem weightedCenterSource_le (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    weightedCenterSource δ u ≤ weightedSource u := by
  have hw := continuous_fullVorticity u (summable_firstMoment_of_second u hu)
  have hC : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 * |centerSource δ u x|) :=
    ((hw.norm.pow 6).mul (continuous_centerSource δ hδ u hu hd hr).abs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hS : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 4 * |⟪fullVorticity u x, source u x⟫|) :=
    ((hw.norm.pow 4).mul (continuous_sourcePairing u hu hd hr).abs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact integral_mono hC hS (weighted_centerSource_le δ hδ u)

/-- Uniform in the positive center regularization parameter. This pays only
the angular forcing term of the displayed material equation. -/
theorem weightedCenterSource_le_dissipation_advection (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (η : ℝ) (hη : 0 < η) :
    weightedCenterSource δ u ≤ η * weightedPalinstrophy u + sixthMoment u / η +
      4 * advectionSquareIntegral u / η ^ 3 :=
  (weightedCenterSource_le δ hδ u (summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu) hd hr).trans
    (weightedSource_le_dissipation_advection u hu hd hr η hη)

theorem weightedCenterSource_le_velocity_enstrophy (δ : ℝ) (hδ : 0 < δ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (η : ℝ) (hη : 0 < η) :
    weightedCenterSource δ u ≤ η * weightedPalinstrophy u + (1 + meanEnergy u) / η +
      4 * velocitySupNorm u ^ 2 * InfiniteConvectionEnergy.kineticEnergy (fourierCurl u) / η ^ 3 :=
  (weightedCenterSource_le δ hδ u (summable_fourierMoment_of_le _ (by omega : 2 ≤ 3) hu) hd hr).trans
    (weightedSource_le_velocity_enstrophy u hu hd hr η hη)

end Mettapedia.FluidDynamics.NavierStokes.LocalHelicityCenterSourceBudget
