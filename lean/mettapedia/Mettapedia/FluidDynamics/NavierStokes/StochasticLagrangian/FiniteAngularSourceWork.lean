import Mettapedia.Analysis.AngularCurlSpatialVariation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FilteredAngularViscousBalance

/-!
# Explicit signed angular source work for actual Fourier fields

All value and derivative jets are reconstructed from one finite velocity.
Integration by parts transfers the derivative off the varied vorticity.
The resulting polynomial gradient is evaluated on the retained field,
while an incoming restricted source still contains every original input
frequency contributing to that output. No source budget is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteAngularSourceWork

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeHaarTransportRate
open PancakeFourierTranslationCurve LocalLowDiffusionBudget LocalSpatialVorticityJets
open LocalVorticityEighthMoment FourierFiniteSupport FiniteVorticityMixedJets
open FiniteAngularCurlVariation FilteredAngularMean FiniteVorticityVariation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def angularGradient (u : FourierVelocity) (x : T3) : R3 :=
  AngularCurlDecomposition.variationalGradient (fullVorticity u x)
    (fun j ↦ fullCurlGradient u j x) (fun j k ↦ mixed u k j x)

theorem continuous_angularGradient (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) : Continuous (angularGradient u) :=
  AngularCurlDecomposition.continuous_variationalGradient _ _ _
    (continuous_fullVorticity u (summable_fourierMoment P u hs 1))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u) (fun _ _ ↦ continuous_mappedField _)

theorem integral_densityRate_eq (P Q : Finset Wavevector) (u v : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (hv : ∀ q, q ∉ Q → v q = 0) :
    (∫ x : T3, FiniteAngularCurlVariation.densityRate u v x) =
      ∫ x : T3, ⟪angularGradient u x, fullVorticity v x⟫ :=
  AngularCurlDecomposition.integral_angularCurlDensityRate_eq
    (fullVorticity u) (fullVorticity v) (fullCurlGradient u) (fullCurlGradient v)
    (fun j k ↦ mixed u k j) coordinateShift
    (continuous_fullVorticity u (summable_fourierMoment P u hs 1))
    (continuous_fullVorticity v (summable_fourierMoment Q v hv 1))
    (LocalSquaredGapGradient.continuous_fullCurlGradient u)
    (LocalSquaredGapGradient.continuous_fullCurlGradient v) (fun _ _ ↦ continuous_mappedField _)
    continuous_coordinateShift coordinateShift_zero
    (hasDerivAt_fullVorticity_shift u (summable_fourierMoment P u hs 3))
    (hasDerivAt_fullVorticity_shift v (summable_fourierMoment Q v hv 3))
    (fun j k ↦ hasDerivAt_gradient_shift P u hs k j)

def correctedGradient (κ : ℝ) (u : FourierVelocity) (x : T3) : R3 :=
  ‖fullVorticity u x‖ ^ 6 • fullVorticity u x - (3 / κ) • angularGradient u x

theorem continuous_correctedGradient (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) : Continuous (correctedGradient κ u) := by
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  exact ((ha.norm.pow 6).smul ha).sub ((continuous_angularGradient P u hs).const_smul _)

theorem integral_correctedDensityRate_eq (κ : ℝ) (P Q : Finset Wavevector) (u v : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (hv : ∀ q, q ∉ Q → v q = 0) :
    (∫ x : T3, FiniteAngularCurlVariation.correctedDensityRate κ u v x) =
      ∫ x : T3, ⟪correctedGradient κ u x, fullVorticity v x⟫ := by
  have ha := continuous_fullVorticity u (summable_fourierMoment P u hs 1)
  have hb := continuous_fullVorticity v (summable_fourierMoment Q v hv 1)
  have hA : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 6 * ⟪fullVorticity u x, fullVorticity v x⟫) :=
    ((ha.norm.pow 6).mul (ha.inner hb)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (FiniteAngularCurlVariation.densityRate u v) :=
    (AngularCurlDecomposition.continuous_angularCurlDensityRate _ _ _ _ ha hb
      (LocalSquaredGapGradient.continuous_fullCurlGradient u)
      (LocalSquaredGapGradient.continuous_fullCurlGradient v)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hF : Integrable (fun x : T3 ↦ ⟪angularGradient u x, fullVorticity v x⟫) :=
    ((continuous_angularGradient P u hs).inner hb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [FiniteAngularCurlVariation.correctedDensityRate, correctedGradient, inner_sub_left, real_inner_smul_left]
  rw [integral_sub hA (hK.const_mul _), integral_sub hA (hF.const_mul _), integral_const_mul,
    integral_const_mul, integral_densityRate_eq P Q u v hs hv]

/-- A common resolved variational gradient pairs with either the resolved
RHS or the subgrid source; no derivative of that vorticity source remains. -/
theorem work_eq_pairing (κ : ℝ) (P : Finset Wavevector) (u v : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    FilteredAngularViscousBalance.work κ P u v =
      ∫ x : T3, ⟪correctedGradient κ u x, fullVorticity (restrictVelocity P v) x⟫ :=
  integral_correctedDensityRate_eq κ P P u _ hs (restrictVelocity_eq_zero P v)

/-- The spatial variational gradient has the same degree-eight amplitude
response as the original density, including the integration-by-parts sign. -/
theorem integral_angularGradient_self (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    (∫ x : T3, ⟪angularGradient u x, fullVorticity u x⟫) =
      8 * LocalAngularCurlBudget.angularCurlEnergy u := by
  rw [← integral_densityRate_eq P P u u hs hs]
  have he (x : T3) : FiniteAngularCurlVariation.densityRate u u x =
      8 * LocalAngularCurlBudget.angularCurlDensity u x := by
    simpa only [one_smul, mul_one, FiniteAngularCurlVariation.densityRate,
      LocalAngularCurlBudget.angularCurlDensity, LocalAngularCurlBudget.angularCurl,
      AngularCurlDecomposition.angularCurlDensity] using
      AngularCurlDecomposition.angularCurlDensityRate_proportional
        (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) 1
  simp_rw [he]
  exact integral_const_mul _ _

theorem integral_correctedGradient_self (κ : ℝ) (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) :
    (∫ x : T3, ⟪correctedGradient κ u x, fullVorticity u x⟫) =
      8 * FiniteBandAngularEnergy.correctedEnergy κ u := by
  rw [← integral_correctedDensityRate_eq κ P P u u hs hs]
  have he (x : T3) : FiniteAngularCurlVariation.correctedDensityRate κ u u x =
      8 * FiniteAngularCurlVariation.correctedDensity κ u x := by
    have h := AngularCurlDecomposition.angularCurlDensityRate_proportional
      (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) 1
    simp only [one_smul, mul_one] at h
    simp only [FiniteAngularCurlVariation.correctedDensityRate, FiniteAngularCurlVariation.densityRate, h,
      FiniteAngularCurlVariation.correctedDensity, LocalVorticityEighthMoment.energy,
      real_inner_self_eq_norm_sq, LocalAngularCurlBudget.angularCurlDensity,
      AngularCurlDecomposition.angularCurlDensity]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_correctedDensity_eq κ P u hs]

end Mettapedia.FluidDynamics.NavierStokes.FiniteAngularSourceWork
