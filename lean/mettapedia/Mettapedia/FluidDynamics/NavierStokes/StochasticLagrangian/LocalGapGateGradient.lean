import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianSquaredRootTranslation

/-!
# Actual spatial cost of the spectral-gap gate

The clipped gap is locally Lipschitz through collisions. Its actual
coordinate derivatives exist almost everywhere and have squared sum at
most `36 / gamma²` times the filtered strain-gradient energy density.
This retains the inverse-threshold cost instead of assuming it harmless.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalGapGateGradient

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFilteredStrainDynamics
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open SpectralGapTiltWeight GapTruncatedProjector GaussianRootVorticity
open LocalSpatialSpectralRelation PancakeFourierStrainGradient
open PancakeFourierTranslationCurve PancakeHaarTransportRate PancakeFourierMaterialPaths

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "X3" => Fin 3 → ℝ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def gate (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  gapCutoff gamma (topGap (spatialStrain modes (filteredVelocity chi u) x))

theorem locallyLipschitz_gate (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) :
    LocallyLipschitz (fun r : X3 ↦ gate gamma chi modes u (torusPoint r)) := by
  have hS : LocallyLipschitz
      (fun r : X3 ↦ spatialStrain modes (filteredVelocity chi u) (torusPoint r)) :=
    fun r ↦ (LocalSpatialBottomProjector.contDiff_spatialStrain (n := 1) chi modes u).locallyLipschitz r
  exact (((locallyLipschitz_gapCutoff gamma hg).comp locallyLipschitz_topGap).comp hS)

theorem continuous_gate (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) :
    Continuous (gate gamma chi modes u) :=
  ((locallyLipschitz_gapCutoff gamma hg).comp locallyLipschitz_topGap).continuous.comp
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))

theorem ae_coordinate_differentiable_gate (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (j : Fin 3) :
    ∀ᵐ x : T3, DifferentiableAt ℝ (fun h ↦ gate gamma chi modes u (x + coordinateShift j h)) 0 :=
  PancakePeriodicWeakDerivative.ae_coordinate_differentiable _ j
    (continuous_gate gamma hg chi modes u) (locallyLipschitz_gate gamma hg chi modes u)

theorem norm_deriv_gate_le (gamma : ℝ) (hg : 0 < gamma)
    (S : ℝ → SymmetricStrain) (t : ℝ) (V : R3 →L[ℝ] R3)
    (hS : HasDerivAt (fun s ↦ (S s).1) V t) :
    ‖deriv (fun s ↦ gapCutoff gamma (topGap (S s))) t‖ ≤ (6 / gamma) * ‖V‖ := by
  by_cases hd : DifferentiableAt ℝ (fun s ↦ gapCutoff gamma (topGap (S s))) t
  · apply le_of_tendsto_of_tendsto' hd.hasDerivAt.tendsto_slope.norm
      (hS.tendsto_slope.norm.const_mul (6 / gamma))
    intro s
    have hgap := (abs_gapCutoff_sub_le gamma hg (topGap (S s)) (topGap (S t))).trans
      (div_le_div_of_nonneg_right (abs_topGap_sub_le (S s) (S t)) hg.le)
    have h := mul_le_mul_of_nonneg_left hgap (norm_nonneg ((s - t)⁻¹))
    simp only [slope_def_module, norm_smul, Real.norm_eq_abs]
    simpa only [Real.norm_eq_abs, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  · rw [deriv_zero_of_not_differentiableAt hd, norm_zero]
    positivity

theorem norm_coordinate_gate_deriv_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (j : Fin 3) (x : T3) :
    ‖deriv (fun h ↦ gate gamma chi modes u (x + coordinateShift j h)) 0‖ ≤
      (6 / gamma) * ‖strainGradient modes (filteredVelocity chi u) x j‖ := by
  simpa only [gate, strainCurve, coordinateShift_zero, add_zero] using
    norm_deriv_gate_le gamma hg (strainCurve chi modes u j x) 0 _
      (hasDerivAt_strainCurve chi modes u j x 0)

theorem gradientSquare_gate_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    PeriodicFourierGradientEnergy.gradientSquare (gate gamma chi modes u) x ≤
      (36 / gamma ^ 2) * ∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2 := by
  unfold PeriodicFourierGradientEnergy.gradientSquare shiftRate
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_coordinate_gate_deriv_le gamma hg chi modes u j x) 2
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow, div_pow, show (6 : ℝ) ^ 2 = 36 by norm_num] using h

end Mettapedia.FluidDynamics.NavierStokes.LocalGapGateGradient
