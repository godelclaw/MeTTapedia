import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianSquaredRootLocalization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicTranslationEnergy

/-!
# Translation energy of the actual squared Gaussian roots

The energy is constructed from actual almost-everywhere derivatives.
The finite patch sum introduces no additional patch-count factor. The
gate derivative and the original Gaussian patch energy remain explicit;
this is not a time-uniform or threshold-uniform bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootTranslation

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeHigherDerivativeMoments
open PancakeCurlOutputTail PancakeFilteredStrainDynamics
open PancakeFourierMaterialPaths PancakeFourierTranslationCurve PancakeHaarTransportRate
open GaussianRootVorticity GaussianRootPartition GaussianSquaredRootLocalization
open LocalGaussianPressurePartition LocalLowDiffusionBudget SpectralGapTiltWeight
open PancakeSpectralProjectorRegularity.SymmetricStrain

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def squaredRootGradientSquare (gamma : ℝ) (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (x : T3) : ℝ :=
  ∑ i : ↑centers, PeriodicFourierGradientEnergy.gradientSquare
    (fun y ↦ rootPatch gamma chi modes u centers tau i y ^ 2) x

theorem squaredRootGradientSquare_nonneg (gamma : ℝ) (chi : Wavevector → ℂ)
    (modes : Finset Wavevector) (u : FourierVelocity) (centers : Finset T3) (tau : ℝ) (x : T3) :
    0 ≤ squaredRootGradientSquare gamma chi modes u centers tau x := by
  exact Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ sq_nonneg _))

theorem integrable_squaredRootGradientSquare (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) :
    Integrable (squaredRootGradientSquare gamma chi modes u centers tau) := by
  apply integrable_finsetSum
  intro i _
  exact PeriodicFourierGradientEnergy.integrable_gradientSquare _
    ((continuous_rootPatch gamma hg chi modes u
      (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau i).pow 2)
    (locallyLipschitz_rootPatch_sq gamma hg chi modes u hu centers hc tau i)

theorem continuous_squaredPatchDifference_translate (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (a : T3) :
    Continuous (fun x ↦ squaredPatchDifference gamma chi modes u centers tau x (x - a)) := by
  have hp := continuous_rootPatch gamma hg chi modes u hu centers hc tau
  unfold squaredPatchDifference
  fun_prop

theorem integral_squaredPatchDifference_translate_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty)
    (tau : ℝ) (a : T3) :
    (∫ x : T3, squaredPatchDifference gamma chi modes u centers tau x (x - a)) ≤
      3 * ‖a‖ ^ 2 * ∫ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x := by
  have hp := continuous_rootPatch gamma hg chi modes u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) centers hc tau
  have hL := locallyLipschitz_rootPatch_sq gamma hg chi modes u hu centers hc tau
  have h := PeriodicTranslationEnergy.sum_integral_sub_translate_sq_le
    (fun i y ↦ rootPatch gamma chi modes u centers tau i y ^ 2)
    (fun i ↦ (hp i).pow 2) hL a
  simp only [squaredPatchDifference, squaredRootGradientSquare]
  rw [integral_finsetSum] -- the integrands are continuous
  · rw [integral_finsetSum]
    · exact h
    · intro i _
      exact PeriodicFourierGradientEnergy.integrable_gradientSquare _ ((hp i).pow 2) (hL i)
  · intro i _
    exact (((hp i).pow 2).sub (((hp i).comp (continuous_id.sub continuous_const)).pow 2)).pow 2
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem ae_squaredRootGradientSquare_le (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (centers : Finset T3) (hc : centers.Nonempty) (tau : ℝ) :
    let g := fun x ↦ gapCutoff gamma (topGap (spatialStrain modes (filteredVelocity chi u) x))
    ∀ᵐ x : T3, squaredRootGradientSquare gamma chi modes u centers tau x ≤
      2 * PeriodicFourierGradientEnergy.gradientSquare g x *
        (∑ i : ↑centers, patch gamma chi modes u centers tau i x ^ 2) +
      2 * g x ^ 2 * patchGradientSquare gamma chi modes u centers tau x := by
  dsimp only
  have hd := ae_all_iff.mpr
    (ae_coordinate_rootPatch_sq_derivative_bound gamma hg chi modes u hu centers hc tau)
  filter_upwards [hd] with x hx
  have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) ↦ hx j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at h
  simp only [squaredRootGradientSquare, PeriodicFourierGradientEnergy.gradientSquare,
    shiftRate, patchGradientSquare]
  rw [Finset.sum_comm]
  exact h

end Mettapedia.FluidDynamics.NavierStokes.GaussianSquaredRootTranslation
