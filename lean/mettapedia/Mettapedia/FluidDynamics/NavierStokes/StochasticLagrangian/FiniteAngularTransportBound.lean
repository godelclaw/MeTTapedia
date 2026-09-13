import Mettapedia.Analysis.AngularCurlTransportBound
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteAngularTransport

/-!
# Angular-only payment for the actual transport deformation

The gradient-entry coefficient remains explicit. The estimate consumes
only `G8 - R8`, after the radial cancellation, and supplies no initial-data
bound on that coefficient or on its accumulated product with dissipation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteAngularTransport

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalVorticityEighthMoment
open FourierFiniteSupport GaussianRootWeightedIncrement

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_deformationDensity (P : Finset Wavevector) (u v : FourierVelocity)
    (hv : ∀ q, q ∉ P → v q = 0) : Continuous (deformationDensity u v) := by
  unfold deformationDensity AngularCurlDecomposition.deformationWork AngularCurlDecomposition.deformationStress
  exact continuous_finsetSum Finset.univ (fun j _ ↦ continuous_finsetSum Finset.univ (fun k _ ↦
    (continuous_velocityDerivative u j k).mul
      ((AngularCurlDecomposition.continuous_jetGradient _ _
        (continuous_fullVorticity v (summable_fourierMoment P v hv 1))
        (LocalSquaredGapGradient.continuous_fullCurlGradient v) j).inner
          (LocalSquaredGapGradient.continuous_fullCurlGradient v k))))

theorem abs_deformationDensity_le (u v : FourierVelocity) (M : ℝ) (hM : 0 ≤ M)
    (x : T3) (hB : ∀ j k, |velocityDerivative u j k x| ≤ M) :
    |deformationDensity u v x| ≤
      36 * M * (weightedPalinstrophyDensity v x - radialGradientDensity v x) :=
  AngularCurlDecomposition.abs_deformationWork_le _ _ _ M hM hB

theorem abs_deformationIntegral_le (P : Finset Wavevector) (u v : FourierVelocity)
    (hv : ∀ q, q ∉ P → v q = 0) (M : ℝ) (hM : 0 ≤ M)
    (hB : ∀ x j k, |velocityDerivative u j k x| ≤ M) :
    |deformationIntegral u v| ≤ 36 * M * (weightedPalinstrophy v - radialDissipation v) := by
  have hiD : Integrable (fun x : T3 ↦ |deformationDensity u v x|) :=
    (continuous_deformationDensity P u v hv).abs.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiG : Integrable (weightedPalinstrophyDensity v) :=
    (continuous_weightedPalinstrophyDensity v (summable_fourierMoment P v hv 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiR : Integrable (radialGradientDensity v) :=
    (continuous_radialGradientDensity v (summable_fourierMoment P v hv 3)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x : T3, |deformationDensity u v x| := abs_integral_le_integral_abs
    _ ≤ ∫ x : T3, 36 * M * (weightedPalinstrophyDensity v x - radialGradientDensity v x) :=
      integral_mono hiD ((hiG.sub hiR).const_mul _) (fun x ↦ abs_deformationDensity_le u v M hM x (hB x))
    _ = _ := by rw [integral_const_mul, integral_sub hiG hiR]; rfl

end Mettapedia.FluidDynamics.NavierStokes.FiniteAngularTransport
