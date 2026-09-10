import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFourierTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalLowDiffusionBudget

/-!
# Full-vorticity alignment energy and its incompressible transport

Only the strain is filtered. The transported vorticity and the advecting
velocity are the full fields. Local Lipschitz regularity, rather than a
spectral-gap assumption, supplies weak derivatives and zero mean transport.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentTransport

open scoped RealInnerProductSpace Matrix.Norms.Elementwise
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeCurlOutputTail
open PancakeGalerkinKineticEnergy PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeDyadicDirectionEvolution
open PancakeRegularizedDiffusion PancakeLocallyLipschitzEnergy PancakeSpectralFiniteDifference
open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpacetimeSpectralDifferentiability PancakeMeasurableMaterialRate
open PancakeTopEigenvalueDerivative
open LocalVorticityDiffusion LocalLowDiffusionBudget PancakeWeakIncompressibleTransport

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Lipschitz inputs suffice; neither input needs a continuous derivative. -/
theorem locallyLipschitz_regularizedEnergy_of_locallyLipschitz
    {E : Type*} [PseudoMetricSpace E] (S : E → SymmetricStrain) (w : E → R3) (delta : ℝ)
    (hS : LocallyLipschitz (fun x ↦ (S x).1)) (hw : LocallyLipschitz w) :
    LocallyLipschitz (fun x ↦ regularizedEnergy (S x) delta (w x)) := by
  have hSL : LocallyLipschitz S := fun x ↦ hS x
  have hn : ContDiff ℝ 1 (fun v : R3 ↦ ‖v‖ ^ 2) := by
    simp only [← real_inner_self_eq_norm_sq]
    exact contDiff_id.inner ℝ contDiff_id
  have hq : ContDiff ℝ 1 (fun z : (R3 →L[ℝ] R3) × R3 ↦ ⟪z.2, z.1 z.2⟫) := by
    exact contDiff_snd.inner ℝ (contDiff_fst.clm_apply contDiff_snd)
  have hL := (lipschitzWith_topEigenvalue.locallyLipschitz.comp hSL).add
    (LocallyLipschitz.const delta)
  have h := (locallyLipschitz_mul_real _ _ hL (hn.locallyLipschitz.comp hw)).sub
    (hq.locallyLipschitz.comp (hS.prodMk hw))
  simpa only [Function.comp_def, regularizedEnergy, regularizedGap, sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] using h

theorem locallyLipschitz_fullVorticity (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) :
    LocallyLipschitz (fun r : X3 ↦ fullVorticity u (torusPoint r)) := by
  have hc : Summable (fourierMoment 1 (fourierCurl u)) :=
    (hu.mul_left (2 * Real.pi)).of_nonneg_of_le (fourierMoment_nonneg _ _)
      (fourierMoment_curl_le 1 u)
  simp only [fullVorticity, spatialCurl_velocity u (summable_firstMoment_of_second u hu)]
  exact complexRealPartEuclideanCLM.lipschitz.locallyLipschitz.comp
    (InfiniteFourierTransport.lipschitzWith_fullFourierField_lift _ hc).locallyLipschitz

def alignmentEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (delta : ℝ) (x : T3) : ℝ :=
  regularizedEnergy (spatialStrain modes (filteredVelocity chi u) x) delta (fullVorticity u x)

theorem continuous_alignmentEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) (delta : ℝ) :
    Continuous (alignmentEnergy chi modes u delta) :=
  PancakeHaarDiffusionIncrement.continuous_regularizedEnergy _ _ delta
    (PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u))
    (continuous_fullVorticity u hu)

theorem locallyLipschitz_alignmentEnergy (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) (delta : ℝ) :
    LocallyLipschitz (fun r : X3 ↦ alignmentEnergy chi modes u delta (torusPoint r)) := by
  have hS := (contDiff_real_strain chi modes (fun _ : ℝ ↦ u)
    (fun _ _ _ ↦ contDiff_const)).comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ 1 (fun r : X3 ↦ ((0 : ℝ), r)))
  exact locallyLipschitz_regularizedEnergy_of_locallyLipschitz _ _ delta
    hS.locallyLipschitz (locallyLipschitz_fullVorticity u hu)

theorem integral_alignmentEnergy_transport_zero
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0) (delta : ℝ) :
    Integrable (coordinateTransport (alignmentEnergy chi modes u delta)
      (InfiniteFourierTransport.velocityComponent u)) ∧
    (∫ x : T3, coordinateTransport (alignmentEnergy chi modes u delta)
      (InfiniteFourierTransport.velocityComponent u) x) = 0 :=
  InfiniteFourierTransport.integral_coordinateTransport_zero u hu hd _
    (continuous_alignmentEnergy chi modes u (summable_firstMoment_of_second u hu) delta)
    (locallyLipschitz_alignmentEnergy chi modes u hu delta)

end Mettapedia.FluidDynamics.NavierStokes.LocalAlignmentTransport
