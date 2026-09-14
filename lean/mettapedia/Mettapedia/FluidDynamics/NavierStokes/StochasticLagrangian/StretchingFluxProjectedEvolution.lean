import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxMaterialRate

/-!
# Signed projected stretching-flux evolution

The material source and the projected transport pairing are joined in the
actual Eulerian time derivative. The deformation-remainder work retains its
sign; no smallness of the discarded projection component is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxProjectedEvolution

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis ContinuousFieldBilinear UnitTorusGradientProjection
open UnitTorusGradientTransport
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeHigherDerivativeMoments
open PancakeCurlOutputTail PancakeCoefficientLimitEquation PancakeGalerkinKineticEnergy
open PancakeDyadicDirectionEvolution PancakeInfiniteRealCurl PancakeLocalInfiniteVelocity
open PancakeFourierTranslationCurve PancakeHaarTransportRate LocalWeightedCurlCancellation
open LongitudinalVorticityTime FullLambVector LongitudinalGradientFlux
open LongitudinalProjectedTransport LocalStretchingFluxTime StretchingFluxMaterialRate

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def stretchingGradientField (u : FourierVelocity) (k : Fin 3) : C(T3, R3) :=
  ∑ j, (pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (velocitySecondDerivativeField u j k) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (LongitudinalVorticityTime.gradientField u k)) (velocityDerivativeField u j))

def fluxGradientField (u : FourierVelocity) (j k : Fin 3) : C(T3, R3) :=
  -(pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
    (componentField j (vorticityField u)) (stretchingGradientField u k) +
      pointwise (ContinuousLinearMap.lsmul ℝ ℝ)
        (componentField j (LongitudinalVorticityTime.gradientField u k)) (stretchingField u))

theorem hasDerivAt_stretchingField_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (k : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ stretchingField u (x + coordinateShift k t))
      (stretchingGradientField u k (x + coordinateShift k h)) h := by
  have hw := hasDerivAt_realFullField_shift (fourierCurl u)
    (summable_fourierMoment_curl 1 u hu) k x h
  have ha (j : Fin 3) := hasDerivAt_realFullField_shift (indexedDerivativeCoeff id j u)
    (summable_fourierMoment_derivative 1 u hu j) k x h
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦
    ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h hw).smul (ha j))
  convert! hh using 1

theorem hasDerivAt_fluxField_shift (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (j k : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ fluxField 0 u j (x + coordinateShift k t))
      (fluxGradientField u j k (x + coordinateShift k h)) h := by
  have hw := hasDerivAt_realFullField_shift (fourierCurl u)
    (summable_fourierMoment_curl 1 u hu) k x h
  have hh := (((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h hw).smul
    (hasDerivAt_stretchingField_shift u hu k x h)).neg
  simp only [fluxField_zero_eq]
  convert! hh using 1

theorem fluxTransportField_eq_sum_gradient (u : FourierVelocity) (j : Fin 3) (x : T3) :
    fluxTransportField u j x =
      ∑ k, realFullField u x k • fluxGradientField u j k x := by
  ext i
  simp only [fluxTransportField, fluxGradientField, stretchingTransportField,
    stretchingGradientField, velocityGradientTransportField, vorticityTransportField,
    pointwise, ContinuousMap.coe_mk, ContinuousLinearMap.lsmul_apply, componentField_apply,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, realField_apply,
    Fin.sum_univ_three, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem fluxTransportField_eq_transport (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) (j : Fin 3) :
    fluxTransportField u j = transport (velocityComponentJet u hu) (rawFluxJet u hu j) := by
  apply ContinuousMap.ext
  intro x
  rw [transport_rawFluxJet_apply u hu hr, fluxTransportField_eq_sum_gradient]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simpa only [realCoordinateDerivative, coordinateShift_zero, add_zero] using
    (hasDerivAt_fluxField_shift u hu j k x 0).deriv.symm

def materialWork (ν : ℝ) (u : FourierVelocity) : ℝ :=
  ⟪projectedFlux 0 u, toTensorL2 (fluxMaterialRateField ν u)⟫

def transportWork (u : FourierVelocity) : ℝ :=
  ⟪projectedFlux 0 u, toTensorL2 (fluxTransportField u)⟫

theorem eulerianWork_eq_material_sub_transport (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    LocalStretchingFluxTime.eulerianWork ν u = materialWork ν u - transportWork u := by
  have he : fluxRateField ν u = fluxMaterialRateField ν u - fluxTransportField u := by
    funext j
    exact eq_sub_iff_add_eq.mpr (flux_materialRate_eq ν u hu hd hr j)
  unfold LocalStretchingFluxTime.eulerianWork projectedRate
  rw [show projectedFlux 0 u = gradientProjection (toTensorL2 (fluxField 0 u)) from rfl,
    inner_gradientProjection_gradientProjection, he]
  change ⟪_, (tensorEmbedding (d := Fin 3) (E := R3)) (_ - _)⟫ = _
  rw [map_sub, inner_sub_right]
  rfl

theorem transportWork_eq_deformation (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    transportWork u =
      ⟪toTensorL2 (deformation (velocityComponentJet u hu) (projectedFluxJet u hu)),
        toTensorL2 (fluxField 0 u) - projectedFlux 0 u⟫ := by
  unfold transportWork
  simp only [funext (fluxTransportField_eq_transport u hu hr)]
  exact transport_work_eq_deformation u hu hr hd

theorem materialWork_eq_integral (ν : ℝ) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    materialWork ν u = ∫ x : T3, ∑ j,
      ⟪(projectedFluxJet u (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) j).value x,
        -(stretchingField u x j • stretchingField u x) +
          vorticityField u x j • pressureAction u x -
          (ν • LocalJointDiffusionBudget.fullVorticityLaplacian u x) j • stretchingField u x -
          vorticityField u x j • stretchingDiffusion ν u x⟫ := by
  unfold materialWork
  rw [← projectedFluxJet_eq u (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) hr,
    inner_toTensorL2]
  simp only [fluxMaterialRateField_apply ν u hu hd hr]

theorem transportWork_eq_integral (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = PancakeBlockReality.coefficientConjugate (u q)) :
    transportWork u = ∫ x : T3, ∑ j, ∑ k, velocityJet u j x k *
      ⟪(projectedFluxJet u hu k).value x, fluxField 0 u j x - (projectedFluxJet u hu j).value x⟫ := by
  unfold transportWork
  simp only [funext (fluxTransportField_eq_transport u hu hr)]
  exact transport_work_eq_integral u hu hr hd

variable {ν T B : ℝ} {u₀ : FourierVelocity}
  (s : LocalInfiniteVelocitySolution ν u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients τ) q ≤ g q)

include hg hSum hu

theorem hasDerivAt_projectedFluxSquare (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ projectedFluxSquare 0 (s.coefficients τ))
      (2 * (materialWork ν (s.coefficients t) - transportWork (s.coefficients t))) t := by
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  rw [← eulerianWork_eq_material_sub_transport ν _ hm (s.transverse t) (s.reality t)]
  exact LocalStretchingFluxTime.hasDerivAt_projectedFluxSquare s g hg hSum hu t ht

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxProjectedEvolution
