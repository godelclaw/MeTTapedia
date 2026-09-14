import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicProjectedTensorJet
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LongitudinalInviscidFluxFourier

/-!
# The actual longitudinal flux transport as an off-diagonal work term

The raw tensor, its projected continuous representative, their spatial
jets, and the incompressible transport velocity are all constructed from
one infinite Fourier velocity. The resulting signed identity puts the
derivative on the velocity and retains the orthogonal flux residual.
There is no assumed projector regularity or commutation with transport.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LongitudinalProjectedTransport

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection UnitTorusGradientTransport
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeHigherDerivativeMoments
open PancakeCurlOutputTail PancakeInfiniteSpatialCurl PancakeBlockReality
open PancakeFourierTranslationCurve PancakeDyadicDirectionEvolution
open PancakePeriodicVorticityEquation LocalSpatialVorticityJets LocalWeightedCurlCancellation
open PancakeGalerkinKineticEnergy
open PeriodicGradientFluxTriple PeriodicProjectedTensorJet LongitudinalInviscidFluxFourier
open LongitudinalGradientFlux FullLambVector
open PancakeInfiniteRealCurl PancakeLocalInfiniteVelocity PancakeHigherLocalVelocity
open PancakeArbitraryDataBlocks PancakeContinuousCoordinateJet

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem derivative_tripleCoeff (a b c : FourierVelocity) (i j k : Fin 3) :
    indexedDerivativeCoeff tripleFrequency k (tripleCoeff a b c i j) =
      fun p ↦ tripleCoeff (indexedDerivativeCoeff id k a) b c i j p +
        tripleCoeff a (indexedDerivativeCoeff id k b) c i j p +
          tripleCoeff a b (indexedDerivativeCoeff id k c) i j p := by
  funext p l
  simp only [indexedDerivativeCoeff, tripleFrequency, tripleCoeff, indexedProductCoeff,
    Pi.smul_apply, smul_eq_mul, Pi.add_apply, Int.cast_add, id_eq]
  ring

theorem summable_norm_derivative_tripleCoeff (a b c : FourierVelocity)
    (ha : Summable (indexedFirstMoment id a)) (hb : Summable (indexedFirstMoment id b))
    (hc : Summable (indexedFirstMoment id c)) (i j k : Fin 3) :
    Summable (fun p ↦ ‖indexedDerivativeCoeff tripleFrequency k (tripleCoeff a b c i j) p‖) := by
  have ha0 := summable_norm_coefficients id a ha
  have hb0 := summable_norm_coefficients id b hb
  have hc0 := summable_norm_coefficients id c hc
  have h1 := summable_norm_tripleCoeff _ b c (summable_norm_derivativeCoefficients id a ha k) hb0 hc0 i j
  have h2 := summable_norm_tripleCoeff a _ c ha0 (summable_norm_derivativeCoefficients id b hb k) hc0 i j
  have h3 := summable_norm_tripleCoeff a b _ ha0 hb0 (summable_norm_derivativeCoefficients id c hc k) i j
  rw [derivative_tripleCoeff]
  exact ((h1.add h2).add h3).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun p ↦
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))

def negSumJet {ι : Type*} [Fintype ι] (f : ι → TranslationJet (Fin 3) R3) :
    TranslationJet (Fin 3) R3 where
  value := -∑ i, (f i).value
  gradient k := -∑ i, (f i).gradient k
  hasDerivAt k x h := by
    have hd := (HasDerivAt.sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦
      (f i).hasDerivAt k x h)).neg
    convert! hd using 1
    · funext t
      simp only [ContinuousMap.neg_apply, ContinuousMap.sum_apply, Pi.neg_apply, Finset.sum_apply]
    · simp only [ContinuousMap.neg_apply, ContinuousMap.sum_apply]

variable (u : FourierVelocity) (hu : Summable (fourierMoment 2 u))

include hu

theorem summable_curl_firstMoment : Summable (indexedFirstMoment id (fourierCurl u)) := by
  simpa only [indexedFirstMoment_id] using summable_fourierMoment_curl 1 u hu

theorem summable_derivative_firstMoment (r : Fin 3) :
    Summable (indexedFirstMoment id (indexedDerivativeCoeff id r u)) := by
  simpa only [indexedFirstMoment_id] using summable_fourierMoment_derivative 1 u hu r

def rawCoefficient (r j : Fin 3) : TripleIndex → VelocityCoefficient :=
  tripleCoeff (fourierCurl u) (fourierCurl u) (indexedDerivativeCoeff id r u) r j

theorem summable_rawCoefficient (r j : Fin 3) : Summable (fun p ↦ ‖rawCoefficient u r j p‖) :=
  summable_norm_tripleCoeff _ _ _
    (summable_norm_coefficients id _ (summable_curl_firstMoment u hu))
    (summable_norm_coefficients id _ (summable_curl_firstMoment u hu))
    (summable_norm_coefficients id _ (summable_derivative_firstMoment u hu r)) r j

theorem summable_derivative_rawCoefficient (r j k : Fin 3) :
    Summable (fun p ↦ ‖indexedDerivativeCoeff tripleFrequency k (rawCoefficient u r j) p‖) :=
  summable_norm_derivative_tripleCoeff _ _ _ (summable_curl_firstMoment u hu)
    (summable_curl_firstMoment u hu) (summable_derivative_firstMoment u hu r) r j k

def rawFluxJet (j : Fin 3) : TranslationJet (Fin 3) R3 :=
  negSumJet (fun r ↦ fieldJet tripleFrequency (rawCoefficient u r j)
    (summable_rawCoefficient u hu r j) (summable_derivative_rawCoefficient u hu r j))

def projectedFluxJet (j : Fin 3) : TranslationJet (Fin 3) R3 :=
  negSumJet (fun r ↦ projectedJet tripleFrequency (rawCoefficient u r)
    (summable_rawCoefficient u hu r) (summable_derivative_rawCoefficient u hu r) j)

theorem rawFluxJet_value (hr : ∀ n, u (-n) = coefficientConjugate (u n)) (j : Fin 3) :
    (rawFluxJet u hu j).value = fluxField 0 u j := by
  change -(∑ r, indexedRealField tripleFrequency (rawCoefficient u r j)) = _
  rw [inviscid_fluxField_eq]
  simp only [Pi.neg_apply, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  have hw := summable_norm_coefficients id _ (summable_curl_firstMoment u hu)
  exact (tripleField_eq_tripleFourierField _ _ _ hw hw
    (summable_norm_coefficients id _ (summable_derivative_firstMoment u hu r))
    (fourierCurl_real u hr) (fourierCurl_real u hr) r j).symm

theorem projectedFluxJet_curl (j k : Fin 3) :
    (projectedFluxJet u hu k).gradient j = (projectedFluxJet u hu j).gradient k := by
  simp only [projectedFluxJet, negSumJet, projectedJet_curl]

theorem projection_rawFluxJet :
    gradientProjection (toTensorL2 (fun j ↦ (rawFluxJet u hu j).value)) =
      toTensorL2 (fun j ↦ (projectedFluxJet u hu j).value) := by
  have hraw : (fun j ↦ (rawFluxJet u hu j).value) =
      -∑ r, fun j ↦ indexedRealField tripleFrequency (rawCoefficient u r j) := by
    funext j
    simp only [rawFluxJet, negSumJet, fieldJet, Pi.neg_apply, Finset.sum_apply]
  have hproj : (fun j ↦ (projectedFluxJet u hu j).value) =
      -∑ r, fun j ↦ indexedRealField tripleFrequency (projectedFamily tripleFrequency (rawCoefficient u r) j) := by
    funext j
    simp only [projectedFluxJet, negSumJet, projectedJet, fieldJet, Pi.neg_apply, Finset.sum_apply]
  rw [hraw, hproj]
  change ((gradientProjectionCLM (d := Fin 3) (E := R3)).comp
    (tensorEmbedding (d := Fin 3) (E := R3))) (-∑ r, _) =
      (tensorEmbedding (d := Fin 3) (E := R3)) (-∑ r, _)
  rw [map_neg, map_sum, map_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact gradientProjection_eq_field tripleFrequency _ (summable_rawCoefficient u hu r)

theorem projectedFluxJet_eq (hr : ∀ n, u (-n) = coefficientConjugate (u n)) :
    toTensorL2 (fun j ↦ (projectedFluxJet u hu j).value) = projectedFlux 0 u := by
  rw [← projection_rawFluxJet u hu]
  simp only [rawFluxJet_value u hu hr, projectedFlux]

def velocityComponentJet (j : Fin 3) : TranslationJet (Fin 3) ℝ where
  value := ⟨fun x ↦ PancakeInfiniteRealCurl.realFullField u x j,
    (EuclideanSpace.proj j).continuous.comp (continuous_realFullField u)⟩
  gradient k := ⟨fun x ↦ velocityJet u k x j,
    (EuclideanSpace.proj j).continuous.comp (continuous_velocityJet u k)⟩
  hasDerivAt k x h :=
    (EuclideanSpace.proj j : R3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt h
      (hasDerivAt_realFullField_shift u (summable_fourierMoment_of_le u (by omega : 1 ≤ 2) hu) k x h)

theorem velocityComponentJet_divergence (hd : ∀ q, modeDot q (u q) = 0) (x : T3) :
    (∑ k, (velocityComponentJet u hu k).gradient k x) = 0 :=
  sum_velocityJet_diagonal u hu hd x

/-- The actual projected inviscid flux work, with no derivative on the
flux in the final deformation-residual pairing. -/
theorem transport_work_eq_deformation
    (hr : ∀ n, u (-n) = coefficientConjugate (u n))
    (hd : ∀ q, modeDot q (u q) = 0) :
    ⟪projectedFlux 0 u,
      toTensorL2 (fun j ↦ transport (velocityComponentJet u hu) (rawFluxJet u hu j))⟫ =
      ⟪toTensorL2 (deformation (velocityComponentJet u hu) (projectedFluxJet u hu)),
        toTensorL2 (fluxField 0 u) - projectedFlux 0 u⟫ := by
  have h := inner_projected_transport_eq_deformation (velocityComponentJet u hu)
    (projectedFluxJet u hu) (rawFluxJet u hu) (velocityComponentJet_divergence u hu hd)
    (projectedFluxJet_curl u hu) (projection_rawFluxJet u hu)
  simpa only [projectedFluxJet_eq u hu hr, rawFluxJet_value u hu hr] using h

theorem rawFluxJet_gradient
    (hr : ∀ n, u (-n) = coefficientConjugate (u n)) (j k : Fin 3) (x : T3) :
    (rawFluxJet u hu j).gradient k x = realCoordinateDerivative (fluxField 0 u j) k x := by
  have h := (rawFluxJet u hu j).hasDerivAt k x 0
  rw [rawFluxJet_value u hu hr] at h
  have hs : UnitTorusWeakDerivative.coordinateShift k = coordinateShift k := by
    funext t
    rfl
  simpa only [realCoordinateDerivative, hs, PancakeHaarTransportRate.coordinateShift_zero,
    add_zero] using h.deriv.symm

theorem transport_rawFluxJet_apply
    (hr : ∀ n, u (-n) = coefficientConjugate (u n)) (j : Fin 3) (x : T3) :
    transport (velocityComponentJet u hu) (rawFluxJet u hu j) x =
      ∑ k, realFullField u x k • realCoordinateDerivative (fluxField 0 u j) k x := by
  simp only [transport, ContinuousMap.sum_apply, ContinuousMap.smul_apply',
    velocityComponentJet, ContinuousMap.coe_mk, rawFluxJet_gradient u hu hr]

/-- The spatial integral retains the off-diagonal coupling with its sign. -/
theorem transport_work_eq_integral
    (hr : ∀ n, u (-n) = coefficientConjugate (u n))
    (hd : ∀ q, modeDot q (u q) = 0) :
    ⟪projectedFlux 0 u,
      toTensorL2 (fun j ↦ transport (velocityComponentJet u hu) (rawFluxJet u hu j))⟫ =
      ∫ x : T3, ∑ j, ∑ k, velocityJet u j x k *
        ⟪(projectedFluxJet u hu k).value x, fluxField 0 u j x - (projectedFluxJet u hu j).value x⟫ := by
  rw [transport_work_eq_deformation u hu hr hd, ← projectedFluxJet_eq u hu hr]
  have he : toTensorL2 (fluxField 0 u) -
      toTensorL2 (fun j ↦ (projectedFluxJet u hu j).value) =
      toTensorL2 (fun j ↦ fluxField 0 u j - (projectedFluxJet u hu j).value) :=
    ((tensorEmbedding (d := Fin 3) (E := R3)).map_sub _ _).symm
  rw [he, inner_toTensorL2]
  simp only [deformation, ContinuousMap.sum_apply, ContinuousMap.smul_apply',
    ContinuousMap.sub_apply, sum_inner, real_inner_smul_left, velocityComponentJet,
    ContinuousMap.coe_mk]

theorem transport_work_eq_zero_of_projected
    (hr : ∀ n, u (-n) = coefficientConjugate (u n))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hJ : toTensorL2 (fluxField 0 u) = projectedFlux 0 u) :
    ⟪projectedFlux 0 u,
      toTensorL2 (fun j ↦ transport (velocityComponentJet u hu) (rawFluxJet u hu j))⟫ = 0 := by
  rw [transport_work_eq_deformation u hu hr hd, hJ, sub_self, inner_zero_right]

omit hu in
/-- The periodic physical data construct the solution and every jet used
by the transport identity on the local interval. No transport bound is assumed. -/
theorem exists_physical_local_transport_identity (ν : ℝ) (hν : 0 < ν)
    (f : T3 → VelocityCoefficient)
    (hf : ∀ i, HasContinuousCoordinateJet 8 (fun x ↦ f x i))
    (hr : ∀ x i, star (f x i) = f x i)
    (hd : ∀ q, modeDot q (torusFourierVelocity f q) = 0)
    (hzero : torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution ν (torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ hu : Summable (fourierMoment 2 (s.coefficients t)),
          ⟪projectedFlux 0 (s.coefficients t),
            toTensorL2 (fun j ↦ transport (velocityComponentJet (s.coefficients t) hu)
              (rawFluxJet (s.coefficients t) hu j))⟫ =
          ∫ x : T3, ∑ j, ∑ k, velocityJet (s.coefficients t) j x k *
            ⟪(projectedFluxJet (s.coefficients t) hu k).value x,
              fluxField 0 (s.coefficients t) j x - (projectedFluxJet (s.coefficients t) hu j).value x⟫ := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    exists_physical_localMomentEnvelope 2 ν hν f hf hr hd hzero
  refine ⟨T, hT, B, hB, s, fun t ht ↦ ?_⟩
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)
  exact ⟨hm, transport_work_eq_integral _ hm (s.reality t) (s.transverse t)⟩

end Mettapedia.FluidDynamics.NavierStokes.LongitudinalProjectedTransport
