import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicFourierCollection
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PeriodicTensorParseval
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxVariation

/-!
# Canonical Fourier coefficients of the physical stretching flux

All triples with a common output frequency are collected before pairing.
The resulting absolutely summable tensor reconstructs the actual cubic
flux `J_j=-omega_j (omega dot grad)u`, including its sign. Its reality
and signed projected Parseval identity follow from the original velocity.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxCoefficients

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeHigherDerivativeMoments
open PancakeInfiniteFourierTime PancakeInfiniteSpatialCurl PancakeCurlOutputTail
open PancakeFourierTranslationCurve
open PancakeBlockReality PancakeLocalStrainReality PancakeGalerkinKineticEnergy
open PancakePeriodicVorticityEquation PancakeDyadicDirectionEvolution
open LongitudinalVorticityTime LongitudinalGradientFlux PeriodicGradientFluxTriple
open LongitudinalInviscidFluxFourier PeriodicProjectedTensorJet PeriodicGradientFluxSymbol
open PeriodicFourierCollection PeriodicTensorParseval

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def term (u : FourierVelocity) (r j : Fin 3) : TripleIndex → VelocityCoefficient :=
  tripleCoeff (fourierCurl u) (fourierCurl u) (indexedDerivativeCoeff id r u) r j

def interaction (u : FourierVelocity) (j : Fin 3) (p : TripleIndex) : VelocityCoefficient :=
  -∑ r, term u r j p

def coefficients (u : FourierVelocity) (j : Fin 3) : FourierVelocity :=
  collect tripleFrequency (interaction u j)

theorem summable_norm_term (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (r j : Fin 3) : Summable (fun p ↦ ‖term u r j p‖) := by
  have hui : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  have hw := summable_norm_curlCoefficients id u hui
  exact summable_norm_tripleCoeff _ _ _ hw hw
    (summable_norm_derivativeCoefficients id u hui r) r j

theorem summable_norm_interaction (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (j : Fin 3) : Summable (fun p ↦ ‖interaction u j p‖) := by
  apply (summable_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin 3))) ↦
    summable_norm_term u hu r j)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro p
  simpa only [interaction, norm_neg] using norm_sum_le Finset.univ (fun r ↦ term u r j p)

theorem summable_norm_coefficients (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (j : Fin 3) : Summable (fun q ↦ ‖coefficients u j q‖) :=
  summable_norm_collect tripleFrequency _ (summable_norm_interaction u hu j)

theorem term_reality (u : FourierVelocity)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (r j : Fin 3) (p : TripleIndex) :
    term u r j (-p) = coefficientConjugate (term u r j p) := by
  ext i
  simp [term, tripleCoeff, indexedProductCoeff, fourierCurl_real u hr,
    indexedDerivativeCoeff_conjugate u hr r, coefficientConjugate, map_mul]

theorem interaction_reality (u : FourierVelocity)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (j : Fin 3) (p : TripleIndex) :
    interaction u j (-p) = coefficientConjugate (interaction u j p) := by
  ext i
  simp [interaction, term_reality u hr, coefficientConjugate, map_sum]

theorem coefficients_reality (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (j : Fin 3) (q : Wavevector) :
    coefficients u j (-q) = coefficientConjugate (coefficients u j q) := by
  apply collect_reality tripleFrequency _ _ (summable_norm_interaction u hu j)
    (interaction_reality u hr j) q
  intro p
  simp [tripleFrequency]
  abel

theorem fullFourierField_interaction (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (j : Fin 3) :
    fullFourierField tripleFrequency (interaction u j) =
      -∑ r, fullFourierField tripleFrequency (term u r j) := by
  have hm (p : TripleIndex) : modeField (tripleFrequency p) (interaction u j p) =
      -∑ r, modeField (tripleFrequency p) (term u r j p) := by
    change modeFieldCLM (tripleFrequency p) (-∑ r, term u r j p) = _
    rw [map_neg, map_sum]
    rfl
  change (∑' p, modeField (tripleFrequency p) (interaction u j p)) =
    -∑ r, ∑' p, modeField (tripleFrequency p) (term u r j p)
  simp_rw [hm]
  rw [tsum_neg, Summable.tsum_finsetSum]
  intro r _
  exact summable_modeField tripleFrequency _ (summable_norm_term u hu r j)

theorem realField_coefficients (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (j : Fin 3) :
    realField (coefficients u j) = fluxField 0 u j := by
  have hui : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu
  have hw := summable_norm_curlCoefficients id u hui
  change (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3)
    (fullFourierField id (collect tripleFrequency (interaction u j))) = _
  rw [fullFourierField_collect _ _ (summable_norm_interaction u hu j),
    fullFourierField_interaction u hu j, map_neg, map_sum]
  have ht (r : Fin 3) := tripleField_eq_tripleFourierField
    (fourierCurl u) (fourierCurl u) (indexedDerivativeCoeff id r u)
      hw hw (summable_norm_derivativeCoefficients id u hui r)
      (fourierCurl_real u hr) (fourierCurl_real u hr) r j
  simp_rw [show ∀ r, (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3)
    (fullFourierField tripleFrequency (term u r j)) =
      tripleField (fourierCurl u) (fourierCurl u) (indexedDerivativeCoeff id r u) r j
    from fun r ↦ (ht r).symm]
  simpa only [Pi.neg_apply, Finset.sum_apply] using
    (congrArg (fun F ↦ F j) (inviscid_fluxField_eq u)).symm

theorem projected_work_eq_tsum (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (K : Fin 3 → FourierVelocity) (hK : ∀ j, Summable (fun q ↦ ‖K j q‖)) :
    ⟪projectedFlux 0 u, toTensorL2 (fun j ↦ realField (K j))⟫ =
      ∑' q, (coefficientHermitian
        (divergenceCoeff q (fun j ↦ coefficients u j q))
        (divergenceCoeff q (fun j ↦ K j q)) /
          (((2 * Real.pi : ℝ) : ℂ) ^ 2 * modeSquare q)).re := by
  have h := inner_projected_eq_tsum_divergence (coefficients u) K
    (summable_norm_coefficients u hu) hK (coefficients_reality u hu hr)
  simpa only [realField_coefficients u hu hr, projectedFlux] using h

/-- Signed inverse-Laplacian pairing of the divergences of two physical fluxes. -/
def spectralPair (u v : FourierVelocity) : ℝ :=
  ∑' q, (coefficientHermitian
    (divergenceCoeff q (fun j ↦ coefficients u j q))
    (divergenceCoeff q (fun j ↦ coefficients v j q)) /
      (((2 * Real.pi : ℝ) : ℂ) ^ 2 * modeSquare q)).re

theorem projected_flux_pair (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (hru : ∀ q, u (-q) = coefficientConjugate (u q))
    (hrv : ∀ q, v (-q) = coefficientConjugate (v q)) :
    ⟪projectedFlux 0 u, projectedFlux 0 v⟫ = spectralPair u v := by
  have h := projected_work_eq_tsum u hu hru (coefficients v)
    (summable_norm_coefficients v hv)
  simp only [realField_coefficients v hv hrv] at h
  change ⟪gradientProjection (toTensorL2 (fluxField 0 u)),
    gradientProjection (toTensorL2 (fluxField 0 v))⟫ = _
  rw [inner_gradientProjection_gradientProjection]
  exact h

theorem spectralPair_self (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    spectralPair u u = ‖projectedFlux 0 u‖ ^ 2 := by
  rw [← projected_flux_pair u u hu hu hr hr, real_inner_self_eq_norm_sq]

/-- Cubic polarization differentiates all three flux slots, not only the velocity slot. -/
def spectralVariationWork (u v : FourierVelocity) : ℝ :=
  (1 / 2 : ℝ) * (spectralPair u (u + v) - spectralPair u (u - v)) - spectralPair u v

theorem physical_variation_work (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (hru : ∀ q, u (-q) = coefficientConjugate (u q))
    (hrv : ∀ q, v (-q) = coefficientConjugate (v q)) :
    ⟪projectedFlux 0 u, toTensorL2 (StretchingFluxVariation.variationField u v)⟫ =
      spectralVariationWork u v := by
  have hp := ExchangedFluxPolarization.summable_fourierMoment_add 1 u v hu hv
  have hm := CurlEigenfieldDefect.summable_fourierMoment_sub 1 u v hu hv
  have hrp (q : Wavevector) : (u + v) (-q) = coefficientConjugate ((u + v) q) := by
    ext i
    simp [Pi.add_apply, hru, hrv, coefficientConjugate]
  have hrm (q : Wavevector) : (u - v) (-q) = coefficientConjugate ((u - v) q) := by
    ext i
    simp [Pi.sub_apply, hru, hrv, coefficientConjugate]
  change ⟪gradientProjection (toTensorL2 (fluxField 0 u)), _⟫ = _
  rw [← inner_gradientProjection_gradientProjection,
    StretchingFluxVariation.projected_variationField_eq_polarization u v hu hv]
  change ⟪projectedFlux 0 u, _⟫ = _
  rw [inner_sub_right, real_inner_smul_right, inner_sub_right,
    projected_flux_pair u (u + v) hu hp hru hrp,
    projected_flux_pair u (u - v) hu hm hru hrm,
    projected_flux_pair u v hu hv hru hrv]
  rfl

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxCoefficients
