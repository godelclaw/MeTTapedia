import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxCoefficients

/-!
# Collected coefficients of the three separate flux-variation slots

The mixed flux is `-omega(a)_j ((omega(b) dot grad)c)`. Its three
insertions of a rate reconstruct the actual product rule. Keeping
these coefficients explicit supports signed parity and finite-arithmetic
tests without expanding a cubic polarization after pairing.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxMixedCoefficients

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis UnitTorusGradientProjection ContinuousFieldBilinear
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeHigherDerivativeMoments
open PancakeCurlOutputTail PancakeInfiniteFourierTime PancakeFourierTranslationCurve
open PancakeBlockReality PancakeDyadicDirectionEvolution PancakeLocalStrainReality
open PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation
open LongitudinalVorticityTime LocalStretchingFluxTime LongitudinalGradientFlux
open PeriodicGradientFluxTriple PeriodicGradientFluxProduct PeriodicGradientFluxSymbol
open PeriodicTensorParseval PeriodicFourierCollection StretchingFluxVariation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def mixedTerm (a b c : FourierVelocity) (r j : Fin 3) : TripleIndex → VelocityCoefficient :=
  tripleCoeff (fourierCurl a) (fourierCurl b) (indexedDerivativeCoeff id r c) r j

def mixedInteraction (a b c : FourierVelocity) (j : Fin 3) (p : TripleIndex) : VelocityCoefficient :=
  -∑ r, mixedTerm a b c r j p

def mixedCoefficients (a b c : FourierVelocity) (j : Fin 3) : FourierVelocity :=
  collect tripleFrequency (mixedInteraction a b c j)

def variationCoefficients (u v : FourierVelocity) (j : Fin 3) : FourierVelocity :=
  mixedCoefficients v u u j + mixedCoefficients u v u j + mixedCoefficients u u v j

theorem mixedCoefficients_self (u : FourierVelocity) (j : Fin 3) :
    mixedCoefficients u u u j = StretchingFluxCoefficients.coefficients u j := rfl

theorem summable_norm_mixedTerm (a b c : FourierVelocity)
    (ha : Summable (fourierMoment 1 a)) (hb : Summable (fourierMoment 1 b))
    (hc : Summable (fourierMoment 1 c)) (r j : Fin 3) :
    Summable (fun p ↦ ‖mixedTerm a b c r j p‖) := by
  have hwa := summable_norm_curlCoefficients id a (by simpa only [indexedFirstMoment_id] using ha)
  have hwb := summable_norm_curlCoefficients id b (by simpa only [indexedFirstMoment_id] using hb)
  exact summable_norm_tripleCoeff _ _ _ hwa hwb
    (summable_norm_derivativeCoefficients id c (by simpa only [indexedFirstMoment_id] using hc) r) r j

theorem summable_norm_mixedInteraction (a b c : FourierVelocity)
    (ha : Summable (fourierMoment 1 a)) (hb : Summable (fourierMoment 1 b))
    (hc : Summable (fourierMoment 1 c)) (j : Fin 3) :
    Summable (fun p ↦ ‖mixedInteraction a b c j p‖) := by
  apply (summable_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin 3))) ↦
    summable_norm_mixedTerm a b c ha hb hc r j)).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro p
  simpa only [mixedInteraction, norm_neg] using norm_sum_le Finset.univ (fun r ↦ mixedTerm a b c r j p)

theorem summable_norm_mixedCoefficients (a b c : FourierVelocity)
    (ha : Summable (fourierMoment 1 a)) (hb : Summable (fourierMoment 1 b))
    (hc : Summable (fourierMoment 1 c)) (j : Fin 3) :
    Summable (fun q ↦ ‖mixedCoefficients a b c j q‖) :=
  summable_norm_collect tripleFrequency _ (summable_norm_mixedInteraction a b c ha hb hc j)

theorem summable_norm_variationCoefficients (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) (j : Fin 3) :
    Summable (fun q ↦ ‖variationCoefficients u v j q‖) := by
  have h1 := summable_norm_mixedCoefficients v u u hv hu hu j
  have h2 := summable_norm_mixedCoefficients u v u hu hv hu j
  have h3 := summable_norm_mixedCoefficients u u v hu hu hv j
  apply ((h1.add h2).add h3).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro q
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

theorem fullFourierField_mixedInteraction (a b c : FourierVelocity)
    (ha : Summable (fourierMoment 1 a)) (hb : Summable (fourierMoment 1 b))
    (hc : Summable (fourierMoment 1 c)) (j : Fin 3) :
    fullFourierField tripleFrequency (mixedInteraction a b c j) =
      -∑ r, fullFourierField tripleFrequency (mixedTerm a b c r j) := by
  have hm (p : TripleIndex) : modeField (tripleFrequency p) (mixedInteraction a b c j p) =
      -∑ r, modeField (tripleFrequency p) (mixedTerm a b c r j p) := by
    change modeFieldCLM (tripleFrequency p) (-∑ r, mixedTerm a b c r j p) = _
    rw [map_neg, map_sum]
    rfl
  change (∑' p, modeField (tripleFrequency p) (mixedInteraction a b c j p)) =
    -∑ r, ∑' p, modeField (tripleFrequency p) (mixedTerm a b c r j p)
  simp_rw [hm]
  rw [tsum_neg, Summable.tsum_finsetSum]
  intro r _
  exact summable_modeField tripleFrequency _ (summable_norm_mixedTerm a b c ha hb hc r j)

theorem realField_mixedCoefficients (a b c : FourierVelocity)
    (ha : Summable (fourierMoment 1 a)) (hb : Summable (fourierMoment 1 b))
    (hc : Summable (fourierMoment 1 c))
    (hra : ∀ q, a (-q) = coefficientConjugate (a q))
    (hrb : ∀ q, b (-q) = coefficientConjugate (b q)) (j : Fin 3) :
    realField (mixedCoefficients a b c j) =
      -∑ r, tripleField (fourierCurl a) (fourierCurl b) (indexedDerivativeCoeff id r c) r j := by
  have hwa := summable_norm_curlCoefficients id a (by simpa only [indexedFirstMoment_id] using ha)
  have hwb := summable_norm_curlCoefficients id b (by simpa only [indexedFirstMoment_id] using hb)
  change (complexRealPartEuclideanCLM.compLeftContinuous ℝ T3)
    (fullFourierField id (collect tripleFrequency (mixedInteraction a b c j))) = _
  rw [fullFourierField_collect _ _ (summable_norm_mixedInteraction a b c ha hb hc j),
    fullFourierField_mixedInteraction a b c ha hb hc j, map_neg, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact (tripleField_eq_tripleFourierField _ _ _ hwa hwb
    (summable_norm_derivativeCoefficients id c (by simpa only [indexedFirstMoment_id] using hc) r)
    (fourierCurl_real a hra) (fourierCurl_real b hrb) r j).symm

theorem realField_variationCoefficients (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (hru : ∀ q, u (-q) = coefficientConjugate (u q))
    (hrv : ∀ q, v (-q) = coefficientConjugate (v q)) (j : Fin 3) :
    realField (variationCoefficients u v j) = variationField u v j := by
  have h1 := summable_norm_mixedCoefficients v u u hv hu hu j
  have h2 := summable_norm_mixedCoefficients u v u hu hv hu j
  have h3 := summable_norm_mixedCoefficients u u v hu hu hv j
  have h12 : Summable (fun q ↦ ‖(mixedCoefficients v u u j + mixedCoefficients u v u j) q‖) :=
    (h1.add h2).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_add_le _ _)
  rw [variationCoefficients, realField_add _ _ h12 h3, realField_add _ _ h1 h2,
    realField_mixedCoefficients v u u hv hu hu hrv hru,
    realField_mixedCoefficients u v u hu hv hu hru hrv,
    realField_mixedCoefficients u u v hu hu hv hru hru]
  apply ContinuousMap.ext
  intro x
  ext i
  simp only [variationField, stretchingVariationField, stretchingField, tripleField,
    productField, pointwise, ContinuousMap.coe_mk, ContinuousLinearMap.lsmul_apply,
    componentField_apply, vorticityField, velocityDerivativeField,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, Fin.sum_univ_three,
    PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem projected_variation_work_eq_tsum (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (hru : ∀ q, u (-q) = coefficientConjugate (u q))
    (hrv : ∀ q, v (-q) = coefficientConjugate (v q)) :
    ⟪projectedFlux 0 u, toTensorL2 (variationField u v)⟫ =
      ∑' q, (coefficientHermitian
        (divergenceCoeff q (fun j ↦ StretchingFluxCoefficients.coefficients u j q))
        (divergenceCoeff q (fun j ↦ variationCoefficients u v j q)) /
          (((2 * Real.pi : ℝ) : ℂ) ^ 2 * modeSquare q)).re := by
  have h := StretchingFluxCoefficients.projected_work_eq_tsum u hu hru
    (variationCoefficients u v) (summable_norm_variationCoefficients u v hu hv)
  simpa only [realField_variationCoefficients u v hu hv hru hrv] using h

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxMixedCoefficients
