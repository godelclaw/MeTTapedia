import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.StretchingFluxMixedCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.TwoShearViscousData

/-!
# Horizontal parity cancellation in the full inviscid flux work

Odd horizontal Fourier data have an even inviscid NS tangent. The cubic
flux is odd while its tangent is even, so the actual projected pairing
vanishes. This is an instantaneous identity for the unrestricted equation,
not an assertion that the evolving solution preserves the odd sector.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StretchingFluxHorizontalParity

open scoped RealInnerProductSpace ComplexConjugate
open Mettapedia.Analysis UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeCurlOutputTail PancakeHigherDerivativeMoments
open PancakeGalerkinKineticEnergy PancakeBlockReality PancakePeriodicVorticityEquation
open PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope FullVelocityRHSReality
open PeriodicGradientFluxTriple PeriodicGradientFluxSymbol PeriodicTensorParseval
open PeriodicFourierCollection StretchingFluxMixedCoefficients StretchingFluxCoefficients
open StretchingFluxVariation StretchingFluxSpectralEvolution
open LongitudinalGradientFlux

def horizontalClass (q : Wavevector) : ℤ := (q 0 + q 1) % 2

def HasHorizontalParity (r : ℤ) (u : FourierVelocity) : Prop :=
  ∀ q, horizontalClass q ≠ r → u q = 0

theorem horizontalClass_triple (p : TripleIndex) :
    horizontalClass (tripleFrequency p) =
      (horizontalClass p.1 + horizontalClass p.2.1 + horizontalClass p.2.2) % 2 := by
  simp only [horizontalClass, tripleFrequency, Pi.add_apply]
  omega

theorem curl_eq_zero_of_coefficient_zero (u : FourierVelocity) (q : Wavevector)
    (hq : u q = 0) : fourierCurl u q = 0 := by
  ext i
  fin_cases i <;> simp [fourierCurl, hq, coefficientCross]

theorem mixedTerm_eq_zero_of_parity (a b c : FourierVelocity) (ra rb rc : ℤ)
    (ha : HasHorizontalParity ra a) (hb : HasHorizontalParity rb b)
    (hc : HasHorizontalParity rc c) (r j : Fin 3) (p : TripleIndex)
    (hp : horizontalClass (tripleFrequency p) ≠ (ra + rb + rc) % 2) :
    mixedTerm a b c r j p = 0 := by
  by_cases h1 : horizontalClass p.1 = ra
  · by_cases h2 : horizontalClass p.2.1 = rb
    · by_cases h3 : horizontalClass p.2.2 = rc
      · exact False.elim (hp (by rw [horizontalClass_triple, h1, h2, h3]))
      · simp [mixedTerm, tripleCoeff, indexedProductCoeff, indexedDerivativeCoeff, hc _ h3]
    · simp [mixedTerm, tripleCoeff, indexedProductCoeff,
        curl_eq_zero_of_coefficient_zero b _ (hb _ h2)]
  · simp [mixedTerm, tripleCoeff, indexedProductCoeff,
      curl_eq_zero_of_coefficient_zero a _ (ha _ h1)]

theorem mixedCoefficients_parity (a b c : FourierVelocity) (ra rb rc : ℤ)
    (ha : HasHorizontalParity ra a) (hb : HasHorizontalParity rb b)
    (hc : HasHorizontalParity rc c) (j : Fin 3) :
    HasHorizontalParity ((ra + rb + rc) % 2) (mixedCoefficients a b c j) := by
  intro q hq
  unfold mixedCoefficients collect
  refine (tsum_congr (g := fun _ ↦ 0) ?_).trans tsum_zero
  intro p
  have hp : horizontalClass (tripleFrequency p.val) ≠ (ra + rb + rc) % 2 := by
    simpa only [show tripleFrequency p.val = q from p.property] using hq
  simp only [mixedInteraction, mixedTerm_eq_zero_of_parity a b c ra rb rc ha hb hc _ j _ hp,
    Finset.sum_const_zero, neg_zero]

theorem flux_parity (u : FourierVelocity) (hu : HasHorizontalParity 1 u) (j : Fin 3) :
    HasHorizontalParity 1 (coefficients u j) := by
  simpa only [mixedCoefficients_self, show ((1 : ℤ) + 1 + 1) % 2 = 1 from rfl] using
    mixedCoefficients_parity u u u 1 1 1 hu hu hu j

theorem variation_parity (u v : FourierVelocity) (hu : HasHorizontalParity 1 u)
    (hv : HasHorizontalParity 0 v) (j : Fin 3) :
    HasHorizontalParity 0 (variationCoefficients u v j) := by
  have h1 := mixedCoefficients_parity v u u 0 1 1 hv hu hu j
  have h2 := mixedCoefficients_parity u v u 1 0 1 hu hv hu j
  have h3 := mixedCoefficients_parity u u v 1 1 0 hu hu hv j
  norm_num only at h1 h2 h3
  intro q hq
  simp [variationCoefficients, h1 q hq, h2 q hq, h3 q hq]

theorem inviscidRHS_parity (u : FourierVelocity) (hu : HasHorizontalParity 1 u) :
    HasHorizontalParity 0 (infiniteVelocityRHS 0 u) := by
  intro q hq
  have hconv : infiniteConvection u q = 0 := by
    ext i
    refine (tsum_congr (g := fun _ ↦ 0) ?_).trans tsum_zero
    intro k
    by_cases hk : horizontalClass k = 1
    · have hl : horizontalClass (q - k) ≠ 1 := by
        simp only [horizontalClass, Pi.sub_apply] at hk hq ⊢
        omega
      simp [outputFiber, hu _ hl]
    · simp [outputFiber, hu _ hk, modeDot]
  ext i
  simp [infiniteVelocityRHS, hconv, unitTorusViscousVorticityCoeff, lerayMode, modeDot]
  split_ifs <;> rfl

theorem projected_variation_work_eq_zero (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (hru : ∀ q, u (-q) = coefficientConjugate (u q))
    (hrv : ∀ q, v (-q) = coefficientConjugate (v q))
    (hpu : HasHorizontalParity 1 u) (hpv : HasHorizontalParity 0 v) :
    ⟪projectedFlux 0 u, toTensorL2 (variationField u v)⟫ = 0 := by
  rw [projected_variation_work_eq_tsum u v hu hv hru hrv]
  refine (tsum_congr (g := fun _ ↦ 0) ?_).trans tsum_zero
  intro q
  by_cases hq : horizontalClass q = 1
  · have hq0 : horizontalClass q ≠ 0 := by omega
    simp [variation_parity u v hpu hpv _ q hq0, divergenceCoeff, contraction,
      coefficientHermitian]
  · simp [flux_parity u hpu _ q hq, divergenceCoeff, contraction, coefficientHermitian]

theorem spectralRHSWork_inviscid_eq_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (hp : HasHorizontalParity 1 u) : spectralRHSWork 0 u = 0 := by
  rw [spectralRHSWork, ← physical_variation_work u _
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
    (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 0 u hu)
    hr (infiniteVelocityRHS_conjugate 0 u hr)]
  exact projected_variation_work_eq_zero u _
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
    (VelocityRHSMoments.summable_fourierMoment_infiniteVelocityRHS 1 0 u hu)
    hr (infiniteVelocityRHS_conjugate 0 u hr) hp (inviscidRHS_parity u hp)

theorem twoShear_parity : HasHorizontalParity 1 TwoShearViscousData.velocity := by
  intro q hq
  have h1 : ¬ TwoShearViscousData.firstHorizontal q := by
    simp only [TwoShearViscousData.firstHorizontal, horizontalClass] at hq ⊢
    omega
  have h2 : ¬ TwoShearViscousData.secondHorizontal q := by
    simp only [TwoShearViscousData.secondHorizontal, horizontalClass] at hq ⊢
    omega
  ext i
  fin_cases i <;> simp [TwoShearViscousData.velocity, h1, h2]

theorem twoShear_inviscid_work_zero : spectralRHSWork 0 TwoShearViscousData.velocity = 0 :=
  spectralRHSWork_inviscid_eq_zero _ (TwoShearViscousData.all_moments 3)
    TwoShearViscousData.reality twoShear_parity

theorem twoShear_full_work_eq_heat (ν : ℝ) :
    spectralRHSWork ν TwoShearViscousData.velocity =
      ν * spectralVariationWork TwoShearViscousData.velocity
        (PancakeInfiniteSpatialLaplacian.laplacianCoeff TwoShearViscousData.velocity) := by
  rw [spectralRHSWork_affine_viscosity ν _ (TwoShearViscousData.all_moments 3)
    TwoShearViscousData.transverse TwoShearViscousData.reality,
    twoShear_inviscid_work_zero, zero_add,
    spectral_heat_work_eq_mixed_sub_dissipation _ (TwoShearViscousData.all_moments 3)
      TwoShearViscousData.transverse TwoShearViscousData.reality]

end Mettapedia.FluidDynamics.NavierStokes.StretchingFluxHorizontalParity
