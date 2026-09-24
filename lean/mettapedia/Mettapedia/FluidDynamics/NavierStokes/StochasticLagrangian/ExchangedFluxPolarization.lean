import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxVariationSeries
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.CurlEigenfieldDefect

/-!
# Exact cubic polarization of the infinite exchanged flux

The three-slot variation is recovered from three diagonal evaluations.
All infinite sums are absolutely convergent before they are rearranged.
This algebraic identity identifies the Fourier variation with the
variation of the reconstructed physical flux in `StretchingFluxVariation`.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxPolarization

open Mettapedia.Analysis.UnitTorusGradientProjection
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeCurlOutputTail PancakeGalerkinKineticEnergy PancakeBlockReality
open LocalVorticityNegation CurlEigenfieldDefect
open PeriodicGradientFluxTriple ExchangedFluxModeDynamics ExchangedFluxVariation
open ExchangedFluxVariationSeries ExchangedFluxHeatRepresentation
open LongitudinalExchangeFluxFourier LongitudinalGradientFlux

theorem mixedMode_add_first (u v w z : FourierVelocity) (p : TripleIndex) :
    mixedMode (u + v) w z p = mixedMode u w z p + mixedMode v w z p := by
  simp only [mixedMode, mixedTensor_add_first, map_add]

theorem mixedMode_add_second (u v w z : FourierVelocity) (p : TripleIndex) :
    mixedMode u (v + w) z p = mixedMode u v z p + mixedMode u w z p := by
  simp only [mixedMode, mixedTensor_add_second, map_add]

theorem mixedMode_add_third (u v w z : FourierVelocity) (p : TripleIndex) :
    mixedMode u v (w + z) p = mixedMode u v w p + mixedMode u v z p := by
  simp only [mixedMode, mixedTensor_add_third, map_add]

theorem mixedMode_neg_first (u v w : FourierVelocity) (p : TripleIndex) :
    mixedMode (-u) v w p = -mixedMode u v w p := by
  have he : mixedTensor (-u) v w p = -mixedTensor u v w p := by
    funext j
    simp only [mixedTensor, fourierCurl_neg, Pi.neg_apply, neg_smul, smul_neg]
  rw [mixedMode, he, map_neg]
  rfl

theorem mixedMode_neg_second (u v w : FourierVelocity) (p : TripleIndex) :
    mixedMode u (-v) w p = -mixedMode u v w p := by
  have hn (a b : VelocityCoefficient) : coefficientCross (-a) b = -coefficientCross a b := by
    ext i
    fin_cases i <;> simp [coefficientCross] <;> ring
  have he : mixedTensor u (-v) w p = -mixedTensor u v w p := by
    funext j
    simp only [mixedTensor, fourierCurl_neg, Pi.neg_apply, hn, map_neg, smul_neg]
  rw [mixedMode, he, map_neg]
  rfl

theorem mixedMode_neg_third (u v w : FourierVelocity) (p : TripleIndex) :
    mixedMode u v (-w) p = -mixedMode u v w p := by
  have hn (a b : VelocityCoefficient) : coefficientCross a (-b) = -coefficientCross a b := by
    ext i
    fin_cases i <;> simp [coefficientCross] <;> ring
  have he : mixedTensor u v (-w) p = -mixedTensor u v w p := by
    funext j
    simp only [mixedTensor, fourierCurl_neg, Pi.neg_apply, hn, map_neg, smul_neg]
  rw [mixedMode, he, map_neg]
  rfl

/-- Polarization identifies the coefficient of the linear perturbation. -/
theorem variationMode_eq_polarization (u v : FourierVelocity) (p : TripleIndex) :
    variationMode u v p =
      (1 / 2 : ℝ) • (mode (u + v) p - mode (u - v) p) - mode v p := by
  simp only [← mixedMode_self, sub_eq_add_neg, mixedMode_add_first,
    mixedMode_add_second, mixedMode_add_third, mixedMode_neg_first,
    mixedMode_neg_second, mixedMode_neg_third, variationMode]
  module

theorem summable_fourierMoment_neg (m : ℕ) (u : FourierVelocity)
    (hu : Summable (fourierMoment m u)) : Summable (fourierMoment m (-u)) := by
  simpa only [neg_one_smul] using summable_fourierMoment_smul m (-1) u hu

theorem summable_fourierMoment_add (m : ℕ) (u v : FourierVelocity)
    (hu : Summable (fourierMoment m u)) (hv : Summable (fourierMoment m v)) :
    Summable (fourierMoment m (u + v)) := by
  simpa only [sub_neg_eq_add] using
    summable_fourierMoment_sub m u (-v) hu (summable_fourierMoment_neg m v hv)

theorem fluxVariation_eq_polarized_series (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) :
    fluxVariation u v = -(1 / 2 : ℝ) •
      ((∑' p : TripleIndex, mode (u + v) p) - ∑' p : TripleIndex, mode (u - v) p) +
        ∑' p : TripleIndex, mode v p := by
  have hp := (summable_norm_mode (u + v) (summable_fourierMoment_add 1 u v hu hv)).of_norm
  have hm := (summable_norm_mode (u - v) (summable_fourierMoment_sub 1 u v hu hv)).of_norm
  have hv' := (summable_norm_mode v hv).of_norm
  rw [fluxVariation, tsum_active_variationMode]
  simp_rw [variationMode_eq_polarization]
  rw [((hp.sub hm).const_smul (1 / 2 : ℝ)).tsum_sub hv',
    (hp.sub hm).tsum_const_smul, hp.tsum_sub hm]
  module

theorem neg_tsum_mode_eq_projectedFlux (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    -(∑' p : TripleIndex, mode u p) = projectedFlux 0 u := by
  simp only [mode_eq_exchangeMode u _ (hd _) (hd _)]
  exact (projectedFlux_inviscid_eq_exchangeSeries u hu hr).symm

/-- The Fourier variation is a polarization of the actual projected flux. -/
theorem fluxVariation_eq_polarization (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (hdu : ∀ q, modeDot q (u q) = 0) (hdv : ∀ q, modeDot q (v q) = 0)
    (hru : ∀ q, u (-q) = coefficientConjugate (u q))
    (hrv : ∀ q, v (-q) = coefficientConjugate (v q)) :
    fluxVariation u v = (1 / 2 : ℝ) • (projectedFlux 0 (u + v) - projectedFlux 0 (u - v)) -
      projectedFlux 0 v := by
  have hdadd (q : Wavevector) : modeDot q ((u + v) q) = 0 := by
    calc
      _ = modeDot q (u q) + modeDot q (v q) := by
        simp only [modeDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      _ = 0 := by rw [hdu q, hdv q, add_zero]
  have hdsub (q : Wavevector) : modeDot q ((u - v) q) = 0 := by
    simp only [Pi.sub_apply, modeDot_sub, hdu, hdv, sub_self]
  have hradd (q : Wavevector) : (u + v) (-q) = coefficientConjugate ((u + v) q) := by
    simp only [Pi.add_apply, coefficientConjugate_add, hru, hrv]
  have hrsub (q : Wavevector) : (u - v) (-q) = coefficientConjugate ((u - v) q) := by
    simp only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply, coefficientConjugate_add,
      coefficientConjugate_neg, hru, hrv]
  rw [fluxVariation_eq_polarized_series u v hu hv,
    ← neg_tsum_mode_eq_projectedFlux (u + v) (summable_fourierMoment_add 1 u v hu hv) hdadd hradd,
    ← neg_tsum_mode_eq_projectedFlux (u - v) (summable_fourierMoment_sub 1 u v hu hv) hdsub hrsub,
    ← neg_tsum_mode_eq_projectedFlux v hv hdv hrv]
  module

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxPolarization
