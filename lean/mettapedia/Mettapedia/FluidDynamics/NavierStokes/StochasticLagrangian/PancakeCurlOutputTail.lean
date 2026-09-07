import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeExteriorReconstructionTail
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeGalerkinVorticityBridge

/-!
# Summable output-curl tails from explicit Fourier moments

Two first weighted absolute Fourier moments dominate the actual bilinear
curl interaction. For velocity paired with its curl, a second weighted
absolute velocity moment suffices. This condition is a smoothness input,
not a bound proved from finite kinetic energy.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeCurlOutputTail

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeDyadicDirectionEvolution
open PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator PancakeExchangeSymmetricCurl PancakeLowTouchEnergy
open PancakeSameSectorDissipation PancakeIncomingLowSourceEnergy PancakeGalerkinKineticEnergy
open PancakePeriodicVorticityEquation PancakeTransverseEnergyFreezing
open PancakeSummableOutputTail PancakeExteriorReconstructionTail

local notation "T3" => UnitAddTorus (Fin 3)

def fourierMoment (s : ℕ) (u : FourierVelocity) (k : Wavevector) : ℝ :=
  (1 + ‖frequencyVec k‖) ^ s * ‖coefficientVec (u k)‖

theorem fourierMoment_nonneg (s : ℕ) (u : FourierVelocity) (k : Wavevector) :
    0 ≤ fourierMoment s u k := by unfold fourierMoment; positivity

def curlPair (u v : FourierVelocity) (p : Wavevector × Wavevector) : VelocityCoefficient :=
  unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient (p.1 + p.2))
    (coefficientCross (u p.1) (v p.2))

def curlMajorant (u v : FourierVelocity) (p : Wavevector × Wavevector) : ℝ :=
  (2 * Real.pi) * (fourierMoment 1 u p.1 * fourierMoment 1 v p.2)

theorem curlMajorant_nonneg (u v : FourierVelocity) (p : Wavevector × Wavevector) :
    0 ≤ curlMajorant u v p := by
  unfold curlMajorant
  exact mul_nonneg (by positivity) (mul_nonneg (fourierMoment_nonneg _ _ _) (fourierMoment_nonneg _ _ _))

theorem frequencyVec_add (k l : Wavevector) : frequencyVec (k + l) = frequencyVec k + frequencyVec l := by
  ext i
  simp [frequencyVec, coefficientVec, wavevectorCoefficient]

theorem norm_curlPair_le (u v : FourierVelocity) (p : Wavevector × Wavevector) :
    ‖coefficientVec (curlPair u v p)‖ ≤ curlMajorant u v p := by
  have hf : ‖frequencyVec (p.1 + p.2)‖ ≤ (1 + ‖frequencyVec p.1‖) * (1 + ‖frequencyVec p.2‖) := by
    rw [frequencyVec_add]
    have h := norm_add_le (frequencyVec p.1) (frequencyVec p.2)
    nlinarith [mul_nonneg (norm_nonneg (frequencyVec p.1)) (norm_nonneg (frequencyVec p.2))]
  calc
    _ = (2 * Real.pi) * ‖coefficientVec (coefficientCross (wavevectorCoefficient (p.1 + p.2))
        (coefficientCross (u p.1) (v p.2)))‖ := by
      change ‖unitTorusDerivativePhase • coefficientVec _‖ = _
      rw [norm_smul, norm_derivativePhase]
      rfl
    _ ≤ (2 * Real.pi) * (‖frequencyVec (p.1 + p.2)‖ * (‖coefficientVec (u p.1)‖ * ‖coefficientVec (v p.2)‖)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_cross_le _ _).trans (mul_le_mul_of_nonneg_left (norm_complex_cross_le _ _) (norm_nonneg _))
    _ ≤ (2 * Real.pi) * ((1 + ‖frequencyVec p.1‖) * (1 + ‖frequencyVec p.2‖) *
        (‖coefficientVec (u p.1)‖ * ‖coefficientVec (v p.2)‖)) := by gcongr
    _ = _ := by simp only [curlMajorant, fourierMoment, pow_one]; ring

theorem summable_curlMajorant (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) :
    Summable (curlMajorant u v) :=
  (hu.mul_of_nonneg hv (fourierMoment_nonneg _ _) (fourierMoment_nonneg _ _)).mul_left (2 * Real.pi)

theorem pairOutputCoeff_curlPair (modes : Finset Wavevector) (u v : FourierVelocity) :
    pairOutputCoeff (modes ×ˢ modes) (curlPair u v) = curlConvolutionCoeff modes modes u v := by
  funext q
  simp only [pairOutputCoeff, curlConvolutionCoeff_eq_pairSum, Finset.sum_filter, curlPair]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs with h
  · rw [h]
  · rfl

theorem norm_exteriorCurl_le_outputTail (modes outputs : Finset Wavevector) (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) (x : T3) :
    ‖complexRealPartEuclidean (finiteFourierReconstruction (outputs \ modes)
      (curlConvolutionCoeff modes modes u v) x)‖ ≤ outputTail (curlMajorant u v) modes := by
  rw [← pairOutputCoeff_curlPair]
  exact norm_exterior_reconstruction_le_outputTail modes outputs _ _ _ (curlMajorant_nonneg _ _)
    (summable_curlMajorant _ _ hu hv) (fun p _ ↦ norm_curlPair_le _ _ p) x

theorem exists_uniform_exteriorCurl_lt (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ core : Finset Wavevector, ∀ modes : Finset Wavevector, core ⊆ modes →
      ∀ (outputs : Finset Wavevector) (x : T3),
        ‖complexRealPartEuclidean (finiteFourierReconstruction (outputs \ modes)
          (curlConvolutionCoeff modes modes u v) x)‖ < epsilon := by
  obtain ⟨core, hc⟩ := exists_outputTail_lt (curlMajorant u v) (curlMajorant_nonneg _ _)
    (summable_curlMajorant _ _ hu hv) epsilon hepsilon
  exact ⟨core, fun modes hm outputs x ↦ (norm_exteriorCurl_le_outputTail modes outputs u v hu hv x).trans_lt (hc modes hm)⟩

theorem norm_fourierCurl_le (u : FourierVelocity) (k : Wavevector) :
    ‖coefficientVec (fourierCurl u k)‖ ≤ (2 * Real.pi) * ‖frequencyVec k‖ * ‖coefficientVec (u k)‖ := by
  change ‖unitTorusDerivativePhase • coefficientVec (coefficientCross (wavevectorCoefficient k) (u k))‖ ≤ _
  rw [norm_smul, norm_derivativePhase]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (norm_cross_le k (u k)) (show 0 ≤ 2 * Real.pi by positivity)

theorem firstMoment_le_second (u : FourierVelocity) (k : Wavevector) :
    fourierMoment 1 u k ≤ fourierMoment 2 u k := by
  unfold fourierMoment
  rw [pow_one]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [norm_nonneg (frequencyVec k)]

theorem summable_firstMoment_of_second (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Summable (fourierMoment 1 u) :=
  Summable.of_nonneg_of_le (fourierMoment_nonneg _ _) (firstMoment_le_second u) hu

theorem firstMoment_curl_le_second (u : FourierVelocity) (k : Wavevector) :
    fourierMoment 1 (fourierCurl u) k ≤ (2 * Real.pi) * fourierMoment 2 u k := by
  unfold fourierMoment
  rw [pow_one]
  calc
    _ ≤ (1 + ‖frequencyVec k‖) * ((2 * Real.pi) * ‖frequencyVec k‖ * ‖coefficientVec (u k)‖) :=
      mul_le_mul_of_nonneg_left (norm_fourierCurl_le u k) (by positivity)
    _ ≤ (1 + ‖frequencyVec k‖) * ((2 * Real.pi) * (1 + ‖frequencyVec k‖) * ‖coefficientVec (u k)‖) := by
      gcongr
      exact le_add_of_nonneg_left zero_le_one
    _ = _ := by ring

theorem summable_firstMoment_curl (u : FourierVelocity) (hu : Summable (fourierMoment 2 u)) :
    Summable (fourierMoment 1 (fourierCurl u)) :=
  Summable.of_nonneg_of_le (fourierMoment_nonneg _ _) (firstMoment_curl_le_second u) (hu.mul_left (2 * Real.pi))

end Mettapedia.FluidDynamics.NavierStokes.PancakeCurlOutputTail
