import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeRetainedProjectionDefect

/-!
# Output curl with the zero frequency retained

The curl coefficient at zero is zero. A mean-zero velocity therefore has
the same physical nonlinear curl identity even when the retained finite
set includes zero, as ordinary exhausting lattice boxes do.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeZeroModeCurlBridge

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeExchangeSymmetricCurl PancakeFrequencyProjectorCommutator
open PancakeGalerkinKineticEnergy PancakeIncomingLowSourceEnergy PancakeRetainedProjectionDefect

theorem fourierCurl_zero (u : FourierVelocity) : fourierCurl u 0 = 0 := by
  ext i
  fin_cases i <;> simp [fourierCurl, coefficientCross, wavevectorCoefficient]

theorem biotSavart_zero (w : VelocityCoefficient) : unitTorusBiotSavartAmp 0 w = 0 := by
  simp [unitTorusBiotSavartAmp, complexBiotSavartAmp, modeSquare]

theorem physicalBiotSavart_fourierCurl_meanZero (u : FourierVelocity) (hzero : u 0 = 0)
    (k : Wavevector) (hu : modeDot k (u k) = 0) :
    unitTorusBiotSavartAmp k (fourierCurl u k) = u k := by
  by_cases hk : k = 0
  · subst k
    rw [biotSavart_zero, hzero]
  · exact physicalBiotSavart_fourierCurl k u (frequencyVec_ne_zero hk) hu

theorem incomingNonlinearCoeff_eq_curl_with_zero (modes : Finset Wavevector)
    (omega : FourierVelocity) (q : Wavevector) (hzero : omega 0 = 0)
    (hw : ∀ k ∈ modes, modeDot k (omega k) = 0) :
    incomingNonlinearCoeff modes modes omega omega q =
      curlConvolutionCoeff modes modes (physicalVelocity omega) omega q := by
  classical
  let pairs := (modes ×ˢ modes).filter (fun p ↦ p.1 + p.2 = q)
  have hs : ∀ p, p ∈ pairs ↔ p.swap ∈ pairs := by
    intro p
    simp [pairs, add_comm, and_comm]
  have hp (p : Wavevector × Wavevector) (h : p ∈ pairs) :
      p.1 ∈ modes ∧ p.2 ∈ modes := (Finset.mem_product.mp (Finset.mem_filter.mp h).1)
  have hc (k : Wavevector) (hk : k ∈ modes) :
      unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient k)
        (unitTorusBiotSavartAmp k (omega k)) = omega k := by
    by_cases hz : k = 0
    · subst k
      simp [hzero, biotSavart_zero, coefficientCross]
    · exact curl_physicalVelocity k (omega k) (frequencyVec_ne_zero hz) (hw k hk)
  have h := swap_closed_outputCurl q pairs omega hs
    (fun p h ↦ (Finset.mem_filter.mp h).2) (fun p h ↦ hc p.1 (hp p h).1)
    (fun p _ ↦ by
      simp [unitTorusBiotSavartAmp, complexBiotSavartAmp, coefficientCross,
        wavevectorCoefficient, modeDot, Fin.sum_univ_three]
      ring)
    (fun p h ↦ hw p.2 (hp p h).2)
  rw [incomingNonlinearCoeff_eq_pairSum, curlConvolutionCoeff_eq_pairSum]
  change (∑ p ∈ pairs, _) = ∑ p ∈ pairs, _
  rw [h, cross_sum_right, Finset.smul_sum]
  rfl

theorem nonlinearVorticityCoeff_eq_curl_meanZero (modes : Finset Wavevector)
    (u : FourierVelocity) (hzero : u 0 = 0) (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    nonlinearVorticityCoeff modes u = curlConvolutionCoeff modes modes u (fourierCurl u) := by
  have hn := fun q ↦ incomingNonlinearCoeff_eq_curl_with_zero modes (fourierCurl u) q
    (fourierCurl_zero u) (fun k _ ↦ fourierCurl_transverse k u)
  have hp : ∀ k ∈ modes, physicalVelocity (fourierCurl u) k = u k := fun k hk ↦
    physicalBiotSavart_fourierCurl_meanZero u hzero k (hu k hk)
  funext q
  have he : nonlinearVorticityCoeff modes u q = incomingNonlinearCoeff modes modes (fourierCurl u) (fourierCurl u) q := by
    simp [nonlinearVorticityCoeff, incomingNonlinearCoeff, finiteUnitTorusVorticityRHS,
      finiteUnitTorusNonstretchingCoeff, unitTorusViscousVorticityCoeff, add_comm]
  rw [he, hn q, curlConvolutionCoeff_eq_pairSum, curlConvolutionCoeff_eq_pairSum]
  apply Finset.sum_congr rfl
  intro p h
  rw [hp p.1 (Finset.mem_product.mp (Finset.mem_filter.mp h).1).1]

end Mettapedia.FluidDynamics.NavierStokes.PancakeZeroModeCurlBridge
