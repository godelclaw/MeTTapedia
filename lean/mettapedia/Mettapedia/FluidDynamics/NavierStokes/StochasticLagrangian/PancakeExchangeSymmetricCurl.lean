import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeIncomingLowSourceEnergy

/-!
# Exchange-symmetric output curl for physical Fourier interactions

The difference between full stretching and symmetric strain is an
antisymmetric vorticity cross product. On swap-closed ordered input pairs,
this defect cancels exactly, leaving a derivative at the output frequency.
The physical curl-recovery and transversality conditions are explicit.
No solution-existence, time-budget, or regularity theorem is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeExchangeSymmetricCurl

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeBlockReality
open PancakeFrequencyProjectorCommutator PancakeIncomingLowSourceEnergy
open PancakeMaterialTransportCommutator

def fullStretch (k : Wavevector) (w v : VelocityCoefficient) : VelocityCoefficient :=
  (unitTorusDerivativePhase * modeDot k v) • unitTorusBiotSavartAmp k w

theorem fullStretch_sub_strain (k : Wavevector) (w v : VelocityCoefficient)
    (hcurl : unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient k)
      (unitTorusBiotSavartAmp k w) = w) :
    fullStretch k w v - unitTorusStrainStretchAmp k w v =
      (1 / 2 : ℂ) • coefficientCross w v := by
  calc
    _ = (1 / 2 : ℂ) • coefficientCross
        (unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient k)
          (unitTorusBiotSavartAmp k w)) v := by
      ext i
      fin_cases i <;>
        simp [fullStretch, unitTorusStrainStretchAmp, coefficientCross,
          coefficientDot, modeDot, wavevectorCoefficient, Fin.sum_univ_three] <;> ring
    _ = _ := by rw [hcurl]

theorem fullStretch_add_transport (k l : Wavevector) (w v : VelocityCoefficient)
    (hk : modeDot k (unitTorusBiotSavartAmp k w) = 0)
    (hl : modeDot l v = 0) :
    fullStretch k w v + unitTorusNegativeTransportAmp k l w v =
      unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient (k + l))
        (coefficientCross (unitTorusBiotSavartAmp k w) v) := by
  have he :
      unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient (k + l))
        (coefficientCross (unitTorusBiotSavartAmp k w) v) =
      fullStretch k w v + unitTorusNegativeTransportAmp k l w v +
        (unitTorusDerivativePhase * modeDot l v) • unitTorusBiotSavartAmp k w -
        (unitTorusDerivativePhase * modeDot k (unitTorusBiotSavartAmp k w)) • v := by
    ext i
    fin_cases i <;>
      simp [fullStretch, unitTorusNegativeTransportAmp, coefficientCross,
        modeDot, wavevectorCoefficient, Fin.sum_univ_three] <;> ring
  simpa [hk, hl] using he.symm

theorem physical_pair_outputCurl (k l : Wavevector) (w v : VelocityCoefficient)
    (hcurl : unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient k)
      (unitTorusBiotSavartAmp k w) = w)
    (hk : modeDot k (unitTorusBiotSavartAmp k w) = 0)
    (hl : modeDot l v = 0) :
    unitTorusNegativeTransportAmp k l w v + unitTorusStrainStretchAmp k w v =
      unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient (k + l))
        (coefficientCross (unitTorusBiotSavartAmp k w) v) -
      (1 / 2 : ℂ) • coefficientCross w v := by
  rw [← fullStretch_sub_strain k w v hcurl, ← fullStretch_add_transport k l w v hk hl]
  abel

theorem cross_swap (u v : VelocityCoefficient) :
    coefficientCross v u = -coefficientCross u v := by
  ext i
  fin_cases i <;> simp [coefficientCross] <;> ring

theorem zero_mode_curl_hypothesis_is_needed :
    modeDot (0 : Wavevector) (![1, 0, 0] : VelocityCoefficient) = 0 ∧
    fullStretch 0 ![1, 0, 0] ![0, 1, 0] -
      unitTorusStrainStretchAmp 0 ![1, 0, 0] ![0, 1, 0] ≠
        (1 / 2 : ℂ) • coefficientCross ![1, 0, 0] ![0, 1, 0] := by
  constructor
  · simp [modeDot]
  · intro he
    have he2 := congrFun he (2 : Fin 3)
    norm_num [fullStretch, unitTorusStrainStretchAmp, unitTorusBiotSavartAmp,
      complexBiotSavartAmp, coefficientCross, wavevectorCoefficient, modeSquare,
      modeDot, coefficientDot, Fin.sum_univ_three] at he2
    change (1 : ℂ) = 0 at he2
    exact one_ne_zero he2

theorem sum_cross_eq_zero (pairs : Finset (Wavevector × Wavevector))
    (omega : FourierVelocity)
    (hswap : ∀ p, p ∈ pairs ↔ p.swap ∈ pairs) :
    ∑ p ∈ pairs, coefficientCross (omega p.1) (omega p.2) = 0 := by
  classical
  have he : (∑ p ∈ pairs, coefficientCross (omega p.1) (omega p.2)) =
      ∑ p ∈ pairs, coefficientCross (omega p.2) (omega p.1) :=
    Finset.sum_equiv (Equiv.prodComm Wavevector Wavevector) hswap (by intros; rfl)
  have hn : (∑ p ∈ pairs, coefficientCross (omega p.2) (omega p.1)) =
      -(∑ p ∈ pairs, coefficientCross (omega p.1) (omega p.2)) := by
    calc
      _ = ∑ p ∈ pairs, -coefficientCross (omega p.1) (omega p.2) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact cross_swap _ _
      _ = _ := by rw [Finset.sum_neg_distrib]
  rw [hn] at he
  ext i
  have hi := congrFun he i
  simp only [Pi.neg_apply] at hi
  change (∑ p ∈ pairs, coefficientCross (omega p.1) (omega p.2)) i = 0
  linear_combination (1 / 2 : ℂ) * hi

theorem cross_sum_right {α : Type*} (s : Finset α)
    (u : VelocityCoefficient) (v : α → VelocityCoefficient) :
    coefficientCross u (∑ a ∈ s, v a) = ∑ a ∈ s, coefficientCross u (v a) := by
  ext i
  fin_cases i <;>
    simp [coefficientCross, Finset.sum_apply, Finset.mul_sum,
      Finset.sum_sub_distrib]

theorem swap_closed_outputCurl (q : Wavevector)
    (pairs : Finset (Wavevector × Wavevector)) (omega : FourierVelocity)
    (hswap : ∀ p, p ∈ pairs ↔ p.swap ∈ pairs)
    (hsum : ∀ p ∈ pairs, p.1 + p.2 = q)
    (hcurl : ∀ p ∈ pairs, unitTorusDerivativePhase •
      coefficientCross (wavevectorCoefficient p.1)
        (unitTorusBiotSavartAmp p.1 (omega p.1)) = omega p.1)
    (hu : ∀ p ∈ pairs, modeDot p.1 (unitTorusBiotSavartAmp p.1 (omega p.1)) = 0)
    (hw : ∀ p ∈ pairs, modeDot p.2 (omega p.2) = 0) :
    (∑ p ∈ pairs, (unitTorusNegativeTransportAmp p.1 p.2 (omega p.1) (omega p.2) +
      unitTorusStrainStretchAmp p.1 (omega p.1) (omega p.2))) =
    unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient q)
      (∑ p ∈ pairs, coefficientCross (unitTorusBiotSavartAmp p.1 (omega p.1))
        (omega p.2)) := by
  have hp : (∑ p ∈ pairs,
      (unitTorusNegativeTransportAmp p.1 p.2 (omega p.1) (omega p.2) +
      unitTorusStrainStretchAmp p.1 (omega p.1) (omega p.2))) =
      ∑ p ∈ pairs, (unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient q)
        (coefficientCross (unitTorusBiotSavartAmp p.1 (omega p.1)) (omega p.2)) -
        (1 / 2 : ℂ) • coefficientCross (omega p.1) (omega p.2)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [physical_pair_outputCurl p.1 p.2 (omega p.1) (omega p.2)
      (hcurl p hp) (hu p hp) (hw p hp), hsum p hp]
  rw [hp, Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
    sum_cross_eq_zero pairs omega hswap, smul_zero, sub_zero,
    ← cross_sum_right]

theorem curl_physicalVelocity (k : Wavevector) (w : VelocityCoefficient)
    (hk : frequencyVec k ≠ 0) (hw : modeDot k w = 0) :
    unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient k)
      (unitTorusBiotSavartAmp k w) = w := by
  have hks := modeSquare_ne_zero_of_frequencyVec_ne_zero hk
  have hcross : coefficientCross (wavevectorCoefficient k)
      (coefficientCross (wavevectorCoefficient k) w) =
      modeDot k w • wavevectorCoefficient k - modeSquare k • w := by
    ext i
    fin_cases i <;>
      simp [coefficientCross, wavevectorCoefficient, modeDot, modeSquare,
        Fin.sum_univ_three] <;> ring
  unfold unitTorusBiotSavartAmp complexBiotSavartAmp
  rw [coefficientCross_smul_right, coefficientCross_smul_right, hcross, hw,
    zero_smul, zero_sub]
  ext i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  field_simp [hks, unitTorusDerivativePhase_ne_zero]


/-- Output curl of a finite bilinear cross-product convolution. -/
def curlConvolutionCoeff (sources receivers : Finset Wavevector)
    (u v : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  ∑ l ∈ receivers, if q - l ∈ sources then
    unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient q)
      (coefficientCross (u (q - l)) (v l)) else 0

theorem curlConvolutionCoeff_eq_pairSum (sources receivers : Finset Wavevector)
    (u v : FourierVelocity) (q : Wavevector) :
    curlConvolutionCoeff sources receivers u v q =
      ∑ p ∈ (sources ×ˢ receivers).filter (fun p ↦ p.1 + p.2 = q),
        unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient q)
          (coefficientCross (u p.1) (v p.2)) := by
  classical
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_comm]
  unfold curlConvolutionCoeff
  apply Finset.sum_congr rfl
  intro l hl
  simp only [← eq_sub_iff_add_eq]
  simp

theorem incomingNonlinearCoeff_eq_pairSum (sources receivers : Finset Wavevector)
    (omega eta : FourierVelocity) (q : Wavevector) :
    incomingNonlinearCoeff sources receivers omega eta q =
      ∑ p ∈ (sources ×ˢ receivers).filter (fun p ↦ p.1 + p.2 = q),
        (unitTorusNegativeTransportAmp p.1 p.2 (omega p.1) (eta p.2) +
          unitTorusStrainStretchAmp p.1 (omega p.1) (eta p.2)) := by
  simp only [incomingNonlinearCoeff, finiteUnitTorusNegativeTransportCoeff,
    finiteUnitTorusStretchingCoeff, Finset.sum_add_distrib]

/-- A self-consistent square source/receiver channel is an output curl. -/
theorem incomingNonlinearCoeff_eq_curl (modes : Finset Wavevector)
    (omega : FourierVelocity) (q : Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
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
  have h := swap_closed_outputCurl q pairs omega hs
    (fun p h ↦ (Finset.mem_filter.mp h).2)
    (fun p h ↦ curl_physicalVelocity p.1 (omega p.1) (hk _ (hp p h).1) (hw _ (hp p h).1))
    (fun p h ↦ by
      simp [unitTorusBiotSavartAmp, complexBiotSavartAmp,
        coefficientCross, wavevectorCoefficient, modeDot, Fin.sum_univ_three]
      ring)
    (fun p h ↦ hw _ (hp p h).2)
  rw [incomingNonlinearCoeff_eq_pairSum, curlConvolutionCoeff_eq_pairSum]
  change (∑ p ∈ pairs, _) = ∑ p ∈ pairs, _
  rw [h, cross_sum_right, Finset.smul_sum]
  rfl

theorem incomingNonlinearCoeff_receiver_low_add_high (cutoff : ℝ)
    (sources receivers : Finset Wavevector) (omega eta : FourierVelocity) (q : Wavevector) :
    incomingNonlinearCoeff sources receivers omega eta q =
      incomingNonlinearCoeff sources (lowSources cutoff receivers) omega eta q +
        incomingNonlinearCoeff sources (highSources cutoff receivers) omega eta q := by
  classical
  simp only [incomingNonlinearCoeff_eq_receiverSum, lowSources, highSources]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem curlConvolutionCoeff_receiver_low_add_high (cutoff : ℝ)
    (sources receivers : Finset Wavevector) (u v : FourierVelocity) (q : Wavevector) :
    curlConvolutionCoeff sources receivers u v q =
      curlConvolutionCoeff sources (lowSources cutoff receivers) u v q +
        curlConvolutionCoeff sources (highSources cutoff receivers) u v q := by
  classical
  simp only [curlConvolutionCoeff, lowSources, highSources]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem curlConvolutionCoeff_source_low_add_high (cutoff : ℝ)
    (sources receivers : Finset Wavevector) (u v : FourierVelocity) (q : Wavevector) :
    curlConvolutionCoeff sources receivers u v q =
      curlConvolutionCoeff (lowSources cutoff sources) receivers u v q +
        curlConvolutionCoeff (highSources cutoff sources) receivers u v q := by
  classical
  unfold curlConvolutionCoeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hs : q - l ∈ sources <;> by_cases hc : ‖frequencyVec (q - l)‖ ≤ cutoff <;>
    simp [lowSources, highSources, hs, hc]

/-- Disjoint low-low, low-high, and high-low interactions. -/
def lowTouchCoeff (cutoff : ℝ) (modes : Finset Wavevector)
    (omega : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  incomingNonlinearCoeff (lowSources cutoff modes) modes omega omega q +
    incomingNonlinearCoeff (highSources cutoff modes) (lowSources cutoff modes) omega omega q

/-- The complementary channel has both input frequencies above the cutoff. -/
def highHighCoeff (cutoff : ℝ) (modes : Finset Wavevector)
    (omega : FourierVelocity) (q : Wavevector) : VelocityCoefficient :=
  incomingNonlinearCoeff (highSources cutoff modes) (highSources cutoff modes) omega omega q

theorem incomingNonlinearCoeff_lowTouch_add_highHigh (cutoff : ℝ)
    (modes : Finset Wavevector) (omega : FourierVelocity) (q : Wavevector) :
    incomingNonlinearCoeff modes modes omega omega q =
      lowTouchCoeff cutoff modes omega q + highHighCoeff cutoff modes omega q := by
  rw [incomingNonlinearCoeff_low_add_high cutoff,
    incomingNonlinearCoeff_receiver_low_add_high cutoff (highSources cutoff modes)]
  simp only [lowTouchCoeff, highHighCoeff, add_assoc]

/-- Restoring both orientations eliminates the antisymmetric strain defect. -/
theorem lowTouchCoeff_eq_curl (cutoff : ℝ) (modes : Finset Wavevector)
    (omega : FourierVelocity) (q : Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hw : ∀ k ∈ modes, modeDot k (omega k) = 0) :
    lowTouchCoeff cutoff modes omega q =
      curlConvolutionCoeff (lowSources cutoff modes) modes (physicalVelocity omega) omega q +
        curlConvolutionCoeff (highSources cutoff modes) (lowSources cutoff modes)
          (physicalVelocity omega) omega q := by
  have hfull := incomingNonlinearCoeff_eq_curl modes omega q hk hw
  have hhigh := incomingNonlinearCoeff_eq_curl (highSources cutoff modes) omega q
    (fun k h ↦ hk k (Finset.mem_filter.mp h).1)
    (fun k h ↦ hw k (Finset.mem_filter.mp h).1)
  rw [incomingNonlinearCoeff_lowTouch_add_highHigh cutoff, highHighCoeff, hhigh,
    curlConvolutionCoeff_source_low_add_high cutoff modes modes,
    curlConvolutionCoeff_receiver_low_add_high cutoff (highSources cutoff modes) modes] at hfull
  exact add_right_cancel (by simpa only [← add_assoc] using hfull)

end Mettapedia.FluidDynamics.NavierStokes.PancakeExchangeSymmetricCurl
