import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeExchangeSymmetricCurl

/-!
# Low-touch physical vorticity energy

After exchange cancellation, each interaction with at least one low input
has an output derivative. Rectangular Schur estimates may then be used in
either input orientation. The cutoff stays fixed and all receivers remain.
Kinetic-energy and trajectory-realization hypotheses are kept explicit.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLowTouchEnergy

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeBlockReality PancakeArbitraryDataBlocks
open PancakeSignedTransportEnergy PancakeFrequencyProjectorCommutator
open PancakeViscousMisalignmentAbsorption PancakeSameSectorDissipation
open PancakeIncomingLowSourceEnergy PancakeExchangeSymmetricCurl

/-- The complex Lagrange identity uses the Hermitian, not bilinear, dot. -/
theorem complex_cross_energy (u v : VelocityCoefficient) :
    coefficientEnergy (coefficientCross u v) =
      coefficientEnergy u * coefficientEnergy v - Complex.normSq (coefficientHermitian u v) := by
  simp [coefficientEnergy, coefficientCross, coefficientHermitian,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Fin.sum_univ_three]
  ring

theorem norm_complex_cross_le (u v : VelocityCoefficient) :
    ‖coefficientVec (coefficientCross u v)‖ ≤ ‖coefficientVec u‖ * ‖coefficientVec v‖ := by
  have h := complex_cross_energy u v
  rw [← norm_coefficientVec_sq, ← norm_coefficientVec_sq, ← norm_coefficientVec_sq] at h
  nlinarith [Complex.normSq_nonneg (coefficientHermitian u v),
    norm_nonneg (coefficientVec (coefficientCross u v)),
    mul_nonneg (norm_nonneg (coefficientVec u)) (norm_nonneg (coefficientVec v))]

theorem cross_neg_right (u v : VelocityCoefficient) :
    coefficientCross u (-v) = -coefficientCross u v := by
  ext i
  fin_cases i <;> simp [coefficientCross] <;> ring

theorem curlConvolutionCoeff_swap (sources receivers : Finset Wavevector)
    (u v : FourierVelocity) (q : Wavevector) :
    curlConvolutionCoeff sources receivers u v q =
      -curlConvolutionCoeff receivers sources v u q := by
  classical
  rw [curlConvolutionCoeff_eq_pairSum, curlConvolutionCoeff_eq_pairSum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_equiv (Equiv.prodComm Wavevector Wavevector)
  · intro p
    simp [add_comm, and_comm]
  · intro p hp
    dsimp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [cross_swap (u p.1) (v p.2), cross_neg_right, smul_neg, neg_neg]

def curlEnergyRate (sources receivers outputs : Finset Wavevector)
    (u v eta : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ outputs, (coefficientHermitian (misalignedField eta q)
    (curlConvolutionCoeff sources receivers u v q)).re

theorem curlEnergyRate_swap (sources receivers outputs : Finset Wavevector)
    (u v eta : FourierVelocity) :
    curlEnergyRate sources receivers outputs u v eta =
      -curlEnergyRate receivers sources outputs v u eta := by
  unfold curlEnergyRate
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [curlConvolutionCoeff_swap sources receivers u v q]
  simp [coefficientHermitian]

theorem curl_pair_le (sources : Finset Wavevector) (u v eta : FourierVelocity)
    (q l : Wavevector) :
    |(coefficientHermitian (misalignedField eta q)
      (if q - l ∈ sources then unitTorusDerivativePhase •
        coefficientCross (wavevectorCoefficient q) (coefficientCross (u (q - l)) (v l))
        else 0)).re| ≤
      (2 * Real.pi) * sourceWeight sources u q l *
        (‖frequencyVec q‖ * ‖coefficientVec (misalignedField eta q)‖) * ‖coefficientVec (v l)‖ := by
  classical
  by_cases hm : q - l ∈ sources
  · rw [if_pos hm, sourceWeight, if_pos hm]
    have hc := norm_cross_le q (coefficientCross (u (q - l)) (v l))
    have hb := norm_complex_cross_le (u (q - l)) (v l)
    calc
      _ ≤ ‖coefficientVec (misalignedField eta q)‖ *
          ‖coefficientVec (unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient q)
            (coefficientCross (u (q - l)) (v l)))‖ := abs_hermitian_re_le _ _
      _ = ‖coefficientVec (misalignedField eta q)‖ * ((2 * Real.pi) *
          ‖coefficientVec (coefficientCross (wavevectorCoefficient q)
            (coefficientCross (u (q - l)) (v l)))‖) := by
        change _ * ‖unitTorusDerivativePhase • coefficientVec _‖ = _
        rw [norm_smul, norm_derivativePhase]
        rfl
      _ ≤ ‖coefficientVec (misalignedField eta q)‖ * ((2 * Real.pi) *
          (‖frequencyVec q‖ * (‖coefficientVec (u (q - l))‖ * ‖coefficientVec (v l)‖))) := by
        gcongr
        exact hc.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
      _ = _ := by ring
  · simp [hm, sourceWeight, coefficientHermitian]

/-- Either input orientation may serve as the finite Schur source. -/
theorem curlEnergyRate_young (sources receivers outputs : Finset Wavevector)
    (u v eta : FourierVelocity) (r : ℝ) (hr : 0 < r) :
    |curlEnergyRate sources receivers outputs u v eta| ≤
      (2 * Real.pi) * sourceAmplitude sources u *
        (r * misalignedDissipation outputs eta + fullEnergy receivers v / r) := by
  classical
  let f (q l : Wavevector) : ℝ := (coefficientHermitian (misalignedField eta q)
    (if q - l ∈ sources then unitTorusDerivativePhase •
      coefficientCross (wavevectorCoefficient q) (coefficientCross (u (q - l)) (v l)) else 0)).re
  let b (q : Wavevector) : ℝ := ‖frequencyVec q‖ * ‖coefficientVec (misalignedField eta q)‖
  let c (q : Wavevector) : ℝ := ‖coefficientVec (v q)‖
  have hsum : |∑ q ∈ outputs, ∑ l ∈ receivers, f q l| ≤
      (2 * Real.pi) * (∑ q ∈ outputs, ∑ l ∈ receivers, sourceWeight sources u q l * b q * c l) := by
    calc
      _ ≤ ∑ q ∈ outputs, ∑ l ∈ receivers, |f q l| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun q _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ q ∈ outputs, ∑ l ∈ receivers,
          (2 * Real.pi) * sourceWeight sources u q l * b q * c l :=
        Finset.sum_le_sum fun q _ ↦ Finset.sum_le_sum fun l _ ↦ curl_pair_le sources u v eta q l
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro l hl
        ring
  have hschur := rectangular_schur_young outputs receivers (sourceWeight sources u) b c
    (sourceAmplitude sources u) r hr (sourceWeight_nonneg _ _)
    (fun q _ ↦ sum_sourceWeight_row_le sources receivers u q)
    (fun l _ ↦ sum_sourceWeight_column_le sources outputs u l)
  have hb : (∑ q ∈ outputs, b q ^ 2) = misalignedDissipation outputs eta := by
    simp only [b, mul_pow, norm_frequencyVec_sq, norm_coefficientVec_sq, misalignedDissipation]
  have hc : (∑ q ∈ receivers, c q ^ 2) = fullEnergy receivers v := by
    simp [c, fullEnergy, norm_coefficientVec_sq]
  rw [hb, hc] at hschur
  unfold curlEnergyRate
  simp_rw [curlConvolutionCoeff, hermitian_sum_right, Complex.re_sum]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  change 2 * |∑ q ∈ outputs, ∑ l ∈ receivers, f q l| ≤ _
  nlinarith [Real.pi_pos]

theorem curlEnergyRate_absorb (sources receivers outputs : Finset Wavevector)
    (u v eta : FourierVelocity) (theta nu : ℝ) (htheta : 0 < theta) (hnu : 0 < nu) :
    |curlEnergyRate sources receivers outputs u v eta| ≤
      theta * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs eta +
        sourceAmplitude sources u ^ 2 / (theta * nu) * fullEnergy receivers v := by
  have hd : 0 < theta * nu * (2 * Real.pi) ^ 2 := by positivity
  have h := optimize_bilinear_young (|curlEnergyRate sources receivers outputs u v eta|)
    ((2 * Real.pi) * sourceAmplitude sources u) (misalignedDissipation outputs eta)
    (fullEnergy receivers v) (theta * nu * (2 * Real.pi) ^ 2)
    (mul_nonneg (by positivity) (sourceAmplitude_nonneg _ _))
    (misalignedDissipation_nonneg _ _) hd (curlEnergyRate_young sources receivers outputs u v eta)
  have he : ((2 * Real.pi) * sourceAmplitude sources u) ^ 2 /
      (theta * nu * (2 * Real.pi) ^ 2) = sourceAmplitude sources u ^ 2 / (theta * nu) := by
    field_simp [htheta.ne', hnu.ne', Real.pi_ne_zero]
  rw [he] at h
  exact h

theorem sourceAmplitude_sq_le_card_energy (sources : Finset Wavevector) (u : FourierVelocity) :
    sourceAmplitude sources u ^ 2 ≤ (sources.card : ℝ) * fullEnergy sources u := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq sources (fun _ ↦ (1 : ℝ))
    (fun k ↦ ‖coefficientVec (u k)‖)
  simpa [sourceAmplitude, fullEnergy, norm_coefficientVec_sq] using h

theorem fullEnergy_mono {small large : Finset Wavevector} (u : FourierVelocity)
    (h : small ⊆ large) : fullEnergy small u ≤ fullEnergy large u :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun k _ _ ↦ coefficientEnergy_nonneg (u k))

theorem curlEnergyRate_absorb_card (sources receivers outputs : Finset Wavevector)
    (u v eta : FourierVelocity) (theta nu : ℝ) (htheta : 0 < theta) (hnu : 0 < nu) :
    |curlEnergyRate sources receivers outputs u v eta| ≤
      theta * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs eta +
        (sources.card : ℝ) / (theta * nu) * fullEnergy sources u * fullEnergy receivers v := by
  refine (curlEnergyRate_absorb sources receivers outputs u v eta theta nu htheta hnu).trans ?_
  have h := sourceAmplitude_sq_le_card_energy sources u
  have hE := fullEnergy_nonneg receivers v
  calc
    _ ≤ theta * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs eta +
        ((sources.card : ℝ) * fullEnergy sources u) / (theta * nu) * fullEnergy receivers v := by
      gcongr
    _ = _ := by ring

def lowTouchEnergyRate (cutoff : ℝ) (modes outputs : Finset Wavevector)
    (omega : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ outputs, (coefficientHermitian (misalignedField omega q)
    (lowTouchCoeff cutoff modes omega q)).re

def highHighEnergyRate (cutoff : ℝ) (modes outputs : Finset Wavevector)
    (omega : FourierVelocity) : ℝ :=
  incomingEnergyRate (highSources cutoff modes) (highSources cutoff modes) outputs omega omega

theorem lowTouchEnergyRate_eq_curl (cutoff : ℝ) (modes outputs : Finset Wavevector)
    (omega : FourierVelocity) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hw : ∀ k ∈ modes, modeDot k (omega k) = 0) :
    lowTouchEnergyRate cutoff modes outputs omega =
      curlEnergyRate (lowSources cutoff modes) modes outputs (physicalVelocity omega) omega omega +
        curlEnergyRate (highSources cutoff modes) (lowSources cutoff modes) outputs
          (physicalVelocity omega) omega omega := by
  unfold lowTouchEnergyRate curlEnergyRate
  simp_rw [lowTouchCoeff_eq_curl cutoff modes omega _ hk hw, hermitian_add_right,
    Complex.add_re, Finset.sum_add_distrib, mul_add]

theorem incomingEnergyRate_lowTouch_add_highHigh (cutoff : ℝ)
    (modes outputs : Finset Wavevector) (omega : FourierVelocity) :
    incomingEnergyRate modes modes outputs omega omega =
      lowTouchEnergyRate cutoff modes outputs omega + highHighEnergyRate cutoff modes outputs omega := by
  unfold incomingEnergyRate lowTouchEnergyRate highHighEnergyRate
  simp_rw [incomingNonlinearCoeff_lowTouch_add_highHigh cutoff modes omega,
    hermitian_add_right, Complex.add_re, Finset.sum_add_distrib, mul_add]
  rfl

/-- A fixed-cutoff cost uses full physical kinetic energy and enstrophy. -/
def lowTouchCost (theta nu cutoff : ℝ) (modes : Finset Wavevector)
    (omega : FourierVelocity) : ℝ :=
  4 * ((lowSources cutoff modes).card : ℝ) / (theta * nu) *
    sourceKineticEnergy modes omega * fullEnergy modes omega

/-- All interactions touching a low input spend a prescribed fraction of
output diffusion. Neither an output-frequency lower bound nor receiver
confinement is needed. -/
theorem lowTouchEnergyRate_absorb (cutoff : ℝ) (modes outputs : Finset Wavevector)
    (omega : FourierVelocity) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hw : ∀ k ∈ modes, modeDot k (omega k) = 0)
    (theta nu : ℝ) (htheta : 0 < theta) (hnu : 0 < nu) :
    |lowTouchEnergyRate cutoff modes outputs omega| ≤
      theta * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs omega +
        lowTouchCost theta nu cutoff modes omega := by
  let K := lowSources cutoff modes
  let H := highSources cutoff modes
  let u := physicalVelocity omega
  have hK : K ⊆ modes := Finset.filter_subset _ _
  have hH : H ⊆ modes := Finset.filter_subset _ _
  have htheta2 : 0 < theta / 2 := by positivity
  have hOm := fullEnergy_nonneg modes omega
  have hUm := fullEnergy_nonneg modes u
  have hUH := fullEnergy_nonneg H u
  have h1 := curlEnergyRate_absorb_card K modes outputs u omega omega (theta / 2) nu htheta2 hnu
  have h2 := curlEnergyRate_absorb_card K H outputs omega u omega (theta / 2) nu htheta2 hnu
  have h1' : |curlEnergyRate K modes outputs u omega omega| ≤
      (theta / 2) * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs omega +
        2 * (K.card : ℝ) / (theta * nu) * fullEnergy modes u * fullEnergy modes omega := by
    refine h1.trans ?_
    calc
      _ ≤ (theta / 2) * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs omega +
          (K.card : ℝ) / ((theta / 2) * nu) * fullEnergy modes u * fullEnergy modes omega := by
        gcongr
        exact fullEnergy_mono u hK
      _ = _ := by ring
  have h2' : |curlEnergyRate K H outputs omega u omega| ≤
      (theta / 2) * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs omega +
        2 * (K.card : ℝ) / (theta * nu) * fullEnergy modes u * fullEnergy modes omega := by
    refine h2.trans ?_
    calc
      _ ≤ (theta / 2) * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs omega +
          (K.card : ℝ) / ((theta / 2) * nu) * fullEnergy modes omega * fullEnergy modes u := by
        gcongr
        · exact fullEnergy_mono omega hK
        · exact fullEnergy_mono u hH
      _ = _ := by ring
  have he : lowTouchEnergyRate cutoff modes outputs omega =
      curlEnergyRate K modes outputs u omega omega - curlEnergyRate K H outputs omega u omega := by
    rw [lowTouchEnergyRate_eq_curl cutoff modes outputs omega hk hw,
      curlEnergyRate_swap (highSources cutoff modes) (lowSources cutoff modes)]
    rfl
  rw [he]
  calc
    _ ≤ |curlEnergyRate K modes outputs u omega omega| +
        |curlEnergyRate K H outputs omega u omega| := abs_sub _ _
    _ ≤ _ := add_le_add h1' h2'
    _ = _ := by
      change _ = theta * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs omega +
        4 * (K.card : ℝ) / (theta * nu) * fullEnergy modes u * fullEnergy modes omega
      ring

/-- The finite physical vorticity equation leaves only the high-high
channel after low-touch absorption. Choose `theta < 2` for coercivity. -/
theorem misalignedEnergy_deriv_lowTouch_absorption
    (cutoff : ℝ) (modes outputs : Finset Wavevector) (omega : ℝ → FourierVelocity)
    (theta nu t : ℝ) (htheta : 0 < theta) (hnu : 0 < nu)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hw : ∀ k ∈ modes, modeDot k (omega t k) = 0)
    (he : ∀ q ∈ outputs, ∀ i, HasDerivAt (fun tau ↦ omega tau q i)
      (finiteUnitTorusVorticityRHS modes modes (omega t) (omega t) nu q i) t) :
    deriv (fun tau ↦ misalignedEnergy outputs (omega tau)) t +
      (2 - theta) * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs (omega t) ≤
        highHighEnergyRate cutoff modes outputs (omega t) + lowTouchCost theta nu cutoff modes (omega t) := by
  rw [(hasDerivAt_misalignedEnergy_fullReceiver modes modes outputs (omega t) omega nu t he).deriv,
    incomingEnergyRate_lowTouch_add_highHigh cutoff]
  have hb := lowTouchEnergyRate_absorb cutoff modes outputs (omega t) hk hw theta nu htheta hnu
  have ha := le_abs_self (lowTouchEnergyRate cutoff modes outputs (omega t))
  nlinarith

/-- Time accounting depends on a fixed low cutoff and the displayed
kinetic/enstrophy bounds. It does not assume a high-frequency tail estimate. -/
theorem lowTouchCost_integral_le
    (cutoff : ℝ) (modes : Finset Wavevector) (omega : ℝ → FourierVelocity)
    (theta nu T U : ℝ) (htheta : 0 < theta) (hnu : 0 < nu) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hkinetic : ∀ t ∈ Set.Icc (0 : ℝ) T, sourceKineticEnergy modes (omega t) ≤ U)
    (hC : IntervalIntegrable (fun t ↦ lowTouchCost theta nu cutoff modes (omega t))
      MeasureTheory.volume 0 T)
    (hE : IntervalIntegrable (fun t ↦ fullEnergy modes (omega t)) MeasureTheory.volume 0 T)
    (hbudget : 2 * nu * (∫ t in (0 : ℝ)..T, fullEnergy modes (omega t)) ≤ U) :
    (∫ t in (0 : ℝ)..T, lowTouchCost theta nu cutoff modes (omega t)) ≤
      2 * ((lowSources cutoff modes).card : ℝ) * U ^ 2 / (theta * nu ^ 2) := by
  let c : ℝ := 4 * ((lowSources cutoff modes).card : ℝ) / (theta * nu)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) T,
      lowTouchCost theta nu cutoff modes (omega t) ≤ (c * U) * fullEnergy modes (omega t) := by
    intro t ht
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hkinetic t ht) hc)
      (fullEnergy_nonneg _ _)
  have hm := intervalIntegral.integral_mono_on hT hC (hE.const_mul (c * U)) hb
  rw [intervalIntegral.integral_const_mul] at hm
  have hh : (∫ t in (0 : ℝ)..T, fullEnergy modes (omega t)) ≤ U / (2 * nu) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * nu)).mpr
    nlinarith
  calc
    _ ≤ (c * U) * (U / (2 * nu)) :=
      hm.trans (mul_le_mul_of_nonneg_left hh (mul_nonneg hc hU))
    _ = _ := by dsimp [c]; ring

theorem lowTouchCost_integral_le_fixed_cutoff
    (L : ℕ) (modes : Finset Wavevector) (omega : ℝ → FourierVelocity)
    (theta nu T U : ℝ) (htheta : 0 < theta) (hnu : 0 < nu) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hkinetic : ∀ t ∈ Set.Icc (0 : ℝ) T, sourceKineticEnergy modes (omega t) ≤ U)
    (hC : IntervalIntegrable (fun t ↦ lowTouchCost theta nu (L : ℝ) modes (omega t))
      MeasureTheory.volume 0 T)
    (hE : IntervalIntegrable (fun t ↦ fullEnergy modes (omega t)) MeasureTheory.volume 0 T)
    (hbudget : 2 * nu * (∫ t in (0 : ℝ)..T, fullEnergy modes (omega t)) ≤ U) :
    (∫ t in (0 : ℝ)..T, lowTouchCost theta nu (L : ℝ) modes (omega t)) ≤
      2 * (2 * (L : ℝ) + 1) ^ 3 * U ^ 2 / (theta * nu ^ 2) := by
  have h := lowTouchCost_integral_le (L : ℝ) modes omega theta nu T U htheta hnu hT hU
    hkinetic hC hE hbudget
  have hcard : ((lowSources (L : ℝ) modes).card : ℝ) ≤ (2 * (L : ℝ) + 1) ^ 3 := by
    exact_mod_cast lowSources_card_le L modes
  exact h.trans (by gcongr)

/-- Integrate the absolute low-touch flux, including the explicit
viscous payment, with constants independent of outputs and retained support. -/
theorem integrated_lowTouch_absorption
    (cutoff : ℝ) (modes outputs : Finset Wavevector) (omega : ℝ → FourierVelocity)
    (theta nu T U : ℝ) (htheta : 0 < theta) (hnu : 0 < nu) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hw : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (omega t k) = 0)
    (hkinetic : ∀ t ∈ Set.Icc (0 : ℝ) T, sourceKineticEnergy modes (omega t) ≤ U)
    (hI : IntervalIntegrable (fun t ↦ |lowTouchEnergyRate cutoff modes outputs (omega t)|)
      MeasureTheory.volume 0 T)
    (hD : IntervalIntegrable (fun t ↦ misalignedDissipation outputs (omega t))
      MeasureTheory.volume 0 T)
    (hC : IntervalIntegrable (fun t ↦ lowTouchCost theta nu cutoff modes (omega t))
      MeasureTheory.volume 0 T)
    (hE : IntervalIntegrable (fun t ↦ fullEnergy modes (omega t)) MeasureTheory.volume 0 T)
    (hbudget : 2 * nu * (∫ t in (0 : ℝ)..T, fullEnergy modes (omega t)) ≤ U) :
    (∫ t in (0 : ℝ)..T, |lowTouchEnergyRate cutoff modes outputs (omega t)|) ≤
      theta * nu * (2 * Real.pi) ^ 2 * (∫ t in (0 : ℝ)..T, misalignedDissipation outputs (omega t)) +
        2 * ((lowSources cutoff modes).card : ℝ) * U ^ 2 / (theta * nu ^ 2) := by
  have hm := intervalIntegral.integral_mono_on hT hI ((hD.const_mul _).add hC)
    (fun t ht ↦ lowTouchEnergyRate_absorb cutoff modes outputs (omega t) hk (hw t ht)
      theta nu htheta hnu)
  rw [intervalIntegral.integral_add (hD.const_mul _) hC, intervalIntegral.integral_const_mul] at hm
  exact hm.trans (add_le_add le_rfl (lowTouchCost_integral_le cutoff modes omega theta nu T U
    htheta hnu hT hU hkinetic hC hE hbudget))

/-- The complete finite equation, not an autonomous sector equation,
retains the terminal energy and only the actual high-high dynamic remainder. -/
theorem integrated_misalignedEnergy_highHigh_remainder
    (cutoff : ℝ) (modes outputs : Finset Wavevector) (omega : ℝ → FourierVelocity)
    (theta nu T U : ℝ) (htheta : 0 < theta) (hnu : 0 < nu) (hT : 0 ≤ T) (hU : 0 ≤ U)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hw : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (omega t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ outputs, ∀ i,
      HasDerivAt (fun tau ↦ omega tau q i)
        (finiteUnitTorusVorticityRHS modes modes (omega t) (omega t) nu q i) t)
    (hi : IntervalIntegrable (fun t ↦ incomingEnergyRate modes modes outputs (omega t) (omega t) -
      2 * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs (omega t)) MeasureTheory.volume 0 T)
    (hD : IntervalIntegrable (fun t ↦ misalignedDissipation outputs (omega t))
      MeasureTheory.volume 0 T)
    (hHH : IntervalIntegrable (fun t ↦ highHighEnergyRate cutoff modes outputs (omega t))
      MeasureTheory.volume 0 T)
    (hC : IntervalIntegrable (fun t ↦ lowTouchCost theta nu cutoff modes (omega t))
      MeasureTheory.volume 0 T)
    (hE : IntervalIntegrable (fun t ↦ fullEnergy modes (omega t)) MeasureTheory.volume 0 T)
    (hkinetic : ∀ t ∈ Set.Icc (0 : ℝ) T, sourceKineticEnergy modes (omega t) ≤ U)
    (hbudget : 2 * nu * (∫ t in (0 : ℝ)..T, fullEnergy modes (omega t)) ≤ U) :
    misalignedEnergy outputs (omega T) + (2 - theta) * nu * (2 * Real.pi) ^ 2 *
      (∫ t in (0 : ℝ)..T, misalignedDissipation outputs (omega t)) ≤
        misalignedEnergy outputs (omega 0) +
          (∫ t in (0 : ℝ)..T, highHighEnergyRate cutoff modes outputs (omega t)) +
          2 * ((lowSources cutoff modes).card : ℝ) * U ^ 2 / (theta * nu ^ 2) := by
  have h := integrated_energy_inequality _ _ _ _ ((2 - theta) * nu * (2 * Real.pi) ^ 2) T hT
    (fun t ht ↦ hasDerivAt_misalignedEnergy_fullReceiver modes modes outputs (omega t) omega nu t (he t ht))
    hi hD (hHH.add hC) (fun t ht ↦ by
      have hb := misalignedEnergy_deriv_lowTouch_absorption cutoff modes outputs omega
        theta nu t htheta hnu hk (hw t ht) (he t ht)
      rw [(hasDerivAt_misalignedEnergy_fullReceiver modes modes outputs (omega t) omega nu t (he t ht)).deriv] at hb
      exact hb)
  rw [intervalIntegral.integral_add hHH hC] at h
  have hc := lowTouchCost_integral_le cutoff modes omega theta nu T U htheta hnu hT hU
    hkinetic hC hE hbudget
  linarith

end Mettapedia.FluidDynamics.NavierStokes.PancakeLowTouchEnergy
