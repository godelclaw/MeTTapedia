import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLowTouchEnergy

/-!
# Physical finite Galerkin velocity energy

The low-source estimate requires kinetic-energy and enstrophy bounds.
This module starts from the physical projected finite velocity equation,
defines its Fourier curl, and derives the energy balance.  The curl inverse
and nonlinear normalization are identified with the existing symbols.

These are a priori estimates on coefficient paths satisfying the finite
equation.  Construction, invariant-subspace preservation, convergence of
those paths, and the high-source misalignment estimate are separate tasks.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeGalerkinKineticEnergy

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeBlockReality PancakeMaterialTransportCommutator
open PancakeSignedTransportEnergy PancakeFrequencyProjectorCommutator
open PancakeViscousMisalignmentAbsorption PancakeSameSectorDissipation PancakeIncomingLowSourceEnergy
open PancakeLowTouchEnergy

/-- Curl in the physical unit-torus normalization. -/
def fourierCurl (u : FourierVelocity) : FourierVelocity :=
  fun k ↦ unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient k) (u k)

theorem cross_cross_wavevector (k : Wavevector) (v : VelocityCoefficient) :
    coefficientCross (wavevectorCoefficient k) (coefficientCross (wavevectorCoefficient k) v) =
      modeDot k v • wavevectorCoefficient k - modeSquare k • v := by
  ext i
  fin_cases i <;>
    simp [coefficientCross, wavevectorCoefficient, modeDot, modeSquare, Fin.sum_univ_three] <;> ring

theorem physicalBiotSavart_fourierCurl (k : Wavevector) (u : FourierVelocity)
    (hk : frequencyVec k ≠ 0) (hu : modeDot k (u k) = 0) :
    unitTorusBiotSavartAmp k (fourierCurl u k) = u k := by
  have hks := modeSquare_ne_zero_of_frequencyVec_ne_zero hk
  unfold unitTorusBiotSavartAmp complexBiotSavartAmp fourierCurl
  rw [coefficientCross_smul_right, cross_cross_wavevector, hu, zero_smul, zero_sub]
  ext i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  field_simp [hks, unitTorusDerivativePhase_ne_zero]

theorem fourierCurl_transverse (k : Wavevector) (u : FourierVelocity) :
    modeDot k (fourierCurl u k) = 0 := by
  simp [fourierCurl, modeDot, coefficientCross, wavevectorCoefficient, Fin.sum_univ_three]
  ring

theorem fourierCurl_real (u : FourierVelocity)
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) :
    ∀ k, fourierCurl u (-k) = coefficientConjugate (fourierCurl u k) := by
  intro k
  unfold fourierCurl
  rw [hr]
  ext i
  fin_cases i <;>
    simp [coefficientCross, coefficientConjugate, wavevectorCoefficient,
      unitTorusDerivativePhase, map_mul, map_sub] <;>
    simp only [starRingEnd_apply, star_ofNat] <;> ring

theorem fourierCurl_energy (k : Wavevector) (u : FourierVelocity)
    (hu : modeDot k (u k) = 0) :
    coefficientEnergy (fourierCurl u k) =
      (2 * Real.pi) ^ 2 * ‖frequencyVec k‖ ^ 2 * coefficientEnergy (u k) := by
  rw [fourierCurl, coefficientEnergy_smul, norm_derivativePhase,
    cross_coefficientEnergy, hu]
  simp only [map_zero, sub_zero]
  ring

theorem hermitian_wavevector_right (q : Wavevector) (u : VelocityCoefficient) :
    coefficientHermitian u (wavevectorCoefficient q) = conj (modeDot q u) := by
  simp only [coefficientHermitian, wavevectorCoefficient, modeDot, map_sum, map_mul,
    map_intCast]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Pressure projection does no work against a transverse velocity mode. -/
theorem hermitian_leray_right (q : Wavevector) (u v : VelocityCoefficient)
    (hu : modeDot q u = 0) :
    coefficientHermitian u (lerayMode q v) = coefficientHermitian u v := by
  by_cases hq : modeSquare q = 0
  · simp [lerayMode, hq]
  · have he : lerayMode q v = v - (modeDot q v / modeSquare q) • wavevectorCoefficient q := by
      ext i
      simp [lerayMode, hq, wavevectorCoefficient]
      ring
    rw [he, coefficientHermitian_sub_right, coefficientHermitian_smul_right,
      hermitian_wavevector_right, hu, map_zero, mul_zero, sub_zero]

theorem lerayMode_smul (q : Wavevector) (a : ℂ) (v : VelocityCoefficient) :
    lerayMode q (a • v) = a • lerayMode q v := by
  by_cases hq : modeSquare q = 0
  · simp [lerayMode, hq]
  · ext i
    simp [lerayMode, hq, modeDot_smul]
    ring

/-- The physical finite velocity equation, using the curl-recovered source
velocity and the existing Fourier Leray projection. -/
def velocityRHS (modes : Finset Wavevector) (u : FourierVelocity) (nu : ℝ)
    (q : Wavevector) : VelocityCoefficient :=
  lerayMode q (finiteUnitTorusNegativeTransportCoeff modes modes (fourierCurl u) u q) +
    unitTorusViscousVorticityCoeff nu u q

/-- Curl recovery reproduces the original velocity convection tensor on
every retained nonzero transverse source mode. -/
theorem finiteTransport_fourierCurl_eq (modes : Finset Wavevector) (u : FourierVelocity)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) (q : Wavevector) :
    finiteUnitTorusNegativeTransportCoeff modes modes (fourierCurl u) u q =
      (-unitTorusDerivativePhase) • convectionConvolution modes u q := by
  classical
  rw [finiteUnitTorusNegativeTransportCoeff_eq_doubleSum]
  unfold convectionConvolution
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hkm
  apply Finset.sum_congr rfl
  intro l hlm
  by_cases he : k + l = q
  · rw [if_pos he, if_pos he, unitTorusNegativeTransportAmp,
      physicalBiotSavart_fourierCurl k u (hk k hkm) (hu k hkm)]
    simp [orderedConvection, smul_smul]
  · simp [he]

/-- Exact identification with the already defined projected nonlinearity,
restoring its omitted positive `2π` factor. -/
theorem velocityRHS_eq_projectedNonlinearity (modes : Finset Wavevector) (u : FourierVelocity)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) (nu : ℝ) (q : Wavevector) :
    velocityRHS modes u nu q =
      (2 * (Real.pi : ℂ)) • projectedNonlinearity modes u q +
        unitTorusViscousVorticityCoeff nu u q := by
  rw [velocityRHS, finiteTransport_fourierCurl_eq modes u hk hu q, lerayMode_smul,
    projectedNonlinearity, smul_smul]
  congr 2
  simp [unitTorusDerivativePhase]

/-- Exact kinetic balance of the physical finite velocity vector field.
Pressure does no work and signed transport cancels before any estimates. -/
theorem velocityRHS_energy_balance (modes : Finset Wavevector) (u : FourierVelocity)
    (nu : ℝ) (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    2 * (∑ q ∈ modes, (coefficientHermitian (u q) (velocityRHS modes u nu q)).re) =
      -2 * nu * fullEnergy modes (fourierCurl u) := by
  have ht := total_transport_energy_zero modes modes (fourierCurl u) u hs (fourierCurl_real u hr)
  have hv : (∑ q ∈ modes,
      (coefficientHermitian (u q) (unitTorusViscousVorticityCoeff nu u q)).re) =
      -nu * fullEnergy modes (fourierCurl u) := by
    calc
      _ = ∑ q ∈ modes, -nu * coefficientEnergy (fourierCurl u q) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [viscous_energy_pair, fourierCurl_energy q u (hu q hq), norm_frequencyVec_sq]
        ring
      _ = _ := by rw [fullEnergy, Finset.mul_sum]
  have hp : (∑ q ∈ modes, (coefficientHermitian (u q) (velocityRHS modes u nu q)).re) =
      (∑ q ∈ modes, (coefficientHermitian (u q)
        (finiteUnitTorusNegativeTransportCoeff modes modes (fourierCurl u) u q)).re) +
      ∑ q ∈ modes, (coefficientHermitian (u q) (unitTorusViscousVorticityCoeff nu u q)).re := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [velocityRHS, hermitian_add_right, hermitian_leray_right q (u q) _ (hu q hq), Complex.add_re]
  rw [hp, ht, hv]
  ring

theorem hasDerivAt_kineticEnergy (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (nu t : ℝ) (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    HasDerivAt (fun tau ↦ fullEnergy modes (u tau))
      (-2 * nu * fullEnergy modes (fourierCurl (u t))) t := by
  have h := HasDerivAt.fun_sum (fun q hq ↦ hasDerivAt_coefficientEnergy
    (fun tau ↦ u tau q) (velocityRHS modes (u t) nu q) t (he q hq))
  have hsum : HasDerivAt (fun tau ↦ fullEnergy modes (u tau))
      (2 * ∑ q ∈ modes, (coefficientHermitian (u t q) (velocityRHS modes (u t) nu q)).re) t := by
    simpa only [fullEnergy, Finset.mul_sum] using h
  rw [velocityRHS_energy_balance modes (u t) nu hs hr hu] at hsum
  exact hsum

theorem sourceKineticEnergy_fourierCurl (modes : Finset Wavevector) (u : FourierVelocity)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    sourceKineticEnergy modes (fourierCurl u) = fullEnergy modes u := by
  apply Finset.sum_congr rfl
  intro k hkm
  rw [physicalBiotSavart_fourierCurl k u (hk k hkm) (hu k hkm)]

theorem continuousOn_fullEnergy (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (domain : Set ℝ)
    (hu : ∀ q ∈ modes, ∀ i, ContinuousOn (fun t ↦ u t q i) domain) :
    ContinuousOn (fun t ↦ fullEnergy modes (u t)) domain := by
  apply continuousOn_finsetSum
  intro q hq
  apply continuousOn_finsetSum
  intro i hi
  exact Complex.continuous_normSq.comp_continuousOn (hu q hq i)

theorem continuousOn_fourierCurl_coefficient (u : ℝ → FourierVelocity)
    (domain : Set ℝ) (q : Wavevector)
    (hu : ∀ i, ContinuousOn (fun t ↦ u t q i) domain) (i : Fin 3) :
    ContinuousOn (fun t ↦ fourierCurl (u t) q i) domain := by
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  fin_cases i <;> dsimp [fourierCurl, coefficientCross] <;> fun_prop

theorem continuousOn_coefficients_of_velocityRHS (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu : ℝ) (domain : Set ℝ)
    (he : ∀ t ∈ domain, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    ∀ q ∈ modes, ∀ i, ContinuousOn (fun t ↦ u t q i) domain := by
  intro q hq i t ht
  exact (he t ht q hq i).continuousAt.continuousWithinAt

theorem continuousOn_enstrophy_of_velocityRHS (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu : ℝ) (domain : Set ℝ)
    (he : ∀ t ∈ domain, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    ContinuousOn (fun t ↦ fullEnergy modes (fourierCurl (u t))) domain := by
  apply continuousOn_fullEnergy
  intro q hq i
  exact continuousOn_fourierCurl_coefficient u domain q
    (continuousOn_coefficients_of_velocityRHS modes u nu domain he q hq) i

/-- The physical energy identity on a finite horizon. Enstrophy
integrability is derived from the coefficient equation, not supplied. -/
theorem integrated_kineticEnergy_identity
    (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (nu T : ℝ) (hT : 0 ≤ T)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    fullEnergy modes (u T) + 2 * nu *
      (∫ t in (0 : ℝ)..T, fullEnergy modes (fourierCurl (u t))) = fullEnergy modes (u 0) := by
  have hcont := continuousOn_enstrophy_of_velocityRHS modes u nu (Set.Icc 0 T) he
  have hE : IntervalIntegrable (fun t ↦ fullEnergy modes (fourierCurl (u t)))
      MeasureTheory.volume 0 T := ContinuousOn.intervalIntegrable_of_Icc hT hcont
  have hi := hE.const_mul (-2 * nu)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_kineticEnergy modes u nu t hs
      (hr t (by simpa [Set.uIcc_of_le hT] using ht))
      (hu t (by simpa [Set.uIcc_of_le hT] using ht))
      (he t (by simpa [Set.uIcc_of_le hT] using ht))) hi
  rw [intervalIntegral.integral_const_mul] at hFTC
  linarith

theorem kineticEnergy_le_initial
    (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (nu T : ℝ) (hnu : 0 ≤ nu) (hT : 0 ≤ T)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    fullEnergy modes (u T) ≤ fullEnergy modes (u 0) := by
  have hb := integrated_kineticEnergy_identity modes u nu T hT hs hr hu he
  have hn : 0 ≤ ∫ t in (0 : ℝ)..T, fullEnergy modes (fourierCurl (u t)) :=
    intervalIntegral.integral_nonneg_of_forall hT (fun t ↦ fullEnergy_nonneg _ _)
  nlinarith [mul_nonneg hnu hn]

theorem enstrophy_integral_le_initial
    (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (nu T : ℝ) (hT : 0 ≤ T)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    2 * nu * (∫ t in (0 : ℝ)..T, fullEnergy modes (fourierCurl (u t))) ≤ fullEnergy modes (u 0) := by
  have hb := integrated_kineticEnergy_identity modes u nu T hT hs hr hu he
  linarith [fullEnergy_nonneg modes (u T)]

theorem kineticEnergy_le_initial_on
    (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (nu T : ℝ) (hnu : 0 ≤ nu)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, fullEnergy modes (u t) ≤ fullEnergy modes (u 0) := by
  intro t ht
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun s hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
  exact kineticEnergy_le_initial modes u nu t hnu ht.1 hs
    (fun s hs ↦ hr s (hsub hs)) (fun s hs ↦ hu s (hsub hs)) (fun s hs ↦ he s (hsub hs))

theorem continuousOn_lowTouchCost_fourierCurl
    (modes : Finset Wavevector) (u : ℝ → FourierVelocity) (theta nu cutoff : ℝ) (domain : Set ℝ)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ t ∈ domain, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ domain, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    ContinuousOn (fun t ↦ lowTouchCost theta nu cutoff modes (fourierCurl (u t))) domain := by
  have hU := continuousOn_fullEnergy modes u domain
    (continuousOn_coefficients_of_velocityRHS modes u nu domain he)
  have hO := continuousOn_enstrophy_of_velocityRHS modes u nu domain he
  have h := (hU.const_mul (4 * ((lowSources cutoff modes).card : ℝ) / (theta * nu))).mul hO
  apply h.congr
  intro t ht
  dsimp only [lowTouchCost, Pi.mul_apply]
  rw [sourceKineticEnergy_fourierCurl modes (u t) hk (hu t ht)]

/-- The low-touch cost budget now follows from a physical velocity path.
No independent kinetic, enstrophy, or cost-integrability budget is assumed.
Existence and preservation of reality/transversality remain separate. -/
theorem lowTouchCost_integral_of_velocityRHS
    (cutoff : ℝ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (theta nu T : ℝ) (htheta : 0 < theta) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    (∫ t in (0 : ℝ)..T, lowTouchCost theta nu cutoff modes (fourierCurl (u t))) ≤
      2 * ((lowSources cutoff modes).card : ℝ) * fullEnergy modes (u 0) ^ 2 / (theta * nu ^ 2) := by
  apply lowTouchCost_integral_le cutoff modes (fun t ↦ fourierCurl (u t)) theta nu T
    (fullEnergy modes (u 0)) htheta hnu hT (fullEnergy_nonneg _ _)
  · intro t ht
    rw [sourceKineticEnergy_fourierCurl modes (u t) hk (hu t ht)]
    exact kineticEnergy_le_initial_on modes u nu T hnu.le hs hr hu he t ht
  · exact ContinuousOn.intervalIntegrable_of_Icc hT
      (continuousOn_lowTouchCost_fourierCurl modes u theta nu cutoff (Set.Icc 0 T) hk hu he)
  · exact ContinuousOn.intervalIntegrable_of_Icc hT
      (continuousOn_enstrophy_of_velocityRHS modes u nu (Set.Icc 0 T) he)
  · exact enstrophy_integral_le_initial modes u nu T hT hs hr hu he

theorem lowTouchCost_integral_fixed_cutoff_of_velocityRHS
    (L : ℕ) (modes : Finset Wavevector) (u : ℝ → FourierVelocity)
    (theta nu T : ℝ) (htheta : 0 < theta) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    (∫ t in (0 : ℝ)..T, lowTouchCost theta nu (L : ℝ) modes (fourierCurl (u t))) ≤
      2 * (2 * (L : ℝ) + 1) ^ 3 * fullEnergy modes (u 0) ^ 2 / (theta * nu ^ 2) := by
  have h := lowTouchCost_integral_of_velocityRHS (L : ℝ) modes u theta nu T htheta hnu hT hk hs hr hu he
  have hc : ((lowSources (L : ℝ) modes).card : ℝ) ≤ (2 * (L : ℝ) + 1) ^ 3 := by
    exact_mod_cast lowSources_card_le L modes
  exact h.trans (by gcongr)

end Mettapedia.FluidDynamics.NavierStokes.PancakeGalerkinKineticEnergy
