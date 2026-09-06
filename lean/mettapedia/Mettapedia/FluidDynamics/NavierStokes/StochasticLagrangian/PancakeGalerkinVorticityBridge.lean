import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeGalerkinKineticEnergy

/-!
# Curl of the physical finite velocity equation

The exchange-symmetric velocity convolution has exactly the curl used by
the finite vorticity equation. Pressure disappears under curl and viscosity
commutes with it. The resulting coefficient-path bridge requires no
independent vorticity evolution hypothesis.

These are identities and a priori estimates for finite coefficient paths;
existence, invariant-subspace preservation, and the high-high estimate are
not asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeGalerkinVorticityBridge

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeBlockReality
open PancakeMaterialTransportCommutator PancakeFrequencyProjectorCommutator
open PancakeIncomingLowSourceEnergy PancakeExchangeSymmetricCurl
open PancakeLowTouchEnergy PancakeGalerkinKineticEnergy
open PancakeViscousMisalignmentAbsorption PancakeSameSectorDissipation

/-- An exchange-symmetric sum sees only the symmetrized pair value. -/
theorem sum_eq_of_swap_pair_identity (pairs : Finset (Wavevector × Wavevector))
    (F G : Wavevector × Wavevector → VelocityCoefficient)
    (hs : ∀ p, p ∈ pairs ↔ p.swap ∈ pairs)
    (hp : ∀ p ∈ pairs, F p + F p.swap = G p + G p.swap) :
    ∑ p ∈ pairs, F p = ∑ p ∈ pairs, G p := by
  have hf : (∑ p ∈ pairs, F p) = ∑ p ∈ pairs, F p.swap :=
    Finset.sum_equiv (Equiv.prodComm Wavevector Wavevector) hs (by intros; rfl)
  have hg : (∑ p ∈ pairs, G p) = ∑ p ∈ pairs, G p.swap :=
    Finset.sum_equiv (Equiv.prodComm Wavevector Wavevector) hs (by intros; rfl)
  have h := Finset.sum_congr rfl hp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← hf, ← hg] at h
  ext i
  have hi := congrFun h i
  simp only [Pi.add_apply] at hi
  linear_combination (1 / 2 : ℂ) * hi

/-- The gradient defect between the velocity and cross-product formulas
cancels after exchanging the two inputs and taking output curl. -/
theorem symmetrized_velocity_curl_pair (k l : Wavevector) (u v : VelocityCoefficient) :
    unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient (k + l))
        (coefficientCross u (unitTorusDerivativePhase •
          coefficientCross (wavevectorCoefficient l) v)) +
      unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient (k + l))
        (coefficientCross v (unitTorusDerivativePhase •
          coefficientCross (wavevectorCoefficient k) u)) =
    unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient (k + l))
        ((-unitTorusDerivativePhase * modeDot l u) • v) +
      unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient (k + l))
        ((-unitTorusDerivativePhase * modeDot k v) • u) := by
  ext i
  fin_cases i <;>
    simp [coefficientCross, wavevectorCoefficient,
      modeDot, Fin.sum_univ_three] <;> ring

theorem curlConvolution_fourierCurl (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector) :
    curlConvolutionCoeff modes modes u (fourierCurl u) q =
      unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient q)
        ((-unitTorusDerivativePhase) • convectionConvolution modes u q) := by
  classical
  let pairs := (modes ×ˢ modes).filter (fun p ↦ p.1 + p.2 = q)
  have hs : ∀ p, p ∈ pairs ↔ p.swap ∈ pairs := by
    intro p
    simp [pairs, add_comm, and_comm]
  rw [curlConvolutionCoeff_eq_pairSum]
  change (∑ p ∈ pairs, _) = _
  calc
    _ = ∑ p ∈ pairs, unitTorusDerivativePhase •
        coefficientCross (wavevectorCoefficient q)
          ((-unitTorusDerivativePhase) • orderedConvection p.1 p.2 u) := by
      apply sum_eq_of_swap_pair_identity pairs _ _ hs
      intro p hp
      have he := (Finset.mem_filter.mp hp).2
      dsimp only [fourierCurl, Prod.swap]
      rw [← he]
      simpa only [orderedConvection, smul_smul] using
        symmetrized_velocity_curl_pair p.1 p.2 (u p.1) (u p.2)
    _ = _ := by
      rw [← Finset.smul_sum, ← cross_sum_right, ← Finset.smul_sum]
      congr 3
      simp [pairs, Finset.sum_filter, Finset.sum_product, convectionConvolution]

/-- The Leray pressure correction is a gradient, also at output zero. -/
theorem cross_leray (q : Wavevector) (v : VelocityCoefficient) :
    coefficientCross (wavevectorCoefficient q) (lerayMode q v) =
      coefficientCross (wavevectorCoefficient q) v := by
  by_cases hq : modeSquare q = 0
  · simp [lerayMode, hq]
  · ext i
    fin_cases i <;> simp [coefficientCross, lerayMode, hq, wavevectorCoefficient] <;> ring

theorem cross_add_right (u v w : VelocityCoefficient) :
    coefficientCross u (v + w) = coefficientCross u v + coefficientCross u w := by
  ext i
  fin_cases i <;> simp [coefficientCross] <;> ring

theorem curl_viscous (u : FourierVelocity) (nu : ℝ) (q : Wavevector) :
    fourierCurl (unitTorusViscousVorticityCoeff nu u) q =
      unitTorusViscousVorticityCoeff nu (fourierCurl u) q := by
  simp only [fourierCurl, unitTorusViscousVorticityCoeff,
    coefficientCross_smul_right, smul_smul]
  congr 1
  ring

theorem physicalVelocity_curlConvolution (modes : Finset Wavevector)
    (u : FourierVelocity) (q : Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    curlConvolutionCoeff modes modes (physicalVelocity (fourierCurl u)) (fourierCurl u) q =
      curlConvolutionCoeff modes modes u (fourierCurl u) q := by
  classical
  unfold curlConvolutionCoeff
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hs : q - l ∈ modes
  · rw [if_pos hs, if_pos hs, physicalVelocity,
      physicalBiotSavart_fourierCurl (q - l) u (hk _ hs) (hu _ hs)]
  · simp [hs]

/-- Exact coefficient-level curl bridge from physical velocity to the
strain-plus-transport vorticity equation. -/
theorem fourierCurl_velocityRHS (modes : Finset Wavevector)
    (u : FourierVelocity) (nu : ℝ) (q : Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u k) = 0) :
    fourierCurl (velocityRHS modes u nu) q =
      finiteUnitTorusVorticityRHS modes modes (fourierCurl u) (fourierCurl u) nu q := by
  have hn := incomingNonlinearCoeff_eq_curl modes (fourierCurl u) q hk
    (fun k _ ↦ fourierCurl_transverse k u)
  rw [physicalVelocity_curlConvolution modes u q hk hu,
    curlConvolution_fourierCurl] at hn
  have hc : fourierCurl (velocityRHS modes u nu) q =
      unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient q)
        ((-unitTorusDerivativePhase) • convectionConvolution modes u q) +
      unitTorusViscousVorticityCoeff nu (fourierCurl u) q := by
    change unitTorusDerivativePhase • coefficientCross (wavevectorCoefficient q)
      (lerayMode q _ + _) = _
    rw [cross_add_right, smul_add, cross_leray,
      finiteTransport_fourierCurl_eq modes u hk hu q]
    congr 1
    exact curl_viscous u nu q
  rw [hc, ← hn]
  simp only [incomingNonlinearCoeff, finiteUnitTorusVorticityRHS,
    finiteUnitTorusNonstretchingCoeff]
  abel

theorem hasDerivAt_fourierCurl (u : ℝ → FourierVelocity) (du : FourierVelocity)
    (t : ℝ) (q : Wavevector)
    (he : ∀ i, HasDerivAt (fun tau ↦ u tau q i) (du q i) t) (i : Fin 3) :
    HasDerivAt (fun tau ↦ fourierCurl (u tau) q i) (fourierCurl du q i) t := by
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  fin_cases i
  · simpa [fourierCurl, coefficientCross] using
      ((h2.const_mul (wavevectorCoefficient q 1)).sub
        (h1.const_mul (wavevectorCoefficient q 2))).const_mul unitTorusDerivativePhase
  · simpa [fourierCurl, coefficientCross] using
      ((h0.const_mul (wavevectorCoefficient q 2)).sub
        (h2.const_mul (wavevectorCoefficient q 0))).const_mul unitTorusDerivativePhase
  · simpa [fourierCurl, coefficientCross] using
      ((h1.const_mul (wavevectorCoefficient q 0)).sub
        (h0.const_mul (wavevectorCoefficient q 1))).const_mul unitTorusDerivativePhase

/-- The vorticity ODE is derived, rather than assumed separately. -/
theorem hasDerivAt_vorticity_of_velocityRHS (modes : Finset Wavevector)
    (u : ℝ → FourierVelocity) (nu t : ℝ) (q : Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ i, HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t)
    (i : Fin 3) :
    HasDerivAt (fun tau ↦ fourierCurl (u tau) q i)
      (finiteUnitTorusVorticityRHS modes modes (fourierCurl (u t)) (fourierCurl (u t)) nu q i) t := by
  have h := hasDerivAt_fourierCurl u (velocityRHS modes (u t) nu) t q he i
  rw [fourierCurl_velocityRHS modes (u t) nu q hk hu] at h
  exact h

theorem misalignedEnergy_deriv_of_velocityRHS
    (cutoff : ℝ) (modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (theta nu t : ℝ) (htheta : 0 < theta) (hnu : 0 < nu)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hu : ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ q ∈ outputs, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    deriv (fun tau ↦ misalignedEnergy outputs (fourierCurl (u tau))) t +
      (2 - theta) * nu * (2 * Real.pi) ^ 2 * misalignedDissipation outputs (fourierCurl (u t)) ≤
        highHighEnergyRate cutoff modes outputs (fourierCurl (u t)) +
          lowTouchCost theta nu cutoff modes (fourierCurl (u t)) := by
  exact misalignedEnergy_deriv_lowTouch_absorption cutoff modes outputs
    (fun tau ↦ fourierCurl (u tau)) theta nu t htheta hnu hk
    (fun k _ ↦ fourierCurl_transverse k (u t))
    (fun q hq i ↦ hasDerivAt_vorticity_of_velocityRHS modes u nu t q hk hu (he q hq) i)

theorem continuous_misalignment_coefficient (q : Wavevector) (i : Fin 3) :
    Continuous (fun w : VelocityCoefficient ↦ misalignmentComponent q w i) := by
  simp only [misalignmentComponent, coherentComponent, coherentScalar,
    coefficientHermitian, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

theorem continuousOn_misalignedField (omega : ℝ → FourierVelocity)
    (domain : Set ℝ) (q : Wavevector)
    (hw : ∀ i, ContinuousOn (fun t ↦ omega t q i) domain) (i : Fin 3) :
    ContinuousOn (fun t ↦ misalignedField (omega t) q i) domain := by
  exact (continuous_misalignment_coefficient q i).comp_continuousOn (continuousOn_pi.mpr hw)

theorem continuousOn_misalignedDissipation (outputs : Finset Wavevector)
    (omega : ℝ → FourierVelocity) (domain : Set ℝ)
    (hw : ∀ q ∈ outputs, ∀ i, ContinuousOn (fun t ↦ omega t q i) domain) :
    ContinuousOn (fun t ↦ misalignedDissipation outputs (omega t)) domain := by
  apply continuousOn_finsetSum
  intro q hq
  apply ContinuousOn.const_mul
  apply continuousOn_finsetSum
  intro i hi
  exact Complex.continuous_normSq.comp_continuousOn
    (continuousOn_misalignedField omega domain q (hw q hq) i)

theorem continuous_incoming_pair (k l : Wavevector) (i : Fin 3) :
    Continuous (fun p : VelocityCoefficient × VelocityCoefficient ↦
      (unitTorusNegativeTransportAmp k l p.1 p.2 + unitTorusStrainStretchAmp k p.1 p.2) i) := by
  fin_cases i <;>
    simp [unitTorusNegativeTransportAmp, unitTorusStrainStretchAmp,
      unitTorusBiotSavartAmp, complexBiotSavartAmp, coefficientDot, modeDot,
      Fin.sum_univ_three, coefficientCross, wavevectorCoefficient,
      Matrix.vecHead, Matrix.vecTail] <;> fun_prop

theorem continuousOn_incomingNonlinearCoeff
    (sources receivers : Finset Wavevector) (omega : ℝ → FourierVelocity)
    (domain : Set ℝ)
    (hs : ∀ k ∈ sources, ∀ i, ContinuousOn (fun t ↦ omega t k i) domain)
    (hr : ∀ k ∈ receivers, ∀ i, ContinuousOn (fun t ↦ omega t k i) domain)
    (q : Wavevector) (i : Fin 3) :
    ContinuousOn (fun t ↦ incomingNonlinearCoeff sources receivers (omega t) (omega t) q i) domain := by
  have hpair : ContinuousOn (fun t ↦
      ∑ p ∈ (sources ×ˢ receivers).filter (fun p ↦ p.1 + p.2 = q),
        (unitTorusNegativeTransportAmp p.1 p.2 (omega t p.1) (omega t p.2) +
          unitTorusStrainStretchAmp p.1 (omega t p.1) (omega t p.2)) i) domain := by
    apply continuousOn_finsetSum
    intro p hp
    have hm := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    have ha : ContinuousOn (fun t ↦ omega t p.1) domain := continuousOn_pi.mpr (hs p.1 hm.1)
    have hb : ContinuousOn (fun t ↦ omega t p.2) domain := continuousOn_pi.mpr (hr p.2 hm.2)
    have hab : ContinuousOn (fun t ↦ (omega t p.1, omega t p.2)) domain := ha.prodMk hb
    have h := (continuous_incoming_pair p.1 p.2 i).comp_continuousOn hab
    exact h
  apply hpair.congr
  intro t ht
  dsimp only
  rw [incomingNonlinearCoeff_eq_pairSum, Finset.sum_apply]

theorem continuousOn_incomingEnergyRate
    (sources receivers outputs : Finset Wavevector) (omega : ℝ → FourierVelocity)
    (domain : Set ℝ)
    (hs : ∀ k ∈ sources, ∀ i, ContinuousOn (fun t ↦ omega t k i) domain)
    (hr : ∀ k ∈ receivers, ∀ i, ContinuousOn (fun t ↦ omega t k i) domain)
    (ho : ∀ k ∈ outputs, ∀ i, ContinuousOn (fun t ↦ omega t k i) domain) :
    ContinuousOn (fun t ↦ incomingEnergyRate sources receivers outputs (omega t) (omega t)) domain := by
  apply ContinuousOn.const_mul
  apply continuousOn_finsetSum
  intro q hq
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_finsetSum
  intro i hi
  exact ((continuousOn_misalignedField omega domain q (ho q hq) i).star).mul
    (continuousOn_incomingNonlinearCoeff sources receivers omega domain hs hr q i)

/-- The high-high remainder estimate for a physical velocity path. All
vorticity evolution, integrability, kinetic-energy, and enstrophy inputs of
the earlier estimate are derived here from the velocity coefficient ODE.
The output set is a subset of the retained modes, not an autonomous system. -/
theorem integrated_highHigh_remainder_of_velocityRHS
    (cutoff : ℝ) (modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (theta nu T : ℝ) (htheta : 0 < theta) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (ho : outputs ⊆ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    misalignedEnergy outputs (fourierCurl (u T)) + (2 - theta) * nu * (2 * Real.pi) ^ 2 *
      (∫ t in (0 : ℝ)..T, misalignedDissipation outputs (fourierCurl (u t))) ≤
        misalignedEnergy outputs (fourierCurl (u 0)) +
          (∫ t in (0 : ℝ)..T, highHighEnergyRate cutoff modes outputs (fourierCurl (u t))) +
          2 * ((lowSources cutoff modes).card : ℝ) * fullEnergy modes (u 0) ^ 2 / (theta * nu ^ 2) := by
  have hc : ∀ q ∈ modes, ∀ i,
      ContinuousOn (fun t ↦ fourierCurl (u t) q i) (Set.Icc (0 : ℝ) T) := by
    intro q hq i
    exact continuousOn_fourierCurl_coefficient u _ q
      (continuousOn_coefficients_of_velocityRHS modes u nu _ he q hq) i
  have hco := fun q hq ↦ hc q (ho hq)
  have hch := fun q (hq : q ∈ highSources cutoff modes) ↦ hc q (Finset.mem_filter.mp hq).1
  have hD := continuousOn_misalignedDissipation outputs (fun t ↦ fourierCurl (u t)) _ hco
  have hI := continuousOn_incomingEnergyRate modes modes outputs
    (fun t ↦ fourierCurl (u t)) _ hc hc hco
  have hH := continuousOn_incomingEnergyRate (highSources cutoff modes) (highSources cutoff modes)
    outputs (fun t ↦ fourierCurl (u t)) _ hch hch hco
  apply integrated_misalignedEnergy_highHigh_remainder cutoff modes outputs
    (fun t ↦ fourierCurl (u t)) theta nu T (fullEnergy modes (u 0)) htheta hnu hT
    (fullEnergy_nonneg _ _) hk
  · exact fun t _ k _ ↦ fourierCurl_transverse k (u t)
  · exact fun t ht q hq i ↦ hasDerivAt_vorticity_of_velocityRHS modes u nu t q hk
      (hu t ht) (he t ht q (ho hq)) i
  · exact ContinuousOn.intervalIntegrable_of_Icc hT (hI.sub (hD.const_mul _))
  · exact ContinuousOn.intervalIntegrable_of_Icc hT hD
  · exact ContinuousOn.intervalIntegrable_of_Icc hT hH
  · exact ContinuousOn.intervalIntegrable_of_Icc hT
      (continuousOn_lowTouchCost_fourierCurl modes u theta nu cutoff _ hk hu he)
  · exact ContinuousOn.intervalIntegrable_of_Icc hT
      (continuousOn_enstrophy_of_velocityRHS modes u nu _ he)
  · intro t ht
    rw [sourceKineticEnergy_fourierCurl modes (u t) hk (hu t ht)]
    exact kineticEnergy_le_initial_on modes u nu T hnu.le hs hr hu he t ht
  · exact enstrophy_integral_le_initial modes u nu T hT hs hr hu he

theorem integrated_highHigh_remainder_fixed_cutoff_of_velocityRHS
    (L : ℕ) (modes outputs : Finset Wavevector) (u : ℝ → FourierVelocity)
    (theta nu T : ℝ) (htheta : 0 < theta) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (hs : ∀ k, -k ∈ modes ↔ k ∈ modes)
    (ho : outputs ⊆ modes)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, u t (-k) = coefficientConjugate (u t k))
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k ∈ modes, modeDot k (u t k) = 0)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ u tau q i) (velocityRHS modes (u t) nu q i) t) :
    misalignedEnergy outputs (fourierCurl (u T)) + (2 - theta) * nu * (2 * Real.pi) ^ 2 *
      (∫ t in (0 : ℝ)..T, misalignedDissipation outputs (fourierCurl (u t))) ≤
        misalignedEnergy outputs (fourierCurl (u 0)) +
          (∫ t in (0 : ℝ)..T, highHighEnergyRate (L : ℝ) modes outputs (fourierCurl (u t))) +
          2 * (2 * (L : ℝ) + 1) ^ 3 * fullEnergy modes (u 0) ^ 2 / (theta * nu ^ 2) := by
  have h := integrated_highHigh_remainder_of_velocityRHS (L : ℝ) modes outputs u
    theta nu T htheta hnu hT hk hs ho hr hu he
  have hc : ((lowSources (L : ℝ) modes).card : ℝ) ≤ (2 * (L : ℝ) + 1) ^ 3 := by
    exact_mod_cast lowSources_card_le L modes
  exact h.trans (by gcongr)

end Mettapedia.FluidDynamics.NavierStokes.PancakeGalerkinVorticityBridge
