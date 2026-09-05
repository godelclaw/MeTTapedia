import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeViscousMisalignmentAbsorption

/-!
# Joint same-sector transport and stretching absorption

The physical strain symbol has a frequency-independent bilinear bound.
Pairing against the actual misaligned output and combining with the signed
transport commutator permits joint viscous absorption.  The remaining cost
still involves full receiver energy and the source frequency moment.

All receiver and output modes lie in one fixed identity-frame pancake
sector.  This is not an estimate for incoming cross-sector interactions,
moving frames, or the arbitrary-data time-integrated strain budget.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeSameSectorDissipation

open scoped BigOperators ComplexConjugate
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeBlockReality PancakeMaterialTransportCommutator
open PancakeSignedTransportEnergy PancakeFrequencyProjectorCommutator
open PancakeViscousMisalignmentAbsorption PancakeSquareDyadicSectorProjector PancakeFrameCovariance

/-- The complex Lagrange identity gives the sharp norm bound even when the
source amplitude is not transverse. -/
theorem norm_cross_le (k : Wavevector) (w : VelocityCoefficient) :
    ‖coefficientVec (coefficientCross (wavevectorCoefficient k) w)‖ ≤
      ‖frequencyVec k‖ * ‖coefficientVec w‖ := by
  have h := cross_coefficientEnergy k w
  rw [← norm_coefficientVec_sq, ← norm_coefficientVec_sq] at h
  nlinarith [Complex.normSq_nonneg (modeDot k w),
    norm_nonneg (coefficientVec (coefficientCross (wavevectorCoefficient k) w)),
    mul_nonneg (norm_nonneg (frequencyVec k)) (norm_nonneg (coefficientVec w))]

theorem frequency_mul_norm_biot_le (k : Wavevector) (w : VelocityCoefficient) :
    ‖frequencyVec k‖ * ‖coefficientVec (complexBiotSavartAmp k w)‖ ≤
      ‖coefficientVec w‖ := by
  by_cases hk : frequencyVec k = 0
  · simp [hk]
  · have hkn := norm_pos_iff.mpr hk
    change ‖frequencyVec k‖ * ‖(1 / modeSquare k) •
      coefficientVec (coefficientCross (wavevectorCoefficient k) w)‖ ≤ _
    rw [norm_smul, norm_div, norm_one, norm_modeSquare]
    calc
      _ ≤ ‖frequencyVec k‖ * ((1 / ‖frequencyVec k‖ ^ 2) *
          (‖frequencyVec k‖ * ‖coefficientVec w‖)) := by
        gcongr
        exact norm_cross_le k w
      _ = _ := by field_simp [hkn.ne']

/-- A dimension-only estimate for the bilinear, rather than Hermitian,
coefficient pairing. -/
theorem norm_coefficientDot_le (u v : VelocityCoefficient) :
    ‖coefficientDot u v‖ ≤ 3 * ‖coefficientVec u‖ * ‖coefficientVec v‖ := by
  unfold coefficientDot
  calc
    _ ≤ ∑ i : Fin 3, ‖u i * v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, ‖coefficientVec u‖ * ‖coefficientVec v‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul (norm_coefficient_apply_le u i) (norm_coefficient_apply_le v i)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

/-- Curl inversion cancels the source derivative in the physical strain
symbol.  The zero source frequency is included. -/
theorem norm_physical_strain_le (k : Wavevector) (w v : VelocityCoefficient) :
    ‖coefficientVec (unitTorusStrainStretchAmp k w v)‖ ≤
      3 * ‖coefficientVec w‖ * ‖coefficientVec v‖ := by
  rw [unitTorusStrainStretchAmp_eq_neg_complexStretchAmp]
  change ‖-coefficientVec (complexStretchAmp k w v)‖ ≤ _
  rw [norm_neg]
  let u := complexBiotSavartAmp k w
  change ‖(1 / 2 : ℂ) • (coefficientDot u v • frequencyVec k +
    modeDot k v • coefficientVec u)‖ ≤ _
  rw [norm_smul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  have hd := norm_coefficientDot_le u v
  have hk : ‖modeDot k v‖ ≤ 3 * ‖frequencyVec k‖ * ‖coefficientVec v‖ :=
    norm_coefficientDot_le (wavevectorCoefficient k) v
  calc
    _ ≤ (1 / 2 : ℝ) * (‖coefficientDot u v • frequencyVec k‖ +
        ‖modeDot k v • coefficientVec u‖) := by
      gcongr
      exact norm_add_le _ _
    _ = (1 / 2 : ℝ) * (‖coefficientDot u v‖ * ‖frequencyVec k‖ +
        ‖modeDot k v‖ * ‖coefficientVec u‖) := by simp only [norm_smul]
    _ ≤ (1 / 2 : ℝ) * ((3 * ‖coefficientVec u‖ * ‖coefficientVec v‖) * ‖frequencyVec k‖ +
        (3 * ‖frequencyVec k‖ * ‖coefficientVec v‖) * ‖coefficientVec u‖) := by gcongr
    _ = 3 * (‖frequencyVec k‖ * ‖coefficientVec u‖) * ‖coefficientVec v‖ := by ring
    _ ≤ _ := by
      gcongr
      exact frequency_mul_norm_biot_le k w

/-- Reindex the actual physical convolution by its receiver frequency. -/
theorem finiteStretching_eq_receiverSum
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity) (q : Wavevector) :
    finiteUnitTorusStretchingCoeff sources modes omega eta q =
      ∑ l ∈ modes, if q - l ∈ sources then
        unitTorusStrainStretchAmp (q - l) (omega (q - l)) (eta l) else 0 := by
  classical
  rw [finiteUnitTorusStretchingCoeff_eq_doubleSum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hm : q - l ∈ sources
  · rw [Finset.sum_eq_single (q - l)]
    · simp [hm]
    · intro k hk hne
      have h : k + l ≠ q := by
        intro he
        exact hne (eq_sub_iff_add_eq.mpr he)
      simp [h]
    · exact fun hh ↦ (hh hm).elim
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro k hk
    have h : k + l ≠ q := by
      intro he
      exact hm (eq_sub_iff_add_eq.mpr he ▸ hk)
    simp [h]

theorem stretching_pair_le (sources : Finset Wavevector) (omega eta : FourierVelocity)
    (q l : Wavevector) :
    |(coefficientHermitian (misalignedField eta q)
      (if q - l ∈ sources then
        unitTorusStrainStretchAmp (q - l) (omega (q - l)) (eta l) else 0)).re| ≤
      3 * sourceWeight sources omega q l *
        ‖coefficientVec (misalignedField eta q)‖ * ‖coefficientVec (eta l)‖ := by
  classical
  by_cases hm : q - l ∈ sources
  · rw [if_pos hm, sourceWeight, if_pos hm]
    calc
      _ ≤ ‖coefficientVec (misalignedField eta q)‖ *
          ‖coefficientVec (unitTorusStrainStretchAmp (q - l) (omega (q - l)) (eta l))‖ :=
        abs_hermitian_re_le _ _
      _ ≤ ‖coefficientVec (misalignedField eta q)‖ *
          (3 * ‖coefficientVec (omega (q - l))‖ * ‖coefficientVec (eta l)‖) :=
        mul_le_mul_of_nonneg_left (norm_physical_strain_le _ _ _) (norm_nonneg _)
      _ = _ := by ring
  · simp [hm, sourceWeight, coefficientHermitian]

/-- Stretching retains the projected output amplitude, with no shell or
reality hypothesis required for this bilinear estimate. -/
theorem stretchingEnergyRate_young
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (r : ℝ) (hrpos : 0 < r) :
    |stretchingEnergyRate sources modes omega eta| ≤
      3 * sourceAmplitude sources omega *
        (r * misalignedEnergy modes eta + fullEnergy modes eta / r) := by
  classical
  let f (q l : Wavevector) : ℝ :=
    (coefficientHermitian (misalignedField eta q)
      (if q - l ∈ sources then
        unitTorusStrainStretchAmp (q - l) (omega (q - l)) (eta l) else 0)).re
  let b (q : Wavevector) : ℝ := ‖coefficientVec (misalignedField eta q)‖
  let c (q : Wavevector) : ℝ := ‖coefficientVec (eta q)‖
  have hsum : |∑ q ∈ modes, ∑ l ∈ modes, f q l| ≤
      3 * (∑ q ∈ modes, ∑ l ∈ modes, sourceWeight sources omega q l * b q * c l) := by
    calc
      _ ≤ ∑ q ∈ modes, ∑ l ∈ modes, |f q l| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun q _ ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ q ∈ modes, ∑ l ∈ modes, 3 * sourceWeight sources omega q l * b q * c l :=
        Finset.sum_le_sum fun q _ ↦ Finset.sum_le_sum fun l _ ↦ stretching_pair_le sources omega eta q l
      _ = _ := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro l hl
        ring
  have hschur := finite_schur_bilinear_young modes (sourceWeight sources omega)
    b c (sourceAmplitude sources omega) r hrpos (sourceWeight_nonneg sources omega)
    (fun q _ ↦ sum_sourceWeight_row_le sources modes omega q)
    (fun l _ ↦ sum_sourceWeight_column_le sources modes omega l)
  have hb : (∑ q ∈ modes, b q ^ 2) = misalignedEnergy modes eta := by
    simp [b, misalignedEnergy, fullEnergy, norm_coefficientVec_sq]
  have hc : (∑ q ∈ modes, c q ^ 2) = fullEnergy modes eta := by
    simp [c, fullEnergy, norm_coefficientVec_sq]
  rw [hb, hc] at hschur
  unfold stretchingEnergyRate
  simp_rw [finiteStretching_eq_receiverSum, hermitian_sum_right, Complex.re_sum]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  change 2 * |∑ q ∈ modes, ∑ l ∈ modes, f q l| ≤ _
  nlinarith

/-- Both nonlinear channels are estimated with the same balancing
parameter, so the physical diffusion is spent only once. -/
theorem nonlinearEnergyRate_young
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (r : ℝ) (hrpos : 0 < r) :
    |transportEnergyRate sources modes omega eta| + |stretchingEnergyRate sources modes omega eta| ≤
      387 * sourceAmplitude sources omega *
        (r * misalignedEnergy modes eta + fullEnergy modes eta / r) := by
  have ht := transportEnergyRate_young hN sources modes omega eta hs hr hmode r hrpos
  have hst := stretchingEnergyRate_young sources modes omega eta r hrpos
  nlinarith

/-- The cost after jointly absorbing transport and stretching. -/
def jointSourceCost (N : ℕ) (nu : ℝ) (sources modes : Finset Wavevector)
    (omega eta : FourierVelocity) : ℝ :=
  (387 * sourceAmplitude sources omega) ^ 2 /
    (nu * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4) * fullEnergy modes eta

/-- Half the physical diffusion remains after controlling both nonlinear
same-sector channels. -/
theorem totalEnergyRate_joint_absorption
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (nu : ℝ) (hnu : 0 < nu) :
    totalEnergyRate nu sources modes omega eta +
      nu * (2 * Real.pi) ^ 2 * misalignedDissipation modes eta ≤
        jointSourceCost N nu sources modes omega eta := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : 0 < nu * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4 := by positivity
  have hb := optimize_bilinear_young
    (|transportEnergyRate sources modes omega eta| + |stretchingEnergyRate sources modes omega eta|)
    (387 * sourceAmplitude sources omega) (misalignedEnergy modes eta) (fullEnergy modes eta)
    (nu * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4)
    (mul_nonneg (by norm_num) (sourceAmplitude_nonneg _ _)) (misalignedEnergy_nonneg _ _) hd
    (nonlinearEnergyRate_young hN sources modes omega eta hs hr hmode)
  have hc := mul_le_mul_of_nonneg_left (misalignedDissipation_ge_shell hN modes eta hmode)
    (show 0 ≤ nu * (2 * Real.pi) ^ 2 by positivity)
  have ht := le_abs_self (transportEnergyRate sources modes omega eta)
  have hst := le_abs_self (stretchingEnergyRate sources modes omega eta)
  unfold totalEnergyRate jointSourceCost
  nlinarith

/-- The absorption bound applies to the derivative of the actual finite
misalignment energy under the physical coefficient equation. -/
theorem misalignedEnergy_deriv_joint_absorption
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector) (omega : FourierVelocity)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ k, omega (-k) = coefficientConjugate (omega k))
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (eta : ℝ → FourierVelocity) (nu t : ℝ) (hnu : 0 < nu)
    (he : ∀ q ∈ modes, ∀ i, HasDerivAt (fun tau ↦ eta tau q i)
      (finiteUnitTorusVorticityRHS sources modes omega (eta t) nu q i) t) :
    deriv (fun tau ↦ misalignedEnergy modes (eta tau)) t +
      nu * (2 * Real.pi) ^ 2 * misalignedDissipation modes (eta t) ≤
        jointSourceCost N nu sources modes omega (eta t) := by
  rw [(hasDerivAt_misalignedEnergy_rhs sources modes omega hs hr eta nu t he).deriv]
  exact totalEnergyRate_joint_absorption hN sources modes omega (eta t) hs hr hmode nu hnu

theorem integrated_joint_absorption
    {N : ℕ} (hN : 2 ≤ N) (sources modes : Finset Wavevector)
    (omega eta : ℝ → FourierVelocity) (nu T : ℝ) (hnu : 0 < nu) (hT : 0 ≤ T)
    (hs : ∀ k, -k ∈ sources ↔ k ∈ sources)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k, omega t (-k) = coefficientConjugate (omega t k))
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (he : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ modes, ∀ i,
      HasDerivAt (fun tau ↦ eta tau q i)
        (finiteUnitTorusVorticityRHS sources modes (omega t) (eta t) nu q i) t)
    (hi : IntervalIntegrable (fun t ↦ totalEnergyRate nu sources modes (omega t) (eta t))
      MeasureTheory.volume 0 T)
    (hD : IntervalIntegrable (fun t ↦ misalignedDissipation modes (eta t)) MeasureTheory.volume 0 T)
    (hF : IntervalIntegrable (fun t ↦ jointSourceCost N nu sources modes (omega t) (eta t))
      MeasureTheory.volume 0 T) :
    misalignedEnergy modes (eta T) + nu * (2 * Real.pi) ^ 2 *
        (∫ t in (0 : ℝ)..T, misalignedDissipation modes (eta t)) ≤
      misalignedEnergy modes (eta 0) + ∫ t in (0 : ℝ)..T,
        jointSourceCost N nu sources modes (omega t) (eta t) :=
  integrated_energy_inequality _ _ _ _ _ _ hT
    (fun t ht ↦ hasDerivAt_misalignedEnergy_rhs sources modes (omega t) hs (hr t ht) eta nu t (he t ht))
    hi hD hF
    (fun t ht ↦ totalEnergyRate_joint_absorption hN sources modes (omega t) (eta t)
      hs (hr t ht) hmode nu hnu)

theorem sourceKineticEnergy_nonneg (sources : Finset Wavevector) (omega : FourierVelocity) :
    0 ≤ sourceKineticEnergy sources omega := by
  apply Finset.sum_nonneg
  intro k hk
  exact PancakeArbitraryDataBlocks.coefficientEnergy_nonneg _

/-- The actual shell upper bound converts full receiver vorticity energy
into the kinetic energy of its physical Biot--Savart velocity. -/
theorem fullEnergy_le_shell_kinetic
    {N : ℕ} (hN : 2 ≤ N) (modes : Finset Wavevector) (eta : FourierVelocity)
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (hw : ∀ q ∈ modes, modeDot q (eta q) = 0) :
    fullEnergy modes eta ≤
      4 * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4 * sourceKineticEnergy modes eta := by
  unfold fullEnergy sourceKineticEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hq0, _, _, hhi⟩ := pancake_frequency_bounds hN q (hmode q hq)
  have hf : ‖frequencyVec q‖ ^ 2 ≤ 4 * (N : ℝ) ^ 4 := by
    nlinarith [norm_nonneg (frequencyVec q), sq_nonneg (N : ℝ)]
  rw [← physicalBiotSavart_energy_identity q (eta q) hq0 (hw q hq)]
  have he := PancakeArbitraryDataBlocks.coefficientEnergy_nonneg
    (unitTorusBiotSavartAmp q (eta q))
  nlinarith [mul_le_mul_of_nonneg_right hf
    (mul_nonneg (sq_nonneg (2 * Real.pi)) he)]

/-- Receiver curl inversion cancels the entire shell factor in the
absorbed nonlinear cost. -/
theorem jointSourceCost_le_receiverKinetic
    {N : ℕ} (hN : 2 ≤ N) (nu : ℝ) (hnu : 0 < nu)
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (hw : ∀ q ∈ modes, modeDot q (eta q) = 0) :
    jointSourceCost N nu sources modes omega eta ≤
      4 * 387 ^ 2 * sourceAmplitude sources omega ^ 2 / nu * sourceKineticEnergy modes eta := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : 0 ≤ (387 * sourceAmplitude sources omega) ^ 2 /
      (nu * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4) := by positivity
  unfold jointSourceCost
  calc
    _ ≤ (387 * sourceAmplitude sources omega) ^ 2 /
        (nu * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4) *
        (4 * (2 * Real.pi) ^ 2 * (N : ℝ) ^ 4 * sourceKineticEnergy modes eta) :=
      mul_le_mul_of_nonneg_left (fullEnergy_le_shell_kinetic hN modes eta hmode hw) hd
    _ = _ := by field_simp [hnu.ne', hn.ne', Real.pi_ne_zero]

/-- Both amplitudes now enter through physical velocity energy.  Only the
explicit source-set moment prevents this from being cutoff-uniform. -/
theorem jointSourceCost_le_kinetic
    {N : ℕ} (hN : 2 ≤ N) (nu : ℝ) (hnu : 0 < nu)
    (sources modes : Finset Wavevector) (omega eta : FourierVelocity)
    (hmode : ∀ q ∈ modes, InOrientedSquarePancakeConeAnnulus identityFrame N q)
    (hw : ∀ q ∈ modes, modeDot q (eta q) = 0)
    (hk : ∀ k ∈ sources, frequencyVec k ≠ 0)
    (hsource : ∀ k ∈ sources, modeDot k (omega k) = 0) :
    jointSourceCost N nu sources modes omega eta ≤
      4 * 387 ^ 2 * (2 * Real.pi) ^ 2 * sourceFrequencyMoment sources / nu *
        sourceKineticEnergy sources omega * sourceKineticEnergy modes eta := by
  calc
    _ ≤ 4 * 387 ^ 2 * sourceAmplitude sources omega ^ 2 / nu * sourceKineticEnergy modes eta :=
      jointSourceCost_le_receiverKinetic hN nu hnu sources modes omega eta hmode hw
    _ ≤ 4 * 387 ^ 2 * ((2 * Real.pi) ^ 2 * sourceFrequencyMoment sources *
        sourceKineticEnergy sources omega) / nu * sourceKineticEnergy modes eta := by
      apply mul_le_mul_of_nonneg_right _ (sourceKineticEnergy_nonneg _ _)
      exact (div_le_div_iff_of_pos_right hnu).mpr
        (mul_le_mul_of_nonneg_left (sourceAmplitude_sq_le_kinetic sources omega hk hsource) (by positivity))
    _ = _ := by ring

/-- Disjoint receiver sectors spend the physical receiver energy only
once.  The source set is fixed across the sum; its moment is not removed. -/
theorem sum_jointSourceCost_le_kinetic
    {ι : Type*} (sectors : Finset ι) (scale : ι → ℕ) (modes : ι → Finset Wavevector)
    (hscale : ∀ j ∈ sectors, 2 ≤ scale j)
    (hdisjoint : (sectors : Set ι).PairwiseDisjoint modes)
    (nu : ℝ) (hnu : 0 < nu) (sources : Finset Wavevector) (omega eta : FourierVelocity)
    (hmode : ∀ j ∈ sectors, ∀ q ∈ modes j,
      InOrientedSquarePancakeConeAnnulus identityFrame (scale j) q)
    (hw : ∀ j ∈ sectors, ∀ q ∈ modes j, modeDot q (eta q) = 0)
    (hk : ∀ k ∈ sources, frequencyVec k ≠ 0)
    (hsource : ∀ k ∈ sources, modeDot k (omega k) = 0) :
    (∑ j ∈ sectors, jointSourceCost (scale j) nu sources (modes j) omega eta) ≤
      4 * 387 ^ 2 * (2 * Real.pi) ^ 2 * sourceFrequencyMoment sources / nu *
        sourceKineticEnergy sources omega * sourceKineticEnergy (sectors.biUnion modes) eta := by
  classical
  have he : sourceKineticEnergy (sectors.biUnion modes) eta =
      ∑ j ∈ sectors, sourceKineticEnergy (modes j) eta := by
    unfold sourceKineticEnergy
    exact Finset.sum_biUnion hdisjoint
  rw [he, Finset.mul_sum]
  exact Finset.sum_le_sum fun j hj ↦ jointSourceCost_le_kinetic
    (hscale j hj) nu hnu sources (modes j) omega eta (hmode j hj) (hw j hj) hk hsource

end Mettapedia.FluidDynamics.NavierStokes.PancakeSameSectorDissipation
