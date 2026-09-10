import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteKineticCancellation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeInfiniteFourierTime

/-!
# Initial-data energy budget for the actual local velocity

A common second absolute Fourier-moment envelope justifies differentiation
of the infinite kinetic energy and continuity of the enstrophy. The equation
then supplies the energy identity, including the initial endpoint. The
envelope is used only to justify these operations; its size does not appear
in the resulting budget.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalKineticEnergy

open scoped BigOperators ComplexConjugate
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy PancakeSignedTransportEnergy
open PancakeCurlOutputTail PancakeCoefficientLimitEquation PancakeIndexedFourierMoments
open PancakeLocalInfiniteVelocity PancakeInfiniteVelocityEnvelope
open InfiniteConvectionEnergy InfiniteKineticCancellation

theorem amplitude_le_envelope (u : FourierVelocity) (g : Wavevector → ℝ)
    (hu : ∀ q, fourierMoment 2 u q ≤ g q) (q : Wavevector) :
    ‖coefficientVec (u q)‖ ≤ g q :=
  (amplitude_le_firstMoment u q).trans ((firstMoment_le_second u q).trans (hu q))

theorem curl_amplitude_le_envelope (u : FourierVelocity) (g : Wavevector → ℝ)
    (hu : ∀ q, fourierMoment 2 u q ≤ g q) (q : Wavevector) :
    ‖coefficientVec (fourierCurl u q)‖ ≤ (2 * Real.pi) * g q :=
  (amplitude_le_firstMoment _ q).trans ((firstMoment_curl_le_second u q).trans
    (mul_le_mul_of_nonneg_left (hu q) (by positivity)))

theorem coefficientEnergy_le_envelope (u : FourierVelocity) (g : Wavevector → ℝ)
    (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ q, ‖coefficientVec (u q)‖ ≤ g q) (q : Wavevector) :
    coefficientEnergy (u q) ≤ (∑' k, g k) * g q := by
  rw [← norm_coefficientVec_sq, pow_two]
  exact mul_le_mul ((hu q).trans (hSum.le_tsum q (fun k _ ↦ hg k))) (hu q)
    (norm_nonneg _) (tsum_nonneg hg)

/-- A summable amplitude envelope gives continuity of the full energy. -/
theorem continuousOn_kineticEnergy (u : ℝ → FourierVelocity) (I : Set ℝ)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hc : ∀ q i, ContinuousOn (fun t ↦ u t q i) I)
    (hu : ∀ t ∈ I, ∀ q, ‖coefficientVec (u t q)‖ ≤ g q) :
    ContinuousOn (fun t ↦ kineticEnergy (u t)) I := by
  simp only [kineticEnergy_eq_tsum_coefficientEnergy]
  rw [continuousOn_iff_continuous_restrict]
  have hcont (q : Wavevector) : Continuous (fun t : I ↦ coefficientEnergy (u t q)) := by
    change Continuous (fun t : I ↦ ∑ i : Fin 3, Complex.normSq (u t q i))
    exact continuous_finsetSum _ (fun i _ ↦ Complex.continuous_normSq.comp
      (continuousOn_iff_continuous_restrict.mp (hc q i)))
  apply continuous_tsum hcont (hSum.mul_left (∑' k, g k))
  intro q t
  rw [Real.norm_eq_abs, abs_of_nonneg (by rw [← norm_coefficientVec_sq]; positivity)]
  exact coefficientEnergy_le_envelope _ g hg hSum (hu t t.2) q

theorem continuousOn_energy {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q) :
    ContinuousOn (fun t ↦ kineticEnergy (s.coefficients t)) (Set.Icc (0 : ℝ) T) :=
  continuousOn_kineticEnergy _ _ g hg hSum (fun q i ↦ (s.continuous q i).continuousOn)
    (fun t ht ↦ amplitude_le_envelope _ g (hu t ht))

theorem continuousOn_enstrophy {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q) :
    ContinuousOn (fun t ↦ kineticEnergy (fourierCurl (s.coefficients t)))
      (Set.Icc (0 : ℝ) T) :=
  continuousOn_kineticEnergy _ _ (fun q ↦ (2 * Real.pi) * g q)
    (fun q ↦ mul_nonneg (by positivity) (hg q)) (hSum.mul_left _)
    (fun q ↦ continuousOn_fourierCurl_coefficient _ _ q
      (fun i ↦ (s.continuous q i).continuousOn))
    (fun t ht ↦ curl_amplitude_le_envelope _ g (hu t ht))

/-- The local infinite equation, not a closed truncation, differentiates
the full kinetic energy. -/
theorem hasDerivAt_energy {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun τ ↦ kineticEnergy (s.coefficients τ))
      (-2 * nu * kineticEnergy (fourierCurl (s.coefficients t))) t := by
  have hmoment : Summable (fourierMoment 2 (s.coefficients t)) :=
    hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ⟨ht.1.le, ht.2.le⟩)
  have h := hasDerivAt_tsum_of_isPreconnected
    ((summable_velocityEnvelope nu g hg hSum).mul_left (2 * ∑' k, g k))
    isOpen_Ioo (convex_Ioo (0 : ℝ) T).isPreconnected
    (fun q τ hτ ↦ hasDerivAt_coefficientEnergy (fun r ↦ s.coefficients r q)
      (infiniteVelocityRHS nu (s.coefficients τ) q) τ (s.equation τ hτ q))
    (fun q τ hτ ↦ show ‖2 * (coefficientHermitian (s.coefficients τ q)
        (infiniteVelocityRHS nu (s.coefficients τ) q)).re‖ ≤
          (2 * ∑' k, g k) * velocityEnvelope nu g q from by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      calc
        _ ≤ 2 * (‖coefficientVec (s.coefficients τ q)‖ *
            ‖coefficientVec (infiniteVelocityRHS nu (s.coefficients τ) q)‖) := by
          gcongr
          exact abs_hermitian_re_le _ _
        _ ≤ 2 * ((∑' k, g k) * velocityEnvelope nu g q) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul
            ((amplitude_le_envelope _ g (hu τ ⟨hτ.1.le, hτ.2.le⟩) q).trans
              (hSum.le_tsum q (fun k _ ↦ hg k)))
            (norm_infiniteVelocityRHS_le nu _ g hg hSum (hu τ ⟨hτ.1.le, hτ.2.le⟩) q)
            (norm_nonneg _) (tsum_nonneg hg)
        _ = _ := by ring)
    ht (summable_coefficientEnergy _
      (summable_amplitude _ (summable_firstMoment_of_second _ hmoment))) ht
  simp only [← kineticEnergy_eq_tsum_coefficientEnergy, tsum_mul_left,
    infiniteVelocityRHS_kinetic_balance _ nu hmoment (s.reality t) (s.transverse t)] at h
  exact h

/-- The initial-data budget has no dependence on the common envelope or
the local Sobolev bound. Energy uses the normalization without a factor `1/2`. -/
theorem energy_identity {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    kineticEnergy (s.coefficients t) +
      2 * nu * (∫ τ in (0 : ℝ)..t, kineticEnergy (fourierCurl (s.coefficients τ))) =
        kineticEnergy u₀ := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hcont := (continuousOn_energy s g hg hSum hu).mono hsub
  have hint : IntervalIntegrable (fun τ ↦ kineticEnergy (fourierCurl (s.coefficients τ)))
      volume 0 t := ContinuousOn.intervalIntegrable_of_Icc ht.1
    ((continuousOn_enstrophy s g hg hSum hu).mono hsub)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcont
    (fun τ hτ ↦ hasDerivAt_energy s g hg hSum hu τ ⟨hτ.1, hτ.2.trans_le ht.2⟩)
    (hint.const_mul (-2 * nu))
  rw [intervalIntegral.integral_const_mul, s.initial] at he
  linarith

theorem kineticEnergy_nonneg (u : FourierVelocity) : 0 ≤ kineticEnergy u :=
  tsum_nonneg (fun _ ↦ sq_nonneg _)

theorem energy_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 ≤ nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    kineticEnergy (s.coefficients t) ≤ kineticEnergy u₀ := by
  have he := energy_identity s g hg hSum hu t ht
  have hn : 0 ≤ ∫ τ in (0 : ℝ)..t, kineticEnergy (fourierCurl (s.coefficients τ)) :=
    intervalIntegral.integral_nonneg_of_forall ht.1
    (fun τ ↦ kineticEnergy_nonneg (fourierCurl (s.coefficients τ)))
  nlinarith [mul_nonneg hnu hn]

theorem enstrophy_integral_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    2 * nu * (∫ τ in (0 : ℝ)..t, kineticEnergy (fourierCurl (s.coefficients τ))) ≤
      kineticEnergy u₀ := by
  have he := energy_identity s g hg hSum hu t ht
  linarith [kineticEnergy_nonneg (s.coefficients t)]

/-- Squaring the energy identity pays an energy-weighted enstrophy cost
with the exact factor `4`, without replacing energy by its initial value. -/
theorem energy_sq_identity {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    kineticEnergy (s.coefficients t) ^ 2 + 4 * nu *
      (∫ τ in (0 : ℝ)..t, kineticEnergy (s.coefficients τ) *
        kineticEnergy (fourierCurl (s.coefficients τ))) = kineticEnergy u₀ ^ 2 := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hE := (continuousOn_energy s g hg hSum hu).mono hsub
  have hO := (continuousOn_enstrophy s g hg hSum hu).mono hsub
  have hint : IntervalIntegrable (fun τ ↦ kineticEnergy (s.coefficients τ) *
      kineticEnergy (fourierCurl (s.coefficients τ))) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 (hE.mul hO)
  have hd (τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) t) :
      HasDerivAt (fun r ↦ kineticEnergy (s.coefficients r) ^ 2)
        ((-4 * nu) * (kineticEnergy (s.coefficients τ) *
          kineticEnergy (fourierCurl (s.coefficients τ)))) τ := by
    have hp := (hasDerivAt_energy s g hg hSum hu τ ⟨hτ.1, hτ.2.trans_le ht.2⟩).fun_pow 2
    exact hp.congr_deriv (by norm_num; ring)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hE.pow 2) hd
    (hint.const_mul (-4 * nu))
  rw [intervalIntegral.integral_const_mul, s.initial] at he
  linarith

theorem energy_enstrophy_integral_le_initial {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    4 * nu * (∫ τ in (0 : ℝ)..t, kineticEnergy (s.coefficients τ) *
      kineticEnergy (fourierCurl (s.coefficients τ))) ≤ kineticEnergy u₀ ^ 2 := by
  have he := energy_sq_identity s g hg hSum hu t ht
  nlinarith [sq_nonneg (kineticEnergy (s.coefficients t))]

/-- Any integrable cost bounded by `C * energy * enstrophy` is paid from
initial energy alone. Integrability and domination remain explicit here. -/
theorem integral_le_of_energy_enstrophy_majorant {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients t) q ≤ g q)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (f : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : IntervalIntegrable f volume 0 t)
    (hb : ∀ τ ∈ Set.Icc (0 : ℝ) t, f τ ≤ C *
      (kineticEnergy (s.coefficients τ) * kineticEnergy (fourierCurl (s.coefficients τ)))) :
    (∫ τ in (0 : ℝ)..t, f τ) ≤ C * kineticEnergy u₀ ^ 2 / (4 * nu) := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hi : IntervalIntegrable (fun τ ↦ kineticEnergy (s.coefficients τ) *
      kineticEnergy (fourierCurl (s.coefficients τ))) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1
      (((continuousOn_energy s g hg hSum hu).mul
        (continuousOn_enstrophy s g hg hSum hu)).mono hsub)
  have hm := intervalIntegral.integral_mono_on ht.1 hf (hi.const_mul C) hb
  rw [intervalIntegral.integral_const_mul] at hm
  apply hm.trans
  apply (le_div_iff₀ (by positivity : 0 < 4 * nu)).mpr
  have he := mul_le_mul_of_nonneg_left
    (energy_enstrophy_integral_le_initial s g hg hSum hu t ht) hC
  nlinarith

/-- Physical data construct the solution and the envelope needed above;
no energy inequality is added to the solution interface as an assumption. -/
theorem exists_physical_local_energy_identity (nu : ℝ) (hnu : 0 < nu)
    (f : UnitAddTorus (Fin 3) → VelocityCoefficient)
    (hf : ∀ i, PancakeContinuousCoordinateJet.HasContinuousCoordinateJet 8 (fun x ↦ f x i))
    (hr : ∀ x i, conj (f x i) = f x i)
    (hd : ∀ q, modeDot q (PancakeArbitraryDataBlocks.torusFourierVelocity f q) = 0)
    (hzero : PancakeArbitraryDataBlocks.torusFourierVelocity f 0 = 0) :
    ∃ T > (0 : ℝ), ∃ B ≥ (0 : ℝ),
      ∃ s : LocalInfiniteVelocitySolution nu (PancakeArbitraryDataBlocks.torusFourierVelocity f) T B,
        ∀ t ∈ Set.Icc (0 : ℝ) T, kineticEnergy (s.coefficients t) + 2 * nu *
          (∫ τ in (0 : ℝ)..t, kineticEnergy (fourierCurl (s.coefficients τ))) =
            kineticEnergy (PancakeArbitraryDataBlocks.torusFourierVelocity f) := by
  obtain ⟨T, hT, B, hB, s, g, hg, hSum, hu⟩ :=
    PancakeHigherLocalVelocity.exists_physical_localMomentEnvelope 2 nu hnu f hf hr hd hzero
  exact ⟨T, hT, B, hB, s, energy_identity s g hg hSum hu⟩

end Mettapedia.FluidDynamics.NavierStokes.LocalKineticEnergy
