import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalRetainedEnergyBudget

/-!
# Actual high-high remainder after absorbing every low-touch interaction

The exchange-symmetric curl estimate absorbs interactions with a low input
in either slot. Initial kinetic energy pays their time integral through
the actual energy-squared identity. The remaining signed work is high-high
plus all unresolved-input feedback, not high-high alone.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalHighHighEnergyBudget

open scoped BigOperators
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open PancakeGalerkinVorticityBridge PancakeIncomingLowSourceEnergy PancakeLowTouchEnergy
open PancakeViscousMisalignmentAbsorption PancakeLocalInfiniteVelocity
open InfiniteFilteredEquation LocalFilteredVorticity LocalRetainedEnergyBudget
open LocalLowFrequencyBudget LocalKineticEnergy InfiniteConvectionEnergy
open InfiniteKineticCancellation PancakeCurlOutputTail

theorem lowTouchCost_le_energy_enstrophy (theta nu cutoff : ℝ)
    (htheta : 0 < theta) (hnu : 0 < nu) (modes : Finset Wavevector) (u : FourierVelocity)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0) (hd : ∀ k, modeDot k (u k) = 0)
    (hu : Summable (fourierMoment 2 u)) :
    lowTouchCost theta nu cutoff modes (fourierCurl u) ≤
      (4 * ((lowSources cutoff modes).card : ℝ) / (theta * nu)) *
        (kineticEnergy u * kineticEnergy (fourierCurl u)) := by
  rw [lowTouchCost, sourceKineticEnergy_fourierCurl modes u hk (fun k _ ↦ hd k)]
  have he := fullEnergy_le_kineticEnergy modes u
    (summable_coefficientEnergy u (summable_amplitude u (summable_firstMoment_of_second u hu)))
  have hw := fullEnergy_le_kineticEnergy modes (fourierCurl u) (summable_curlEnergy u hu)
  have hc : 0 ≤ 4 * ((lowSources cutoff modes).card : ℝ) / (theta * nu) := by positivity
  calc
    _ ≤ (4 * ((lowSources cutoff modes).card : ℝ) / (theta * nu) * kineticEnergy u) *
        kineticEnergy (fourierCurl u) :=
      mul_le_mul (mul_le_mul_of_nonneg_left he hc) hw (fullEnergy_nonneg _ _)
        (mul_nonneg hc (kineticEnergy_nonneg u))
    _ = _ := by ring

variable {nu T B : ℝ} {u₀ : FourierVelocity}

theorem continuousOn_lowTouchCost (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (theta cutoff : ℝ) (modes : Finset Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0) :
    ContinuousOn (fun t ↦ lowTouchCost theta nu cutoff modes (fourierCurl (s.coefficients t)))
      (Set.Icc (0 : ℝ) T) := by
  have he : (fun t ↦ lowTouchCost theta nu cutoff modes (fourierCurl (s.coefficients t))) =
      fun t ↦ (4 * ((lowSources cutoff modes).card : ℝ) / (theta * nu)) *
        fullEnergy modes (s.coefficients t) * fullEnergy modes (fourierCurl (s.coefficients t)) := by
    funext t
    rw [lowTouchCost, sourceKineticEnergy_fourierCurl modes _ hk (fun k _ ↦ s.transverse t k)]
  rw [he]
  exact (continuousOn_const.mul (continuousOn_fullEnergy modes _ _
    (fun q _ i ↦ (s.continuous q i).continuousOn))).mul
    (continuousOn_fullEnergy modes _ _ (fun q _ ↦
      continuousOn_fourierCurl_coefficient _ _ q (fun i ↦ (s.continuous q i).continuousOn)))

/-- Every low-touch interaction is paid, including high-source/low-receiver
interactions. The energy-squared identity improves the separated payment
by a factor two. -/
theorem lowTouchCost_integral_le_initial (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (theta cutoff : ℝ) (htheta : 0 < theta) (hnu : 0 < nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (modes : Finset Wavevector) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∫ τ in (0 : ℝ)..t, lowTouchCost theta nu cutoff modes (fourierCurl (s.coefficients τ))) ≤
      ((lowSources cutoff modes).card : ℝ) * kineticEnergy u₀ ^ 2 / (theta * nu ^ 2) := by
  have hi : IntervalIntegrable (fun τ ↦
      lowTouchCost theta nu cutoff modes (fourierCurl (s.coefficients τ))) volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1
    ((continuousOn_lowTouchCost s theta cutoff modes hk).mono
      (fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩))
  have h := integral_le_of_energy_enstrophy_majorant s hnu g hg hSum hu t ht _
    (4 * ((lowSources cutoff modes).card : ℝ) / (theta * nu)) (by positivity) hi
    (fun τ hτ ↦ lowTouchCost_le_energy_enstrophy theta nu cutoff htheta hnu modes _ hk
      (s.transverse τ) (hSum.of_nonneg_of_le (fourierMoment_nonneg _ _)
        (hu τ ⟨hτ.1, hτ.2.trans ht.2⟩)))
  convert h using 1
  ring

/-- The unpaid part of the actual equation after both low input slots
have been absorbed. The subgrid work is still signed and still present. -/
def highHighRemainderRate (cutoff : ℝ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) : ℝ :=
  highHighEnergyRate cutoff modes outputs (fourierCurl u) +
    sectorSourceWork outputs (fourierCurl u) (subgridCurl (sharpFilter modes) u)

theorem continuousOn_highHighRemainderRate (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hB : 0 ≤ B) (cutoff : ℝ) (modes outputs : Finset Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0) (ho : outputs ⊆ modes) :
    ContinuousOn (fun t ↦ highHighRemainderRate cutoff modes outputs (s.coefficients t))
      (Set.Icc (0 : ℝ) T) := by
  have hc (q : Wavevector) (i : Fin 3) :
      ContinuousOn (fun t ↦ fourierCurl (s.coefficients t) q i) (Set.Icc (0 : ℝ) T) :=
    continuousOn_fourierCurl_coefficient _ _ q (fun j ↦ (s.continuous q j).continuousOn) i
  exact (continuousOn_incomingEnergyRate _ _ _ _ _
    (fun q _ ↦ hc q) (fun q _ ↦ hc q) (fun q _ ↦ hc q)).add
      (continuousOn_sectorSourceWork outputs _ _ _ (fun q _ ↦ hc q)
        (fun q hq ↦ continuousOn_subgridCurl s hB modes hk q (ho hq)))

/-- A high-high remainder inequality for the actual infinite solution.
Choose `theta < 2` to retain positive output dissipation. Neither a
source/output frequency ordering nor confinement of receivers is assumed. -/
theorem integrated_highHigh_remainder (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hB : 0 ≤ B) (theta cutoff : ℝ) (htheta : 0 < theta) (hnu : 0 < nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (modes outputs : Finset Wavevector) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (ho : outputs ⊆ modes) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    misalignedEnergy outputs (fourierCurl (s.coefficients t)) +
      (2 - theta) * nu * (2 * Real.pi)^2 *
        (∫ τ in (0 : ℝ)..t, misalignedDissipation outputs (fourierCurl (s.coefficients τ))) ≤
      misalignedEnergy outputs (fourierCurl u₀) +
        (∫ τ in (0 : ℝ)..t, highHighRemainderRate cutoff modes outputs (s.coefficients τ)) +
        ((lowSources cutoff modes).card : ℝ) * kineticEnergy u₀ ^ 2 / (theta * nu ^ 2) := by
  let w := fun τ ↦ fourierCurl (s.coefficients τ)
  let E := fun τ ↦ misalignedEnergy outputs (w τ)
  let D := fun τ ↦ misalignedDissipation outputs (w τ)
  let I := fun τ ↦ incomingEnergyRate modes modes outputs (w τ) (w τ)
  let F := fun τ ↦ sectorSourceWork outputs (w τ) (subgridCurl (sharpFilter modes) (s.coefficients τ))
  let R := fun τ ↦ highHighRemainderRate cutoff modes outputs (s.coefficients τ)
  let L := fun τ ↦ lowTouchCost theta nu cutoff modes (w τ)
  let c := nu * (2 * Real.pi)^2
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T :=
    fun _ hτ ↦ ⟨hτ.1, hτ.2.trans ht.2⟩
  have hc (q : Wavevector) (i : Fin 3) : ContinuousOn (fun τ ↦ w τ q i) (Set.Icc (0 : ℝ) t) :=
    continuousOn_fourierCurl_coefficient _ _ q (fun j ↦ (s.continuous q j).continuousOn) i
  have hE : ContinuousOn E (Set.Icc (0 : ℝ) t) :=
    continuousOn_fullEnergy outputs _ _
      (fun q _ ↦ continuousOn_misalignedField w _ q (hc q))
  have hD : IntervalIntegrable D volume 0 t := ContinuousOn.intervalIntegrable_of_Icc ht.1
    (continuousOn_misalignedDissipation outputs w _ (fun q _ ↦ hc q))
  have hI : IntervalIntegrable I volume 0 t := ContinuousOn.intervalIntegrable_of_Icc ht.1
    (continuousOn_incomingEnergyRate modes modes outputs w _
      (fun q _ ↦ hc q) (fun q _ ↦ hc q) (fun q _ ↦ hc q))
  have hF : IntervalIntegrable F volume 0 t := ContinuousOn.intervalIntegrable_of_Icc ht.1
    (continuousOn_sectorSourceWork outputs w _ _ (fun q _ ↦ hc q)
      (fun q hq i ↦ (continuousOn_subgridCurl s hB modes hk q (ho hq) i).mono hsub))
  have hR : IntervalIntegrable R volume 0 t := ContinuousOn.intervalIntegrable_of_Icc ht.1
    ((continuousOn_highHighRemainderRate s hB cutoff modes outputs hk ho).mono hsub)
  have hL : IntervalIntegrable L volume 0 t := ContinuousOn.intervalIntegrable_of_Icc ht.1
    ((continuousOn_lowTouchCost s theta cutoff modes hk).mono hsub)
  have hd (τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) t) :
      HasDerivAt E (I τ - 2 * c * D τ + F τ) τ := by
    simpa only [E, I, D, F, w, c, mul_assoc] using
      hasDerivAt_retained_misalignedEnergy s modes outputs hk ho τ ⟨hτ.1, hτ.2.trans_le ht.2⟩
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hE hd
    ((hI.sub (hD.const_mul (2 * c))).add hF)
  have hb := intervalIntegral.integral_mono_on_of_le_Ioo ht.1
    ((hI.sub (hD.const_mul (2 * c))).add hF)
    ((hR.add hL).sub (hD.const_mul ((2-theta)*c)))
    (fun τ _ ↦ show I τ - 2 * c * D τ + F τ ≤ R τ + L τ - (2-theta)*c * D τ from by
      have h := lowTouchEnergyRate_absorb cutoff modes outputs (w τ) hk
        (fun k _ ↦ fourierCurl_transverse k (s.coefficients τ)) theta nu htheta hnu
      have ha := le_abs_self (lowTouchEnergyRate cutoff modes outputs (w τ))
      have hi : I τ = lowTouchEnergyRate cutoff modes outputs (w τ) +
          highHighEnergyRate cutoff modes outputs (w τ) :=
        incomingEnergyRate_lowTouch_add_highHigh cutoff modes outputs (w τ)
      dsimp only [R, L, F, D, c, highHighRemainderRate, w] at *
      nlinarith)
  rw [he, intervalIntegral.integral_sub (hR.add hL) (hD.const_mul ((2-theta)*c)),
    intervalIntegral.integral_add hR hL, intervalIntegral.integral_const_mul] at hb
  have hl := lowTouchCost_integral_le_initial s theta cutoff htheta hnu g hg hSum hu modes hk t ht
  change (∫ τ in (0 : ℝ)..t, L τ) ≤ _ at hl
  have he0 : E 0 = misalignedEnergy outputs (fourierCurl u₀) := by
    dsimp only [E, w]
    rw [s.initial]
  rw [he0] at hb
  change E t + (2-theta) * nu * (2 * Real.pi)^2 * (∫ τ in (0 : ℝ)..t, D τ) ≤ _
  change E t - misalignedEnergy outputs (fourierCurl u₀) ≤
    (∫ τ in (0 : ℝ)..t, R τ) + (∫ τ in (0 : ℝ)..t, L τ) -
      (2-theta)*c * (∫ τ in (0 : ℝ)..t, D τ) at hb
  dsimp only [c] at hb
  nlinarith

/-- The paid term is uniform over expanding retained sets when the low
cutoff is fixed. Uniform control of the displayed remainder is still open. -/
theorem integrated_highHigh_remainder_fixed_cutoff
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hB : 0 ≤ B) (theta : ℝ) (L : ℕ) (htheta : 0 < theta) (hnu : 0 < nu)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (modes outputs : Finset Wavevector) (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (ho : outputs ⊆ modes) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    misalignedEnergy outputs (fourierCurl (s.coefficients t)) +
      (2 - theta) * nu * (2 * Real.pi)^2 *
        (∫ τ in (0 : ℝ)..t, misalignedDissipation outputs (fourierCurl (s.coefficients τ))) ≤
      misalignedEnergy outputs (fourierCurl u₀) +
        (∫ τ in (0 : ℝ)..t, highHighRemainderRate (L : ℝ) modes outputs (s.coefficients τ)) +
        (2 * (L : ℝ) + 1)^3 * kineticEnergy u₀ ^ 2 / (theta * nu ^ 2) := by
  have h := integrated_highHigh_remainder s hB theta (L : ℝ) htheta hnu
    g hg hSum hu modes outputs hk ho t ht
  have hc : ((lowSources (L : ℝ) modes).card : ℝ) ≤ (2 * (L : ℝ) + 1)^3 := by
    exact_mod_cast lowSources_card_le L modes
  exact h.trans (by gcongr)

end Mettapedia.FluidDynamics.NavierStokes.LocalHighHighEnergyBudget
