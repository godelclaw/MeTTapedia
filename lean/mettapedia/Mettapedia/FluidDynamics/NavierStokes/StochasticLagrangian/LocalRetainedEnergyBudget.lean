import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalFilteredVorticity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalLowFrequencyBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalDefectODEBudget

/-!
# Initial-data absorption in the actual retained energy equation

The low-source estimate is consumed by the actual infinite solution's
retained vorticity equation. Its remaining signed work consists of the
resolved high-source channel and the all-input subgrid curl. Continuity
and integrability are derived, including at the interval endpoints; only
the open interval is used for the differential equation.

The remainder is not estimated here. In particular, this theorem does not
claim uniform control as the retained set expands or at a maximal time.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalRetainedEnergyBudget

open scoped BigOperators
open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakePeriodicVorticityEquation PancakeGalerkinKineticEnergy
open PancakeGalerkinVorticityBridge PancakeIncomingLowSourceEnergy
open PancakeViscousMisalignmentAbsorption PancakeFilteredStrainDynamics
open InfiniteFilteredEquation PancakeLocalInfiniteVelocity LocalFilteredVorticity
open PancakeInfiniteFourierTime PancakePhysicalDefectODEBudget
open LocalLowFrequencyBudget InfiniteConvectionEnergy PancakeCurlOutputTail
open PancakeCoefficientLimitEquation

/-- Subgrid feedback is exactly the difference of the filtered actual RHS
and the resolved finite RHS. This also gives its endpoint continuity. -/
theorem subgridForce_eq_filtered_sub_finite
    (chi : Wavevector → ℂ) (u : FourierVelocity) (C : ℝ)
    (hchi : ∀ k, ‖chi k‖ ≤ C) (modes : Finset Wavevector)
    (hcut : ∀ k, k ∉ modes → chi k = 0)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0) (hd : ∀ k, modeDot k (u k) = 0)
    (nu : ℝ) (q : Wavevector)
    (hu : ∀ i, Summable (fun k ↦ PancakeSobolevFiberEnvelope.outputFiber q u k i)) :
    subgridForce chi u q =
      chi q • infiniteVelocityRHS nu u q - velocityRHS modes (filteredVelocity chi u) nu q := by
  have h := filtered_infiniteVelocityRHS chi u C hchi nu q hu
  rw [infiniteVelocityRHS_eq_finite modes _
    (fun k hkm ↦ by simp [filteredVelocity, hcut k hkm]) hk
    (fun k _ ↦ filteredVelocity_transverse chi u k (hd k))] at h
  rw [h]
  abel

variable {nu T B : ℝ} {u₀ : FourierVelocity}

theorem continuousOn_subgridCurl (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hB : 0 ≤ B) (modes : Finset Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0)
    (q : Wavevector) (hq : q ∈ modes) (i : Fin 3) :
    ContinuousOn (fun t ↦ subgridCurl (sharpFilter modes) (s.coefficients t) q i)
      (Set.Icc (0 : ℝ) T) := by
  apply continuousOn_fourierCurl_coefficient
  intro j
  let v := fun t ↦ filteredVelocity (sharpFilter modes) (s.coefficients t)
  have hc (k : Wavevector) (hkm : k ∈ modes) (l : Fin 3) :
      ContinuousOn (fun t ↦ v t k l) (Set.Icc (0 : ℝ) T) := by
    simpa only [v, filteredVelocity_sharp_mem modes _ k hkm] using (s.continuous k l).continuousOn
  have hf := continuousOn_velocityRHS modes v nu (Set.Icc (0 : ℝ) T) hk
    (fun t _ k _ ↦ filteredVelocity_transverse _ _ _ (s.transverse t k)) hc q hq j
  have hi : ContinuousOn (fun t ↦ infiniteVelocityRHS nu (s.coefficients t) q j)
      (Set.Icc (0 : ℝ) T) :=
    continuousOn_iff_continuous_restrict.mpr (continuous_velocityRHS_component s hB q j)
  apply (hi.sub hf).congr
  intro t ht
  have he := subgridForce_eq_filtered_sub_finite (sharpFilter modes) (s.coefficients t) 1
    (norm_sharpFilter_le_one modes) modes (fun k hkm ↦ by simp [sharpFilter, hkm]) hk
    (s.transverse t) nu q (s.summable_convection t ht q)
  dsimp only [v]
  rw [he]
  simp only [sharpFilter, if_pos hq, one_smul, Pi.sub_apply]

theorem continuousOn_sectorSourceWork (outputs : Finset Wavevector)
    (w f : ℝ → FourierVelocity) (domain : Set ℝ)
    (hw : ∀ q ∈ outputs, ∀ i, ContinuousOn (fun t ↦ w t q i) domain)
    (hf : ∀ q ∈ outputs, ∀ i, ContinuousOn (fun t ↦ f t q i) domain) :
    ContinuousOn (fun t ↦ sectorSourceWork outputs (w t) (f t)) domain := by
  apply ContinuousOn.const_mul
  apply continuousOn_finsetSum
  intro q hq
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_finsetSum
  intro i _
  exact ((continuousOn_misalignedField w domain q (hw q hq) i).star).mul (hf q hq i)

/-- The exact unpaid work after absorbing incoming low sources. The
resolved term alone is not the actual equation's remainder. -/
def retainedRemainderRate (cutoff : ℝ) (modes outputs : Finset Wavevector)
    (u : FourierVelocity) : ℝ :=
  incomingEnergyRate (highSources cutoff modes) modes outputs (fourierCurl u) (fourierCurl u) +
    sectorSourceWork outputs (fourierCurl u) (subgridCurl (sharpFilter modes) u)

theorem continuousOn_retainedRemainderRate (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (hB : 0 ≤ B) (cutoff : ℝ) (modes outputs : Finset Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0) (ho : outputs ⊆ modes) :
    ContinuousOn (fun t ↦ retainedRemainderRate cutoff modes outputs (s.coefficients t))
      (Set.Icc (0 : ℝ) T) := by
  have hc (q : Wavevector) (i : Fin 3) :
      ContinuousOn (fun t ↦ fourierCurl (s.coefficients t) q i) (Set.Icc (0 : ℝ) T) :=
    continuousOn_fourierCurl_coefficient _ _ q (fun j ↦ (s.continuous q j).continuousOn) i
  exact (continuousOn_incomingEnergyRate _ _ _ _ _
    (fun q _ ↦ hc q) (fun q _ ↦ hc q) (fun q _ ↦ hc q)).add
      (continuousOn_sectorSourceWork outputs _ _ _ (fun q _ ↦ hc q)
        (fun q hq ↦ continuousOn_subgridCurl s hB modes hk q (ho hq)))

/-- An initial-data-only low-source cost in the actual retained energy
inequality. Both high-source work and the unresolved curl remain signed.
No independent evolution, energy inequality, or integrability is assumed. -/
theorem integrated_retained_misalignedEnergy
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (hnu : 0 < nu) (hB : 0 ≤ B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 2 (s.coefficients τ) q ≤ g q)
    (cutoff : ℝ) (modes outputs : Finset Wavevector)
    (hk : ∀ k ∈ modes, frequencyVec k ≠ 0) (ho : outputs ⊆ modes)
    (houtput : ∀ q ∈ outputs, cutoff ≤ ‖frequencyVec q‖)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    misalignedEnergy outputs (fourierCurl (s.coefficients t)) +
      nu * (2 * Real.pi)^2 *
        (∫ τ in (0 : ℝ)..t, misalignedDissipation outputs (fourierCurl (s.coefficients τ))) ≤
      misalignedEnergy outputs (fourierCurl u₀) +
        (∫ τ in (0 : ℝ)..t, retainedRemainderRate cutoff modes outputs (s.coefficients τ)) +
        9 * ((lowSources cutoff modes).card : ℝ) * kineticEnergy u₀ ^ 2 / nu ^ 2 := by
  let w := fun τ ↦ fourierCurl (s.coefficients τ)
  let E := fun τ ↦ misalignedEnergy outputs (w τ)
  let D := fun τ ↦ misalignedDissipation outputs (w τ)
  let I := fun τ ↦ incomingEnergyRate modes modes outputs (w τ) (w τ)
  let F := fun τ ↦ sectorSourceWork outputs (w τ) (subgridCurl (sharpFilter modes) (s.coefficients τ))
  let R := fun τ ↦ retainedRemainderRate cutoff modes outputs (s.coefficients τ)
  let L := fun τ ↦ lowSourceCost nu (lowSources cutoff modes) modes (w τ) (w τ)
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
    ((continuousOn_retainedRemainderRate s hB cutoff modes outputs hk ho).mono hsub)
  have hL : IntervalIntegrable L volume 0 t := ContinuousOn.intervalIntegrable_of_Icc ht.1
    ((continuousOn_lowSourceCost s (lowSources cutoff modes) modes
      (fun k hkm ↦ hk k (Finset.mem_filter.mp hkm).1)).mono hsub)
  have hd (τ : ℝ) (hτ : τ ∈ Set.Ioo (0 : ℝ) t) :
      HasDerivAt E (I τ - 2 * c * D τ + F τ) τ := by
    simpa only [E, I, D, F, w, c, mul_assoc] using hasDerivAt_retained_misalignedEnergy s modes outputs hk ho τ
      ⟨hτ.1, hτ.2.trans_le ht.2⟩
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hE hd
    ((hI.sub (hD.const_mul (2 * c))).add hF)
  have hb := intervalIntegral.integral_mono_on_of_le_Ioo ht.1
    ((hI.sub (hD.const_mul (2 * c))).add hF)
    ((hR.add hL).sub (hD.const_mul c))
    (fun τ hτ ↦ show I τ - 2 * c * D τ + F τ ≤ R τ + L τ - c * D τ from by
      have h := retained_misalignedEnergy_lowSource_absorption s hnu cutoff modes outputs
        hk ho houtput τ ⟨hτ.1, hτ.2.trans_le ht.2⟩
      rw [(hd τ hτ).deriv] at h
      change I τ - 2 * c * D τ + F τ + c * D τ ≤ R τ + L τ at h
      linarith)
  rw [he, intervalIntegral.integral_sub (hR.add hL) (hD.const_mul c),
    intervalIntegral.integral_add hR hL, intervalIntegral.integral_const_mul] at hb
  have hl := lowSourceCost_integral_le_initial s hnu g hg hSum hu
    (lowSources cutoff modes) modes (fun k hkm ↦ hk k (Finset.mem_filter.mp hkm).1) t ht
  change (∫ τ in (0 : ℝ)..t, L τ) ≤ _ at hl
  have he0 : E 0 = misalignedEnergy outputs (fourierCurl u₀) := by
    dsimp only [E, w]
    rw [s.initial]
  rw [he0] at hb
  change E t + c * (∫ τ in (0 : ℝ)..t, D τ) ≤ _
  change E t - misalignedEnergy outputs (fourierCurl u₀) ≤
    (∫ τ in (0 : ℝ)..t, R τ) + (∫ τ in (0 : ℝ)..t, L τ) - c * (∫ τ in (0 : ℝ)..t, D τ) at hb
  linarith

end Mettapedia.FluidDynamics.NavierStokes.LocalRetainedEnergyBudget
