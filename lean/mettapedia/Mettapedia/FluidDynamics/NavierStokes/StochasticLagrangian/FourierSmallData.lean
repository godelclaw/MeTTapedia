import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierGlobalSolution

/-!
# Global solutions for small data

For order `m ≥ 3` the Wiener sums of the tame estimate cost at most the
order-`m` energy, and on nonzero modes the energy is at most the dissipation,
so

```text
orderTriad_m ≤ 2^(m+1) √L √E_m D_m.
```

The convection is then absorbed by the dissipation while `E_m` stays below
`δ² = (ν (2π)² / κ_m)²`: along an actual solution the order-`m` energy at most
doubles from its initial value. For tame solutions of order `m + 2` the full
order-`m` energy is continuous in time, and a continuity argument keeps it
below `δ² / 4` forever when the data have `E_m ≤ δ² / 8`. This bounds the
order-one energy on every finite horizon, so there is a unique global
solution: `nonempty_globalSolution_of_small`. Only the order-`m` energy must be
small; the order-`m + 2` energy of the data only has to be finite.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierSmallData

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCurlOutputTail PancakeLatticeDecayEnvelope
open PancakeLocalInfiniteVelocity PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope
open PancakeBlockReality PancakeHigherGalerkinWindow PancakeHigherSobolevWindow
open PancakeArbitraryDataBlocks PancakeGalerkinKineticEnergy PancakeInfinitePressureCoefficients
open FourierTameTriad FourierContinuation FourierInfiniteTameRate FourierTameContinuation
open FourierVorticitySupContinuation FourierGlobalSolution

section Triad

theorem weightedMass_mono_exp (M : Finset Wavevector) (a : Wavevector → ℝ) {r s : ℝ}
    (hrs : r ≤ s) : weightedMass M a r ≤ weightedMass M a s :=
  Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg (frequencyVec k)]) hrs)
    (sq_nonneg _)

theorem orderEnergy_le_orderDissipation (m : ℕ) (M : Finset Wavevector) (a : Wavevector → ℝ)
    (hM : ∀ k ∈ M, k ≠ 0) : orderEnergy m M a ≤ orderDissipation m M a := by
  unfold orderDissipation orderEnergy
  refine Finset.sum_le_sum fun k hk ↦ ?_
  have h1 := one_le_norm_frequencyVec (hM k hk)
  have e : (orderWeight m k * (‖frequencyVec k‖ * a k)) ^ 2 =
      ‖frequencyVec k‖ ^ 2 * (orderWeight m k * a k) ^ 2 := by ring
  rw [e]
  have h2 : 1 ≤ ‖frequencyVec k‖ ^ 2 := one_le_pow₀ h1
  nlinarith [sq_nonneg (orderWeight m k * a k)]

/-- **The small-energy triad bound.** -/
theorem orderTriad_le_small (m : ℕ) (hm : 3 ≤ m) (M : Finset Wavevector) (a : Wavevector → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hM : ∀ k ∈ M, k ≠ 0) :
    orderTriad m M a ≤ 2 ^ (m + 1) * Real.sqrt tameMass *
      Real.sqrt (orderEnergy m M a) * orderDissipation m M a := by
  set E := orderEnergy m M a with hEdef
  set D := orderDissipation m M a with hDdef
  set L := tameMass
  have hE0 : 0 ≤ E := orderEnergy_nonneg m M a
  have hD0 : 0 ≤ D := orderDissipation_nonneg m M a
  have hED : E ≤ D := orderEnergy_le_orderDissipation m M a hM
  have hmass : ∀ r : ℝ, r ≤ 2 * m → weightedMass M a r ≤ E := fun r hr ↦ by
    rw [hEdef, orderEnergy_eq_weightedMass]
    exact weightedMass_mono_exp M a hr
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hW1 : wiener1 M a ≤ Real.sqrt L * Real.sqrt E :=
    (wiener1_le M a ha).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hmass _ (by linarith))) (Real.sqrt_nonneg _))
  have hW0 : wiener0 M a ≤ Real.sqrt L * Real.sqrt E :=
    (wiener0_le M a).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hmass _ (by linarith))) (Real.sqrt_nonneg _))
  have hW1n : 0 ≤ wiener1 M a := Finset.sum_nonneg fun k _ ↦ mul_nonneg (norm_nonneg _) (ha k)
  have hW0n : 0 ≤ wiener0 M a := Finset.sum_nonneg fun k _ ↦ ha k
  have hsqrtED : Real.sqrt (E * D) ≤ D := by
    calc Real.sqrt (E * D) ≤ Real.sqrt (D * D) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hED hD0)
      _ = D := Real.sqrt_mul_self hD0
  have hsE : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
  have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hE_le : E ≤ Real.sqrt E * Real.sqrt E := (Real.mul_self_sqrt hE0).ge
  calc orderTriad m M a ≤ 2 ^ m * (E * wiener1 M a + wiener0 M a * Real.sqrt (E * D)) :=
        orderTriad_le_tame m M a ha
    _ ≤ 2 ^ m * (E * (Real.sqrt L * Real.sqrt E) + (Real.sqrt L * Real.sqrt E) * D) := by
        gcongr
    _ ≤ 2 ^ m * (D * (Real.sqrt L * Real.sqrt E) + (Real.sqrt L * Real.sqrt E) * D) := by
        gcongr
    _ = 2 ^ (m + 1) * Real.sqrt L * Real.sqrt E * D := by ring

/-- The rate constant of the small-energy absorption. -/
def smallRateConst (m : ℕ) : ℝ := 2 * (2 * Real.pi) * (2 ^ (m + 1) * Real.sqrt tameMass)

theorem tameMass_pos : 0 < tameMass :=
  summable_tameDecay.tsum_pos (fun k ↦ (tameDecay_pos k).le) 0 (tameDecay_pos 0)

theorem smallRateConst_pos (m : ℕ) : 0 < smallRateConst m := by
  unfold smallRateConst
  have := Real.sqrt_pos.mpr tameMass_pos
  positivity

theorem truncConvectionRate_le_small (m : ℕ) (hm : 3 ≤ m) (F G : Finset Wavevector)
    (u : FourierVelocity) (hu0 : u 0 = 0) :
    truncConvectionRate m F G u ≤ smallRateConst m *
      Real.sqrt (velocityEnergy m (carrier F G) u) * velocityDissipation m (carrier F G) u := by
  have ha : ∀ k, 0 ≤ amplitude u k := fun k ↦ norm_nonneg _
  have h1 := (le_abs_self _).trans (abs_truncConvectionRate_le m F G u)
  have h2 := truncTriad_le_orderTriad m F G (amplitude u) ha (amplitude_zero_of_zero hu0)
  have h3 := orderTriad_le_small m hm (carrier F G) (amplitude u) ha
    (fun k hk ↦ mem_carrier_ne_zero hk)
  calc truncConvectionRate m F G u ≤ 2 * (2 * Real.pi) * truncTriad m F G (amplitude u) := h1
    _ ≤ 2 * (2 * Real.pi) * orderTriad m (carrier F G) (amplitude u) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2 * (2 * Real.pi) * (2 ^ (m + 1) * Real.sqrt tameMass *
          Real.sqrt (orderEnergy m (carrier F G) (amplitude u)) *
            orderDissipation m (carrier F G) (amplitude u)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by
        unfold smallRateConst velocityEnergy velocityDissipation
        ring

end Triad

section Step

open intervalIntegral
open scoped Interval

variable {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ}

/-- **The integrated step from any bound on the integrated truncated rates.**
The passage to the full convolution and the fundamental theorem of calculus
are those of `integrated_tame_step`. -/
theorem integrated_step_of_rate (m : ℕ) (hm : 2 ≤ m) (c : SolutionOn nu u₀ T)
    {S : ℝ} (hS : 0 < S) (hST : S < T) {B K R : ℝ}
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy m F (c.coefficients τ) ≤ B)
    (hK : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ K)
    (F : Finset Wavevector)
    (hrate : ∀ N : ℕ, ∫ τ in (0 : ℝ)..S,
      truncConvectionRate m F (wavevectorBox N) (c.coefficients τ) ≤ R) :
    velocityEnergy m F (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 *
        (∫ τ in (0 : ℝ)..S, velocityDissipation m F (c.coefficients τ)) ≤
      velocityEnergy m F (c.coefficients 0) + R := by
  set c' := c.coefficients with hc'
  let Tr : ℕ → ℝ → ℝ := fun N τ ↦ truncConvectionRate m F (wavevectorBox N) (c' τ)
  let Rr : ℝ → ℝ := fun τ ↦ infiniteConvectionRate m F (c' τ)
  let Dq : ℝ → ℝ := fun τ ↦ velocityDissipation m F (c' τ)
  let bound : ℝ → ℝ := fun τ ↦
    2 * (2 * Real.pi) * ((∑ q ∈ F, orderWeight m q ^ 2 * amplitude (c' τ) q) * K)
  have hs : ∀ τ ∈ Icc (0 : ℝ) S, ∀ q i, Summable (fun k ↦ outputFiber q (c' τ) k i) := by
    intro τ hτ q i
    exact summable_outputFiber (c' τ) B
      (fun G ↦ (sobolevEnergy_le_velocityEnergy m hm G _).trans (hB τ hτ G)) q i
  have hlim : ∀ τ ∈ Icc (0 : ℝ) S, Tendsto (fun N ↦ Tr N τ) atTop (nhds (Rr τ)) := by
    intro τ hτ
    exact (tendsto_truncConvectionRate m F (c' τ) (c.transverse τ) (hs τ hτ)).comp
      tendsto_wavevectorBox
  have hTrbound : ∀ N, ∀ τ ∈ Icc (0 : ℝ) S, |Tr N τ| ≤ bound τ := by
    intro N τ hτ
    refine (abs_truncConvectionRate_le m F (wavevectorBox N) (c' τ)).trans ?_
    exact mul_le_mul_of_nonneg_left
      (truncTriad_le_dom m F _ _ (fun k ↦ norm_nonneg _) (hK τ hτ)) (by positivity)
  have hbound_cont : Continuous bound := by
    have := continuous_weightedAmplitude_along m F c.continuous
    exact continuous_const.mul (this.mul continuous_const)
  have hTr_cont : ∀ N, Continuous (Tr N) :=
    fun N ↦ continuous_truncConvectionRate m F _ c.continuous
  have hD_cont : Continuous Dq := continuous_velocityDissipation_along m F c.continuous
  have hR_meas : AEStronglyMeasurable Rr (volume.restrict (Ι (0 : ℝ) S)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (fun N ↦ (hTr_cont N).aestronglyMeasurable) ?_
    exact ae_restrict_of_forall_mem measurableSet_uIoc
      fun τ hτ ↦ hlim τ (mem_Icc_of_mem_uIoc hS.le hτ)
  have hR_bound : ∀ τ ∈ Icc (0 : ℝ) S, |Rr τ| ≤ bound τ := fun τ hτ ↦
    le_of_tendsto ((hlim τ hτ).abs) (Eventually.of_forall fun N ↦ hTrbound N τ hτ)
  have hR_int : IntervalIntegrable Rr volume 0 S := by
    refine (hbound_cont.intervalIntegrable 0 S).mono_fun' hR_meas ?_
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun τ hτ ↦ ?_
    show ‖Rr τ‖ ≤ bound τ
    rw [Real.norm_eq_abs]
    exact hR_bound τ (mem_Icc_of_mem_uIoc hS.le hτ)
  have hDCT : Tendsto (fun N ↦ ∫ τ in (0 : ℝ)..S, Tr N τ) atTop
      (nhds (∫ τ in (0 : ℝ)..S, Rr τ)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
    · exact Eventually.of_forall fun N ↦ (hTr_cont N).aestronglyMeasurable
    · refine Eventually.of_forall fun N ↦ Eventually.of_forall fun τ hτ ↦ ?_
      rw [Real.norm_eq_abs]
      exact hTrbound N τ (mem_Icc_of_mem_uIoc hS.le hτ)
    · exact hbound_cont.intervalIntegrable 0 S
    · exact Eventually.of_forall fun τ hτ ↦ hlim τ (mem_Icc_of_mem_uIoc hS.le hτ)
  have hR_int_le : ∫ τ in (0 : ℝ)..S, Rr τ ≤ R := le_of_tendsto' hDCT hrate
  have hFTC : ∫ τ in (0 : ℝ)..S, (Rr τ - 2 * nu * (2 * Real.pi) ^ 2 * Dq τ) =
      velocityEnergy m F (c' S) - velocityEnergy m F (c' 0) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hS.le
    · exact (continuous_velocityEnergy_along m F c.continuous).continuousOn
    · intro τ hτ
      have hd := hasDerivAt_velocityEnergy m F c' (fun q ↦ infiniteVelocityRHS nu (c' τ) q) τ
        (fun q _ i ↦ c.equation τ ⟨hτ.1, lt_trans hτ.2 hST⟩ q i)
      rw [orderVelocityRate_infiniteRHS m F (c' τ) nu (c.transverse τ)] at hd
      exact hd
    · exact hR_int.sub ((hD_cont.intervalIntegrable 0 S).const_mul _)
  rw [intervalIntegral.integral_sub hR_int ((hD_cont.intervalIntegrable 0 S).const_mul _),
    intervalIntegral.integral_const_mul] at hFTC
  change velocityEnergy m F (c' S) + 2 * nu * (2 * Real.pi) ^ 2 * (∫ τ in (0 : ℝ)..S, Dq τ) ≤ _
  linarith

/-- **The small-energy step.** While every truncated order-`m` energy stays
below `δ²`, the integrated convection is at most `κ_m δ X`. -/
theorem integrated_small_step (m : ℕ) (hm : 3 ≤ m) (c : SolutionOn nu u₀ T)
    {S : ℝ} (hS : 0 < S) (hST : S < T) {B δ X : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy m F (c.coefficients τ) ≤ B)
    (hsmall : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy m F (c.coefficients τ) ≤ δ ^ 2)
    (hX : ∀ G, ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients τ) ≤ X)
    (F : Finset Wavevector) :
    velocityEnergy m F (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 *
        (∫ τ in (0 : ℝ)..S, velocityDissipation m F (c.coefficients τ)) ≤
      velocityEnergy m F (c.coefficients 0) + smallRateConst m * δ * X := by
  have hK : ∀ τ ∈ Icc (0 : ℝ) S, ∀ G, velocityEnergy 1 G (c.coefficients τ) ≤ δ ^ 2 :=
    fun τ hτ G ↦ (velocityEnergy_le_of_order_le (by omega) _ G).trans (hsmall τ hτ G)
  refine integrated_step_of_rate m (by omega) c hS hST hB hK F fun N ↦ ?_
  set Dc : ℝ → ℝ := fun τ ↦
    velocityDissipation m (carrier F (wavevectorBox N)) (c.coefficients τ)
  have hDc_cont : Continuous Dc := continuous_velocityDissipation_along m _ c.continuous
  have hpt : ∀ τ ∈ Icc (0 : ℝ) S,
      truncConvectionRate m F (wavevectorBox N) (c.coefficients τ) ≤ smallRateConst m * δ * Dc τ := by
    intro τ hτ
    have h := truncConvectionRate_le_small m hm F (wavevectorBox N) (c.coefficients τ)
      (c.zero τ)
    have hsq : Real.sqrt (velocityEnergy m (carrier F (wavevectorBox N)) (c.coefficients τ)) ≤ δ := by
      calc Real.sqrt (velocityEnergy m (carrier F (wavevectorBox N)) (c.coefficients τ))
          ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt (hsmall τ hτ _)
        _ = δ := Real.sqrt_sq hδ
    have hD0 : 0 ≤ Dc τ := orderDissipation_nonneg m _ _
    have hk := (smallRateConst_pos m).le
    calc truncConvectionRate m F (wavevectorBox N) (c.coefficients τ)
        ≤ smallRateConst m * Real.sqrt (velocityEnergy m (carrier F (wavevectorBox N))
            (c.coefficients τ)) * Dc τ := h
      _ ≤ smallRateConst m * δ * Dc τ := by gcongr
  calc ∫ τ in (0 : ℝ)..S, truncConvectionRate m F (wavevectorBox N) (c.coefficients τ)
      ≤ ∫ τ in (0 : ℝ)..S, smallRateConst m * δ * Dc τ :=
        intervalIntegral.integral_mono_on hS.le
          ((continuous_truncConvectionRate m F _ c.continuous).intervalIntegrable 0 S)
          ((hDc_cont.const_smul (smallRateConst m * δ)).intervalIntegrable 0 S) hpt
    _ = smallRateConst m * δ * ∫ τ in (0 : ℝ)..S, Dc τ := intervalIntegral.integral_const_mul _ _
    _ ≤ smallRateConst m * δ * X :=
        mul_le_mul_of_nonneg_left (hX _) (mul_nonneg (smallRateConst_pos m).le hδ)

/-- **Doubling.** While the order-`m` energy stays below `δ²`, with
`κ_m δ ≤ ν (2π)²`, it at most doubles from its initial value. -/
theorem velocityEnergy_le_two_of_small (m : ℕ) (hm : 3 ≤ m) (hnu : 0 < nu)
    (c : SolutionOn nu u₀ T) {S : ℝ} (hS : 0 < S) (hST : S < T) {B δ X₀ E₀ : ℝ} (hδ : 0 ≤ δ)
    (hκ : smallRateConst m * δ ≤ nu * (2 * Real.pi) ^ 2)
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy m F (c.coefficients τ) ≤ B)
    (hsmall : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy m F (c.coefficients τ) ≤ δ ^ 2)
    (hX₀ : ∀ G, ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients τ) ≤ X₀)
    (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀) (F : Finset Wavevector) :
    velocityEnergy m F (c.coefficients S) ≤ 2 * E₀ := by
  let I : Finset Wavevector → ℝ := fun G ↦
    ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients τ)
  have hbdd : BddAbove (Set.range I) := ⟨X₀, by rintro _ ⟨G, rfl⟩; exact hX₀ G⟩
  set X := sSup (Set.range I) with hXdef
  have hIX : ∀ G, I G ≤ X := fun G ↦ le_csSup hbdd ⟨G, rfl⟩
  have hI0 : ∀ G, 0 ≤ I G := fun G ↦
    intervalIntegral.integral_nonneg hS.le fun τ _ ↦ orderDissipation_nonneg m G _
  have hX0 : 0 ≤ X := (hI0 ∅).trans (hIX ∅)
  have hstep := fun G ↦ integrated_small_step m hm c hS hST hδ hB hsmall hIX G
  have hinit : ∀ G, velocityEnergy m G (c.coefficients 0) ≤ E₀ := fun G ↦ by
    rw [c.initial]
    exact hE₀ G
  have hpos : 0 < 2 * nu * (2 * Real.pi) ^ 2 := by positivity
  have hXle : X ≤ (E₀ + smallRateConst m * δ * X) / (2 * nu * (2 * Real.pi) ^ 2) := by
    refine csSup_le (Set.range_nonempty I) ?_
    rintro _ ⟨G, rfl⟩
    rw [le_div_iff₀ hpos]
    have h := hstep G
    have hE := orderEnergy_nonneg m G (amplitude (c.coefficients S))
    change velocityEnergy m G (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 * I G ≤ _ at h
    change 0 ≤ velocityEnergy m G (c.coefficients S) at hE
    nlinarith [hinit G]
  rw [le_div_iff₀ hpos] at hXle
  have hmix : smallRateConst m * δ * X ≤ nu * (2 * Real.pi) ^ 2 * X :=
    mul_le_mul_of_nonneg_right hκ hX0
  have hXE : nu * (2 * Real.pi) ^ 2 * X ≤ E₀ := by nlinarith
  have h := hstep F
  have hD := hI0 F
  change velocityEnergy m F (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 * I F ≤ _ at h
  nlinarith [hinit F]

end Step

section Bootstrap

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity} {T : ℝ}

/-- The full order-`m` energy. -/
def fullEnergy (m : ℕ) (u : FourierVelocity) : ℝ :=
  ∑' k, orderWeight m k ^ 2 * coefficientEnergy (u k)

theorem coefficientEnergy_nonneg' (v : VelocityCoefficient) : 0 ≤ coefficientEnergy v := by
  rw [← norm_coefficientVec_sq]
  positivity

theorem term_le_envelope (m : ℕ) (u : FourierVelocity) {B : ℝ}
    (hB : ∀ F, velocityEnergy (m + 2) F u ≤ B) (k : Wavevector) :
    orderWeight m k ^ 2 * coefficientEnergy (u k) ≤ B * latticeDecayWeight k := by
  have h := hB {k}
  rw [velocityEnergy_eq, Finset.sum_singleton] at h
  have hw : orderWeight (m + 2) k ^ 2 = orderWeight m k ^ 2 * (1 + ‖frequencyVec k‖) ^ 4 := by
    unfold orderWeight
    ring
  have hp : 0 < (1 + ‖frequencyVec k‖) ^ 4 := by positivity
  rw [hw] at h
  unfold latticeDecayWeight
  rw [mul_one_div, le_div_iff₀ hp]
  nlinarith [coefficientEnergy_nonneg' (u k)]

theorem summable_fullEnergy_terms (m : ℕ) (u : FourierVelocity) {B : ℝ}
    (hB : ∀ F, velocityEnergy (m + 2) F u ≤ B) :
    Summable (fun k ↦ orderWeight m k ^ 2 * coefficientEnergy (u k)) :=
  (summable_latticeDecayWeight.mul_left B).of_nonneg_of_le
    (fun _ ↦ mul_nonneg (sq_nonneg _) (coefficientEnergy_nonneg' _)) (term_le_envelope m u hB)

theorem velocityEnergy_le_fullEnergy (m : ℕ) (u : FourierVelocity) {B : ℝ}
    (hB : ∀ F, velocityEnergy (m + 2) F u ≤ B) (F : Finset Wavevector) :
    velocityEnergy m F u ≤ fullEnergy m u := by
  rw [velocityEnergy_eq]
  exact (summable_fullEnergy_terms m u hB).sum_le_tsum F fun k _ ↦
    mul_nonneg (sq_nonneg _) (coefficientEnergy_nonneg' _)

theorem fullEnergy_le_of_forall (m : ℕ) (u : FourierVelocity) {b : ℝ}
    (h : ∀ F, velocityEnergy m F u ≤ b) : fullEnergy m u ≤ b := by
  refine Real.tsum_le_of_sum_le (fun k ↦ mul_nonneg (sq_nonneg _) (coefficientEnergy_nonneg' _))
    fun F ↦ ?_
  rw [← velocityEnergy_eq]
  exact h F

/-- The full order-`m` energy of a tame solution of order `m + 2` is continuous
in time. -/
theorem continuousOn_fullEnergy (c : TameSolutionOn nu (m + 2) u₀ T) {S : ℝ} (hST : S < T) :
    ContinuousOn (fun t ↦ fullEnergy m (c.coefficients t)) (Icc 0 S) := by
  obtain ⟨B, hB⟩ := c.order_local S hST
  refine continuousOn_iff_continuous_domRestrict.mpr ?_
  refine continuous_tsum (f := fun k (t : Icc (0 : ℝ) S) ↦
      orderWeight m k ^ 2 * coefficientEnergy (c.coefficients t k))
    (fun k ↦ ?_) (summable_latticeDecayWeight.mul_left B) (fun k t ↦ ?_)
  · have hc (i : Fin 3) : Continuous (fun t : Icc (0 : ℝ) S ↦ c.coefficients t k i) :=
      (c.continuous k i).comp continuous_subtype_val
    show Continuous fun t : Icc (0 : ℝ) S ↦
      orderWeight m k ^ 2 * ∑ i : Fin 3, Complex.normSq (c.coefficients t k i)
    exact continuous_const.mul (continuous_finsetSum _ fun i _ ↦ Complex.continuous_normSq.comp (hc i))
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (coefficientEnergy_nonneg' _))]
    exact term_le_envelope m _ (hB t t.2) k

/-- **The small-data bootstrap.** For data with order-`m` energy at most
`δ² / 8`, where `κ_m δ ≤ ν (2π)²`, the order-`m` energy of every tame solution of
order `m + 2` stays below `δ² / 4`. -/
theorem velocityEnergy_le_of_small (hm : 3 ≤ m) (hnu : 0 < nu)
    (c : TameSolutionOn nu (m + 2) u₀ T) {δ : ℝ} (hδ : 0 < δ)
    (hκ : smallRateConst m * δ ≤ nu * (2 * Real.pi) ^ 2)
    (hdata : ∀ F, velocityEnergy m F u₀ ≤ δ ^ 2 / 8) :
    ∀ τ ∈ Ico (0 : ℝ) T, ∀ F, velocityEnergy m F (c.coefficients τ) ≤ δ ^ 2 / 4 := by
  -- the step: smallness on `[0, s]` gives the doubling bound at `s`
  have hstep : ∀ s ∈ Ico (0 : ℝ) T,
      (∀ τ ∈ Icc (0 : ℝ) s, fullEnergy m (c.coefficients τ) ≤ δ ^ 2) →
        ∀ F, velocityEnergy m F (c.coefficients s) ≤ δ ^ 2 / 4 := by
    intro s hs hsmall F
    rcases hs.1.eq_or_lt with h0 | hpos
    · subst h0
      rw [c.initial]
      linarith [hdata F, sq_nonneg δ]
    · obtain ⟨B, hB⟩ := c.order_local s hs.2
      obtain ⟨X, hX⟩ := c.dissipation_local s hs.2
      have hBm : ∀ τ ∈ Icc (0 : ℝ) s, ∀ G, velocityEnergy m G (c.coefficients τ) ≤ B :=
        fun τ hτ G ↦ (velocityEnergy_le_of_order_le (by omega) _ G).trans (hB τ hτ G)
      have hsm : ∀ τ ∈ Icc (0 : ℝ) s, ∀ G, velocityEnergy m G (c.coefficients τ) ≤ δ ^ 2 :=
        fun τ hτ G ↦ (velocityEnergy_le_fullEnergy m _ (hB τ hτ) G).trans (hsmall τ hτ)
      have hXm : ∀ G, ∫ τ in (0 : ℝ)..s, velocityDissipation m G (c.coefficients τ) ≤ X := by
        intro G
        refine le_trans (intervalIntegral.integral_mono_on hpos.le ?_ ?_ fun τ _ ↦ ?_) (hX G)
        · exact (continuous_velocityDissipation_along m G c.continuous).intervalIntegrable 0 s
        · exact (continuous_velocityDissipation_along (m + 2) G c.continuous).intervalIntegrable 0 s
        · unfold velocityDissipation orderDissipation orderEnergy
          refine Finset.sum_le_sum fun k _ ↦ ?_
          have hw : orderWeight m k ≤ orderWeight (m + 2) k :=
            pow_le_pow_right₀ (by linarith [norm_nonneg (frequencyVec k)]) (by omega)
          have h0 : 0 ≤ orderWeight m k := by unfold orderWeight; positivity
          have ha : 0 ≤ ‖frequencyVec k‖ * amplitude (c.coefficients τ) k := by
            unfold amplitude; positivity
          exact pow_le_pow_left₀ (mul_nonneg h0 ha) (mul_le_mul_of_nonneg_right hw ha) 2
      have h := velocityEnergy_le_two_of_small m hm hnu c.toSolutionOn hpos hs.2 hδ.le hκ hBm hsm
        hXm hdata F
      linarith
  intro τ₁ hτ₁
  set S' := (τ₁ + T) / 2 with hS'def
  have hτS' : τ₁ < S' := by linarith [hτ₁.2]
  have hS'T : S' < T := by linarith [hτ₁.2]
  have hec := continuousOn_fullEnergy c hS'T
  obtain ⟨B', hB'⟩ := c.order_local S' hS'T
  set e : ℝ → ℝ := fun t ↦ fullEnergy m (c.coefficients t)
  have hsub : Icc (0 : ℝ) τ₁ ⊆ Icc 0 S' := Icc_subset_Icc le_rfl hτS'.le
  -- the full energy is at most `δ²/4` wherever the smallness held up to that time
  have hfull : ∀ s ∈ Icc (0 : ℝ) τ₁, (∀ τ ∈ Icc (0 : ℝ) s, e τ ≤ δ ^ 2) → e s ≤ δ ^ 2 / 4 :=
    fun s hs h ↦ fullEnergy_le_of_forall m _
      (hstep s ⟨hs.1, hs.2.trans_lt hτ₁.2⟩ h)
  let U : Set ℝ := {t ∈ Icc (0 : ℝ) τ₁ | δ ^ 2 / 2 ≤ e t}
  have hUempty : U = ∅ := by
    by_contra hne
    obtain ⟨t₀, ht₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hbdd : BddBelow U := ⟨0, fun t ht ↦ ht.1.1⟩
    set ts := sInf U with htsdef
    have hclosed : IsClosed U := by
      have h := (hec.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc
        (isClosed_Ici (a := δ ^ 2 / 2))
      exact h
    have htsU : ts ∈ U := hclosed.csInf_mem ⟨t₀, ht₀⟩ hbdd
    have hts0 : 0 < ts := by
      rcases htsU.1.1.eq_or_lt with h | h
      · exfalso
        have he0 : e 0 ≤ δ ^ 2 / 8 := by
          apply fullEnergy_le_of_forall
          intro F
          rw [c.initial]
          exact hdata F
        have hU0 := htsU.2
        rw [← h] at hU0
        nlinarith [sq_nonneg δ, sq_pos_of_pos hδ]
      · exact h
    have hbelow : ∀ t ∈ Ico (0 : ℝ) ts, e t < δ ^ 2 / 2 := by
      intro t ht
      by_contra hge
      have htU : t ∈ U := ⟨⟨ht.1, ht.2.le.trans htsU.1.2⟩, not_lt.mp hge⟩
      exact absurd (csInf_le hbdd htU) (not_le.mpr ht.2)
    have hquarter : ∀ t ∈ Ico (0 : ℝ) ts, e t ≤ δ ^ 2 / 4 := by
      intro t ht
      refine hfull t ⟨ht.1, ht.2.le.trans htsU.1.2⟩ fun τ hτ ↦ ?_
      have h := hbelow τ ⟨hτ.1, hτ.2.trans_lt ht.2⟩
      nlinarith [sq_nonneg δ]
    have hcl : ts ∈ closure (Ico (0 : ℝ) ts) := by
      rw [closure_Ico hts0.ne]
      exact ⟨hts0.le, le_rfl⟩
    have hcw : ContinuousWithinAt e (Ico (0 : ℝ) ts) ts :=
      (hec ts (hsub htsU.1)).mono fun t ht ↦ hsub ⟨ht.1, ht.2.le.trans htsU.1.2⟩
    have hle := ContinuousWithinAt.closure_le hcl hcw continuousWithinAt_const hquarter
    have hge := htsU.2
    nlinarith [sq_pos_of_pos hδ]
  have hall : ∀ τ ∈ Icc (0 : ℝ) τ₁, e τ ≤ δ ^ 2 := by
    intro τ hτ
    by_contra hgt
    have hgt' := not_le.mp hgt
    have hU : τ ∈ U := ⟨hτ, by nlinarith [sq_nonneg δ]⟩
    rw [hUempty] at hU
    exact hU
  exact hstep τ₁ hτ₁ hall

end Bootstrap

section Global

/-- The smallness radius at order `m`. -/
def smallRadius (m : ℕ) (nu : ℝ) : ℝ := nu * (2 * Real.pi) ^ 2 / smallRateConst m

theorem smallRadius_pos (m : ℕ) {nu : ℝ} (hnu : 0 < nu) : 0 < smallRadius m nu :=
  div_pos (by positivity) (smallRateConst_pos m)

theorem smallRateConst_mul_smallRadius (m : ℕ) (nu : ℝ) :
    smallRateConst m * smallRadius m nu = nu * (2 * Real.pi) ^ 2 := by
  unfold smallRadius
  field_simp [(smallRateConst_pos m).ne']

/-- **Global existence for small data.** For `m ≥ 5`, data of finite order-`(m+2)`
energy whose order-`m` energy is at most `smallRadius m ν ² / 8` have a unique
global solution. -/
theorem nonempty_globalSolution_of_small (m : ℕ) (hm : 5 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀)
    (hE₀ : ∀ F, velocityEnergy (m + 2) F u₀ ≤ E₀)
    (hsmall : ∀ F, velocityEnergy m F u₀ ≤ smallRadius m nu ^ 2 / 8) :
    Nonempty (GlobalSolution nu (m + 2) u₀) := by
  have hδ := smallRadius_pos m hnu
  have hκ : smallRateConst m * smallRadius m nu ≤ nu * (2 * Real.pi) ^ 2 :=
    (smallRateConst_mul_smallRadius m nu).le
  refine nonempty_globalSolution (by omega) hnu ?_
  refine exists_tameSolutionOn_of_orderOne (m + 2) (by omega) hnu u₀ hr hd hz hE₀0 hE₀ ?_
  intro H _
  refine ⟨smallRadius m nu ^ 2 / 4, fun T _ c τ hτ F ↦ ?_⟩
  exact (velocityEnergy_le_of_order_le (by omega) _ F).trans
    (velocityEnergy_le_of_small (by omega) hnu c hδ hκ hsmall τ hτ F)

end Global

end Mettapedia.FluidDynamics.NavierStokes.FourierSmallData
