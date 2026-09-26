import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierSmallData
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierTameRestart

/-!
# Global solutions for data with small order-one energy

On the torus the velocity's Wiener sum is bounded by the order-one dissipation
alone, since `∑_{k≠0} (1 + |k|)⁻⁴` converges in three dimensions. With the
finite Young inequality for triad sums, the order-one triad obeys

```text
orderTriad₁ ≤ |(1+|q|)² a_q|_{ℓ²} · |q a_q|_{ℓ²} · ∑ a_k ≤ 4 √L √E₁ D₁,
```

the same small-data form that the lane uses at order five. The convection is
therefore absorbed by the dissipation while `E₁` stays below
`δ₁² = (ν (2π)² / κ₁)²`, and a continuity argument keeps it below `δ₁²/4` forever
when the data have `E₁ ≤ δ₁²/8`: data with small order-one energy have a unique
global solution (`nonempty_globalSolution_of_small_one`). This is the periodic
form of the classical small-`H¹` theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierSmallDataOne

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCurlOutputTail PancakeLatticeDecayEnvelope
open PancakeLocalInfiniteVelocity PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope
open PancakeBlockReality PancakeHigherGalerkinWindow PancakeHigherSobolevWindow
open PancakeArbitraryDataBlocks PancakeGalerkinKineticEnergy PancakeInfinitePressureCoefficients
open PancakeFiniteConvolutionL2
open FourierTameTriad FourierContinuation FourierInfiniteTameRate FourierTameContinuation
open FourierVorticitySupContinuation FourierGlobalSolution FourierSmallData

section Triad

/-- **The order-one triad in small-data form.** -/
theorem orderTriad_one_le_small (M : Finset Wavevector) (a : Wavevector → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hM : ∀ k ∈ M, k ≠ 0) :
    orderTriad 1 M a ≤
      4 * Real.sqrt PancakeSobolevWeights.latticeMass * Real.sqrt (orderEnergy 1 M a) *
        orderDissipation 1 M a := by
  set E := orderEnergy 1 M a with hEdef
  set D := orderDissipation 1 M a with hDdef
  have hE0 : 0 ≤ E := orderEnergy_nonneg 1 M a
  have hD0 : 0 ≤ D := orderDissipation_nonneg 1 M a
  have hw : ∀ k ∈ M, (1 + ‖frequencyVec k‖) ≤ 2 * ‖frequencyVec k‖ := fun k hk ↦ by
    have := one_le_norm_frequencyVec (hM k hk)
    linarith
  -- the three factors
  have h1 : sizeL2 M (fun q ↦ orderWeight 1 q ^ 2 * a q) ≤ 2 * Real.sqrt D := by
    have hsq : (∑ q ∈ M, (orderWeight 1 q ^ 2 * a q) ^ 2) ≤ 4 * D := by
      rw [hDdef]
      unfold orderDissipation orderEnergy
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq ↦ ?_
      have hq' := hw q hq
      have hn : 0 ≤ 1 + ‖frequencyVec q‖ := by positivity
      simp only [orderWeight, pow_one]
      have hsq2 : (1 + ‖frequencyVec q‖) ^ 2 ≤ 4 * ‖frequencyVec q‖ ^ 2 := by nlinarith
      have : ((1 + ‖frequencyVec q‖) ^ 2 * a q) ^ 2 =
          (1 + ‖frequencyVec q‖) ^ 2 * (1 + ‖frequencyVec q‖) ^ 2 * a q ^ 2 := by ring
      rw [this]
      have h' : (1 + ‖frequencyVec q‖) * (‖frequencyVec q‖ * a q) =
          (1 + ‖frequencyVec q‖) * ‖frequencyVec q‖ * a q := by ring
      rw [h']
      have ha2 : 0 ≤ (1 + ‖frequencyVec q‖) ^ 2 * a q ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsq2 ha2]
    unfold sizeL2
    calc Real.sqrt (∑ q ∈ M, (orderWeight 1 q ^ 2 * a q) ^ 2) ≤ Real.sqrt (4 * D) :=
          Real.sqrt_le_sqrt hsq
      _ = 2 * Real.sqrt D := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have h2 : sizeL2 M (fun l ↦ ‖frequencyVec l‖ * a l) ≤ Real.sqrt E := by
    unfold sizeL2
    apply Real.sqrt_le_sqrt
    rw [hEdef]
    unfold orderEnergy
    refine Finset.sum_le_sum fun l _ ↦ ?_
    simp only [orderWeight, pow_one]
    have hl : ‖frequencyVec l‖ ≤ 1 + ‖frequencyVec l‖ := by linarith
    have := mul_le_mul_of_nonneg_right hl (ha l)
    have h0 : 0 ≤ ‖frequencyVec l‖ * a l := mul_nonneg (norm_nonneg _) (ha l)
    exact pow_le_pow_left₀ h0 this 2
  have h3 : (∑ k ∈ M, a k) ≤ Real.sqrt PancakeSobolevWeights.latticeMass * (2 * Real.sqrt D) := by
    refine (sum_le_orderL2 2 le_rfl M a).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    have hsq : (∑ k ∈ M, (orderWeight 2 k * a k) ^ 2) ≤ 4 * D := by
      rw [hDdef]
      unfold orderDissipation orderEnergy
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun q hq ↦ ?_
      have hq' := hw q hq
      simp only [orderWeight, pow_one]
      have hsq2 : (1 + ‖frequencyVec q‖) ^ 2 ≤ 4 * ‖frequencyVec q‖ ^ 2 := by
        have := norm_nonneg (frequencyVec q)
        nlinarith
      have ha2 : 0 ≤ (1 + ‖frequencyVec q‖) ^ 2 * a q ^ 2 := by positivity
      have e1 : ((1 + ‖frequencyVec q‖) ^ 2 * a q) ^ 2 =
          (1 + ‖frequencyVec q‖) ^ 2 * ((1 + ‖frequencyVec q‖) ^ 2 * a q ^ 2) := by ring
      have e2 : (4 : ℝ) * ((1 + ‖frequencyVec q‖) * (‖frequencyVec q‖ * a q)) ^ 2 =
          4 * ‖frequencyVec q‖ ^ 2 * ((1 + ‖frequencyVec q‖) ^ 2 * a q ^ 2) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hsq2 ha2
    unfold sizeL2
    calc Real.sqrt (∑ k ∈ M, (orderWeight 2 k * a k) ^ 2) ≤ Real.sqrt (4 * D) :=
          Real.sqrt_le_sqrt hsq
      _ = 2 * Real.sqrt D := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  have hT := triadSum_le_leftL1 M (fun q ↦ orderWeight 1 q ^ 2 * a q) a
    (fun l ↦ ‖frequencyVec l‖ * a l) (fun k _ ↦ ha k)
  change orderTriad 1 M a ≤ _ at hT
  have hs1 := sizeL2_nonneg M (fun q ↦ orderWeight 1 q ^ 2 * a q)
  have hs2 := sizeL2_nonneg M (fun l ↦ ‖frequencyVec l‖ * a l)
  have hsD := Real.sqrt_nonneg D
  have hsE := Real.sqrt_nonneg E
  have hsL := Real.sqrt_nonneg PancakeSobolevWeights.latticeMass
  have hDD : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hD0
  have hsum0 : 0 ≤ ∑ k ∈ M, a k := Finset.sum_nonneg fun k _ ↦ ha k
  calc orderTriad 1 M a
      ≤ sizeL2 M (fun q ↦ orderWeight 1 q ^ 2 * a q) * sizeL2 M (fun l ↦ ‖frequencyVec l‖ * a l) *
          ∑ k ∈ M, a k := hT
    _ ≤ (2 * Real.sqrt D) * Real.sqrt E *
          (Real.sqrt PancakeSobolevWeights.latticeMass * (2 * Real.sqrt D)) := by
        gcongr
    _ = 4 * Real.sqrt PancakeSobolevWeights.latticeMass * Real.sqrt E *
          (Real.sqrt D * Real.sqrt D) := by ring
    _ = _ := by rw [hDD]

/-- The rate constant of the order-one absorption. -/
def smallRateConstOne : ℝ :=
  2 * (2 * Real.pi) * (4 * Real.sqrt PancakeSobolevWeights.latticeMass)

theorem latticeMass_pos : 0 < PancakeSobolevWeights.latticeMass :=
  summable_latticeDecayWeight.tsum_pos (fun k ↦ (latticeDecayWeight_pos k).le) 0
    (latticeDecayWeight_pos 0)

theorem smallRateConstOne_pos : 0 < smallRateConstOne := by
  unfold smallRateConstOne
  have := Real.sqrt_pos.mpr latticeMass_pos
  positivity

theorem truncConvectionRate_le_small_one (F G : Finset Wavevector)
    (u : FourierVelocity) (hu0 : u 0 = 0) :
    truncConvectionRate 1 F G u ≤ smallRateConstOne *
      Real.sqrt (velocityEnergy 1 (carrier F G) u) * velocityDissipation 1 (carrier F G) u := by
  have ha : ∀ k, 0 ≤ amplitude u k := fun k ↦ norm_nonneg _
  have h1 := (le_abs_self _).trans (abs_truncConvectionRate_le 1 F G u)
  have h2 := truncTriad_le_orderTriad 1 F G (amplitude u) ha (amplitude_zero_of_zero hu0)
  have h3 := orderTriad_one_le_small (carrier F G) (amplitude u) ha
    (fun k hk ↦ mem_carrier_ne_zero hk)
  calc truncConvectionRate 1 F G u ≤ 2 * (2 * Real.pi) * truncTriad 1 F G (amplitude u) := h1
    _ ≤ 2 * (2 * Real.pi) * orderTriad 1 (carrier F G) (amplitude u) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 2 * (2 * Real.pi) * (4 * Real.sqrt PancakeSobolevWeights.latticeMass *
          Real.sqrt (orderEnergy 1 (carrier F G) (amplitude u)) *
            orderDissipation 1 (carrier F G) (amplitude u)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by
        unfold smallRateConstOne velocityEnergy velocityDissipation
        ring

end Triad

section Step

open intervalIntegral
open scoped Interval

variable {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ}

theorem integrated_step_of_rate' (m m' : ℕ) (hm' : 2 ≤ m') (c : SolutionOn nu u₀ T)
    {S : ℝ} (hS : 0 < S) (hST : S < T) {B K R : ℝ}
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy m' F (c.coefficients τ) ≤ B)
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
      (fun G ↦ (sobolevEnergy_le_velocityEnergy m' hm' G _).trans (hB τ hτ G)) q i
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

theorem integrated_small_step_one (c : SolutionOn nu u₀ T)
    {S : ℝ} (hS : 0 < S) (hST : S < T) {B δ X : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 3 F (c.coefficients τ) ≤ B)
    (hsmall : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ δ ^ 2)
    (hX : ∀ G, ∫ τ in (0 : ℝ)..S, velocityDissipation 1 G (c.coefficients τ) ≤ X)
    (F : Finset Wavevector) :
    velocityEnergy 1 F (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 *
        (∫ τ in (0 : ℝ)..S, velocityDissipation 1 F (c.coefficients τ)) ≤
      velocityEnergy 1 F (c.coefficients 0) + smallRateConstOne * δ * X := by
  have hK : ∀ τ ∈ Icc (0 : ℝ) S, ∀ G, velocityEnergy 1 G (c.coefficients τ) ≤ δ ^ 2 := hsmall
  refine integrated_step_of_rate' 1 3 (by norm_num) c hS hST hB hK F fun N ↦ ?_
  set Dc : ℝ → ℝ := fun τ ↦
    velocityDissipation 1 (carrier F (wavevectorBox N)) (c.coefficients τ)
  have hDc_cont : Continuous Dc := continuous_velocityDissipation_along 1 _ c.continuous
  have hpt : ∀ τ ∈ Icc (0 : ℝ) S,
      truncConvectionRate 1 F (wavevectorBox N) (c.coefficients τ) ≤ smallRateConstOne * δ * Dc τ := by
    intro τ hτ
    have h := truncConvectionRate_le_small_one F (wavevectorBox N) (c.coefficients τ)
      (c.zero τ)
    have hsq : Real.sqrt (velocityEnergy 1 (carrier F (wavevectorBox N)) (c.coefficients τ)) ≤ δ := by
      calc Real.sqrt (velocityEnergy 1 (carrier F (wavevectorBox N)) (c.coefficients τ))
          ≤ Real.sqrt (δ ^ 2) := Real.sqrt_le_sqrt (hsmall τ hτ _)
        _ = δ := Real.sqrt_sq hδ
    have hD0 : 0 ≤ Dc τ := orderDissipation_nonneg 1 _ _
    have hk := smallRateConstOne_pos.le
    calc truncConvectionRate 1 F (wavevectorBox N) (c.coefficients τ)
        ≤ smallRateConstOne * Real.sqrt (velocityEnergy 1 (carrier F (wavevectorBox N))
            (c.coefficients τ)) * Dc τ := h
      _ ≤ smallRateConstOne * δ * Dc τ := by gcongr
  calc ∫ τ in (0 : ℝ)..S, truncConvectionRate 1 F (wavevectorBox N) (c.coefficients τ)
      ≤ ∫ τ in (0 : ℝ)..S, smallRateConstOne * δ * Dc τ :=
        intervalIntegral.integral_mono_on hS.le
          ((continuous_truncConvectionRate 1 F _ c.continuous).intervalIntegrable 0 S)
          ((hDc_cont.const_smul (smallRateConstOne * δ)).intervalIntegrable 0 S) hpt
    _ = smallRateConstOne * δ * ∫ τ in (0 : ℝ)..S, Dc τ := intervalIntegral.integral_const_mul _ _
    _ ≤ smallRateConstOne * δ * X :=
        mul_le_mul_of_nonneg_left (hX _) (mul_nonneg smallRateConstOne_pos.le hδ)

/-- **Doubling at order one.** While the order-one energy stays below `δ²`, with
`κ₁ δ ≤ ν (2π)²`, it at most doubles from its initial value. -/
theorem velocityEnergy_le_two_of_small_one (hnu : 0 < nu)
    (c : SolutionOn nu u₀ T) {S : ℝ} (hS : 0 < S) (hST : S < T) {B δ X₀ E₀ : ℝ} (hδ : 0 ≤ δ)
    (hκ : smallRateConstOne * δ ≤ nu * (2 * Real.pi) ^ 2)
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 3 F (c.coefficients τ) ≤ B)
    (hsmall : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ δ ^ 2)
    (hX₀ : ∀ G, ∫ τ in (0 : ℝ)..S, velocityDissipation 1 G (c.coefficients τ) ≤ X₀)
    (hE₀ : ∀ F, velocityEnergy 1 F u₀ ≤ E₀) (F : Finset Wavevector) :
    velocityEnergy 1 F (c.coefficients S) ≤ 2 * E₀ := by
  let I : Finset Wavevector → ℝ := fun G ↦
    ∫ τ in (0 : ℝ)..S, velocityDissipation 1 G (c.coefficients τ)
  have hbdd : BddAbove (Set.range I) := ⟨X₀, by rintro _ ⟨G, rfl⟩; exact hX₀ G⟩
  set X := sSup (Set.range I) with hXdef
  have hIX : ∀ G, I G ≤ X := fun G ↦ le_csSup hbdd ⟨G, rfl⟩
  have hI0 : ∀ G, 0 ≤ I G := fun G ↦
    intervalIntegral.integral_nonneg hS.le fun τ _ ↦ orderDissipation_nonneg 1 G _
  have hX0 : 0 ≤ X := (hI0 ∅).trans (hIX ∅)
  have hstep := fun G ↦ integrated_small_step_one c hS hST hδ hB hsmall hIX G
  have hinit : ∀ G, velocityEnergy 1 G (c.coefficients 0) ≤ E₀ := fun G ↦ by
    rw [c.initial]
    exact hE₀ G
  have hpos : 0 < 2 * nu * (2 * Real.pi) ^ 2 := by positivity
  have hXle : X ≤ (E₀ + smallRateConstOne * δ * X) / (2 * nu * (2 * Real.pi) ^ 2) := by
    refine csSup_le (Set.range_nonempty I) ?_
    rintro _ ⟨G, rfl⟩
    rw [le_div_iff₀ hpos]
    have h := hstep G
    have hE := orderEnergy_nonneg 1 G (amplitude (c.coefficients S))
    change velocityEnergy 1 G (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 * I G ≤ _ at h
    change 0 ≤ velocityEnergy 1 G (c.coefficients S) at hE
    nlinarith [hinit G]
  rw [le_div_iff₀ hpos] at hXle
  have hmix : smallRateConstOne * δ * X ≤ nu * (2 * Real.pi) ^ 2 * X :=
    mul_le_mul_of_nonneg_right hκ hX0
  have hXE : nu * (2 * Real.pi) ^ 2 * X ≤ E₀ := by nlinarith
  have h := hstep F
  have hD := hI0 F
  change velocityEnergy 1 F (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 * I F ≤ _ at h
  nlinarith [hinit F]

end Step

section Bootstrap

variable {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ}

/-- **The order-one bootstrap.** For data with order-one energy at most `δ² / 8`,
where `κ₁ δ ≤ ν (2π)²`, the order-one energy of every tame solution of order three
stays below `δ² / 4`. -/
theorem velocityEnergy_le_of_small_one (hnu : 0 < nu)
    (c : TameSolutionOn nu 3 u₀ T) {δ : ℝ} (hδ : 0 < δ)
    (hκ : smallRateConstOne * δ ≤ nu * (2 * Real.pi) ^ 2)
    (hdata : ∀ F, velocityEnergy 1 F u₀ ≤ δ ^ 2 / 8) :
    ∀ τ ∈ Ico (0 : ℝ) T, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ δ ^ 2 / 4 := by
  -- the step: smallness on `[0, s]` gives the doubling bound at `s`
  have hstep : ∀ s ∈ Ico (0 : ℝ) T,
      (∀ τ ∈ Icc (0 : ℝ) s, fullEnergy 1 (c.coefficients τ) ≤ δ ^ 2) →
        ∀ F, velocityEnergy 1 F (c.coefficients s) ≤ δ ^ 2 / 4 := by
    intro s hs hsmall F
    rcases hs.1.eq_or_lt with h0 | hpos
    · subst h0
      rw [c.initial]
      linarith [hdata F, sq_nonneg δ]
    · obtain ⟨B, hB⟩ := c.order_local s hs.2
      obtain ⟨X, hX⟩ := c.dissipation_local s hs.2
      have hsm : ∀ τ ∈ Icc (0 : ℝ) s, ∀ G, velocityEnergy 1 G (c.coefficients τ) ≤ δ ^ 2 :=
        fun τ hτ G ↦ (velocityEnergy_le_fullEnergy 1 _ (hB τ hτ) G).trans (hsmall τ hτ)
      have hXm : ∀ G, ∫ τ in (0 : ℝ)..s, velocityDissipation 1 G (c.coefficients τ) ≤ X := by
        intro G
        refine le_trans (intervalIntegral.integral_mono_on hpos.le ?_ ?_ fun τ _ ↦ ?_) (hX G)
        · exact (continuous_velocityDissipation_along 1 G c.continuous).intervalIntegrable 0 s
        · exact (continuous_velocityDissipation_along 3 G c.continuous).intervalIntegrable 0 s
        · unfold velocityDissipation orderDissipation orderEnergy
          refine Finset.sum_le_sum fun k _ ↦ ?_
          have hw : orderWeight 1 k ≤ orderWeight 3 k :=
            pow_le_pow_right₀ (by linarith [norm_nonneg (frequencyVec k)]) (by omega)
          have h0 : 0 ≤ orderWeight 1 k := by unfold orderWeight; positivity
          have ha : 0 ≤ ‖frequencyVec k‖ * amplitude (c.coefficients τ) k := by
            unfold amplitude; positivity
          exact pow_le_pow_left₀ (mul_nonneg h0 ha) (mul_le_mul_of_nonneg_right hw ha) 2
      have h := velocityEnergy_le_two_of_small_one hnu c.toSolutionOn hpos hs.2 hδ.le hκ hB hsm
        hXm hdata F
      linarith
  intro τ₁ hτ₁
  set S' := (τ₁ + T) / 2 with hS'def
  have hτS' : τ₁ < S' := by linarith [hτ₁.2]
  have hS'T : S' < T := by linarith [hτ₁.2]
  have hec := continuousOn_fullEnergy c hS'T
  obtain ⟨B', hB'⟩ := c.order_local S' hS'T
  set e : ℝ → ℝ := fun t ↦ fullEnergy 1 (c.coefficients t)
  have hsub : Icc (0 : ℝ) τ₁ ⊆ Icc 0 S' := Icc_subset_Icc le_rfl hτS'.le
  -- the full energy is at most `δ²/4` wherever the smallness held up to that time
  have hfull : ∀ s ∈ Icc (0 : ℝ) τ₁, (∀ τ ∈ Icc (0 : ℝ) s, e τ ≤ δ ^ 2) → e s ≤ δ ^ 2 / 4 :=
    fun s hs h ↦ fullEnergy_le_of_forall 1 _
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

/-- The smallness radius at order one. -/
def smallRadiusOne (nu : ℝ) : ℝ := nu * (2 * Real.pi) ^ 2 / smallRateConstOne

theorem smallRadiusOne_pos {nu : ℝ} (hnu : 0 < nu) : 0 < smallRadiusOne nu :=
  div_pos (by positivity) smallRateConstOne_pos

theorem smallRateConstOne_mul_smallRadiusOne (nu : ℝ) :
    smallRateConstOne * smallRadiusOne nu = nu * (2 * Real.pi) ^ 2 := by
  unfold smallRadiusOne
  field_simp [smallRateConstOne_pos.ne']

/-- **Global existence for data with small order-one energy.** For order `m ≥ 7`,
admissible data of finite order-`m` energy whose order-one energy is at most
`smallRadiusOne ν ² / 8` have a unique global solution. -/
theorem nonempty_globalSolution_of_small_one (m : ℕ) (hm : 7 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀)
    (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀)
    (hsmall : ∀ F, velocityEnergy 1 F u₀ ≤ smallRadiusOne nu ^ 2 / 8) :
    Nonempty (GlobalSolution nu m u₀) := by
  have hδ := smallRadiusOne_pos hnu
  have hκ : smallRateConstOne * smallRadiusOne nu ≤ nu * (2 * Real.pi) ^ 2 :=
    (smallRateConstOne_mul_smallRadiusOne nu).le
  refine nonempty_globalSolution hm hnu ?_
  refine exists_tameSolutionOn_of_orderOne m (by omega) hnu u₀ hr hd hz hE₀0 hE₀ ?_
  intro H _
  refine ⟨smallRadiusOne nu ^ 2 / 4, fun T _ c τ hτ F ↦ ?_⟩
  exact velocityEnergy_le_of_small_one hnu (c.ofLe (by omega)) hδ hκ hsmall τ hτ F

end Global

end Mettapedia.FluidDynamics.NavierStokes.FourierSmallDataOne
