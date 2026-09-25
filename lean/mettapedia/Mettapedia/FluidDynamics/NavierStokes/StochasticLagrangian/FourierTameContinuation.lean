import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierInfiniteTameRate

/-!
# Continuation of the Fourier solutions under order-one control

The Galerkin solutions satisfy `rate_m + ν(2π)² D_m ≤ C_m E_m²`, so their
integrated order-`m` dissipation is bounded on the local window. The bound
passes to the Galerkin limit for every finite truncation. Solutions carrying
local order-`m` bounds and bounds on the truncated integrated dissipations
(`TameSolutionOn`) are therefore produced by restarts and preserved by gluing.

For such solutions `FourierInfiniteTameRate.orderEnergy_le_of_orderOne`
turns a bound on the order-one energy into a bound on the order-`m` energy,
so the solution extends by a length depending only on those bounds. If the
order-one energy of every such solution is bounded on each finite horizon,
solutions exist on every finite interval. That hypothesis is the analytic
input that the dynamical budget must supply; it is not proved here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierTameContinuation

open scoped BigOperators Topology Interval
open Filter Set MeasureTheory intervalIntegral
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeHigherSobolevWindow PancakeLocalVelocityExistence
open PancakeGalerkinCoefficientLimit PancakeCoefficientLimitProperties
open PancakeCoefficientLimitEquation PancakeLocalInfiniteVelocity PancakeHigherGalerkinWindow
open PancakeHigherLocalVelocity FourierContinuation FourierTameTriad FourierInfiniteTameRate
open PancakeGalerkinKineticEnergy PancakeBlockReality PancakeArbitraryDataBlocks

/-! ### Integrated dissipation of the Galerkin solutions -/

theorem continuousOn_coefficient {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) (q : Wavevector) (i : Fin 3) :
    ContinuousOn (fun t ↦ s.coefficients t q i) (Icc (0 : ℝ) T) := by
  by_cases hq : q ∈ M
  · exact fun t ht ↦ (s.equation t ht q hq i).continuousAt.continuousWithinAt
  · have h : (fun t ↦ s.coefficients t q i) = fun _ ↦ 0 := by
      funext t
      rw [s.support t q hq]
      rfl
    rw [h]
    exact continuousOn_const

theorem continuousOn_velocityEnergy_galerkin (m : ℕ) (F : Finset Wavevector)
    {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) :
    ContinuousOn (fun t ↦ velocityEnergy m F (s.coefficients t)) (Icc (0 : ℝ) T) := by
  have hc := continuousOn_coefficient s
  simp only [velocityEnergy_eq, coefficientEnergy]
  fun_prop

theorem continuousOn_velocityDissipation_galerkin (m : ℕ) (F : Finset Wavevector)
    {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}
    (s : LocalVelocitySolution M nu u₀ T) :
    ContinuousOn (fun t ↦ velocityDissipation m F (s.coefficients t)) (Icc (0 : ℝ) T) := by
  have hc := continuousOn_coefficient s
  simp only [velocityDissipation_eq, coefficientEnergy]
  fun_prop

/-- The integrated order-`m` dissipation of a Galerkin solution on its window. -/
theorem galerkin_dissipation_le (m : ℕ) (hm : 2 ≤ m) {M : Finset Wavevector} {nu T : ℝ}
    {u₀ : FourierVelocity} (s : LocalVelocitySolution M nu u₀ T) (hnu : 0 < nu)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (hT : 0 ≤ T) {B : ℝ}
    (hB : ∀ t ∈ Icc (0 : ℝ) T, velocityEnergy m M (s.coefficients t) ≤ B) :
    nu * (2 * Real.pi) ^ 2 * (∫ τ in (0 : ℝ)..T, velocityDissipation m M (s.coefficients τ)) ≤
      velocityEnergy m M (s.coefficients 0) + orderGrowthConstant m nu * B ^ 2 * T := by
  set E := fun t ↦ velocityEnergy m M (s.coefficients t)
  set D := fun t ↦ velocityDissipation m M (s.coefficients t)
  set C := orderGrowthConstant m nu
  have hC : 0 ≤ C := orderGrowthConstant_nonneg m nu hnu
  have hDcont : ContinuousOn D (Icc (0 : ℝ) T) := continuousOn_velocityDissipation_galerkin m M s
  have hφint : IntegrableOn (fun t ↦ C * B ^ 2 - nu * (2 * Real.pi) ^ 2 * D t) (Icc (0 : ℝ) T) :=
    (continuousOn_const.sub (continuousOn_const.mul hDcont)).integrableOn_Icc
  have hmain := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le_Ico hT
    (continuousOn_velocityEnergy_galerkin m M s)
    (fun t ht ↦ (localSolution_order_derivative m s t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    hφint (fun t ht ↦ by
      have hrate := absorbed_orderVelocityRate_le m hm M (s.coefficients t) nu hnu hk
        (fun q hq ↦ s.transverse t q hq)
      have hE0 : 0 ≤ E t := orderEnergy_nonneg m M _
      have hEB : E t ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hE0 (hB t ⟨ht.1, ht.2.le⟩) 2
      have := mul_le_mul_of_nonneg_left hEB hC
      change orderVelocityRate m M (s.coefficients t) (velocityRHS M (s.coefficients t) nu) ≤
        C * B ^ 2 - nu * (2 * Real.pi) ^ 2 * D t
      linarith)
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((hDcont.intervalIntegrable_of_Icc hT).const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hmain
  simp only [sub_zero, smul_eq_mul] at hmain
  have hET : 0 ≤ E T := orderEnergy_nonneg m M _
  change E T - E 0 ≤ T * (C * B ^ 2) - nu * (2 * Real.pi) ^ 2 * ∫ τ in (0 : ℝ)..T, D τ at hmain
  change nu * (2 * Real.pi) ^ 2 * (∫ τ in (0 : ℝ)..T, D τ) ≤ E 0 + C * B ^ 2 * T
  linarith

/-! ### The dissipation bound of the Galerkin limit -/

theorem velocityDissipation_of_support_le (m : ℕ) (M F : Finset Wavevector)
    (u : FourierVelocity) (hs : ∀ q, q ∉ M → u q = 0) :
    velocityDissipation m F u ≤ velocityDissipation m M u := by
  rw [velocityDissipation_eq, velocityDissipation_eq]
  have he : (∑ q ∈ F ∩ M, orderWeight m q ^ 2 * ‖frequencyVec q‖ ^ 2 *
      coefficientEnergy (u q)) =
      ∑ q ∈ F, orderWeight m q ^ 2 * ‖frequencyVec q‖ ^ 2 * coefficientEnergy (u q) := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro q hq hn
    have hM : q ∉ M := fun hm ↦ hn (Finset.mem_inter.mpr ⟨hq, hm⟩)
    rw [hs q hM]
    simp [coefficientEnergy]
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
  intro q _ _
  rw [← norm_coefficientVec_sq]
  positivity

theorem continuous_velocityDissipation (m : ℕ) (F : Finset Wavevector) :
    Continuous (velocityDissipation m F) := by
  change Continuous (fun u : FourierVelocity ↦ velocityDissipation m F u)
  simp only [velocityDissipation_eq, coefficientEnergy]
  fun_prop

/-- The truncated order-`m` dissipation is bounded by the order-`m` energy. -/
theorem velocityDissipation_le_energy (m : ℕ) (G : Finset Wavevector) (u : FourierVelocity)
    {B : ℝ} (hB : ∀ F, velocityEnergy m F u ≤ B) :
    velocityDissipation m G u ≤ (∑ k ∈ G, ‖frequencyVec k‖ ^ 2) * B := by
  rw [velocityDissipation_eq, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have h := hB {k}
  rw [velocityEnergy_eq, Finset.sum_singleton] at h
  calc orderWeight m k ^ 2 * ‖frequencyVec k‖ ^ 2 * coefficientEnergy (u k)
      = ‖frequencyVec k‖ ^ 2 * (orderWeight m k ^ 2 * coefficientEnergy (u k)) := by ring
    _ ≤ ‖frequencyVec k‖ ^ 2 * B := mul_le_mul_of_nonneg_left h (sq_nonneg _)

/-- A common bound on the integrated Galerkin dissipations passes to every
truncation of the coefficient limit. -/
theorem limit_dissipation_le (m : ℕ) {nu T : ℝ} {u₀ : FourierVelocity}
    (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
    (phi : ℕ → ℕ) (a : CoefficientLimit T) (h : IsCoefficientLimit s phi a) (hT : 0 ≤ T)
    {X B : ℝ}
    (hX : ∀ n, ∫ τ in (0 : ℝ)..T, velocityDissipation m (galerkinModes n) ((s n).coefficients τ) ≤ X)
    (hB : ∀ n t, t ∈ Icc (0 : ℝ) T → velocityEnergy m (galerkinModes n) ((s n).coefficients t) ≤ B)
    (G : Finset Wavevector) :
    ∫ τ in (0 : ℝ)..T, velocityDissipation m G (coefficientCurve a hT τ) ≤ X := by
  set f : ℕ → ℝ → ℝ := fun n τ ↦ velocityDissipation m G ((s (phi n)).coefficients τ)
  have hbound : ∀ n, ∀ τ ∈ Icc (0 : ℝ) T, |f n τ| ≤ (∑ k ∈ G, ‖frequencyVec k‖ ^ 2) * B := by
    intro n τ hτ
    have h0 : 0 ≤ f n τ := orderDissipation_nonneg m G _
    rw [abs_of_nonneg h0]
    exact velocityDissipation_le_energy m G _ fun F ↦
      (velocityEnergy_of_support_le m _ F _ ((s (phi n)).support τ)).trans (hB (phi n) τ hτ)
  have hlim : ∀ τ ∈ Icc (0 : ℝ) T, Tendsto (fun n ↦ f n τ) atTop
      (nhds (velocityDissipation m G (coefficientCurve a hT τ))) := by
    intro τ hτ
    rw [coefficientCurve_apply a hT τ hτ]
    exact ((continuous_velocityDissipation m G).tendsto _).comp
      (tendsto_limitField s phi a h ⟨τ, hτ⟩)
  have hmem : ∀ τ, τ ∈ Ι (0 : ℝ) T → τ ∈ Icc (0 : ℝ) T := fun τ hτ ↦
    mem_Icc_of_mem_uIoc hT hτ
  have hDCT : Tendsto (fun n ↦ ∫ τ in (0 : ℝ)..T, f n τ) atTop
      (nhds (∫ τ in (0 : ℝ)..T, velocityDissipation m G (coefficientCurve a hT τ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ ↦ (∑ k ∈ G, ‖frequencyVec k‖ ^ 2) * B)
    · refine Eventually.of_forall fun n ↦ ?_
      have hc : ContinuousOn (f n) (Icc (0 : ℝ) T) :=
        continuousOn_velocityDissipation_galerkin m G (s (phi n))
      rw [uIoc_of_le hT]
      exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · exact Eventually.of_forall fun n ↦ Eventually.of_forall fun τ hτ ↦ by
        rw [Real.norm_eq_abs]
        exact hbound n τ (hmem τ hτ)
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun τ hτ ↦ hlim τ (hmem τ hτ)
  refine le_of_tendsto' hDCT fun n ↦ ?_
  have hc1 := continuousOn_velocityDissipation_galerkin m G (s (phi n))
  have hc2 := continuousOn_velocityDissipation_galerkin m (galerkinModes (phi n)) (s (phi n))
  calc ∫ τ in (0 : ℝ)..T, f n τ ≤
        ∫ τ in (0 : ℝ)..T, velocityDissipation m (galerkinModes (phi n))
          ((s (phi n)).coefficients τ) :=
      intervalIntegral.integral_mono_on hT (hc1.intervalIntegrable_of_Icc hT)
        (hc2.intervalIntegrable_of_Icc hT) fun τ _ ↦
          velocityDissipation_of_support_le m _ G _ ((s (phi n)).support τ)
    _ ≤ X := hX (phi n)

/-! ### Restarts with dissipation bounds -/

/-- The bound on the integrated order-`m` dissipation of a restart. -/
def dissBound (m : ℕ) (nu B₀ : ℝ) : ℝ :=
  (B₀ + orderGrowthConstant m nu * (2 * (B₀ + 1)) ^ 2 * window m nu B₀) /
    (nu * (2 * Real.pi) ^ 2)

theorem exists_tameRestart (m : ℕ) (hm : 2 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (v : FourierVelocity) (hr : ∀ q, v (-q) = coefficientConjugate (v q))
    (hd : ∀ q, modeDot q (v q) = 0) (hz : v 0 = 0) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hE₀ : ∀ M : Finset Wavevector, velocityEnergy m M v ≤ B₀) :
    ∃ d : RestartData nu v (window m nu B₀),
      (∀ t ∈ Icc (0 : ℝ) (window m nu B₀), ∀ F,
        velocityEnergy m F (d.curve t) ≤ 2 * (B₀ + 1)) ∧
      ∀ G, ∫ τ in (0 : ℝ)..window m nu B₀, velocityDissipation m G (d.curve τ) ≤
        dissBound m nu B₀ := by
  obtain ⟨s, a, phi, hphi, hb, ha⟩ := exists_window_limit m hm hnu v hr hd hB₀ hE₀
  have hT := window_pos m hnu hB₀
  have hB : (0 : ℝ) ≤ 2 * (B₀ + 1) := by positivity
  let sol := localInfiniteVelocitySolutionOfOrder m hm s phi a ha hphi hT.le hz
    (2 * (B₀ + 1)) hB hb
  have hE₂ : ∀ n t, t ∈ Icc (0 : ℝ) (window m nu B₀) →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ 2 * (B₀ + 1) :=
    fun n t ht ↦ (sobolevEnergy_le_velocityEnergy m hm _ _).trans (hb n t ht)
  let D : RestartData nu v (window m nu B₀) :=
    { curve := sol.coefficients
      continuous := sol.continuous
      initial := sol.initial
      reality := sol.reality
      transverse := sol.transverse
      zero := sol.zero
      sobolev := ⟨2 * (B₀ + 1), fun t ht F ↦ sol.sobolev_bound t ht F⟩
      equation := sol.equation
      start := fun q i ↦ coefficientCurve_hasDerivWithinAt_zero s phi a ha hphi hT
        (2 * (B₀ + 1)) hB hE₂ q i }
  refine ⟨D, fun t ht F ↦ localInfiniteVelocitySolutionOfOrder_bound m hm s phi a ha hphi
    hT.le hz (2 * (B₀ + 1)) hB hb t ht F, fun G ↦ ?_⟩
  have hν : 0 < nu * (2 * Real.pi) ^ 2 := by positivity
  apply limit_dissipation_le m s phi a ha hT.le (X := dissBound m nu B₀) (B := 2 * (B₀ + 1))
    _ hb G
  intro n
  have hg := galerkin_dissipation_le m hm (s n) hnu (fun k hk ↦ galerkinModes_nonzero n k hk)
    hT.le (hb n)
  rw [initial_velocityEnergy m (s n)] at hg
  unfold dissBound
  rw [le_div_iff₀ hν]
  linarith [hE₀ (galerkinModes n)]

/-! ### Solutions with local order-`m` and dissipation bounds -/

/-- A solution on `[0, T)` with local order-`m` bounds and local bounds on
every truncated integrated order-`m` dissipation. -/
structure TameSolutionOn (nu : ℝ) (m : ℕ) (u₀ : FourierVelocity) (T : ℝ)
    extends SolutionOn nu u₀ T where
  order_local : ∀ S < T, ∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) S, ∀ F : Finset Wavevector,
    velocityEnergy m F (coefficients τ) ≤ B
  dissipation_local : ∀ S < T, ∃ X : ℝ, ∀ G : Finset Wavevector,
    ∫ τ in (0 : ℝ)..S, velocityDissipation m G (coefficients τ) ≤ X

theorem integral_dissipation_mono {c : ℝ → FourierVelocity}
    (hc : ∀ q i, Continuous (fun t ↦ c t q i)) (m : ℕ) (G : Finset Wavevector) {S S' : ℝ}
    (hS : 0 ≤ S) (hSS' : S ≤ S') :
    ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c τ) ≤
      ∫ τ in (0 : ℝ)..S', velocityDissipation m G (c τ) :=
  intervalIntegral.integral_mono_interval le_rfl hS hSS'
    (Eventually.of_forall fun _ ↦ orderDissipation_nonneg m G _)
    ((continuous_velocityDissipation_along m G hc).intervalIntegrable 0 S')

/-- A restart with its bounds is a tame solution on its window. -/
def TameSolutionOn.ofRestart {nu : ℝ} (m : ℕ) {v : FourierVelocity} {δ B X : ℝ}
    (d : RestartData nu v δ)
    (hB : ∀ t ∈ Icc (0 : ℝ) δ, ∀ F, velocityEnergy m F (d.curve t) ≤ B)
    (hX : ∀ G, ∫ τ in (0 : ℝ)..δ, velocityDissipation m G (d.curve τ) ≤ X) :
    TameSolutionOn nu m v δ where
  coefficients := d.curve
  continuous := d.continuous
  initial := d.initial
  reality := d.reality
  transverse := d.transverse
  zero := d.zero
  sobolev_local := fun S hS ↦ by
    obtain ⟨B', hB'⟩ := d.sobolev
    exact ⟨B', fun t ht F ↦ hB' t ⟨ht.1, ht.2.trans hS.le⟩ F⟩
  equation := d.equation
  order_local := fun S hS ↦ ⟨B, fun t ht F ↦ hB t ⟨ht.1, ht.2.trans hS.le⟩ F⟩
  dissipation_local := fun S hS ↦ ⟨max X 0, fun G ↦ by
    rcases le_or_gt 0 S with h0 | h0
    · exact (integral_dissipation_mono d.continuous m G h0 hS.le).trans
        ((hX G).trans (le_max_left _ _))
    · have : ∫ τ in (0 : ℝ)..S, velocityDissipation m G (d.curve τ) ≤ 0 := by
        rw [intervalIntegral.integral_symm]
        have hnn := intervalIntegral.integral_nonneg (μ := volume) h0.le
          (fun τ _ ↦ orderDissipation_nonneg m G (amplitude (d.curve τ)))
        change 0 ≤ ∫ τ in S..0, velocityDissipation m G (d.curve τ) at hnn
        linarith
      exact this.trans (le_max_right _ _)⟩

/-- Restricting a tame solution to a shorter interval. -/
def TameSolutionOn.restrict {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity} {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) {T' : ℝ} (hT' : T' ≤ T) : TameSolutionOn nu m u₀ T' where
  coefficients := c.coefficients
  continuous := c.continuous
  initial := c.initial
  reality := c.reality
  transverse := c.transverse
  zero := c.zero
  sobolev_local := fun S hS ↦ c.sobolev_local S (lt_of_lt_of_le hS hT')
  equation := fun t ht ↦ c.equation t ⟨ht.1, lt_of_lt_of_le ht.2 hT'⟩
  order_local := fun S hS ↦ c.order_local S (lt_of_lt_of_le hS hT')
  dissipation_local := fun S hS ↦ c.dissipation_local S (lt_of_lt_of_le hS hT')

/-- **Gluing preserves the tame bounds.** -/
def TameSolutionOn.glue {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity} {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) {t₁ δ T' B X : ℝ} (ht₁0 : 0 ≤ t₁) (ht₁T : t₁ < T)
    (d : RestartData nu (c.coefficients t₁) δ)
    (hB : ∀ t ∈ Icc (0 : ℝ) δ, ∀ F, velocityEnergy m F (d.curve t) ≤ B)
    (hX : ∀ G, ∫ τ in (0 : ℝ)..δ, velocityDissipation m G (d.curve τ) ≤ X)
    (hT' : T' ≤ t₁ + δ) : TameSolutionOn nu m u₀ T' where
  toSolutionOn := c.toSolutionOn.glue ht₁0 ht₁T d hT'
  order_local := fun S hS ↦ by
    obtain ⟨Bc, hBc⟩ := c.order_local t₁ ht₁T
    refine ⟨max Bc B, fun t ht F ↦ ?_⟩
    rw [SolutionOn.glue_coefficients]
    by_cases h : t ≤ t₁
    · simp only [h, ↓reduceIte]
      exact (hBc t ⟨ht.1, h⟩ F).trans (le_max_left _ _)
    · simp only [h, ↓reduceIte]
      exact (hB (t - t₁) ⟨by linarith [not_le.mp h], by linarith [ht.2]⟩ F).trans
        (le_max_right _ _)
  dissipation_local := fun S hS ↦ by
    obtain ⟨Xc, hXc⟩ := c.dissipation_local t₁ ht₁T
    refine ⟨max Xc 0 + max X 0, fun G ↦ ?_⟩
    set g := c.toSolutionOn.glue ht₁0 ht₁T d hT'
    have hgc := g.continuous
    have hDg := continuous_velocityDissipation_along m G hgc
    have hDc := continuous_velocityDissipation_along m G c.continuous
    have hDd := continuous_velocityDissipation_along m G d.continuous
    have hint0 : ∫ τ in (0 : ℝ)..t₁, velocityDissipation m G (g.coefficients τ) ≤ max Xc 0 := by
      have heq : ∫ τ in (0 : ℝ)..t₁, velocityDissipation m G (g.coefficients τ) =
          ∫ τ in (0 : ℝ)..t₁, velocityDissipation m G (c.coefficients τ) := by
        refine intervalIntegral.integral_congr fun τ hτ ↦ ?_
        rw [uIcc_of_le ht₁0] at hτ
        simp [g, SolutionOn.glue_coefficients, hτ.2]
      rw [heq]
      exact (hXc G).trans (le_max_left _ _)
    have hXd0 : ∀ r, 0 ≤ r → r ≤ δ →
        ∫ τ in (0 : ℝ)..r, velocityDissipation m G (d.curve τ) ≤ max X 0 := fun r hr hrδ ↦
      (integral_dissipation_mono d.continuous m G hr hrδ).trans ((hX G).trans (le_max_left _ _))
    rcases le_or_gt S t₁ with hSt | hSt
    · rcases le_or_gt 0 S with h0 | h0
      · have h1 := integral_dissipation_mono hgc m G h0 hSt
        have := hint0
        have : 0 ≤ max X 0 := le_max_right _ _
        linarith
      · have hneg : ∫ τ in (0 : ℝ)..S, velocityDissipation m G (g.coefficients τ) ≤ 0 := by
          rw [intervalIntegral.integral_symm]
          have hnn := intervalIntegral.integral_nonneg (μ := volume) h0.le
            (fun τ _ ↦ orderDissipation_nonneg m G (amplitude (g.coefficients τ)))
          change 0 ≤ ∫ τ in S..0, velocityDissipation m G (g.coefficients τ) at hnn
          linarith
        have : 0 ≤ max Xc 0 := le_max_right _ _
        have : 0 ≤ max X 0 := le_max_right _ _
        linarith
    · have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hDg.intervalIntegrable (μ := volume) 0 t₁) (hDg.intervalIntegrable (μ := volume) t₁ S)
      have heq : ∫ τ in t₁..S, velocityDissipation m G (g.coefficients τ) =
          ∫ τ in (0 : ℝ)..(S - t₁), velocityDissipation m G (d.curve τ) := by
        have h1 : ∫ τ in t₁..S, velocityDissipation m G (g.coefficients τ) =
            ∫ τ in t₁..S, velocityDissipation m G (d.curve (τ - t₁)) := by
          refine intervalIntegral.integral_congr fun τ hτ ↦ ?_
          rw [uIcc_of_le hSt.le] at hτ
          rcases eq_or_lt_of_le hτ.1 with h | h
          · subst h
            simp [g, SolutionOn.glue_coefficients, d.initial]
          · simp [g, SolutionOn.glue_coefficients, not_le.mpr h]
        rw [h1, intervalIntegral.integral_comp_sub_right
          (fun σ ↦ velocityDissipation m G (d.curve σ)) t₁, sub_self]
      have hd2 := hXd0 (S - t₁) (by linarith) (by linarith [hS])
      rw [← hsplit, heq]
      linarith

/-! ### Continuation under order-one control -/

/-- **Continuation criterion.** A tame solution on `[0, T)` whose order-one
energy stays at most `K` extends by `window m ν M / 2` for every
`M ≥ 2 (E₀ + C K^(4m+1) T)`. -/
theorem TameSolutionOn.extend_of_orderOne (m : ℕ) (hm : 2 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    {u₀ : FourierVelocity} {T : ℝ} (hT : 0 < T) (c : TameSolutionOn nu m u₀ T)
    {K E₀ M : ℝ}
    (hK : ∀ τ ∈ Ico (0 : ℝ) T, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ K)
    (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀)
    (hM : 2 * (E₀ + tameRateConst m nu * K ^ (4 * m + 1) * T) ≤ M) :
    Nonempty (TameSolutionOn nu m u₀ (T + window m nu M / 2)) := by
  have hK0 : 0 ≤ K := le_trans (orderEnergy_nonneg 1 ∅ _) (hK 0 ⟨le_rfl, hT⟩ ∅)
  have hE₀0 : 0 ≤ E₀ := le_trans (orderEnergy_nonneg m ∅ _) (hE₀ ∅)
  have hC0 : 0 ≤ tameRateConst m nu * K ^ (4 * m + 1) :=
    mul_nonneg (tameRateConst_nonneg m hnu) (pow_nonneg hK0 _)
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  have hbound : ∀ t ∈ Ico (0 : ℝ) T, ∀ F, velocityEnergy m F (c.coefficients t) ≤ M := by
    intro t ht F
    obtain ⟨B, hB⟩ := c.order_local t ht.2
    obtain ⟨X, hX⟩ := c.dissipation_local t ht.2
    have h := orderEnergy_le_of_orderOne m hm hnu c.toSolutionOn ht.1 ht.2 hB hX
      (fun τ hτ F ↦ hK τ ⟨hτ.1, lt_of_le_of_lt hτ.2 ht.2⟩ F) hE₀ F
    have ht' : tameRateConst m nu * K ^ (4 * m + 1) * t ≤
        tameRateConst m nu * K ^ (4 * m + 1) * T :=
      mul_le_mul_of_nonneg_left ht.2.le hC0
    linarith
  set δ := window m nu M
  have hδ : 0 < δ := window_pos m hnu hM0
  set t₁ := max 0 (T - δ / 2) with ht₁def
  have ht₁0 : 0 ≤ t₁ := le_max_left _ _
  have ht₁T : t₁ < T := max_lt hT (by linarith)
  have ht₁end : T + δ / 2 ≤ t₁ + δ := by
    rcases le_total 0 (T - δ / 2) with h | h
    · rw [ht₁def, max_eq_right h]
      linarith
    · rw [ht₁def, max_eq_left h]
      linarith
  obtain ⟨d, hdB, hdX⟩ := exists_tameRestart m hm hnu (c.coefficients t₁) (c.reality t₁)
    (c.transverse t₁) (c.zero t₁) hM0 (hbound t₁ ⟨ht₁0, ht₁T⟩)
  exact ⟨c.glue ht₁0 ht₁T d hdB hdX ht₁end⟩

/-- Admissible Fourier data start a tame solution. -/
theorem exists_tameSolutionOn (m : ℕ) (hm : 2 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀)
    (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀) :
    Nonempty (TameSolutionOn nu m u₀ (window m nu E₀)) := by
  obtain ⟨d, hdB, hdX⟩ := exists_tameRestart m hm hnu u₀ hr hd hz hE₀0 hE₀
  exact ⟨TameSolutionOn.ofRestart m d hdB hdX⟩

/-- **Global existence under order-one control.** If on every finite horizon
the order-one energy of every tame solution from `u₀` is bounded by a common
constant, tame solutions exist on every interval `[0, H)`. -/
theorem exists_tameSolutionOn_of_orderOne (m : ℕ) (hm : 2 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀)
    (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀)
    (horder : ∀ H, 0 < H → ∃ K, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
      ∀ τ ∈ Ico (0 : ℝ) T, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ K) :
    ∀ H, 0 < H → Nonempty (TameSolutionOn nu m u₀ H) := by
  intro H hH
  obtain ⟨K, hK⟩ := horder H hH
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  set M := 2 * (E₀ + tameRateConst m nu * max K 0 ^ (4 * m + 1) * H) with hMdef
  have hC0 : 0 ≤ tameRateConst m nu * max K 0 ^ (4 * m + 1) :=
    mul_nonneg (tameRateConst_nonneg m hnu) (pow_nonneg hK0 _)
  have hM0 : 0 ≤ M := by positivity
  set δ := window m nu M
  have hδ : 0 < δ := window_pos m hnu hM0
  obtain ⟨c₀⟩ := exists_tameSolutionOn m hm hnu u₀ hr hd hz hE₀0 hE₀
  set δ₀ := min (window m nu E₀) H
  have hδ₀ : 0 < δ₀ := lt_min (window_pos m hnu hE₀0) hH
  -- existence on the horizons `min H (δ₀ + n δ/2)`
  have hstep : ∀ n : ℕ, Nonempty (TameSolutionOn nu m u₀ (min H (δ₀ + n * (δ / 2)))) := by
    intro n
    induction n with
    | zero =>
        simp only [Nat.cast_zero, zero_mul, add_zero]
        exact ⟨c₀.restrict ((min_le_right _ _).trans (min_le_left _ _))⟩
    | succ n ih =>
        obtain ⟨c⟩ := ih
        set Tn := min H (δ₀ + n * (δ / 2))
        have hTn : 0 < Tn := lt_min hH (by positivity)
        have hTnH : Tn ≤ H := min_le_left _ _
        by_cases hfull : Tn = H
        · have htarget : min H (δ₀ + (n + 1 : ℕ) * (δ / 2)) = H := by
            apply min_eq_left
            have : H ≤ δ₀ + n * (δ / 2) := by
              rw [← hfull]; exact min_le_right _ _
            push_cast
            nlinarith
          rw [htarget]
          rw [hfull] at c
          exact ⟨c⟩
        · have hext := TameSolutionOn.extend_of_orderOne m hm hnu hTn c
            (K := max K 0) (E₀ := E₀) (M := M)
            (fun τ hτ F ↦ (hK Tn hTnH c τ hτ F).trans (le_max_left _ _)) hE₀
            (by
              have : tameRateConst m nu * max K 0 ^ (4 * m + 1) * Tn ≤
                  tameRateConst m nu * max K 0 ^ (4 * m + 1) * H :=
                mul_le_mul_of_nonneg_left hTnH hC0
              rw [hMdef]
              linarith)
          obtain ⟨c'⟩ := hext
          have hTn_eq : Tn = δ₀ + n * (δ / 2) := by
            rcases min_choice H (δ₀ + n * (δ / 2)) with h | h
            · exact absurd h hfull
            · exact h
          have hle : min H (δ₀ + (n + 1 : ℕ) * (δ / 2)) ≤ Tn + δ / 2 := by
            refine (min_le_right _ _).trans (le_of_eq ?_)
            rw [hTn_eq]
            push_cast
            ring
          exact ⟨c'.restrict hle⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((H - δ₀) / (δ / 2))
  have hHle : min H (δ₀ + n * (δ / 2)) = H := by
    apply min_eq_left
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < δ / 2)).mp hn
    linarith
  have hc := hstep n
  rw [hHle] at hc
  exact hc

end Mettapedia.FluidDynamics.NavierStokes.FourierTameContinuation
