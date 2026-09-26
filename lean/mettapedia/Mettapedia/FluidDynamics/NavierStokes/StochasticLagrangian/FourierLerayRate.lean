import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierAgmon
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierLerayTime

/-!
# The order-one lifespan and Leray's lower bound on the blowup rate

With Agmon's inequality the order-one convection is absorbed by the dissipation
up to a cubic term (`FourierAgmon.truncConvectionRate_le_agmon`), so along every
tame solution

```text
E₁(S) + ν (2π)² ∫₀^S D₁ ≤ E₁(0) + C ∫₀^S E₁³,   C = cubicConst ν ≍ ν⁻³,
```

in the integrated form of `dE₁/dt ≤ C E₁³`. A continuity argument turns it into a
lifespan bound: data with order-one energy `E₀` keep `E₁ ≤ 3 E₀` for as long as
`128 C E₀² t ≤ 1` (`velocityEnergy_le_three_of_lifespan`), and a tame solution
exists on that interval (`nonempty_tameSolutionOn_of_lifespan`): the lifespan of
the periodic problem is at least of order `ν³ / E₁(0)²`, whatever the higher
norms.

Restarting at any time `t₀` gives **Leray's lower bound on the blowup rate**: if a
tame solution on `[0, T)` admits no extension to a longer interval, then at every
earlier time `t₀`

```text
128 C E₁(t₀)² (T - t₀) ≥ 1,   that is   E₁(t₀) ≥ (128 C (T - t₀))^(-1/2)
```

(`one_le_lerayRate`). A singularity at `T` forces the order-one energy to blow
up at least like `ν^(3/2) / √(T - t)`.

The same rate, with the interpolation `E₁² ≤ 4 K D₁` on nonzero modes and the
non-increasing kinetic energy `K`, puts the cubic term under the dissipation when
`64 C K₀ E₀ ≤ ν (2π)²`. Data with `K₀ E₀ ≲ ν⁴`, a smallness condition invariant
under the Navier–Stokes scaling, therefore have a unique global solution
(`nonempty_globalSolution_of_small_product`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierLerayRate

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCurlOutputTail PancakeLatticeDecayEnvelope
open PancakeLocalInfiniteVelocity PancakeGalerkinKineticEnergy PancakeArbitraryDataBlocks
open FourierTameTriad FourierContinuation FourierTameContinuation FourierInfiniteTameRate
open FourierGlobalSolution FourierRegularityEquivalence FourierSmallData FourierSmallDataOne
open PancakeBlockReality FourierAgmon

/-- The constant of the cubic order-one inequality `dE₁/dt ≤ C E₁³`. -/
def cubicConst (nu : ℝ) : ℝ := agmonRateConst ^ 4 / (8 * (nu * (2 * Real.pi) ^ 2) ^ 3)

theorem cubicConst_pos {nu : ℝ} (hnu : 0 < nu) : 0 < cubicConst nu := by
  unfold cubicConst
  have := agmonRateConst_pos
  positivity

/-! ## A continuity bootstrap -/

/-- **A continuity bootstrap.** If a continuous `e` starts at most `a < b`, and staying
at most `b` up to any time forces it to be at most `a` at that time, then it stays at
most `a`. -/
theorem bootstrap_le {e : ℝ → ℝ} {τ₁ a b : ℝ} (hab : a < b)
    (he : ContinuousOn e (Icc 0 τ₁)) (h0 : e 0 ≤ a)
    (hstep : ∀ s ∈ Icc (0 : ℝ) τ₁, (∀ τ ∈ Icc 0 s, e τ ≤ b) → e s ≤ a) :
    ∀ s ∈ Icc (0 : ℝ) τ₁, e s ≤ a := by
  have hlt : ∀ s ∈ Icc (0 : ℝ) τ₁, e s < b := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₀, ht₀, hbt₀⟩ := hcon
    let U : Set ℝ := {t ∈ Icc (0 : ℝ) τ₁ | b ≤ e t}
    have hU : IsClosed U := he.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hne : U.Nonempty := ⟨t₀, ht₀, hbt₀⟩
    have hbdd : BddBelow U := ⟨0, fun t ht ↦ ht.1.1⟩
    have htsU : sInf U ∈ U := hU.csInf_mem hne hbdd
    have hbelow : ∀ t ∈ Ico (0 : ℝ) (sInf U), e t < b := by
      intro t ht
      by_contra hge
      push Not at hge
      have htU : t ∈ U := ⟨⟨ht.1, ht.2.le.trans htsU.1.2⟩, hge⟩
      exact absurd (csInf_le hbdd htU) (not_le.mpr ht.2)
    have hts_le : ∀ τ ∈ Icc (0 : ℝ) (sInf U), e τ ≤ b := by
      intro τ hτ
      rcases hτ.2.lt_or_eq with h | h
      · exact (hbelow τ ⟨hτ.1, h⟩).le
      · rcases htsU.1.1.eq_or_lt with h0' | hpos
        · rw [h, ← h0']
          linarith
        · have hcl : sInf U ∈ closure (Ico (0 : ℝ) (sInf U)) := by
            rw [closure_Ico hpos.ne]
            exact ⟨hpos.le, le_rfl⟩
          have hcw : ContinuousWithinAt e (Ico (0 : ℝ) (sInf U)) (sInf U) :=
            (he (sInf U) htsU.1).mono fun t ht ↦ ⟨ht.1, ht.2.le.trans htsU.1.2⟩
          rw [h]
          exact ContinuousWithinAt.closure_le hcl hcw continuousWithinAt_const
            fun t ht ↦ (hbelow t ht).le
    have := hstep (sInf U) htsU.1 hts_le
    linarith [htsU.2]
  intro s hs
  exact hstep s hs fun τ hτ ↦ (hlt τ ⟨hτ.1, hτ.2.trans hs.2⟩).le

section Step

variable {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ}

/-- **The integrated cubic inequality.** While the order-one energy stays at most `K`,
the order-one energy balance holds with the rate `ν (2π)² X + C K³ S`, where `X`
bounds every integrated truncated dissipation. -/
theorem integrated_cubic_step_one (hnu : 0 < nu) (c : SolutionOn nu u₀ T)
    {S : ℝ} (hS : 0 < S) (hST : S < T) {B K X : ℝ}
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 3 F (c.coefficients τ) ≤ B)
    (hK : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ K)
    (hX : ∀ G, ∫ τ in (0 : ℝ)..S, velocityDissipation 1 G (c.coefficients τ) ≤ X)
    (F : Finset Wavevector) :
    velocityEnergy 1 F (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 *
        (∫ τ in (0 : ℝ)..S, velocityDissipation 1 F (c.coefficients τ)) ≤
      velocityEnergy 1 F (c.coefficients 0) +
        (nu * (2 * Real.pi) ^ 2 * X + cubicConst nu * K ^ 3 * S) := by
  have hν : 0 < nu * (2 * Real.pi) ^ 2 := by positivity
  have hC := (cubicConst_pos hnu).le
  refine integrated_step_of_rate' 1 3 (by norm_num) c hS hST hB hK F fun N ↦ ?_
  let Dc : ℝ → ℝ := fun τ ↦
    velocityDissipation 1 (carrier F (wavevectorBox N)) (c.coefficients τ)
  have hDc_cont : Continuous Dc := continuous_velocityDissipation_along 1 _ c.continuous
  have hpt : ∀ τ ∈ Icc (0 : ℝ) S,
      truncConvectionRate 1 F (wavevectorBox N) (c.coefficients τ) ≤
        nu * (2 * Real.pi) ^ 2 * Dc τ + cubicConst nu * K ^ 3 := by
    intro τ hτ
    have h := truncConvectionRate_le_agmon F (wavevectorBox N) (c.coefficients τ) (c.zero τ) hν
    have hE := hK τ hτ (carrier F (wavevectorBox N))
    have hE0 : 0 ≤ velocityEnergy 1 (carrier F (wavevectorBox N)) (c.coefficients τ) :=
      orderEnergy_nonneg 1 _ _
    have hcube : velocityEnergy 1 (carrier F (wavevectorBox N)) (c.coefficients τ) ^ 3 ≤ K ^ 3 :=
      pow_le_pow_left₀ hE0 hE 3
    have hconst : agmonRateConst ^ 4 / (8 * (nu * (2 * Real.pi) ^ 2) ^ 3) = cubicConst nu := rfl
    rw [hconst] at h
    have := mul_le_mul_of_nonneg_left hcube hC
    change _ ≤ nu * (2 * Real.pi) ^ 2 *
      velocityDissipation 1 (carrier F (wavevectorBox N)) (c.coefficients τ) + _
    linarith
  have hint1 : IntervalIntegrable (fun τ ↦ nu * (2 * Real.pi) ^ 2 * Dc τ) volume 0 S :=
    (continuous_const.mul hDc_cont).intervalIntegrable 0 S
  have hint2 : IntervalIntegrable (fun _ : ℝ ↦ cubicConst nu * K ^ 3) volume 0 S :=
    continuous_const.intervalIntegrable 0 S
  calc ∫ τ in (0 : ℝ)..S, truncConvectionRate 1 F (wavevectorBox N) (c.coefficients τ)
      ≤ ∫ τ in (0 : ℝ)..S, (nu * (2 * Real.pi) ^ 2 * Dc τ + cubicConst nu * K ^ 3) :=
        intervalIntegral.integral_mono_on hS.le
          ((continuous_truncConvectionRate 1 F _ c.continuous).intervalIntegrable 0 S)
          (hint1.add hint2) hpt
    _ = nu * (2 * Real.pi) ^ 2 * (∫ τ in (0 : ℝ)..S, Dc τ) + cubicConst nu * K ^ 3 * S := by
        rw [intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        ring
    _ ≤ nu * (2 * Real.pi) ^ 2 * X + cubicConst nu * K ^ 3 * S := by
        have := hX (carrier F (wavevectorBox N))
        have hmono := mul_le_mul_of_nonneg_left this hν.le
        linarith

/-- **The cubic step.** While the order-one energy stays at most `K` on `[0, S]`, it is
at most `2 (E₀ + C K³ S)` at `S`. -/
theorem velocityEnergy_le_of_cubic (hnu : 0 < nu) (c : SolutionOn nu u₀ T)
    {S : ℝ} (hS : 0 < S) (hST : S < T) {B K X₀ E₀ : ℝ}
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 3 F (c.coefficients τ) ≤ B)
    (hK : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ K)
    (hX₀ : ∀ G, ∫ τ in (0 : ℝ)..S, velocityDissipation 1 G (c.coefficients τ) ≤ X₀)
    (hE₀ : ∀ F, velocityEnergy 1 F u₀ ≤ E₀) (F : Finset Wavevector) :
    velocityEnergy 1 F (c.coefficients S) ≤ 2 * (E₀ + cubicConst nu * K ^ 3 * S) := by
  let I : Finset Wavevector → ℝ := fun G ↦
    ∫ τ in (0 : ℝ)..S, velocityDissipation 1 G (c.coefficients τ)
  have hbdd : BddAbove (Set.range I) := ⟨X₀, by rintro _ ⟨G, rfl⟩; exact hX₀ G⟩
  obtain ⟨X, hXdef⟩ : ∃ X, X = sSup (Set.range I) := ⟨_, rfl⟩
  have hIX : ∀ G, I G ≤ X := fun G ↦ hXdef ▸ le_csSup hbdd ⟨G, rfl⟩
  have hI0 : ∀ G, 0 ≤ I G := fun G ↦
    intervalIntegral.integral_nonneg hS.le fun τ _ ↦ orderDissipation_nonneg 1 G _
  have hstep := fun G ↦ integrated_cubic_step_one hnu c hS hST hB hK hIX G
  have hinit : ∀ G, velocityEnergy 1 G (c.coefficients 0) ≤ E₀ := fun G ↦ by
    rw [c.initial]
    exact hE₀ G
  have hpos : 0 < 2 * nu * (2 * Real.pi) ^ 2 := by positivity
  have hν : 0 < nu * (2 * Real.pi) ^ 2 := by positivity
  have hXle : X ≤ (E₀ + (nu * (2 * Real.pi) ^ 2 * X + cubicConst nu * K ^ 3 * S)) /
      (2 * nu * (2 * Real.pi) ^ 2) := by
    rw [hXdef]
    refine csSup_le (Set.range_nonempty I) ?_
    rintro _ ⟨G, rfl⟩
    rw [le_div_iff₀ hpos, ← hXdef]
    have h := hstep G
    have hE := orderEnergy_nonneg 1 G (amplitude (c.coefficients S))
    change velocityEnergy 1 G (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 * I G ≤ _ at h
    change 0 ≤ velocityEnergy 1 G (c.coefficients S) at hE
    nlinarith [hinit G]
  rw [le_div_iff₀ hpos] at hXle
  have hXE : nu * (2 * Real.pi) ^ 2 * X ≤ E₀ + cubicConst nu * K ^ 3 * S := by nlinarith
  have h := hstep F
  have hD := hI0 F
  change velocityEnergy 1 F (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 * I F ≤ _ at h
  have hDpos : 0 ≤ 2 * nu * (2 * Real.pi) ^ 2 * I F := mul_nonneg hpos.le hD
  linarith [hinit F]

end Step

section Lifespan

variable {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ}

/-- **The order-one lifespan bound.** For data with order-one energy at most
`E₀ > 0`, every tame solution of order three keeps its order-one energy at most
`3 E₀` up to every time `S` with `128 C E₀² S ≤ 1`. -/
theorem velocityEnergy_le_three_of_lifespan (hnu : 0 < nu) (c : TameSolutionOn nu 3 u₀ T)
    {E₀ S : ℝ} (hE₀ : 0 < E₀) (hdata : ∀ F, velocityEnergy 1 F u₀ ≤ E₀)
    (hS : 128 * cubicConst nu * E₀ ^ 2 * S ≤ 1) :
    ∀ τ ∈ Ico (0 : ℝ) T, τ ≤ S → ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ 3 * E₀ := by
  intro τ₁ hτ₁ hτ₁S
  have hτS' : τ₁ < (τ₁ + T) / 2 := by linarith [hτ₁.2]
  have hS'T : (τ₁ + T) / 2 < T := by linarith [hτ₁.2]
  have hec := continuousOn_fullEnergy (m := 1) c hS'T
  have hC := (cubicConst_pos hnu).le
  let e : ℝ → ℝ := fun t ↦ fullEnergy 1 (c.coefficients t)
  have hstep : ∀ s ∈ Icc (0 : ℝ) τ₁, (∀ τ ∈ Icc 0 s, e τ ≤ 4 * E₀) → e s ≤ 3 * E₀ := by
    intro s hs hsmall
    apply fullEnergy_le_of_forall
    intro F
    rcases hs.1.eq_or_lt with h0 | hpos
    · rw [← h0, c.initial]
      linarith [hdata F]
    · have hsT : s < T := lt_of_le_of_lt hs.2 hτ₁.2
      obtain ⟨B, hB⟩ := c.order_local s hsT
      obtain ⟨X, hX⟩ := c.dissipation_local s hsT
      have hsm : ∀ τ ∈ Icc (0 : ℝ) s, ∀ G, velocityEnergy 1 G (c.coefficients τ) ≤ 4 * E₀ :=
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
      have h := velocityEnergy_le_of_cubic hnu c.toSolutionOn hpos hsT hB hsm hXm hdata F
      have hsS : s ≤ S := hs.2.trans hτ₁S
      have h1 : 128 * cubicConst nu * E₀ ^ 2 * s ≤ 1 :=
        le_trans (mul_le_mul_of_nonneg_left hsS (by positivity)) hS
      have h2 : cubicConst nu * (4 * E₀) ^ 3 * s ≤ E₀ / 2 := by
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ E₀ / 2)
        nlinarith
      linarith
  have hsub : Icc (0 : ℝ) τ₁ ⊆ Icc 0 ((τ₁ + T) / 2) := Icc_subset_Icc le_rfl hτS'.le
  have he0 : e 0 ≤ 3 * E₀ := by
    apply fullEnergy_le_of_forall
    intro F
    rw [c.initial]
    linarith [hdata F]
  have hall := bootstrap_le (by linarith : 3 * E₀ < 4 * E₀) (hec.mono hsub) he0 hstep
  intro F
  obtain ⟨B', hB'⟩ := c.order_local ((τ₁ + T) / 2) hS'T
  exact (velocityEnergy_le_fullEnergy 1 _ (hB' τ₁ ⟨hτ₁.1, hτS'.le⟩) F).trans
    (hall τ₁ ⟨hτ₁.1, le_rfl⟩)

/-- **The order-one lifespan.** Admissible data of finite order-`m` energy (`m ≥ 3`)
whose order-one energy is at most `E₀ > 0` have a tame solution on `[0, S)` for every
`S` with `128 C E₀² S ≤ 1`: the lifespan is at least of order `ν³ / E₀²`. -/
theorem nonempty_tameSolutionOn_of_lifespan (m : ℕ) (hm : 3 ≤ m) (hnu : 0 < nu)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q)) (hd : ∀ q, modeDot q (u₀ q) = 0)
    (hz : u₀ 0 = 0) {Em : ℝ} (hEm0 : 0 ≤ Em) (hEm : ∀ F, velocityEnergy m F u₀ ≤ Em)
    {E₀ : ℝ} (hE₀ : 0 < E₀) (hdata : ∀ F, velocityEnergy 1 F u₀ ≤ E₀) {S : ℝ} (hS0 : 0 < S)
    (hS : 128 * cubicConst nu * E₀ ^ 2 * S ≤ 1) :
    Nonempty (TameSolutionOn nu m u₀ S) :=
  exists_tameSolutionOn_of_orderOne_at m (by omega) hnu u₀ hr hd hz hEm0 hEm hS0 (K := 3 * E₀)
    fun _ hT c τ hτ F ↦ velocityEnergy_le_three_of_lifespan hnu (c.ofLe (by omega)) hE₀ hdata hS
      τ hτ (hτ.2.le.trans hT) F

end Lifespan

section Rate

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity}

theorem exists_pos_ge_of_mul_sq_lt {A E : ℝ} (hA : 0 < A) (h : A * max E 0 ^ 2 < 1) :
    ∃ E', 0 < E' ∧ E ≤ E' ∧ A * E' ^ 2 < 1 := by
  set Ep := max E 0 with hEp
  have hEp0 : 0 ≤ Ep := le_max_right _ _
  set r := 1 / Real.sqrt A with hr
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hr0 : 0 < r := by positivity
  have hr2 : A * r ^ 2 = 1 := by
    rw [hr, div_pow, one_pow, Real.sq_sqrt hA.le]
    field_simp
  have hlt : Ep < r := by
    have h2 : Ep ^ 2 < r ^ 2 := by
      have := mul_lt_mul_of_pos_left (show Ep ^ 2 < r ^ 2 from by nlinarith) hA
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hr0.le h2
  refine ⟨(Ep + r) / 2, by positivity, (le_max_left E 0).trans (by linarith), ?_⟩
  have hm : (Ep + r) / 2 < r := by linarith
  have hm0 : 0 ≤ (Ep + r) / 2 := by positivity
  have hsq : ((Ep + r) / 2) ^ 2 < r ^ 2 := pow_lt_pow_left₀ hm hm0 (by norm_num)
  nlinarith

/-- **Leray's lower bound on the blowup rate.** For order `m ≥ 7`, if a tame solution
on `[0, T)` admits no tame solution on any longer interval, then at every earlier
time `t₀`, every bound `E` on its order-one energy obeys `128 C E² (T - t₀) ≥ 1`,
with `C = cubicConst ν` of order `ν⁻³`. -/
theorem one_le_lerayRate (hm : 7 ≤ m) (hnu : 0 < nu)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q)) (hd : ∀ q, modeDot q (u₀ q) = 0)
    (hz : u₀ 0 = 0) {Em : ℝ} (hEm0 : 0 ≤ Em) (hEm : ∀ F, velocityEnergy m F u₀ ≤ Em)
    {T : ℝ} (c : TameSolutionOn nu m u₀ T)
    (hmax : ∀ T', T < T' → IsEmpty (TameSolutionOn nu m u₀ T'))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) T) {E : ℝ}
    (hE : ∀ F, velocityEnergy 1 F (c.coefficients t₀) ≤ E) :
    1 ≤ 128 * cubicConst nu * E ^ 2 * (T - t₀) := by
  by_contra hlt
  push Not at hlt
  have hC := cubicConst_pos hnu
  have hTt : 0 < T - t₀ := by linarith [ht₀.2]
  have hA : 0 < 128 * cubicConst nu * (T - t₀) := by positivity
  have hmaxlt : 128 * cubicConst nu * (T - t₀) * max E 0 ^ 2 < 1 := by
    rcases le_total 0 E with h | h
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right h]
      simp
  obtain ⟨E', hE'0, hEE', hE'lt⟩ := exists_pos_ge_of_mul_sq_lt hA hmaxlt
  -- the lifespan from `t₀` exceeds the remaining time
  set S' := 1 / (128 * cubicConst nu * E' ^ 2) with hS'def
  have hq : 0 < 128 * cubicConst nu * E' ^ 2 := by positivity
  have hS'0 : 0 < S' := by positivity
  have hS'eq : 128 * cubicConst nu * E' ^ 2 * S' = 1 := by
    rw [hS'def]
    field_simp
  have hS'gt : T - t₀ < S' := by
    rw [hS'def, lt_div_iff₀ hq]
    nlinarith
  have hH : 0 < t₀ + S' := by linarith [ht₀.1]
  -- a bound before `t₀`, by compactness
  have hec := continuousOn_fullEnergy (m := 1) (c.ofLe (by omega : 1 + 2 ≤ m)) (S := t₀) ht₀.2
  obtain ⟨M, -, hM⟩ := exists_bound_on _ hec
  -- every tame solution up to `t₀ + S'` keeps a bounded order-one energy
  have hK : ∀ T', T' ≤ t₀ + S' → ∀ d : TameSolutionOn nu m u₀ T',
      ∀ τ ∈ Ico (0 : ℝ) T', ∀ F, velocityEnergy 1 F (d.coefficients τ) ≤ max M (3 * E') := by
    intro T' hT' d τ hτ F
    rcases le_or_gt τ t₀ with hτt | hτt
    · have hτT : τ < T := lt_of_le_of_lt hτt ht₀.2
      have he : d.coefficients τ = c.coefficients τ :=
        coefficients_eq_of_lt hm hnu d c hτ.1 hτ.2 hτT
      rw [he]
      obtain ⟨B, hB⟩ := (c.ofLe (by omega : 1 + 2 ≤ m)).order_local τ hτT
      have h := velocityEnergy_le_fullEnergy 1 _ (hB τ ⟨hτ.1, le_rfl⟩) F
      exact (h.trans (hM τ ⟨hτ.1, hτt⟩)).trans (le_max_left _ _)
    · have ht₀T' : t₀ < T' := hτt.trans hτ.2
      have hd0 : d.coefficients t₀ = c.coefficients t₀ :=
        coefficients_eq_of_lt hm hnu d c ht₀.1 ht₀T' ht₀.2
      let d' := (d.shift ht₀.1).ofLe (by omega : 3 ≤ m)
      have hdata : ∀ F, velocityEnergy 1 F (d.coefficients t₀) ≤ E' := by
        intro F
        rw [hd0]
        exact (hE F).trans hEE'
      have hb := velocityEnergy_le_three_of_lifespan hnu d' hE'0 hdata hS'eq.le (τ - t₀)
        ⟨by linarith, by linarith [hτ.2]⟩ (by linarith [hτ.2]) F
      have e : d'.coefficients (τ - t₀) = d.coefficients τ := by
        show d.coefficients (τ - t₀ + t₀) = d.coefficients τ
        rw [sub_add_cancel]
      rw [e] at hb
      exact hb.trans (le_max_right _ _)
  obtain ⟨c'⟩ := exists_tameSolutionOn_of_orderOne_at m (by omega) hnu u₀ hr hd hz hEm0 hEm hH hK
  exact (hmax (t₀ + S') (by linarith)).false c'

end Rate

/-! ## Scale-invariant small data -/

section SmallProduct

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity}

/-- **Interpolation.** On nonzero modes `E₁² ≤ 4 K D₁`, with `K` the kinetic energy. -/
theorem orderEnergy_one_sq_le (M : Finset Wavevector) (hM : ∀ k ∈ M, k ≠ 0)
    (a : Wavevector → ℝ) :
    orderEnergy 1 M a ^ 2 ≤ 4 * orderEnergy 0 M a * orderDissipation 1 M a := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq M a (fun k ↦ (1 + ‖frequencyVec k‖) ^ 2 * a k)
  have e1 : ∑ k ∈ M, a k * ((1 + ‖frequencyVec k‖) ^ 2 * a k) = orderEnergy 1 M a := by
    unfold orderEnergy orderWeight
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have e2 : ∑ k ∈ M, a k ^ 2 = orderEnergy 0 M a := by
    unfold orderEnergy orderWeight
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have h3 : ∑ k ∈ M, ((1 + ‖frequencyVec k‖) ^ 2 * a k) ^ 2 ≤ 4 * orderDissipation 1 M a := by
    unfold orderDissipation orderEnergy orderWeight
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have h1 := PancakeInfinitePressureCoefficients.one_le_norm_frequencyVec (hM k hk)
    have hw : (1 + ‖frequencyVec k‖) ^ 2 ≤ 4 * ‖frequencyVec k‖ ^ 2 := by nlinarith
    have ha : 0 ≤ (1 + ‖frequencyVec k‖) ^ 2 * a k ^ 2 := by positivity
    calc ((1 + ‖frequencyVec k‖) ^ 2 * a k) ^ 2 =
          (1 + ‖frequencyVec k‖) ^ 2 * ((1 + ‖frequencyVec k‖) ^ 2 * a k ^ 2) := by ring
      _ ≤ (4 * ‖frequencyVec k‖ ^ 2) * ((1 + ‖frequencyVec k‖) ^ 2 * a k ^ 2) :=
          mul_le_mul_of_nonneg_right hw ha
      _ = 4 * ((1 + ‖frequencyVec k‖) ^ 1 * (‖frequencyVec k‖ * a k)) ^ 2 := by ring
  rw [e1, e2] at hcs
  have hE0 : 0 ≤ orderEnergy 0 M a := orderEnergy_nonneg 0 M a
  calc orderEnergy 1 M a ^ 2 ≤ orderEnergy 0 M a *
        ∑ k ∈ M, ((1 + ‖frequencyVec k‖) ^ 2 * a k) ^ 2 := hcs
    _ ≤ orderEnergy 0 M a * (4 * orderDissipation 1 M a) := mul_le_mul_of_nonneg_left h3 hE0
    _ = 4 * orderEnergy 0 M a * orderDissipation 1 M a := by ring

/-- The kinetic energy of every tame solution stays below every bound for the data. -/
theorem velocityEnergy_zero_le_of_tame (hm : 7 ≤ m) (hnu : 0 < nu) {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) {K₀ : ℝ} (hK₀ : ∀ F, velocityEnergy 0 F u₀ ≤ K₀) :
    ∀ τ ∈ Ico (0 : ℝ) T, ∀ F, velocityEnergy 0 F (c.coefficients τ) ≤ K₀ := by
  intro τ hτ F
  obtain ⟨B, s, hs, g, hg, hSum, hu3⟩ := FourierUniqueness.local_envelope_at hm c hτ.2
  have hu2 : ∀ t ∈ Icc (0 : ℝ) τ, ∀ k, fourierMoment 2 (s.coefficients t) k ≤ g k :=
    fun t ht k ↦ (PancakeHigherDerivativeMoments.fourierMoment_mono _ (by omega : 2 ≤ 3) k).trans
      (hu3 t ht k)
  have hkin := LocalKineticEnergy.energy_le_initial s hnu.le g hg hSum hu2 τ ⟨hτ.1, le_rfl⟩
  have hveq : ∀ (v : FourierVelocity) (G : Finset Wavevector),
      velocityEnergy 0 G v = ∑ k ∈ G, ‖coefficientVec (v k)‖ ^ 2 := by
    intro v G
    simp [velocityEnergy, orderEnergy, orderWeight, amplitude]
  have hsum : Summable (fun k ↦ ‖coefficientVec (s.coefficients τ k)‖ ^ 2) := by
    refine (hSum.mul_left (∑' k, g k)).of_nonneg_of_le (fun k ↦ sq_nonneg _) fun k ↦ ?_
    have h1 := LocalKineticEnergy.amplitude_le_envelope _ g (hu2 τ ⟨hτ.1, le_rfl⟩) k
    have h2 : g k ≤ ∑' k, g k := hSum.le_tsum k fun j _ ↦ hg j
    rw [pow_two]
    exact mul_le_mul (h1.trans h2) h1 (norm_nonneg _) (tsum_nonneg hg)
  have hdata : InfiniteConvectionEnergy.kineticEnergy u₀ ≤ K₀ := by
    refine Real.tsum_le_of_sum_le (fun k ↦ sq_nonneg _) fun G ↦ ?_
    rw [← hveq]
    exact hK₀ G
  rw [hveq, ← hs]
  exact (hsum.sum_le_tsum F fun k _ ↦ sq_nonneg _).trans (hkin.trans hdata)

theorem integrated_product_step_one (hnu : 0 < nu) {T : ℝ} (c : SolutionOn nu u₀ T)
    {S : ℝ} (hS : 0 < S) (hST : S < T) {B K₀ E X : ℝ} (hK₀ : 0 ≤ K₀) (hE : 0 ≤ E)
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 3 F (c.coefficients τ) ≤ B)
    (hK : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ E)
    (hKin : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 0 F (c.coefficients τ) ≤ K₀)
    (hX : ∀ G, ∫ τ in (0 : ℝ)..S, velocityDissipation 1 G (c.coefficients τ) ≤ X)
    (F : Finset Wavevector) :
    velocityEnergy 1 F (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 *
        (∫ τ in (0 : ℝ)..S, velocityDissipation 1 F (c.coefficients τ)) ≤
      velocityEnergy 1 F (c.coefficients 0) +
        (nu * (2 * Real.pi) ^ 2 + 4 * cubicConst nu * K₀ * E) * X := by
  have hν : 0 < nu * (2 * Real.pi) ^ 2 := by positivity
  have hC := (cubicConst_pos hnu).le
  have hβ : 0 ≤ nu * (2 * Real.pi) ^ 2 + 4 * cubicConst nu * K₀ * E := by positivity
  refine integrated_step_of_rate' 1 3 (by norm_num) c hS hST hB hK F fun N ↦ ?_
  let Dc : ℝ → ℝ := fun τ ↦
    velocityDissipation 1 (carrier F (wavevectorBox N)) (c.coefficients τ)
  have hDc_cont : Continuous Dc := continuous_velocityDissipation_along 1 _ c.continuous
  have hpt : ∀ τ ∈ Icc (0 : ℝ) S,
      truncConvectionRate 1 F (wavevectorBox N) (c.coefficients τ) ≤
        (nu * (2 * Real.pi) ^ 2 + 4 * cubicConst nu * K₀ * E) * Dc τ := by
    intro τ hτ
    have h := truncConvectionRate_le_agmon F (wavevectorBox N) (c.coefficients τ) (c.zero τ) hν
    have hconst : agmonRateConst ^ 4 / (8 * (nu * (2 * Real.pi) ^ 2) ^ 3) = cubicConst nu := rfl
    rw [hconst] at h
    set G := carrier F (wavevectorBox N)
    have hEc := hK τ hτ G
    have hKc := hKin τ hτ G
    have hEc0 : 0 ≤ velocityEnergy 1 G (c.coefficients τ) := orderEnergy_nonneg 1 _ _
    have hKc0 : 0 ≤ velocityEnergy 0 G (c.coefficients τ) := orderEnergy_nonneg 0 _ _
    have hDc0 : 0 ≤ Dc τ := orderDissipation_nonneg 1 _ _
    have hint := orderEnergy_one_sq_le G (fun k hk ↦ mem_carrier_ne_zero hk)
      (amplitude (c.coefficients τ))
    change velocityEnergy 1 G (c.coefficients τ) ^ 2 ≤
      4 * velocityEnergy 0 G (c.coefficients τ) * Dc τ at hint
    have hcube : velocityEnergy 1 G (c.coefficients τ) ^ 3 ≤ 4 * K₀ * E * Dc τ := by
      calc velocityEnergy 1 G (c.coefficients τ) ^ 3 =
            velocityEnergy 1 G (c.coefficients τ) * velocityEnergy 1 G (c.coefficients τ) ^ 2 := by
            ring
        _ ≤ E * (4 * velocityEnergy 0 G (c.coefficients τ) * Dc τ) :=
            mul_le_mul hEc hint (by positivity) hE
        _ ≤ E * (4 * K₀ * Dc τ) := by gcongr
        _ = 4 * K₀ * E * Dc τ := by ring
    have := mul_le_mul_of_nonneg_left hcube hC
    change _ ≤ nu * (2 * Real.pi) ^ 2 * Dc τ + _ at h
    nlinarith
  calc ∫ τ in (0 : ℝ)..S, truncConvectionRate 1 F (wavevectorBox N) (c.coefficients τ)
      ≤ ∫ τ in (0 : ℝ)..S, (nu * (2 * Real.pi) ^ 2 + 4 * cubicConst nu * K₀ * E) * Dc τ :=
        intervalIntegral.integral_mono_on hS.le
          ((continuous_truncConvectionRate 1 F _ c.continuous).intervalIntegrable 0 S)
          ((continuous_const.mul hDc_cont).intervalIntegrable 0 S) hpt
    _ = (nu * (2 * Real.pi) ^ 2 + 4 * cubicConst nu * K₀ * E) * ∫ τ in (0 : ℝ)..S, Dc τ :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (nu * (2 * Real.pi) ^ 2 + 4 * cubicConst nu * K₀ * E) * X :=
        mul_le_mul_of_nonneg_left (hX _) hβ

/-- **The product step.** While `E₁ ≤ E` and the kinetic energy stays at most `K₀`,
with `16 C K₀ E ≤ ν (2π)²`, the order-one energy is at most `8/3` times its initial
bound. -/
theorem velocityEnergy_le_of_product (hnu : 0 < nu) {T : ℝ} (c : SolutionOn nu u₀ T)
    {S : ℝ} (hS : 0 < S) (hST : S < T) {B K₀ E X₀ E₀ : ℝ} (hK₀ : 0 ≤ K₀) (hE : 0 ≤ E)
    (hsmall : 16 * cubicConst nu * K₀ * E ≤ nu * (2 * Real.pi) ^ 2)
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 3 F (c.coefficients τ) ≤ B)
    (hK : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ E)
    (hKin : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 0 F (c.coefficients τ) ≤ K₀)
    (hX₀ : ∀ G, ∫ τ in (0 : ℝ)..S, velocityDissipation 1 G (c.coefficients τ) ≤ X₀)
    (hE₀ : ∀ F, velocityEnergy 1 F u₀ ≤ E₀) (F : Finset Wavevector) :
    velocityEnergy 1 F (c.coefficients S) ≤ 8 / 3 * E₀ := by
  let I : Finset Wavevector → ℝ := fun G ↦
    ∫ τ in (0 : ℝ)..S, velocityDissipation 1 G (c.coefficients τ)
  have hbdd : BddAbove (Set.range I) := ⟨X₀, by rintro _ ⟨G, rfl⟩; exact hX₀ G⟩
  obtain ⟨X, hXdef⟩ : ∃ X, X = sSup (Set.range I) := ⟨_, rfl⟩
  have hIX : ∀ G, I G ≤ X := fun G ↦ hXdef ▸ le_csSup hbdd ⟨G, rfl⟩
  have hI0 : ∀ G, 0 ≤ I G := fun G ↦
    intervalIntegral.integral_nonneg hS.le fun τ _ ↦ orderDissipation_nonneg 1 G _
  have hX0 : 0 ≤ X := (hI0 ∅).trans (hIX ∅)
  have hstep := fun G ↦ integrated_product_step_one hnu c hS hST hK₀ hE hB hK hKin hIX G
  have hinit : ∀ G, velocityEnergy 1 G (c.coefficients 0) ≤ E₀ := fun G ↦ by
    rw [c.initial]
    exact hE₀ G
  set ν' := nu * (2 * Real.pi) ^ 2 with hν'
  have hν : 0 < ν' := by positivity
  set β := 4 * cubicConst nu * K₀ * E with hβdef
  have hβ0 : 0 ≤ β := by have := (cubicConst_pos hnu).le; positivity
  have hβ : 4 * β ≤ ν' := by rw [hβdef]; linarith
  have hXle : 2 * ν' * X ≤ E₀ + (ν' + β) * X := by
    have hpos : 0 < 2 * ν' := by positivity
    have hle : X ≤ (E₀ + (ν' + β) * X) / (2 * ν') := by
      rw [hXdef]
      refine csSup_le (Set.range_nonempty I) ?_
      rintro _ ⟨G, rfl⟩
      rw [le_div_iff₀ hpos, ← hXdef]
      have h := hstep G
      have hE' := orderEnergy_nonneg 1 G (amplitude (c.coefficients S))
      change velocityEnergy 1 G (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 * I G ≤ _ at h
      change 0 ≤ velocityEnergy 1 G (c.coefficients S) at hE'
      have h2 : 2 * nu * (2 * Real.pi) ^ 2 * I G = I G * (2 * ν') := by rw [hν']; ring
      linarith [hinit G]
    rw [le_div_iff₀ hpos] at hle
    linarith
  have hXE : 3 * ν' * X ≤ 4 * E₀ := by nlinarith
  have h := hstep F
  have hD := hI0 F
  change velocityEnergy 1 F (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 * I F ≤ _ at h
  have hDpos : 0 ≤ 2 * nu * (2 * Real.pi) ^ 2 * I F := by positivity
  have hmain : (ν' + β) * X ≤ 5 / 3 * E₀ := by nlinarith
  linarith [hinit F]

/-- **The small-product bootstrap.** For order `m ≥ 7`, data with kinetic energy at most
`K₀` and order-one energy at most `E₀ > 0`, with `64 C K₀ E₀ ≤ ν (2π)²`, keep
`E₁ ≤ 3 E₀` along every tame solution, for all time. -/
theorem velocityEnergy_le_three_of_small_product (hm : 7 ≤ m) (hnu : 0 < nu) {T : ℝ}
    (c : TameSolutionOn nu m u₀ T) {K₀ E₀ : ℝ} (hK₀ : ∀ F, velocityEnergy 0 F u₀ ≤ K₀)
    (hE₀ : 0 < E₀) (hdata : ∀ F, velocityEnergy 1 F u₀ ≤ E₀)
    (hsmall : 64 * cubicConst nu * K₀ * E₀ ≤ nu * (2 * Real.pi) ^ 2) :
    ∀ τ ∈ Ico (0 : ℝ) T, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ 3 * E₀ := by
  have hK₀0 : 0 ≤ K₀ := (orderEnergy_nonneg 0 ∅ _).trans (hK₀ ∅)
  have hkin := velocityEnergy_zero_le_of_tame hm hnu c hK₀
  let c3 := c.ofLe (by omega : 3 ≤ m)
  intro τ₁ hτ₁
  have hτS' : τ₁ < (τ₁ + T) / 2 := by linarith [hτ₁.2]
  have hS'T : (τ₁ + T) / 2 < T := by linarith [hτ₁.2]
  have hec := continuousOn_fullEnergy (m := 1) c3 hS'T
  let e : ℝ → ℝ := fun t ↦ fullEnergy 1 (c.coefficients t)
  have hstep : ∀ s ∈ Icc (0 : ℝ) τ₁, (∀ τ ∈ Icc 0 s, e τ ≤ 4 * E₀) → e s ≤ 3 * E₀ := by
    intro s hs hsmall'
    apply fullEnergy_le_of_forall
    intro F
    rcases hs.1.eq_or_lt with h0 | hpos
    · rw [← h0, c.initial]
      linarith [hdata F]
    · have hsT : s < T := lt_of_le_of_lt hs.2 hτ₁.2
      obtain ⟨B, hB⟩ := c3.order_local s hsT
      obtain ⟨X, hX⟩ := c3.dissipation_local s hsT
      have hsm : ∀ τ ∈ Icc (0 : ℝ) s, ∀ G, velocityEnergy 1 G (c.coefficients τ) ≤ 4 * E₀ :=
        fun τ hτ G ↦ (velocityEnergy_le_fullEnergy 1 _ (hB τ hτ) G).trans (hsmall' τ hτ)
      have hXm : ∀ G, ∫ τ in (0 : ℝ)..s, velocityDissipation 1 G (c.coefficients τ) ≤ X := by
        intro G
        refine le_trans (intervalIntegral.integral_mono_on hpos.le ?_ ?_ fun τ _ ↦ ?_) (hX G)
        · exact (continuous_velocityDissipation_along 1 G c.continuous).intervalIntegrable 0 s
        · exact (continuous_velocityDissipation_along 3 G c3.continuous).intervalIntegrable 0 s
        · unfold velocityDissipation orderDissipation orderEnergy
          refine Finset.sum_le_sum fun k _ ↦ ?_
          have hw : orderWeight 1 k ≤ orderWeight 3 k :=
            pow_le_pow_right₀ (by linarith [norm_nonneg (frequencyVec k)]) (by omega)
          have h0 : 0 ≤ orderWeight 1 k := by unfold orderWeight; positivity
          have ha : 0 ≤ ‖frequencyVec k‖ * amplitude (c.coefficients τ) k := by
            unfold amplitude; positivity
          exact pow_le_pow_left₀ (mul_nonneg h0 ha) (mul_le_mul_of_nonneg_right hw ha) 2
      have hkin' : ∀ τ ∈ Icc (0 : ℝ) s, ∀ G, velocityEnergy 0 G (c.coefficients τ) ≤ K₀ :=
        fun τ hτ G ↦ hkin τ ⟨hτ.1, lt_of_le_of_lt hτ.2 hsT⟩ G
      have hsm' : 16 * cubicConst nu * K₀ * (4 * E₀) ≤ nu * (2 * Real.pi) ^ 2 := by linarith
      have h : velocityEnergy 1 F (c.coefficients s) ≤ 8 / 3 * E₀ :=
        velocityEnergy_le_of_product hnu c3.toSolutionOn hpos hsT hK₀0 (by positivity)
          hsm' hB hsm hkin' hXm hdata F
      linarith
  have hsub : Icc (0 : ℝ) τ₁ ⊆ Icc 0 ((τ₁ + T) / 2) := Icc_subset_Icc le_rfl hτS'.le
  have he0 : e 0 ≤ 3 * E₀ := by
    apply fullEnergy_le_of_forall
    intro F
    rw [c.initial]
    linarith [hdata F]
  have hall := bootstrap_le (by linarith : 3 * E₀ < 4 * E₀) (hec.mono hsub) he0 hstep
  intro F
  obtain ⟨B', hB'⟩ := c3.order_local ((τ₁ + T) / 2) hS'T
  exact (velocityEnergy_le_fullEnergy 1 _ (hB' τ₁ ⟨hτ₁.1, hτS'.le⟩) F).trans
    (hall τ₁ ⟨hτ₁.1, le_rfl⟩)

/-- **Global regularity for scale-invariant small data.** For order `m ≥ 7`, admissible
data of finite order-`m` energy whose kinetic energy `K₀` and order-one energy `E₀`
satisfy `64 C K₀ E₀ ≤ ν (2π)²` have a unique global solution. Since
`C = cubicConst ν ≍ ν⁻³`, the condition is `K₀ E₀ ≲ ν⁴`, invariant under the
Navier–Stokes scaling. -/
theorem nonempty_globalSolution_of_small_product (hm : 7 ≤ m) (hnu : 0 < nu)
    (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q)) (hd : ∀ q, modeDot q (u₀ q) = 0)
    (hz : u₀ 0 = 0) {Em : ℝ} (hEm0 : 0 ≤ Em) (hEm : ∀ F, velocityEnergy m F u₀ ≤ Em)
    {K₀ E₀ : ℝ} (hK₀ : ∀ F, velocityEnergy 0 F u₀ ≤ K₀) (hE₀ : 0 < E₀)
    (hdata : ∀ F, velocityEnergy 1 F u₀ ≤ E₀)
    (hsmall : 64 * cubicConst nu * K₀ * E₀ ≤ nu * (2 * Real.pi) ^ 2) :
    Nonempty (GlobalSolution nu m u₀) :=
  nonempty_globalSolution hm hnu
    (exists_tameSolutionOn_of_orderOne m (by omega) hnu u₀ hr hd hz hEm0 hEm
      fun _ _ ↦ ⟨3 * E₀, fun _ _ c τ hτ F ↦
        velocityEnergy_le_three_of_small_product hm hnu c hK₀ hE₀ hdata hsmall τ hτ F⟩)

end SmallProduct

end Mettapedia.FluidDynamics.NavierStokes.FourierLerayRate
