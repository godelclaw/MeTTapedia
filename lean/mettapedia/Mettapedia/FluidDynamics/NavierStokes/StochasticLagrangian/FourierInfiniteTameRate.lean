import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierTameTriad
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierContinuation

/-!
# The tame rate along actual infinite Fourier solutions

Truncating the order-`m` energy to a finite output set `F` gives a finite sum
whose derivative along an actual solution involves the full infinite
convolution. For transverse fields that convolution is the sum of the lane's
ordered convection terms, so truncating also the inputs to a finite set `G`
gives a finite sum dominated by the order-`m` triad on a finite set of
nonzero modes. The tame bound therefore applies at every input truncation.
This module proves those finite-level facts; the passage to the limit in the
inputs and in time is separate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierInfiniteTameRate

open scoped BigOperators ComplexConjugate
open Filter Set
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakePeriodicVorticityEquation PancakeFrequencyProjectorCommutator
open PancakeSignedTransportEnergy PancakeGalerkinKineticEnergy PancakeLowPressureBudget
open PancakeFiniteConvolutionL2 PancakeSobolevWeights PancakeIncomingLowSourceEnergy
open PancakeSobolevVelocityRate PancakeHigherSobolevWeights PancakeHigherSobolevVelocityRate
open PancakeCoefficientLimitEquation PancakeSobolevFiberEnvelope
open FourierTameTriad FourierContinuation PancakeArbitraryDataBlocks
open PancakeHigherGalerkinWindow PancakeHigherSobolevWindow

/-! ### The rate identity with the full convolution -/

/-- The convective part of the order-`m` rate with the full convolution. -/
def infiniteConvectionRate (m : ℕ) (F : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ F, orderWeight m q ^ 2 *
    (coefficientHermitian (u q) ((-unitTorusDerivativePhase) • infiniteConvection u q)).re

theorem orderVelocityRate_infiniteRHS (m : ℕ) (F : Finset Wavevector) (u : FourierVelocity)
    (nu : ℝ) (hd : ∀ q, modeDot q (u q) = 0) :
    orderVelocityRate m F u (fun q ↦ infiniteVelocityRHS nu u q) =
      infiniteConvectionRate m F u - 2 * nu * (2 * Real.pi) ^ 2 * velocityDissipation m F u := by
  have he (q : Wavevector) :
      (coefficientHermitian (u q) (infiniteVelocityRHS nu u q)).re =
      (coefficientHermitian (u q) ((-unitTorusDerivativePhase) • infiniteConvection u q)).re -
      nu * (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * coefficientEnergy (u q) := by
    rw [infiniteVelocityRHS, hermitian_add_right, Complex.add_re,
      hermitian_leray_right q (u q) _ (hd q), viscous_energy_pair, ← norm_frequencyVec_sq]
    ring
  rw [orderVelocityRate, infiniteConvectionRate, velocityDissipation_eq]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [he q]
  ring

/-! ### Fibers as ordered convection terms -/

theorem outputFiber_eq_orderedConvection (u : FourierVelocity)
    (hd : ∀ q, modeDot q (u q) = 0) (q k : Wavevector) (i : Fin 3) :
    outputFiber q u k i = orderedConvection k (q - k) u i := by
  have h : modeDot q (u k) = modeDot (q - k) (u k) := by
    rw [modeDot_sub_left, hd k, sub_zero]
  simp [outputFiber, orderedConvection, h]

theorem abs_convection_pair_le (u : FourierVelocity) (q k l : Wavevector) :
    |(coefficientHermitian (u q) ((-unitTorusDerivativePhase) • orderedConvection k l u)).re| ≤
      (2 * Real.pi) * amplitude u q * amplitude u k * (‖frequencyVec l‖ * amplitude u l) := by
  apply (abs_hermitian_re_le _ _).trans
  change amplitude u q * ‖(-unitTorusDerivativePhase) •
    (modeDot l (u k) • coefficientVec (u l))‖ ≤ _
  rw [norm_smul, norm_neg, norm_derivativePhase, norm_smul]
  have h := norm_modeDot_le l (u k)
  change ‖modeDot l (u k)‖ ≤ ‖frequencyVec l‖ * amplitude u k at h
  calc
    _ ≤ amplitude u q * ((2 * Real.pi) *
        ((‖frequencyVec l‖ * amplitude u k) * amplitude u l)) := by
      dsimp [amplitude] at h ⊢
      gcongr
    _ = _ := by ring

/-! ### Input truncation -/

/-- The convective rate with outputs in `F` and inputs in `G`. -/
def truncConvectionRate (m : ℕ) (F G : Finset Wavevector) (u : FourierVelocity) : ℝ :=
  2 * ∑ q ∈ F, orderWeight m q ^ 2 * ∑ k ∈ G,
    (coefficientHermitian (u q) ((-unitTorusDerivativePhase) • orderedConvection k (q - k) u)).re

/-- The matching nonnegative triad. -/
def truncTriad (m : ℕ) (F G : Finset Wavevector) (a : Wavevector → ℝ) : ℝ :=
  ∑ q ∈ F, ∑ k ∈ G, orderWeight m q ^ 2 * a q * (a k * (‖frequencyVec (q - k)‖ * a (q - k)))

theorem abs_truncConvectionRate_le (m : ℕ) (F G : Finset Wavevector) (u : FourierVelocity) :
    |truncConvectionRate m F G u| ≤ 2 * (2 * Real.pi) * truncTriad m F G (amplitude u) := by
  unfold truncConvectionRate truncTriad
  calc |2 * ∑ q ∈ F, orderWeight m q ^ 2 * ∑ k ∈ G,
          (coefficientHermitian (u q) ((-unitTorusDerivativePhase) •
            orderedConvection k (q - k) u)).re|
      = 2 * |∑ q ∈ F, orderWeight m q ^ 2 * ∑ k ∈ G,
          (coefficientHermitian (u q) ((-unitTorusDerivativePhase) •
            orderedConvection k (q - k) u)).re| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * ∑ q ∈ F, orderWeight m q ^ 2 * ∑ k ∈ G,
          |(coefficientHermitian (u q) ((-unitTorusDerivativePhase) •
            orderedConvection k (q - k) u)).re| := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ ↦ ?_)
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ 2 * ∑ q ∈ F, orderWeight m q ^ 2 * ∑ k ∈ G,
          ((2 * Real.pi) * amplitude u q * amplitude u k *
            (‖frequencyVec (q - k)‖ * amplitude u (q - k))) := by
        gcongr with q _ k _
        exact abs_convection_pair_le u q k (q - k)
    _ = _ := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
        ring

/-- The finite set of nonzero modes that carries an input truncation. -/
def carrier (F G : Finset Wavevector) : Finset Wavevector :=
  (F ∪ G ∪ Finset.image₂ (· - ·) F G).erase 0

theorem mem_carrier_ne_zero {F G : Finset Wavevector} {k : Wavevector} (hk : k ∈ carrier F G) :
    k ≠ 0 := (Finset.mem_erase.mp hk).1

/-- **Domination.** An input-truncated triad is part of the order-`m` triad on
a finite set of nonzero modes. -/
theorem truncTriad_le_orderTriad (m : ℕ) (F G : Finset Wavevector) (a : Wavevector → ℝ)
    (ha : ∀ k, 0 ≤ a k) (ha0 : a 0 = 0) :
    truncTriad m F G a ≤ orderTriad m (carrier F G) a := by
  classical
  set M := carrier F G with hMdef
  let T : Wavevector × Wavevector → ℝ := fun p ↦
    orderWeight m p.1 ^ 2 * a p.1 * (a p.2 * (‖frequencyVec (p.1 - p.2)‖ * a (p.1 - p.2)))
  let g : Wavevector × Wavevector → ℝ := fun x ↦
    cut M (fun q ↦ orderWeight m q ^ 2 * a q) (x.1 + x.2) * a x.1 * (‖frequencyVec x.2‖ * a x.2)
  let S := (F ×ˢ G).filter (fun p ↦ p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 - p.2 ≠ 0)
  let φ : Wavevector × Wavevector → Wavevector × Wavevector := fun p ↦ (p.2, p.1 - p.2)
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    have hc : 0 ≤ cut M (fun q ↦ orderWeight m q ^ 2 * a q) (x.1 + x.2) := by
      unfold cut
      split_ifs
      · exact mul_nonneg (sq_nonneg _) (ha _)
      · exact le_rfl
    exact mul_nonneg (mul_nonneg hc (ha _)) (mul_nonneg (norm_nonneg _) (ha _))
  have hT : ∀ p ∈ F ×ˢ G, p ∉ S → T p = 0 := by
    intro p hp hpS
    have hnot : ¬ (p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 - p.2 ≠ 0) := fun h ↦ hpS (Finset.mem_filter.mpr ⟨hp, h⟩)
    push Not at hnot
    by_cases h1 : p.1 = 0
    · simp [T, h1, ha0]
    · by_cases h2 : p.2 = 0
      · simp [T, h2, ha0]
      · have h3 := hnot h1 h2
        simp [T, h3, ha0]
  have hinj : Set.InjOn φ S := by
    intro p _ p' _ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨h2, h3⟩ := h
    have h1 : p.1 = p'.1 := by
      have := congrArg (· + p.2) h3
      simp only [sub_add_cancel] at this
      rw [this, h2, sub_add_cancel]
    exact Prod.ext h1 h2
  have himage : S.image φ ⊆ M ×ˢ M := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hpFG, hq0, hk0, hd0⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq, hk⟩ := Finset.mem_product.mp hpFG
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_erase.mpr ⟨hk0, Finset.mem_union_left _ (Finset.mem_union_right _ hk)⟩
    · exact Finset.mem_erase.mpr ⟨hd0, Finset.mem_union_right _
        (Finset.mem_image₂_of_mem hq hk)⟩
  have hTg : ∀ p ∈ S, T p = g (φ p) := by
    intro p hp
    obtain ⟨hpFG, hq0, -, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq, -⟩ := Finset.mem_product.mp hpFG
    have hqM : p.1 ∈ M :=
      Finset.mem_erase.mpr ⟨hq0, Finset.mem_union_left _ (Finset.mem_union_left _ hq)⟩
    simp only [T, g, φ, cut, add_sub_cancel, hqM, ↓reduceIte]
    ring
  calc truncTriad m F G a = ∑ p ∈ F ×ˢ G, T p := by
        rw [Finset.sum_product]
        rfl
    _ = ∑ p ∈ S, T p := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        split_ifs with h
        · rfl
        · exact hT p hp (fun hS ↦ h (Finset.mem_filter.mp hS).2)
    _ = ∑ p ∈ S, g (φ p) := Finset.sum_congr rfl hTg
    _ = ∑ x ∈ S.image φ, g x := (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ M ×ˢ M, g x := Finset.sum_le_sum_of_subset_of_nonneg himage fun x _ _ ↦ hg0 x
    _ = orderTriad m M a := by
        rw [Finset.sum_product]
        rfl

/-! ### Convergence of the input truncations -/

theorem hasSum_convectionTerm (u : FourierVelocity) (hd : ∀ q, modeDot q (u q) = 0)
    (hs : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) (q : Wavevector) :
    HasSum (fun k ↦ (coefficientHermitian (u q) ((-unitTorusDerivativePhase) •
        orderedConvection k (q - k) u)).re)
      ((coefficientHermitian (u q) ((-unitTorusDerivativePhase) • infiniteConvection u q)).re) := by
  apply Complex.hasSum_re
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      HasSum (fun k ↦ conj (u q i) * ((-unitTorusDerivativePhase) *
          orderedConvection k (q - k) u i))
        (conj (u q i) * ((-unitTorusDerivativePhase) * infiniteConvection u q i)) := by
    intro i _
    have h' : HasSum (fun k ↦ orderedConvection k (q - k) u i) (infiniteConvection u q i) := by
      have h := (hs q i).hasSum
      convert h using 1
      · funext k
        exact (outputFiber_eq_orderedConvection u hd q k i).symm
      · rfl
    exact (h'.mul_left _).mul_left _
  have := hasSum_sum hi
  simpa [coefficientHermitian, Pi.smul_apply, smul_eq_mul] using this

theorem truncConvectionRate_eq_sum (m : ℕ) (F G : Finset Wavevector) (u : FourierVelocity) :
    truncConvectionRate m F G u = ∑ k ∈ G, 2 * ∑ q ∈ F, orderWeight m q ^ 2 *
      (coefficientHermitian (u q) ((-unitTorusDerivativePhase) •
        orderedConvection k (q - k) u)).re := by
  unfold truncConvectionRate
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- The input-truncated rates converge to the full convective rate. -/
theorem hasSum_truncRate (m : ℕ) (F : Finset Wavevector) (u : FourierVelocity)
    (hd : ∀ q, modeDot q (u q) = 0) (hs : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) :
    HasSum (fun k ↦ 2 * ∑ q ∈ F, orderWeight m q ^ 2 *
        (coefficientHermitian (u q) ((-unitTorusDerivativePhase) •
          orderedConvection k (q - k) u)).re)
      (infiniteConvectionRate m F u) := by
  unfold infiniteConvectionRate
  apply HasSum.mul_left
  apply hasSum_sum
  intro q _
  exact (hasSum_convectionTerm u hd hs q).mul_left _

theorem tendsto_truncConvectionRate (m : ℕ) (F : Finset Wavevector) (u : FourierVelocity)
    (hd : ∀ q, modeDot q (u q) = 0) (hs : ∀ q i, Summable (fun k ↦ outputFiber q u k i)) :
    Tendsto (fun G ↦ truncConvectionRate m F G u) atTop (nhds (infiniteConvectionRate m F u)) := by
  have h2 := (hasSum_truncRate m F u hd hs)
  simp_rw [truncConvectionRate_eq_sum]
  exact h2

/-! ### The tame bound at every input truncation -/

theorem amplitude_zero_of_zero {u : FourierVelocity} (h : u 0 = 0) : amplitude u 0 = 0 := by
  simp [amplitude, h, coefficientVec]

/-- Each input truncation obeys the tame bound on its finite carrier. -/
theorem truncConvectionRate_le_absorb (m : ℕ) (hm : 2 ≤ m) (F G : Finset Wavevector)
    (u : FourierVelocity) (hu0 : u 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    truncConvectionRate m F G u ≤ 2 * (2 * Real.pi) *
      (ε * velocityDissipation m (carrier F G) u +
        ((2 : ℝ) ^ (m + 1) * Real.sqrt tameMass * 4 ^ (1 - 1 / (8 * m) : ℝ) *
          ε ^ (-(1 - 1 / (8 * m)) : ℝ)) ^ (8 * m : ℝ) *
          velocityEnergy 1 (carrier F G) u ^ (4 * m + 1)) := by
  have ha : ∀ k, 0 ≤ amplitude u k := fun k ↦ norm_nonneg _
  have h1 := (le_abs_self _).trans (abs_truncConvectionRate_le m F G u)
  have h2 := truncTriad_le_orderTriad m F G (amplitude u) ha (amplitude_zero_of_zero hu0)
  have h3 := orderTriad_le_absorb m hm (carrier F G) (amplitude u) ha
    (fun k hk ↦ mem_carrier_ne_zero hk) hε
  calc truncConvectionRate m F G u ≤ 2 * (2 * Real.pi) * truncTriad m F G (amplitude u) := h1
    _ ≤ 2 * (2 * Real.pi) * orderTriad m (carrier F G) (amplitude u) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- A bound on every truncation that is uniform in the inputs. -/
theorem truncTriad_le_dom (m : ℕ) (F G : Finset Wavevector) (a : Wavevector → ℝ)
    (ha : ∀ k, 0 ≤ a k) {K : ℝ} (hK : ∀ S : Finset Wavevector, orderEnergy 1 S a ≤ K) :
    truncTriad m F G a ≤ (∑ q ∈ F, orderWeight m q ^ 2 * a q) * K := by
  classical
  unfold truncTriad
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  have hw : 0 ≤ orderWeight m q ^ 2 * a q := mul_nonneg (sq_nonneg _) (ha q)
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hw
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt G a (fun k ↦ ‖frequencyVec (q - k)‖ * a (q - k))
  have hA : ∑ k ∈ G, a k ^ 2 ≤ K := by
    refine le_trans ?_ (hK G)
    unfold orderEnergy orderWeight
    refine Finset.sum_le_sum fun k _ ↦ ?_
    rw [pow_one, mul_pow]
    have h1 : 1 ≤ (1 + ‖frequencyVec k‖) ^ 2 :=
      one_le_pow₀ (by linarith [norm_nonneg (frequencyVec k)])
    calc a k ^ 2 = 1 * a k ^ 2 := by ring
      _ ≤ (1 + ‖frequencyVec k‖) ^ 2 * a k ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hB : ∑ k ∈ G, (‖frequencyVec (q - k)‖ * a (q - k)) ^ 2 ≤ K := by
    have hinj : Set.InjOn (fun k ↦ q - k) G := by
      intro k _ k' _ h
      simpa using h
    have himg : ∑ k ∈ G, (‖frequencyVec (q - k)‖ * a (q - k)) ^ 2 =
        ∑ l ∈ G.image (fun k ↦ q - k), (‖frequencyVec l‖ * a l) ^ 2 :=
      (Finset.sum_image (f := fun l ↦ (‖frequencyVec l‖ * a l) ^ 2) hinj).symm
    rw [himg]
    refine le_trans ?_ (hK (G.image (fun k ↦ q - k)))
    unfold orderEnergy orderWeight
    refine Finset.sum_le_sum fun l _ ↦ ?_
    rw [pow_one, mul_pow, mul_pow]
    have h1 : ‖frequencyVec l‖ ^ 2 ≤ (1 + ‖frequencyVec l‖) ^ 2 := by
      nlinarith [norm_nonneg (frequencyVec l)]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  calc ∑ k ∈ G, a k * (‖frequencyVec (q - k)‖ * a (q - k))
      ≤ Real.sqrt (∑ k ∈ G, a k ^ 2) *
          Real.sqrt (∑ k ∈ G, (‖frequencyVec (q - k)‖ * a (q - k)) ^ 2) := hCS
    _ ≤ Real.sqrt K * Real.sqrt K := by
        gcongr
    _ = K := by
        have hK0 : 0 ≤ K := le_trans (Finset.sum_nonneg fun k _ ↦ sq_nonneg (a k)) hA
        exact Real.mul_self_sqrt hK0

/-! ### Exhausting the inputs -/

theorem tendsto_wavevectorBox : Tendsto wavevectorBox atTop atTop := by
  apply tendsto_atTop_finset_of_monotone
  · intro N N' hNN' k hk
    rw [mem_wavevectorBox_iff] at hk ⊢
    intro i
    exact (hk i).trans (by exact_mod_cast hNN')
  · intro k
    refine ⟨(k 0).natAbs + (k 1).natAbs + (k 2).natAbs, ?_⟩
    rw [mem_wavevectorBox_iff]
    intro i
    have h0 := abs_nonneg (k 0)
    have h1 := abs_nonneg (k 1)
    have h2 := abs_nonneg (k 2)
    fin_cases i <;> simp <;> omega

/-! ### Continuity along a solution -/

theorem continuous_truncConvectionRate (m : ℕ) (F G : Finset Wavevector)
    {c : ℝ → FourierVelocity} (hc : ∀ q i, Continuous (fun t ↦ c t q i)) :
    Continuous (fun t ↦ truncConvectionRate m F G (c t)) := by
  unfold truncConvectionRate coefficientHermitian orderedConvection modeDot
  simp only [Pi.smul_apply, smul_eq_mul]
  have hc' : ∀ q i, Continuous (fun t ↦ conj (c t q i)) := fun q i ↦ (hc q i).star
  fun_prop

theorem continuous_velocityEnergy_along (m : ℕ) (F : Finset Wavevector)
    {c : ℝ → FourierVelocity} (hc : ∀ q i, Continuous (fun t ↦ c t q i)) :
    Continuous (fun t ↦ velocityEnergy m F (c t)) := by
  simp only [velocityEnergy_eq, coefficientEnergy]
  fun_prop

theorem continuous_velocityDissipation_along (m : ℕ) (F : Finset Wavevector)
    {c : ℝ → FourierVelocity} (hc : ∀ q i, Continuous (fun t ↦ c t q i)) :
    Continuous (fun t ↦ velocityDissipation m F (c t)) := by
  simp only [velocityDissipation_eq, coefficientEnergy]
  fun_prop

theorem continuous_weightedAmplitude_along (m : ℕ) (F : Finset Wavevector)
    {c : ℝ → FourierVelocity} (hc : ∀ q i, Continuous (fun t ↦ c t q i)) :
    Continuous (fun t ↦ ∑ q ∈ F, orderWeight m q ^ 2 * amplitude (c t) q) := by
  have h : ∀ q, Continuous (fun t ↦ amplitude (c t) q) := by
    intro q
    have he : (fun t ↦ amplitude (c t) q) = fun t ↦ Real.sqrt (coefficientEnergy (c t q)) := by
      funext t
      rw [← norm_coefficientVec_sq, Real.sqrt_sq (norm_nonneg _)]
      rfl
    rw [he]
    unfold coefficientEnergy
    fun_prop
  fun_prop

/-! ### The integrated tame inequality along an actual solution -/

section Integrated

open MeasureTheory intervalIntegral
open scoped Interval

variable {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ}

theorem mem_Icc_of_mem_uIoc {S τ : ℝ} (hS : 0 ≤ S) (hτ : τ ∈ Ι (0 : ℝ) S) :
    τ ∈ Icc (0 : ℝ) S := by
  rw [uIoc_of_le hS] at hτ
  exact Ioc_subset_Icc_self hτ

/-- **Integrated tame inequality** for one output truncation, with any common
bound `X` for the truncated integrated dissipations. -/
theorem integrated_tame_step (m : ℕ) (hm : 2 ≤ m) (hnu : 0 < nu) (c : SolutionOn nu u₀ T)
    {S : ℝ} (hS : 0 < S) (hST : S < T) {B X K : ℝ}
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy m F (c.coefficients τ) ≤ B)
    (hX : ∀ G, ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients τ) ≤ X)
    (hK : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ K)
    (F : Finset Wavevector) :
    velocityEnergy m F (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 *
        (∫ τ in (0 : ℝ)..S, velocityDissipation m F (c.coefficients τ)) ≤
      velocityEnergy m F (c.coefficients 0) + nu * (2 * Real.pi) ^ 2 * X +
        tameRateConst m nu * K ^ (4 * m + 1) * S := by
  set ε : ℝ := nu * (2 * Real.pi) / 2 with hεdef
  have hε : 0 < ε := by positivity
  set Cε : ℝ := ((2 : ℝ) ^ (m + 1) * Real.sqrt tameMass * 4 ^ (1 - 1 / (8 * m) : ℝ) *
      ε ^ (-(1 - 1 / (8 * m)) : ℝ)) ^ (8 * m : ℝ) with hCε
  have hCε0 : 0 ≤ Cε := by
    have : 0 ≤ (2 : ℝ) ^ (m + 1) * Real.sqrt tameMass * 4 ^ (1 - 1 / (8 * m) : ℝ) *
        ε ^ (-(1 - 1 / (8 * m)) : ℝ) := by positivity
    exact Real.rpow_nonneg this _
  set c' := c.coefficients with hc'
  let Tr : ℕ → ℝ → ℝ := fun N τ ↦ truncConvectionRate m F (wavevectorBox N) (c' τ)
  let R : ℝ → ℝ := fun τ ↦ infiniteConvectionRate m F (c' τ)
  let Dq : ℝ → ℝ := fun τ ↦ velocityDissipation m F (c' τ)
  let bound : ℝ → ℝ := fun τ ↦
    2 * (2 * Real.pi) * ((∑ q ∈ F, orderWeight m q ^ 2 * amplitude (c' τ) q) * K)
  have hs : ∀ τ ∈ Icc (0 : ℝ) S, ∀ q i, Summable (fun k ↦ outputFiber q (c' τ) k i) := by
    intro τ hτ q i
    exact summable_outputFiber (c' τ) B
      (fun G ↦ (sobolevEnergy_le_velocityEnergy m hm G _).trans (hB τ hτ G)) q i
  have hlim : ∀ τ ∈ Icc (0 : ℝ) S, Tendsto (fun N ↦ Tr N τ) atTop (nhds (R τ)) := by
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
  have hR_meas : AEStronglyMeasurable R (volume.restrict (Ι (0 : ℝ) S)) := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (fun N ↦ (hTr_cont N).aestronglyMeasurable) ?_
    exact ae_restrict_of_forall_mem measurableSet_uIoc
      fun τ hτ ↦ hlim τ (mem_Icc_of_mem_uIoc hS.le hτ)
  have hR_bound : ∀ τ ∈ Icc (0 : ℝ) S, |R τ| ≤ bound τ := fun τ hτ ↦
    le_of_tendsto ((hlim τ hτ).abs) (Eventually.of_forall fun N ↦ hTrbound N τ hτ)
  have hR_int : IntervalIntegrable R volume 0 S := by
    refine (hbound_cont.intervalIntegrable 0 S).mono_fun' hR_meas ?_
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun τ hτ ↦ ?_
    show ‖R τ‖ ≤ bound τ
    rw [Real.norm_eq_abs]
    exact hR_bound τ (mem_Icc_of_mem_uIoc hS.le hτ)
  have hDCT : Tendsto (fun N ↦ ∫ τ in (0 : ℝ)..S, Tr N τ) atTop
      (nhds (∫ τ in (0 : ℝ)..S, R τ)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
    · exact Eventually.of_forall fun N ↦ (hTr_cont N).aestronglyMeasurable
    · refine Eventually.of_forall fun N ↦ Eventually.of_forall fun τ hτ ↦ ?_
      rw [Real.norm_eq_abs]
      exact hTrbound N τ (mem_Icc_of_mem_uIoc hS.le hτ)
    · exact hbound_cont.intervalIntegrable 0 S
    · exact Eventually.of_forall fun τ hτ ↦ hlim τ (mem_Icc_of_mem_uIoc hS.le hτ)
  have hTr_int_le : ∀ N, ∫ τ in (0 : ℝ)..S, Tr N τ ≤
      2 * (2 * Real.pi) * (ε * X + Cε * K ^ (4 * m + 1) * S) := by
    intro N
    set Dc : ℝ → ℝ := fun τ ↦ velocityDissipation m (carrier F (wavevectorBox N)) (c' τ)
    have hDc_cont : Continuous Dc := continuous_velocityDissipation_along m _ c.continuous
    have hpt : ∀ τ ∈ Icc (0 : ℝ) S, Tr N τ ≤
        2 * (2 * Real.pi) * (ε * Dc τ + Cε * K ^ (4 * m + 1)) := by
      intro τ hτ
      have h := truncConvectionRate_le_absorb m hm F (wavevectorBox N) (c' τ) (c.zero τ) hε
      have hE1 : velocityEnergy 1 (carrier F (wavevectorBox N)) (c' τ) ^ (4 * m + 1) ≤
          K ^ (4 * m + 1) :=
        pow_le_pow_left₀ (orderEnergy_nonneg _ _ _) (hK τ hτ _) _
      calc Tr N τ ≤ _ := h
        _ ≤ 2 * (2 * Real.pi) * (ε * Dc τ + Cε * K ^ (4 * m + 1)) := by
          gcongr
    have hrhs_cont : Continuous (fun τ ↦ 2 * (2 * Real.pi) * (ε * Dc τ + Cε * K ^ (4 * m + 1))) := by
      fun_prop
    calc ∫ τ in (0 : ℝ)..S, Tr N τ
        ≤ ∫ τ in (0 : ℝ)..S, 2 * (2 * Real.pi) * (ε * Dc τ + Cε * K ^ (4 * m + 1)) :=
          intervalIntegral.integral_mono_on hS.le ((hTr_cont N).intervalIntegrable 0 S)
            (hrhs_cont.intervalIntegrable 0 S) hpt
      _ = 2 * (2 * Real.pi) * (ε * (∫ τ in (0 : ℝ)..S, Dc τ) + Cε * K ^ (4 * m + 1) * S) := by
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
            ((hDc_cont.intervalIntegrable 0 S).const_mul _) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
          simp only [sub_zero, smul_eq_mul]
          ring
      _ ≤ 2 * (2 * Real.pi) * (ε * X + Cε * K ^ (4 * m + 1) * S) := by
          gcongr
          exact hX _
  have hR_int_le : ∫ τ in (0 : ℝ)..S, R τ ≤
      2 * (2 * Real.pi) * (ε * X + Cε * K ^ (4 * m + 1) * S) :=
    le_of_tendsto' hDCT hTr_int_le
  have hFTC : ∫ τ in (0 : ℝ)..S, (R τ - 2 * nu * (2 * Real.pi) ^ 2 * Dq τ) =
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
  have h2π : 2 * (2 * Real.pi) * ε = nu * (2 * Real.pi) ^ 2 := by rw [hεdef]; ring
  have hC : 2 * (2 * Real.pi) * Cε = tameRateConst m nu := by
    rw [hCε, hεdef]
    rfl
  have hexp : 2 * (2 * Real.pi) * (ε * X + Cε * K ^ (4 * m + 1) * S) =
      nu * (2 * Real.pi) ^ 2 * X + tameRateConst m nu * K ^ (4 * m + 1) * S := by
    rw [← h2π, ← hC]
    ring
  rw [hexp] at hR_int_le
  change velocityEnergy m F (c' S) + 2 * nu * (2 * Real.pi) ^ 2 * (∫ τ in (0 : ℝ)..S, Dq τ) ≤ _
  linarith

/-- **Order-one control of an actual solution.** On `[0, S]`, `S < T`, local
order-`m` bounds and a common bound on the truncated integrated dissipations
together with `E₁ ≤ K` give `E_m(S) ≤ 2 (E₀ + C K^(4m+1) S)`, where `E₀`
bounds the order-`m` energy of the data. The bound does not depend on the
local bounds. -/
theorem orderEnergy_le_of_orderOne (m : ℕ) (hm : 2 ≤ m) (hnu : 0 < nu)
    (c : SolutionOn nu u₀ T) {S : ℝ} (hS : 0 ≤ S) (hST : S < T) {B X K E₀ : ℝ}
    (hB : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy m F (c.coefficients τ) ≤ B)
    (hX : ∀ G, ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients τ) ≤ X)
    (hK : ∀ τ ∈ Icc (0 : ℝ) S, ∀ F, velocityEnergy 1 F (c.coefficients τ) ≤ K)
    (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀) :
    ∀ F, velocityEnergy m F (c.coefficients S) ≤
      2 * (E₀ + tameRateConst m nu * K ^ (4 * m + 1) * S) := by
  have hE₀0 : 0 ≤ E₀ := le_trans (orderEnergy_nonneg m ∅ _) (hE₀ ∅)
  have hK0 : 0 ≤ K := le_trans (orderEnergy_nonneg 1 ∅ _) (hK 0 ⟨le_rfl, hS⟩ ∅)
  have hC0 : 0 ≤ tameRateConst m nu * K ^ (4 * m + 1) * S :=
    mul_nonneg (mul_nonneg (tameRateConst_nonneg m hnu) (pow_nonneg hK0 _)) hS
  rcases hS.eq_or_lt with h0 | hSpos
  · intro F
    subst h0
    rw [c.initial]
    linarith [hE₀ F]
  · set C' := tameRateConst m nu * K ^ (4 * m + 1) * S
    set D : Finset Wavevector → ℝ := fun G ↦
      ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients τ)
    have hbdd : BddAbove (Set.range D) := ⟨X, by rintro _ ⟨G, rfl⟩; exact hX G⟩
    set Xs := sSup (Set.range D)
    have hXs : ∀ G, D G ≤ Xs := fun G ↦ le_csSup hbdd ⟨G, rfl⟩
    have hν : 0 < nu * (2 * Real.pi) ^ 2 := by positivity
    have hmain : ∀ F, velocityEnergy m F (c.coefficients S) + 2 * nu * (2 * Real.pi) ^ 2 * D F ≤
        E₀ + nu * (2 * Real.pi) ^ 2 * Xs + C' := by
      intro F
      have h := integrated_tame_step m hm hnu c hSpos hST hB hXs hK F
      rw [c.initial] at h
      linarith [hE₀ F]
    have hDnn : ∀ G, 0 ≤ D G := fun G ↦ intervalIntegral.integral_nonneg hSpos.le
      fun τ _ ↦ orderDissipation_nonneg m G _
    have hXs_le : nu * (2 * Real.pi) ^ 2 * Xs ≤ E₀ + C' := by
      have hb : ∀ G, D G ≤ (E₀ + nu * (2 * Real.pi) ^ 2 * Xs + C') / (2 * (nu * (2 * Real.pi) ^ 2)) := by
        intro G
        rw [le_div_iff₀ (by positivity)]
        have := hmain G
        have := orderEnergy_nonneg m G (amplitude (c.coefficients S))
        change 0 ≤ velocityEnergy m G (c.coefficients S) at this
        nlinarith
      have hsup : Xs ≤ (E₀ + nu * (2 * Real.pi) ^ 2 * Xs + C') / (2 * (nu * (2 * Real.pi) ^ 2)) :=
        csSup_le (Set.range_nonempty D) (by rintro _ ⟨G, rfl⟩; exact hb G)
      rw [le_div_iff₀ (by positivity)] at hsup
      nlinarith
    intro F
    have := hmain F
    have := hDnn F
    nlinarith

end Integrated

end Mettapedia.FluidDynamics.NavierStokes.FourierInfiniteTameRate
