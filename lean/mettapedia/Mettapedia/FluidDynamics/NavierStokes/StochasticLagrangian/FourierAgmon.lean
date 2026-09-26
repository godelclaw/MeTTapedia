import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierSmallDataOne
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierShellFeeding

/-!
# Agmon's inequality on the lattice, and the cubic order-one rate

The velocity's Wiener sum is controlled by the order-one energy and dissipation
together:

```text
(∑ₖ aₖ)² ≤ 104 √(E D),   E = ∑ |k|² aₖ²,   D = ∑ |k|⁴ aₖ²,
```

the Fourier form of Agmon's inequality `‖u‖_∞² ≲ ‖∇u‖ ‖Δu‖` on the
three-dimensional torus. The proof is a weighted Cauchy–Schwarz inequality with
weight `N² |k|² + |k|⁴`, and one lattice sum: grouping the modes by their
sup-norm radius `j`, a shell holds `(2j+1)³ - (2j-1)³ = 24 j² + 2` modes, and the
sum `∑ 1/(N² + j²)` telescopes to at most `2/N`, so
`∑_{k ≠ 0} 1/(|k|² (N² + |k|²)) ≤ 52/N` (`sum_lattice_le`). The choice
`N² = D/E` gives the inequality (`sq_sum_le_agmon`).

With it the order-one triad obeys `orderTriad₁ ≲ E₁^(3/4) D₁^(3/4)`
(`orderTriad_one_le_agmon`), and two AM-GM steps turn the convection rate into
`ν' D₁ + C(ν') E₁³` for every `ν' > 0` (`truncConvectionRate_le_agmon`): the
dissipation absorbs the convection up to a cubic power of the order-one energy.
This is the rate behind Leray's lower bound on the blowup rate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierAgmon

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCurlOutputTail PancakeInfinitePressureCoefficients
open PancakeArbitraryDataBlocks PancakeFiniteConvolutionL2 PancakeGalerkinKineticEnergy
open FourierInfiniteTameRate FourierShellFeeding

/-! ## Counting lattice points by sup-norm radius -/

/-- The sup-norm radius of an integer wavevector. -/
def supRadius (k : Wavevector) : ℕ := Finset.univ.sup fun i ↦ (k i).natAbs

theorem natAbs_le_supRadius (k : Wavevector) (i : Fin 3) : (k i).natAbs ≤ supRadius k :=
  Finset.le_sup (f := fun i ↦ (k i).natAbs) (Finset.mem_univ i)

theorem mem_wavevectorBox_iff_supRadius (R : ℕ) (k : Wavevector) :
    k ∈ wavevectorBox R ↔ supRadius k ≤ R := by
  rw [mem_wavevectorBox_iff, supRadius, Finset.sup_le_iff]
  constructor
  · intro h i _
    have := h i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  · intro h i
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h i (Finset.mem_univ i)

theorem supRadius_sq_le (k : Wavevector) : supRadius k ^ 2 ≤ modeSquareNat k := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i ↦ (k i).natAbs)
  rw [supRadius, hi, modeSquareNat]
  exact Finset.single_le_sum (f := fun i ↦ (k i).natAbs ^ 2) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ i)

theorem supRadius_pos {k : Wavevector} (hk : k ≠ 0) : 0 < supRadius k := by
  by_contra h
  apply hk
  funext i
  have h1 := natAbs_le_supRadius k i
  have h2 : (k i).natAbs = 0 := by omega
  simpa using h2

theorem card_wavevectorBox (R : ℕ) : (wavevectorBox R).card = (2 * R + 1) ^ 3 := by
  rw [wavevectorBox, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem card_filter_supRadius_le (M : Finset Wavevector) (j : ℕ) :
    (M.filter fun k ↦ supRadius k = j + 1).card ≤ 24 * (j + 1) ^ 2 + 2 := by
  have hsub : M.filter (fun k ↦ supRadius k = j + 1) ⊆ wavevectorBox (j + 1) \ wavevectorBox j := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_sdiff, mem_wavevectorBox_iff_supRadius, mem_wavevectorBox_iff_supRadius]
    omega
  have hsub' : wavevectorBox j ⊆ wavevectorBox (j + 1) := fun k hk ↦ by
    rw [mem_wavevectorBox_iff_supRadius] at hk ⊢
    omega
  have hcube : (2 * (j + 1) + 1) ^ 3 = (2 * j + 1) ^ 3 + (24 * (j + 1) ^ 2 + 2) := by ring
  calc (M.filter fun k ↦ supRadius k = j + 1).card
      ≤ (wavevectorBox (j + 1) \ wavevectorBox j).card := Finset.card_le_card hsub
    _ = (wavevectorBox (j + 1)).card - (wavevectorBox j).card := Finset.card_sdiff_of_subset hsub'
    _ = 24 * (j + 1) ^ 2 + 2 := by
        rw [card_wavevectorBox, card_wavevectorBox, hcube, Nat.add_sub_cancel_left]

/-! ## The lattice sum -/

theorem sum_inv_sq_add_le (N : ℝ) (hN : 0 < N) (J : ℕ) :
    ∑ j ∈ Finset.range J, 1 / (N ^ 2 + ((j : ℝ) + 1) ^ 2) ≤ 2 / N - 2 / (N + J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have h1 : 0 < N + J := by positivity
    have h2 : 0 < N + J + 1 := by positivity
    have e : 2 / (N + J) - 2 / (N + J + 1) = 1 / ((N + J) * (N + J + 1) / 2) := by
      field_simp
      ring
    have key : 1 / (N ^ 2 + ((J : ℝ) + 1) ^ 2) ≤ 1 / ((N + J) * (N + J + 1) / 2) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg (N - (J + 1))])
    push_cast
    have e' : N + ((J : ℝ) + 1) = N + J + 1 := by ring
    rw [e']
    linarith

/-- **The lattice sum.** `∑_{k ≠ 0} 1/(|k|² (N² + |k|²)) ≤ 52/N` over any finite set of
nonzero modes. -/
theorem sum_lattice_le (M : Finset Wavevector) (hM : ∀ k ∈ M, k ≠ 0) {N : ℝ} (hN : 0 < N) :
    ∑ k ∈ M, 1 / (‖frequencyVec k‖ ^ 2 * (N ^ 2 + ‖frequencyVec k‖ ^ 2)) ≤ 52 / N := by
  set J := M.sup supRadius
  have hmaps : ∀ k ∈ M, supRadius k - 1 ∈ Finset.range J := by
    intro k hk
    rw [Finset.mem_range]
    have h1 := supRadius_pos (hM k hk)
    have h2 : supRadius k ≤ J := Finset.le_sup (f := supRadius) hk
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ j ∈ Finset.range J,
      ∑ k ∈ M with supRadius k - 1 = j,
          1 / (‖frequencyVec k‖ ^ 2 * (N ^ 2 + ‖frequencyVec k‖ ^ 2)) ≤
        26 * (1 / (N ^ 2 + ((j : ℝ) + 1) ^ 2)) := by
    intro j _
    have hy : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by
      have : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
      nlinarith
    have hz : 0 < N ^ 2 + ((j : ℝ) + 1) ^ 2 := by positivity
    have hterm : ∀ k ∈ M.filter (fun k ↦ supRadius k - 1 = j),
        1 / (‖frequencyVec k‖ ^ 2 * (N ^ 2 + ‖frequencyVec k‖ ^ 2)) ≤
          1 / (((j : ℝ) + 1) ^ 2 * (N ^ 2 + ((j : ℝ) + 1) ^ 2)) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have hk0 := supRadius_pos (hM k hk.1)
      have hsr : supRadius k = j + 1 := by omega
      have hsq : ((j : ℝ) + 1) ^ 2 ≤ ‖frequencyVec k‖ ^ 2 := by
        rw [← modeSquareNat_cast]
        have := supRadius_sq_le k
        rw [hsr] at this
        exact_mod_cast this
      exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul hsq (add_le_add le_rfl hsq) hz.le (by positivity))
    have hcard : ((M.filter fun k ↦ supRadius k - 1 = j).card : ℝ) ≤ 24 * ((j : ℝ) + 1) ^ 2 + 2 := by
      have hsub : M.filter (fun k ↦ supRadius k - 1 = j) ⊆ M.filter fun k ↦ supRadius k = j + 1 := by
        intro k hk
        rw [Finset.mem_filter] at hk ⊢
        have := supRadius_pos (hM k hk.1)
        exact ⟨hk.1, by omega⟩
      have h := (Finset.card_le_card hsub).trans (card_filter_supRadius_le M j)
      exact_mod_cast h
    calc ∑ k ∈ M with supRadius k - 1 = j,
          1 / (‖frequencyVec k‖ ^ 2 * (N ^ 2 + ‖frequencyVec k‖ ^ 2))
        ≤ ∑ k ∈ M with supRadius k - 1 = j,
          1 / (((j : ℝ) + 1) ^ 2 * (N ^ 2 + ((j : ℝ) + 1) ^ 2)) := Finset.sum_le_sum hterm
      _ = ((M.filter fun k ↦ supRadius k - 1 = j).card : ℝ) *
          (1 / (((j : ℝ) + 1) ^ 2 * (N ^ 2 + ((j : ℝ) + 1) ^ 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (24 * ((j : ℝ) + 1) ^ 2 + 2) *
          (1 / (((j : ℝ) + 1) ^ 2 * (N ^ 2 + ((j : ℝ) + 1) ^ 2))) := by
          gcongr
      _ ≤ (26 * ((j : ℝ) + 1) ^ 2) *
          (1 / (((j : ℝ) + 1) ^ 2 * (N ^ 2 + ((j : ℝ) + 1) ^ 2))) := by
          gcongr
          linarith
      _ = 26 * (1 / (N ^ 2 + ((j : ℝ) + 1) ^ 2)) := by
          field_simp
  calc ∑ j ∈ Finset.range J, ∑ k ∈ M with supRadius k - 1 = j,
        1 / (‖frequencyVec k‖ ^ 2 * (N ^ 2 + ‖frequencyVec k‖ ^ 2))
      ≤ ∑ j ∈ Finset.range J, 26 * (1 / (N ^ 2 + ((j : ℝ) + 1) ^ 2)) :=
        Finset.sum_le_sum hfiber
    _ = 26 * ∑ j ∈ Finset.range J, 1 / (N ^ 2 + ((j : ℝ) + 1) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ 26 * (2 / N - 2 / (N + J)) := by
        gcongr
        exact sum_inv_sq_add_le N hN J
    _ ≤ 52 / N := by
        have : 0 ≤ 2 / (N + J) := by positivity
        have e : 26 * (2 / N) = 52 / N := by ring
        linarith

/-! ## Agmon's inequality -/

/-- **Agmon's inequality on the lattice.** For amplitudes on nonzero modes, `(∑ aₖ)² ≤ 104 √((∑ |k|² aₖ²) (∑ |k|⁴ aₖ²))`. -/
theorem sq_sum_le_agmon (M : Finset Wavevector) (hM : ∀ k ∈ M, k ≠ 0) (a : Wavevector → ℝ) :
    (∑ k ∈ M, a k) ^ 2 ≤ 104 * Real.sqrt ((∑ k ∈ M, ‖frequencyVec k‖ ^ 2 * a k ^ 2) *
      ∑ k ∈ M, ‖frequencyVec k‖ ^ 4 * a k ^ 2) := by
  obtain ⟨E, hEdef⟩ : ∃ E, E = ∑ k ∈ M, ‖frequencyVec k‖ ^ 2 * a k ^ 2 := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = ∑ k ∈ M, ‖frequencyVec k‖ ^ 4 * a k ^ 2 := ⟨_, rfl⟩
  rw [← hEdef, ← hDdef]
  have hE0 : 0 ≤ E := by rw [hEdef]; exact Finset.sum_nonneg fun k _ ↦ by positivity
  have hED : E ≤ D := by
    rw [hEdef, hDdef]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have h1 := one_le_norm_frequencyVec (hM k hk)
    have : ‖frequencyVec k‖ ^ 2 ≤ ‖frequencyVec k‖ ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  rcases hE0.eq_or_lt with hE | hE
  · have hz : ∀ k ∈ M, a k = 0 := by
      intro k hk
      have hterm : ‖frequencyVec k‖ ^ 2 * a k ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ by positivity)).mp (hEdef ▸ hE.symm) k hk
      have h1 := one_le_norm_frequencyVec (hM k hk)
      have hpos : 0 < ‖frequencyVec k‖ ^ 2 := by positivity
      have : a k ^ 2 = 0 := (mul_eq_zero.mp hterm).resolve_left hpos.ne'
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    rw [Finset.sum_eq_zero hz]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · have hD : 0 < D := lt_of_lt_of_le hE hED
    obtain ⟨N, hNdef⟩ : ∃ N, N = Real.sqrt (D / E) := ⟨_, rfl⟩
    have hN : 0 < N := by rw [hNdef]; exact Real.sqrt_pos.mpr (div_pos hD hE)
    have hN2 : N ^ 2 = D / E := by rw [hNdef]; exact Real.sq_sqrt (div_pos hD hE).le
    have hw : ∀ k ∈ M, 0 < N ^ 2 * ‖frequencyVec k‖ ^ 2 + ‖frequencyVec k‖ ^ 4 := fun k hk ↦ by
      have h1 := one_le_norm_frequencyVec (hM k hk)
      positivity
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq M
      (fun k ↦ Real.sqrt (N ^ 2 * ‖frequencyVec k‖ ^ 2 + ‖frequencyVec k‖ ^ 4) * a k)
      (fun k ↦ 1 / Real.sqrt (N ^ 2 * ‖frequencyVec k‖ ^ 2 + ‖frequencyVec k‖ ^ 4))
    have hfg : ∑ k ∈ M, Real.sqrt (N ^ 2 * ‖frequencyVec k‖ ^ 2 + ‖frequencyVec k‖ ^ 4) * a k *
        (1 / Real.sqrt (N ^ 2 * ‖frequencyVec k‖ ^ 2 + ‖frequencyVec k‖ ^ 4)) = ∑ k ∈ M, a k :=
      Finset.sum_congr rfl fun k hk ↦ by
        have := (Real.sqrt_pos.mpr (hw k hk)).ne'
        rw [mul_comm _ (a k), mul_assoc, mul_one_div_cancel this, mul_one]
    have hf2 : ∑ k ∈ M,
        (Real.sqrt (N ^ 2 * ‖frequencyVec k‖ ^ 2 + ‖frequencyVec k‖ ^ 4) * a k) ^ 2 =
          N ^ 2 * E + D := by
      rw [hEdef, hDdef, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [mul_pow, Real.sq_sqrt (hw k hk).le]
      ring
    have hg2 : ∑ k ∈ M,
        (1 / Real.sqrt (N ^ 2 * ‖frequencyVec k‖ ^ 2 + ‖frequencyVec k‖ ^ 4)) ^ 2 =
          ∑ k ∈ M, 1 / (‖frequencyVec k‖ ^ 2 * (N ^ 2 + ‖frequencyVec k‖ ^ 2)) :=
      Finset.sum_congr rfl fun k hk ↦ by
        rw [div_pow, one_pow, Real.sq_sqrt (hw k hk).le]
        ring
    rw [hfg, hf2, hg2] at hcs
    have hlat := sum_lattice_le M hM hN
    have hsqrt : Real.sqrt (E * D) = D / N := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (div_pos hD hN)]
      have e : D / N * (D / N) = D ^ 2 / N ^ 2 := by ring
      rw [e, hN2]
      field_simp
    rw [hsqrt]
    have hND : 0 ≤ N ^ 2 * E + D := by positivity
    calc (∑ k ∈ M, a k) ^ 2 ≤ (N ^ 2 * E + D) *
          ∑ k ∈ M, 1 / (‖frequencyVec k‖ ^ 2 * (N ^ 2 + ‖frequencyVec k‖ ^ 2)) := hcs
      _ ≤ (N ^ 2 * E + D) * (52 / N) := mul_le_mul_of_nonneg_left hlat hND
      _ = 104 * (D / N) := by
          rw [hN2, div_mul_cancel₀ _ hE.ne']
          ring

/-! ## The order-one triad and the cubic rate -/

/-- **The order-one triad with Agmon's inequality**:
`orderTriad₁ ≤ 2 √D₁ √E₁ √(104 √(E₁ D₁))`, of order `E₁^(3/4) D₁^(3/4)`. -/
theorem orderTriad_one_le_agmon (M : Finset Wavevector) (a : Wavevector → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hM : ∀ k ∈ M, k ≠ 0) :
    orderTriad 1 M a ≤ 2 * Real.sqrt (orderDissipation 1 M a) * Real.sqrt (orderEnergy 1 M a) *
      Real.sqrt (104 * Real.sqrt (orderEnergy 1 M a * orderDissipation 1 M a)) := by
  obtain ⟨E, hEdef⟩ : ∃ E, E = orderEnergy 1 M a := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = orderDissipation 1 M a := ⟨_, rfl⟩
  rw [← hEdef, ← hDdef]
  have hE0 : 0 ≤ E := hEdef ▸ orderEnergy_nonneg 1 M a
  have hD0 : 0 ≤ D := hDdef ▸ orderDissipation_nonneg 1 M a
  have hw : ∀ k ∈ M, (1 + ‖frequencyVec k‖) ≤ 2 * ‖frequencyVec k‖ := fun k hk ↦ by
    have := one_le_norm_frequencyVec (hM k hk)
    linarith
  have h1 : sizeL2 M (fun q ↦ orderWeight 1 q ^ 2 * a q) ≤ 2 * Real.sqrt D := by
    have hsq : (∑ q ∈ M, (orderWeight 1 q ^ 2 * a q) ^ 2) ≤ 4 * D := by
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
  have h3 : ∑ k ∈ M, a k ≤ Real.sqrt (104 * Real.sqrt (E * D)) := by
    have hag := sq_sum_le_agmon M hM a
    have hEe : ∑ k ∈ M, ‖frequencyVec k‖ ^ 2 * a k ^ 2 ≤ E := by
      rw [hEdef]
      unfold orderEnergy
      refine Finset.sum_le_sum fun k _ ↦ ?_
      simp only [orderWeight, pow_one]
      have : ‖frequencyVec k‖ ^ 2 ≤ (1 + ‖frequencyVec k‖) ^ 2 := by
        nlinarith [norm_nonneg (frequencyVec k)]
      calc ‖frequencyVec k‖ ^ 2 * a k ^ 2 ≤ (1 + ‖frequencyVec k‖) ^ 2 * a k ^ 2 :=
            mul_le_mul_of_nonneg_right this (sq_nonneg _)
        _ = ((1 + ‖frequencyVec k‖) * a k) ^ 2 := by ring
    have hDd : ∑ k ∈ M, ‖frequencyVec k‖ ^ 4 * a k ^ 2 ≤ D := by
      rw [hDdef]
      unfold orderDissipation orderEnergy
      refine Finset.sum_le_sum fun k _ ↦ ?_
      simp only [orderWeight, pow_one]
      have : ‖frequencyVec k‖ ^ 2 ≤ (1 + ‖frequencyVec k‖) ^ 2 := by
        nlinarith [norm_nonneg (frequencyVec k)]
      calc ‖frequencyVec k‖ ^ 4 * a k ^ 2 =
            ‖frequencyVec k‖ ^ 2 * (‖frequencyVec k‖ ^ 2 * a k ^ 2) := by ring
        _ ≤ (1 + ‖frequencyVec k‖) ^ 2 * (‖frequencyVec k‖ ^ 2 * a k ^ 2) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = ((1 + ‖frequencyVec k‖) * (‖frequencyVec k‖ * a k)) ^ 2 := by ring
    have hs0 : 0 ≤ ∑ k ∈ M, a k := Finset.sum_nonneg fun k _ ↦ ha k
    rw [← Real.sqrt_sq hs0]
    apply Real.sqrt_le_sqrt
    refine hag.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num))
    exact mul_le_mul hEe hDd (Finset.sum_nonneg fun k _ ↦ by positivity) hE0
  have hT := triadSum_le_leftL1 M (fun q ↦ orderWeight 1 q ^ 2 * a q) a
    (fun l ↦ ‖frequencyVec l‖ * a l) (fun k _ ↦ ha k)
  change orderTriad 1 M a ≤ _ at hT
  have hs1 := sizeL2_nonneg M (fun q ↦ orderWeight 1 q ^ 2 * a q)
  have hs2 := sizeL2_nonneg M (fun l ↦ ‖frequencyVec l‖ * a l)
  have hsum0 : 0 ≤ ∑ k ∈ M, a k := Finset.sum_nonneg fun k _ ↦ ha k
  calc orderTriad 1 M a
      ≤ sizeL2 M (fun q ↦ orderWeight 1 q ^ 2 * a q) * sizeL2 M (fun l ↦ ‖frequencyVec l‖ * a l) *
          ∑ k ∈ M, a k := hT
    _ ≤ (2 * Real.sqrt D) * Real.sqrt E * Real.sqrt (104 * Real.sqrt (E * D)) := by
        gcongr

theorem mul_le_half_add (ν a b : ℝ) (hν : 0 < ν) : a * b ≤ ν / 2 * a ^ 2 + b ^ 2 / (2 * ν) := by
  have h := sq_nonneg (ν * a - b)
  have e : ν / 2 * a ^ 2 + b ^ 2 / (2 * ν) - a * b = (ν * a - b) ^ 2 / (2 * ν) := by
    field_simp
    ring
  have : 0 ≤ (ν * a - b) ^ 2 / (2 * ν) := div_nonneg h (by positivity)
  linarith

/-- **Two AM-GM steps**: `K p³ q³ ≤ ν p⁴ + K⁴/(8ν³) q¹²`. -/
theorem cube_mul_cube_le (K ν p q : ℝ) (hν : 0 < ν) :
    K * p ^ 3 * q ^ 3 ≤ ν * p ^ 4 + K ^ 4 / (8 * ν ^ 3) * q ^ 12 := by
  have h1 := mul_le_half_add ν (p ^ 2) (K * p * q ^ 3) hν
  have h2 := mul_le_half_add ν (p ^ 2) (K ^ 2 / (2 * ν) * q ^ 6) hν
  have e1 : p ^ 2 * (K * p * q ^ 3) = K * p ^ 3 * q ^ 3 := by ring
  have e2 : (K * p * q ^ 3) ^ 2 / (2 * ν) = p ^ 2 * (K ^ 2 / (2 * ν) * q ^ 6) := by
    field_simp
    try ring
  have e3 : (K ^ 2 / (2 * ν) * q ^ 6) ^ 2 / (2 * ν) = K ^ 4 / (8 * ν ^ 3) * q ^ 12 := by
    field_simp
    try ring
  have e4 : (p ^ 2) ^ 2 = p ^ 4 := by ring
  rw [e1, e2, e4] at h1
  rw [e3, e4] at h2
  linarith

/-- The constant of the cubic order-one rate. -/
def agmonRateConst : ℝ := 4 * (2 * Real.pi) * Real.sqrt 104

theorem agmonRateConst_pos : 0 < agmonRateConst := by
  unfold agmonRateConst
  have := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 104)
  positivity

/-- **The cubic order-one rate.** For every `ν > 0` the truncated order-one convection
rate is at most `ν D₁ + K⁴/(8 ν³) E₁³` on the carrier, with `K = agmonRateConst`. -/
theorem truncConvectionRate_le_agmon (F G : Finset Wavevector) (u : FourierVelocity)
    (hu0 : u 0 = 0) {ν : ℝ} (hν : 0 < ν) :
    truncConvectionRate 1 F G u ≤ ν * velocityDissipation 1 (carrier F G) u +
      agmonRateConst ^ 4 / (8 * ν ^ 3) * velocityEnergy 1 (carrier F G) u ^ 3 := by
  have ha : ∀ k, 0 ≤ amplitude u k := fun k ↦ norm_nonneg _
  have h1 := (le_abs_self _).trans (abs_truncConvectionRate_le 1 F G u)
  have h2 := truncTriad_le_orderTriad 1 F G (amplitude u) ha (amplitude_zero_of_zero hu0)
  have h3 := orderTriad_one_le_agmon (carrier F G) (amplitude u) ha
    (fun k hk ↦ mem_carrier_ne_zero hk)
  unfold velocityDissipation velocityEnergy
  obtain ⟨E, hEdef⟩ : ∃ E, E = orderEnergy 1 (carrier F G) (amplitude u) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = orderDissipation 1 (carrier F G) (amplitude u) := ⟨_, rfl⟩
  rw [← hEdef, ← hDdef] at h3 ⊢
  have hE0 : 0 ≤ E := hEdef ▸ orderEnergy_nonneg _ _ _
  have hD0 : 0 ≤ D := hDdef ▸ orderDissipation_nonneg _ _ _
  obtain ⟨p, hpdef⟩ : ∃ p, p = Real.sqrt (Real.sqrt D) := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q, q = Real.sqrt (Real.sqrt E) := ⟨_, rfl⟩
  have hp2 : p ^ 2 = Real.sqrt D := by rw [hpdef]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hq2 : q ^ 2 = Real.sqrt E := by rw [hqdef]; exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hp4 : p ^ 4 = D := by
    rw [show p ^ 4 = (p ^ 2) ^ 2 by ring, hp2, Real.sq_sqrt hD0]
  have hq4 : q ^ 4 = E := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hq2, Real.sq_sqrt hE0]
  have hmix : Real.sqrt (104 * Real.sqrt (E * D)) = Real.sqrt 104 * (q * p) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hE0, Real.sqrt_mul (Real.sqrt_nonneg _),
      hpdef, hqdef]
  have hrate : truncConvectionRate 1 F G u ≤ agmonRateConst * p ^ 3 * q ^ 3 := by
    calc truncConvectionRate 1 F G u ≤ 2 * (2 * Real.pi) * truncTriad 1 F G (amplitude u) := h1
      _ ≤ 2 * (2 * Real.pi) * orderTriad 1 (carrier F G) (amplitude u) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 2 * (2 * Real.pi) *
          (2 * Real.sqrt D * Real.sqrt E * Real.sqrt (104 * Real.sqrt (E * D))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = agmonRateConst * p ^ 3 * q ^ 3 := by
          rw [hmix, ← hp2, ← hq2]
          unfold agmonRateConst
          ring
  have hcube := cube_mul_cube_le agmonRateConst ν p q hν
  rw [hp4, show q ^ 12 = (q ^ 4) ^ 3 by ring, hq4] at hcube
  linarith

end Mettapedia.FluidDynamics.NavierStokes.FourierAgmon
