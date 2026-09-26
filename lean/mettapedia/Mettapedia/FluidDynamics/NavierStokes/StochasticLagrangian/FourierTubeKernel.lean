import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierShearedLatticeCount

/-!
# Lattice kernels for paired cone interactions

The inverse-radius sum in a three-dimensional box grows quadratically. In a
tube, the inverse-square sum beyond a longitudinal cutoff is bounded using
two uniformly bounded transverse slices and a telescoping one-dimensional
tail. These are the geometric summation ingredients for the paired stretching
kernel; they concern finite sets of actual integer frequencies.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierTubeKernel

open scoped BigOperators
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator PancakeArbitraryDataBlocks
  FourierAgmon FourierShearedLatticeCount FourierShellFeeding

theorem supRadius_le_norm (k : Wavevector) : (supRadius k : ℝ) ≤ ‖frequencyVec k‖ := by
  have hs : (supRadius k : ℝ) ^ 2 ≤ ‖frequencyVec k‖ ^ 2 := by
    rw [← modeSquareNat_cast]
    exact_mod_cast supRadius_sq_le k
  nlinarith [norm_nonneg (frequencyVec k), Nat.cast_nonneg (α := ℝ) (supRadius k)]

/-- The inverse-radius kernel over an ordinary integer box. -/
theorem sum_inv_radius_le (s : Finset Wavevector) (R : ℕ)
    (hs0 : ∀ k ∈ s, k ≠ 0) (hR : ∀ k ∈ s, supRadius k ≤ R) :
    ∑ k ∈ s, 1 / ‖frequencyVec k‖ ≤ 26 * (R : ℝ) ^ 2 := by
  have hmaps : ∀ k ∈ s, supRadius k - 1 ∈ Finset.range R := by
    intro k hk
    have := supRadius_pos (hs0 k hk)
    have := hR k hk
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ j ∈ Finset.range R,
      (∑ k ∈ s with supRadius k - 1 = j, 1 / ‖frequencyVec k‖) ≤ 26 * R := by
    intro j hj
    have hjR : (j : ℝ) + 1 ≤ R := by exact_mod_cast Finset.mem_range.mp hj
    have hj0 : 0 < (j : ℝ) + 1 := by positivity
    have hsr : ∀ k ∈ s.filter (fun k ↦ supRadius k - 1 = j), supRadius k = j + 1 := by
      intro k hk
      obtain ⟨hk, he⟩ := Finset.mem_filter.mp hk
      have := supRadius_pos (hs0 k hk)
      omega
    have hc : ((s.filter fun k ↦ supRadius k - 1 = j).card : ℝ) ≤
        26 * ((j : ℝ) + 1) ^ 2 := by
      have hsub : s.filter (fun k ↦ supRadius k - 1 = j) ⊆
          s.filter (fun k ↦ supRadius k = j + 1) := fun k hk ↦
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, hsr k hk⟩
      have hn := (Finset.card_le_card hsub).trans (card_filter_supRadius_le s j)
      have hn' : ((s.filter fun k ↦ supRadius k - 1 = j).card : ℝ) ≤
          24 * ((j : ℝ) + 1) ^ 2 + 2 := by exact_mod_cast hn
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
    calc
      _ ≤ ∑ k ∈ s.filter (fun k ↦ supRadius k - 1 = j), 1 / ((j : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        apply one_div_le_one_div_of_le hj0
        have := supRadius_le_norm k
        simpa only [hsr k hk, Nat.cast_add, Nat.cast_one] using this
      _ = ((s.filter fun k ↦ supRadius k - 1 = j).card : ℝ) / ((j : ℝ) + 1) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ 26 * ((j : ℝ) + 1) := (div_le_iff₀ hj0).mpr (by nlinarith [hc])
      _ ≤ 26 * R := by gcongr
  calc
    _ ≤ ∑ _j ∈ Finset.range R, 26 * (R : ℝ) := Finset.sum_le_sum hfiber
    _ = _ := by simp [pow_two]; ring

/-- The inverse-square tail telescopes after an arbitrary positive cutoff. -/
theorem sum_inv_sq_tail_le (N : ℝ) (hN : 0 < N) (J : ℕ) :
    ∑ j ∈ Finset.range J, 1 / (N + j + 1) ^ 2 ≤ 1 / N - 1 / (N + J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have h1 : 0 < N + J := by positivity
    have h2 : 0 < N + J + 1 := by positivity
    have he : 1 / (N + J) - 1 / (N + J + 1) =
        1 / ((N + J) * (N + J + 1)) := by field_simp; ring
    have hterm : 1 / (N + J + 1) ^ 2 ≤ 1 / ((N + J) * (N + J + 1)) :=
      one_div_le_one_div_of_le (mul_pos h1 h2) (by nlinarith)
    push_cast
    have he' : N + ((J : ℝ) + 1) = N + J + 1 := by ring
    rw [he']
    linarith

/-- Summing beyond a longitudinal cutoff uses only the two slice counts at each radius. -/
theorem sum_inv_sq_tube_tail_le (s : Finset Wavevector) (j : Fin 3) (v : Fin 3 → ℝ)
    (D N : ℕ) (hN : 0 < N) (hlarge : ∀ k ∈ s, N < (k j).natAbs)
    (hshear : ∀ k ∈ s, ∀ i, i ≠ j → |(k i : ℝ) - v i * k j| ≤ D) :
    ∑ k ∈ s, 1 / ‖frequencyVec k‖ ^ 2 ≤
      (2 * (2 * (D : ℝ) + 2) ^ 2) / N := by
  set J := s.sup fun k ↦ (k j).natAbs
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmaps : ∀ k ∈ s, (k j).natAbs - N - 1 ∈ Finset.range J := by
    intro k hk
    have h1 := hlarge k hk
    have h2 : (k j).natAbs ≤ J := Finset.le_sup (f := fun k ↦ (k j).natAbs) hk
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ m ∈ Finset.range J,
      (∑ k ∈ s with (k j).natAbs - N - 1 = m, 1 / ‖frequencyVec k‖ ^ 2) ≤
        (2 * (2 * (D : ℝ) + 2) ^ 2) * (1 / ((N : ℝ) + m + 1) ^ 2) := by
    intro m _
    have habs : ∀ k ∈ s.filter (fun k ↦ (k j).natAbs - N - 1 = m),
        (k j).natAbs = N + m + 1 := by
      intro k hk
      obtain ⟨hk, he⟩ := Finset.mem_filter.mp hk
      have := hlarge k hk
      omega
    have hc : ((s.filter fun k ↦ (k j).natAbs - N - 1 = m).card : ℝ) ≤
        2 * (2 * (D : ℝ) + 2) ^ 2 := by
      have h := card_abs_slice_le (s.filter fun k ↦ (k j).natAbs - N - 1 = m)
        j v D (N + m + 1) habs
        (fun k hk ↦ hshear k (Finset.mem_filter.mp hk).1)
      exact_mod_cast h
    calc
      _ ≤ ∑ k ∈ s.filter (fun k ↦ (k j).natAbs - N - 1 = m),
          1 / ((N : ℝ) + m + 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hrad : (N : ℝ) + m + 1 ≤ ‖frequencyVec k‖ := by
          have hc : ((k j).natAbs : ℝ) ≤ (supRadius k : ℝ) := by
            exact_mod_cast natAbs_le_supRadius k j
          have h : ((k j).natAbs : ℝ) ≤ ‖frequencyVec k‖ :=
            hc.trans (supRadius_le_norm k)
          simpa only [habs k hk, Nat.cast_add, Nat.cast_one] using h
        exact one_div_le_one_div_of_le (by positivity)
          (sq_le_sq₀ (by positivity) (norm_nonneg _) |>.mpr hrad)
      _ = ((s.filter fun k ↦ (k j).natAbs - N - 1 = m).card : ℝ) *
          (1 / ((N : ℝ) + m + 1) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  calc
    _ ≤ ∑ m ∈ Finset.range J,
        (2 * (2 * (D : ℝ) + 2) ^ 2) * (1 / ((N : ℝ) + m + 1) ^ 2) :=
      Finset.sum_le_sum hfiber
    _ = (2 * (2 * (D : ℝ) + 2) ^ 2) *
        ∑ m ∈ Finset.range J, 1 / ((N : ℝ) + m + 1) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (2 * (2 * (D : ℝ) + 2) ^ 2) * (1 / N - 1 / ((N : ℝ) + J)) :=
      mul_le_mul_of_nonneg_left (sum_inv_sq_tail_le N hN' J) (by positivity)
    _ ≤ (2 * (2 * (D : ℝ) + 2) ^ 2) * (1 / N) := by
      gcongr
      exact sub_le_self _ (by positivity)
    _ = _ := by ring

/-- The inverse-square kernel over an ordinary integer box grows linearly. -/
theorem sum_inv_sq_radius_le (s : Finset Wavevector) (R : ℕ)
    (hs0 : ∀ k ∈ s, k ≠ 0) (hR : ∀ k ∈ s, supRadius k ≤ R) :
    ∑ k ∈ s, 1 / ‖frequencyVec k‖ ^ 2 ≤ 26 * (R : ℝ) := by
  have hmaps : ∀ k ∈ s, supRadius k - 1 ∈ Finset.range R := by
    intro k hk
    have := supRadius_pos (hs0 k hk)
    have := hR k hk
    simp only [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ m ∈ Finset.range R,
      (∑ k ∈ s with supRadius k - 1 = m, 1 / ‖frequencyVec k‖ ^ 2) ≤ 26 := by
    intro m _
    have hm0 : 0 < (m : ℝ) + 1 := by positivity
    have hsr : ∀ k ∈ s.filter (fun k ↦ supRadius k - 1 = m), supRadius k = m + 1 := by
      intro k hk
      obtain ⟨hk, he⟩ := Finset.mem_filter.mp hk
      have := supRadius_pos (hs0 k hk)
      omega
    have hc : ((s.filter fun k ↦ supRadius k - 1 = m).card : ℝ) ≤
        26 * ((m : ℝ) + 1) ^ 2 := by
      have hsub : s.filter (fun k ↦ supRadius k - 1 = m) ⊆
          s.filter (fun k ↦ supRadius k = m + 1) := fun k hk ↦
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, hsr k hk⟩
      have hn := (Finset.card_le_card hsub).trans (card_filter_supRadius_le s m)
      have hn' : ((s.filter fun k ↦ supRadius k - 1 = m).card : ℝ) ≤
          24 * ((m : ℝ) + 1) ^ 2 + 2 := by exact_mod_cast hn
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    calc
      _ ≤ ∑ k ∈ s.filter (fun k ↦ supRadius k - 1 = m), 1 / ((m : ℝ) + 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hrad : (m : ℝ) + 1 ≤ ‖frequencyVec k‖ := by
          simpa only [hsr k hk, Nat.cast_add, Nat.cast_one] using supRadius_le_norm k
        exact one_div_le_one_div_of_le (sq_pos_of_pos hm0)
          ((sq_le_sq₀ hm0.le (norm_nonneg _)).mpr hrad)
      _ = ((s.filter fun k ↦ supRadius k - 1 = m).card : ℝ) / ((m : ℝ) + 1) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ 26 := (div_le_iff₀ (sq_pos_of_pos hm0)).mpr hc
  calc
    _ ≤ ∑ _m ∈ Finset.range R, (26 : ℝ) := Finset.sum_le_sum hfiber
    _ = _ := by simp [mul_comm]

/-- The inverse-square sum in a tube is uniform in its real axis and grows only with its width. -/
theorem sum_inv_sq_tube_le (s : Finset Wavevector) (n : Fin 3 → ℝ) (hn : n ≠ 0)
    (N : ℕ) (hN : 0 < N) (hs0 : ∀ k ∈ s, k ≠ 0)
    (hTube : ∀ k ∈ s, InTube n N k) :
    ∑ k ∈ s, 1 / ‖frequencyVec k‖ ^ 2 ≤ 150 * (N : ℝ) := by
  obtain ⟨j, hj, hdom⟩ := exists_dominant_coordinate n hn
  let v := fun i ↦ n i / n j
  have hv : ∀ i, |v i| ≤ 1 := fun i ↦ by
    rw [show v i = n i / n j from rfl, abs_div, div_le_one (abs_pos.mpr hj)]
    exact hdom i
  have hshear : ∀ k ∈ s, ∀ i, i ≠ j → |(k i : ℝ) - v i * k j| ≤ (2 * N : ℕ) := by
    intro k hk i _
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      tube_shear hj hdom (Nat.cast_nonneg N) (hTube k hk) i
  have hnear : (∑ k ∈ s with (k j).natAbs ≤ N, 1 / ‖frequencyVec k‖ ^ 2) ≤ 78 * (N : ℝ) := by
    have h := sum_inv_sq_radius_le (s.filter fun k ↦ (k j).natAbs ≤ N) (N + 2 * N)
      (fun k hk ↦ hs0 k (Finset.mem_filter.mp hk).1)
      (fun k hk ↦ supRadius_le_of_shear hv (Finset.mem_filter.mp hk).2
        (hshear k (Finset.mem_filter.mp hk).1))
    convert h using 1
    push_cast
    ring
  have hfar : (∑ k ∈ s with ¬(k j).natAbs ≤ N, 1 / ‖frequencyVec k‖ ^ 2) ≤ 72 * (N : ℝ) := by
    have h := sum_inv_sq_tube_tail_le (s.filter fun k ↦ ¬(k j).natAbs ≤ N) j v (2 * N) N hN
      (fun k hk ↦ lt_of_not_ge (Finset.mem_filter.mp hk).2)
      (fun k hk ↦ hshear k (Finset.mem_filter.mp hk).1)
    refine h.trans ?_
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [div_le_iff₀ hN']
    push_cast
    have hsq : (4 * (N : ℝ) + 2) ^ 2 ≤ (6 * N) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    nlinarith
  rw [← Finset.sum_filter_add_sum_filter_not s (fun k ↦ (k j).natAbs ≤ N)]
  linarith

/-- The same bound with the zero mode included, using the zero value of its weight. -/
theorem sum_inv_sq_tube_le_with_zero (s : Finset Wavevector) (n : Fin 3 → ℝ) (hn : n ≠ 0)
    (N : ℕ) (hN : 0 < N) (hTube : ∀ k ∈ s, InTube n N k) :
    ∑ k ∈ s, 1 / ‖frequencyVec k‖ ^ 2 ≤ 150 * (N : ℝ) := by
  have he : (∑ k ∈ s.filter (fun k ↦ k ≠ 0), 1 / ‖frequencyVec k‖ ^ 2) =
      ∑ k ∈ s, 1 / ‖frequencyVec k‖ ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk hnot
    have hk0 : k = 0 := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨hk, h⟩)
    have hz : frequencyVec (0 : Wavevector) = 0 := by
      ext i
      simp [frequencyVec, coefficientVec, PancakePeriodicComplexStretch.wavevectorCoefficient]
    simp [hk0, hz]
  rw [← he]
  exact sum_inv_sq_tube_le _ n hn N hN
    (fun k hk ↦ (Finset.mem_filter.mp hk).2)
    (fun k hk ↦ hTube k (Finset.mem_filter.mp hk).1)

end Mettapedia.FluidDynamics.NavierStokes.FourierTubeKernel
