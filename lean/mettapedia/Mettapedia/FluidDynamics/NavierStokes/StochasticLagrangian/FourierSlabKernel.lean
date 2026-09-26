import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierTubeKernel

/-!
# Inverse-radius lattice sums in arbitrary-axis slabs

After choosing a nonzero coordinate of the slab normal, each column parallel
to that coordinate contains a uniformly bounded number of lattice points.
The other two integer coordinates have exactly eight times the radius points
on a square shell. Summing the inverse radius therefore grows linearly in the
outer radius and the slab width. No rotation of the integer lattice is used.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierSlabKernel

open scoped BigOperators
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator PancakeArbitraryDataBlocks
  FourierAgmon FourierShearedLatticeCount FourierTubeKernel FourierShellFeeding
  PancakeInfinitePressureCoefficients

/-- Forget the coordinate parallel to a column. -/
def eraseCoordinate (j : Fin 3) (k : Wavevector) : Wavevector := Function.update k j 0

@[simp] theorem eraseCoordinate_self (j : Fin 3) (k : Wavevector) :
    eraseCoordinate j k j = 0 := by simp [eraseCoordinate]

theorem eraseCoordinate_apply_of_ne {i j : Fin 3} (hij : i ≠ j) (k : Wavevector) :
    eraseCoordinate j k i = k i := by simp [eraseCoordinate, hij]

theorem supRadius_erase_le (j : Fin 3) (k : Wavevector) :
    supRadius (eraseCoordinate j k) ≤ supRadius k := by
  rw [supRadius, Finset.sup_le_iff]
  intro i _
  by_cases hij : i = j
  · subst i
    simp
  · rw [eraseCoordinate_apply_of_ne hij]
    exact natAbs_le_supRadius k i

/-- The two-dimensional coordinate square perpendicular to a column. -/
def transverseBox (j : Fin 3) (R : ℕ) : Finset Wavevector :=
  Fintype.piFinset fun i ↦ if i = j then {0} else Finset.Icc (-(R : ℤ)) R

theorem card_transverseBox (j : Fin 3) (R : ℕ) :
    (transverseBox j R).card = (2 * R + 1) ^ 2 := by
  have hc : (Finset.Icc (-(R : ℤ)) R).card = 2 * R + 1 := by
    rw [Int.card_Icc]
    omega
  rw [transverseBox, Fintype.card_piFinset]
  fin_cases j <;> simp [Fin.prod_univ_three, hc, pow_two]

theorem mem_transverseBox (j : Fin 3) (R : ℕ) (k : Wavevector) :
    k ∈ transverseBox j R ↔ k j = 0 ∧ supRadius k ≤ R := by
  rw [transverseBox, Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨by simpa using h j, ?_⟩
    rw [supRadius, Finset.sup_le_iff]
    intro i _
    by_cases hij : i = j
    · subst i
      have hz : k j = 0 := by simpa using h j
      simp [hz]
    · have hi : -(R : ℤ) ≤ k i ∧ k i ≤ R := by simpa [hij] using h i
      have hi' : |k i| ≤ (R : ℤ) := abs_le.mpr hi
      rw [Int.abs_eq_natAbs] at hi'
      exact_mod_cast hi'
  · rintro ⟨hj, hR⟩ i
    split_ifs with hij
    · simpa [hij] using hj
    · have hi : |k i| ≤ (R : ℤ) := by
        rw [Int.abs_eq_natAbs]
        exact_mod_cast (natAbs_le_supRadius k i).trans hR
      exact Finset.mem_Icc.mpr (abs_le.mp hi)

/-- A positive transverse square shell has exactly `8 * radius` columns. -/
theorem card_transverseShell (j : Fin 3) (m : ℕ) :
    (transverseBox j (m + 1) \ transverseBox j m).card = 8 * (m + 1) := by
  have hsub : transverseBox j m ⊆ transverseBox j (m + 1) := by
    intro k hk
    rw [mem_transverseBox] at hk ⊢
    exact ⟨hk.1, by omega⟩
  have he : (2 * (m + 1) + 1) ^ 2 = (2 * m + 1) ^ 2 + 8 * (m + 1) := by ring
  rw [Finset.card_sdiff_of_subset hsub, card_transverseBox, card_transverseBox,
    he, Nat.add_sub_cancel_left]

/-- A column whose centre may depend arbitrarily on the other two coordinates. -/
def slabColumn (j : Fin 3) (c : Wavevector → ℝ) (D : ℕ) (v : Wavevector) :
    Finset Wavevector :=
  Fintype.piFinset fun i ↦ if i = j then realWindow (c v) D else {v i}

theorem card_slabColumn (j : Fin 3) (c : Wavevector → ℝ) (D : ℕ) (v : Wavevector) :
    (slabColumn j c D v).card = 2 * D + 2 := by
  rw [slabColumn, Fintype.card_piFinset]
  fin_cases j <;> simp [Fin.prod_univ_three, card_realWindow]

theorem mem_slabColumn {j : Fin 3} {c : Wavevector → ℝ} {D : ℕ} {k : Wavevector}
    (hk : |(k j : ℝ) - c (eraseCoordinate j k)| ≤ D) :
    k ∈ slabColumn j c D (eraseCoordinate j k) := by
  rw [slabColumn, Fintype.mem_piFinset]
  intro i
  split_ifs with hij
  · subst i
    exact mem_realWindow hk
  · simp [eraseCoordinate_apply_of_ne hij]

theorem card_positive_slice_le (s : Finset Wavevector) (j : Fin 3)
    (c : Wavevector → ℝ) (D m : ℕ)
    (hm : ∀ k ∈ s, supRadius (eraseCoordinate j k) = m + 1)
    (hcol : ∀ k ∈ s, |(k j : ℝ) - c (eraseCoordinate j k)| ≤ D) :
    s.card ≤ 8 * (m + 1) * (2 * D + 2) := by
  have hsub : s ⊆ (transverseBox j (m + 1) \ transverseBox j m).biUnion
      (slabColumn j c D) := by
    intro k hk
    apply Finset.mem_biUnion.mpr
    refine ⟨eraseCoordinate j k, ?_, mem_slabColumn (hcol k hk)⟩
    rw [Finset.mem_sdiff, mem_transverseBox, mem_transverseBox]
    simp [hm k hk]
  calc
    s.card ≤ _ := Finset.card_le_card hsub
    _ ≤ (transverseBox j (m + 1) \ transverseBox j m).card * (2 * D + 2) :=
      Finset.card_biUnion_le_card_mul _ _ _ fun v _ ↦ (card_slabColumn j c D v).le
    _ = _ := by rw [card_transverseShell]

theorem card_zero_slice_le (s : Finset Wavevector) (j : Fin 3)
    (c : Wavevector → ℝ) (D : ℕ)
    (hm : ∀ k ∈ s, supRadius (eraseCoordinate j k) = 0)
    (hcol : ∀ k ∈ s, |(k j : ℝ) - c (eraseCoordinate j k)| ≤ D) :
    s.card ≤ 2 * D + 2 := by
  have hsub : s ⊆ slabColumn j c D 0 := by
    intro k hk
    have hz : eraseCoordinate j k = 0 := by
      by_contra h
      have := supRadius_pos h
      rw [hm k hk] at this
      omega
    simpa only [hz] using mem_slabColumn (hcol k hk)
  exact (Finset.card_le_card hsub).trans_eq (card_slabColumn j c D 0)

/-- Every positive transverse shell contributes at most a constant times the column width. -/
theorem sum_inv_radius_positive_columns_le (s : Finset Wavevector) (j : Fin 3)
    (c : Wavevector → ℝ) (D R : ℕ)
    (hpos : ∀ k ∈ s, 0 < supRadius (eraseCoordinate j k))
    (hR : ∀ k ∈ s, supRadius (eraseCoordinate j k) ≤ R)
    (hcol : ∀ k ∈ s, |(k j : ℝ) - c (eraseCoordinate j k)| ≤ D) :
    ∑ k ∈ s, 1 / ‖frequencyVec k‖ ≤ 8 * (2 * (D : ℝ) + 2) * R := by
  have hmaps : ∀ k ∈ s, supRadius (eraseCoordinate j k) - 1 ∈ Finset.range R := by
    intro k hk
    have := hpos k hk
    have := hR k hk
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ m ∈ Finset.range R,
      (∑ k ∈ s with supRadius (eraseCoordinate j k) - 1 = m,
        1 / ‖frequencyVec k‖) ≤ 8 * (2 * (D : ℝ) + 2) := by
    intro m _
    have hm0 : 0 < (m : ℝ) + 1 := by positivity
    have hrad : ∀ k ∈ s.filter (fun k ↦ supRadius (eraseCoordinate j k) - 1 = m),
        supRadius (eraseCoordinate j k) = m + 1 := by
      intro k hk
      obtain ⟨hk, he⟩ := Finset.mem_filter.mp hk
      have := hpos k hk
      omega
    have hc : ((s.filter fun k ↦ supRadius (eraseCoordinate j k) - 1 = m).card : ℝ) ≤
        8 * ((m : ℝ) + 1) * (2 * D + 2) := by
      have h := card_positive_slice_le _ j c D m hrad
        (fun k hk ↦ hcol k (Finset.mem_filter.mp hk).1)
      exact_mod_cast h
    calc
      _ ≤ ∑ k ∈ s.filter (fun k ↦ supRadius (eraseCoordinate j k) - 1 = m),
          1 / ((m : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        apply one_div_le_one_div_of_le hm0
        have h : (supRadius (eraseCoordinate j k) : ℝ) ≤ ‖frequencyVec k‖ :=
          (Nat.cast_le.mpr (supRadius_erase_le j k)).trans (supRadius_le_norm k)
        simpa only [hrad k hk, Nat.cast_add, Nat.cast_one] using h
      _ = ((s.filter fun k ↦ supRadius (eraseCoordinate j k) - 1 = m).card : ℝ) /
          ((m : ℝ) + 1) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ 8 * (2 * D + 2) := (div_le_iff₀ hm0).mpr (by nlinarith [hc])
  calc
    _ ≤ ∑ _m ∈ Finset.range R, 8 * (2 * (D : ℝ) + 2) := Finset.sum_le_sum hfiber
    _ = _ := by simp; ring

/-- A width bound in each column gives a linear inverse-radius sum. -/
theorem sum_inv_radius_columns_le (s : Finset Wavevector) (j : Fin 3)
    (c : Wavevector → ℝ) (D R : ℕ) (hs0 : ∀ k ∈ s, k ≠ 0)
    (hR : ∀ k ∈ s, supRadius (eraseCoordinate j k) ≤ R)
    (hcol : ∀ k ∈ s, |(k j : ℝ) - c (eraseCoordinate j k)| ≤ D) :
    ∑ k ∈ s, 1 / ‖frequencyVec k‖ ≤ (2 * (D : ℝ) + 2) * (8 * R + 1) := by
  have hzero : (∑ k ∈ s with supRadius (eraseCoordinate j k) = 0,
      1 / ‖frequencyVec k‖) ≤ 2 * (D : ℝ) + 2 := by
    have hc : ((s.filter fun k ↦ supRadius (eraseCoordinate j k) = 0).card : ℝ) ≤
        2 * (D : ℝ) + 2 := by
      exact_mod_cast card_zero_slice_le _ j c D
        (fun k hk ↦ (Finset.mem_filter.mp hk).2)
        (fun k hk ↦ hcol k (Finset.mem_filter.mp hk).1)
    calc
      _ ≤ ∑ _k ∈ s.filter (fun k ↦ supRadius (eraseCoordinate j k) = 0), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
          (one_le_norm_frequencyVec (hs0 k (Finset.mem_filter.mp hk).1))
        simpa using h
      _ = ((s.filter fun k ↦ supRadius (eraseCoordinate j k) = 0).card : ℝ) := by simp
      _ ≤ _ := hc
  have hpos := sum_inv_radius_positive_columns_le
    (s.filter fun k ↦ ¬supRadius (eraseCoordinate j k) = 0) j c D R
    (fun k hk ↦ Nat.pos_of_ne_zero (Finset.mem_filter.mp hk).2)
    (fun k hk ↦ hR k (Finset.mem_filter.mp hk).1)
    (fun k hk ↦ hcol k (Finset.mem_filter.mp hk).1)
  rw [← Finset.sum_filter_add_sum_filter_not s (fun k ↦ supRadius (eraseCoordinate j k) = 0)]
  nlinarith

/-- A slab with real normal, expressed without changing lattice coordinates. -/
def InSlab (n : Fin 3 → ℝ) (W : ℝ) (k : Wavevector) : Prop :=
  |∑ i : Fin 3, (k i : ℝ) * n i| ≤ W

theorem InSlab.add {n : Fin 3 → ℝ} {W V : ℝ} {p r : Wavevector}
    (hp : InSlab n W p) (hr : InSlab n V r) : InSlab n (W + V) (p + r) := by
  unfold InSlab at hp hr ⊢
  simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans (add_le_add hp hr)

theorem dot_eraseCoordinate (j : Fin 3) (k : Wavevector) (n : Fin 3 → ℝ) :
    (k j : ℝ) * n j + (∑ i : Fin 3, (eraseCoordinate j k i : ℝ) * n i) =
      ∑ i : Fin 3, (k i : ℝ) * n i := by
  fin_cases j <;> simp [eraseCoordinate, Fin.sum_univ_three] <;> ring

/-- A unit real normal has a coordinate of absolute value at least one half. -/
theorem exists_large_coordinate (n : Fin 3 → ℝ) (hn : ∑ i : Fin 3, (n i) ^ 2 = 1) :
    ∃ j : Fin 3, (1 / 2 : ℝ) ≤ |n j| := by
  by_contra h
  push Not at h
  have hs : ∀ i : Fin 3, (n i) ^ 2 < (1 / 2 : ℝ) ^ 2 := fun i ↦ by
    nlinarith [h i, abs_nonneg (n i), sq_abs (n i)]
  simp only [Fin.sum_univ_three] at hn
  nlinarith [hs 0, hs 1, hs 2]

/-- The slab equation bounds the length of each dominant-coordinate column. -/
theorem slab_column_bound {n : Fin 3 → ℝ} {j : Fin 3}
    (hj : (1 / 2 : ℝ) ≤ |n j|) {W : ℝ} {k : Wavevector} (hk : InSlab n W k) :
    |(k j : ℝ) - (-(∑ i : Fin 3, (eraseCoordinate j k i : ℝ) * n i) / n j)| ≤
      2 * W := by
  have hj0 : n j ≠ 0 := by intro hz; rw [hz, abs_zero] at hj; norm_num at hj
  have he : ((k j : ℝ) - (-(∑ i : Fin 3, (eraseCoordinate j k i : ℝ) * n i) / n j)) *
      n j = ∑ i : Fin 3, (k i : ℝ) * n i := by
    rw [sub_mul, div_mul_cancel₀ _ hj0, sub_neg_eq_add, dot_eraseCoordinate]
  have hm : |(k j : ℝ) - (-(∑ i : Fin 3, (eraseCoordinate j k i : ℝ) * n i) / n j)| *
      |n j| ≤ W := by
    rw [← abs_mul, he]
    exact hk
  have hh := mul_le_mul_of_nonneg_left hj
    (abs_nonneg ((k j : ℝ) - (-(∑ i : Fin 3, (eraseCoordinate j k i : ℝ) * n i) / n j)))
  nlinarith

/-- The inverse-radius sum in a slab grows as width times outer radius, uniformly in its axis. -/
theorem sum_inv_radius_slab_le (s : Finset Wavevector) (n : Fin 3 → ℝ)
    (hn : ∑ i : Fin 3, (n i) ^ 2 = 1) (N R : ℕ) (hN : 0 < N) (hR : 0 < R)
    (hs0 : ∀ k ∈ s, k ≠ 0) (hrad : ∀ k ∈ s, supRadius k ≤ R)
    (hslab : ∀ k ∈ s, InSlab n N k) :
    ∑ k ∈ s, 1 / ‖frequencyVec k‖ ≤ 54 * (N : ℝ) * R := by
  obtain ⟨j, hj⟩ := exists_large_coordinate n hn
  have hc := sum_inv_radius_columns_le s j
    (fun v ↦ -(∑ i : Fin 3, (v i : ℝ) * n i) / n j) (2 * N) R hs0
    (fun k hk ↦ (supRadius_erase_le j k).trans (hrad k hk))
    (fun k hk ↦ by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using slab_column_bound hj (hslab k hk))
  refine hc.trans ?_
  push_cast
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hm : (4 * (N : ℝ) + 2) * (8 * R + 1) ≤ (6 * N) * (9 * R) := by
    gcongr <;> linarith
  nlinarith

/-- Including the zero lattice point changes nothing, since its inverse-radius weight is zero. -/
theorem sum_inv_radius_slab_le_with_zero (s : Finset Wavevector) (n : Fin 3 → ℝ)
    (hn : ∑ i : Fin 3, (n i) ^ 2 = 1) (N R : ℕ) (hN : 0 < N) (hR : 0 < R)
    (hrad : ∀ k ∈ s, supRadius k ≤ R) (hslab : ∀ k ∈ s, InSlab n N k) :
    ∑ k ∈ s, 1 / ‖frequencyVec k‖ ≤ 54 * (N : ℝ) * R := by
  have he : (∑ k ∈ s.filter (fun k ↦ k ≠ 0), 1 / ‖frequencyVec k‖) =
      ∑ k ∈ s, 1 / ‖frequencyVec k‖ := by
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
  exact sum_inv_radius_slab_le _ n hn N R hN hR
    (fun k hk ↦ (Finset.mem_filter.mp hk).2)
    (fun k hk ↦ hrad k (Finset.mem_filter.mp hk).1)
    (fun k hk ↦ hslab k (Finset.mem_filter.mp hk).1)

end Mettapedia.FluidDynamics.NavierStokes.FourierSlabKernel
