import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierAgmon
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Integer points in tubes with arbitrary axes

A tube around any nonzero real axis can be described by two sheared coordinate
windows after choosing the axis's largest coordinate. The slopes then have
absolute value at most one. On each integer slice in that coordinate, the
other two coordinates lie in intervals of bounded length, regardless of their
centres. This gives a uniform lattice count without rotating the integer lattice.

The tube condition below uses coordinate errors. A Euclidean distance bound
implies these coordinate bounds. The count is spatial geometry only; it supplies
no invariance of Fourier support under the Navier–Stokes evolution.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierShearedLatticeCount

open scoped BigOperators
open PeriodicFourierTriad FourierAgmon

/-- An integer window containing every integer within `D` of a real centre. -/
def realWindow (c : ℝ) (D : ℕ) : Finset ℤ :=
  Finset.Icc (⌊c⌋ - D) (⌊c⌋ + D + 1)

theorem card_realWindow (c : ℝ) (D : ℕ) :
    (realWindow c D).card = 2 * D + 2 := by
  rw [realWindow, Int.card_Icc]
  omega

theorem mem_realWindow {c : ℝ} {D : ℕ} {z : ℤ}
    (hz : |(z : ℝ) - c| ≤ D) : z ∈ realWindow c D := by
  rw [realWindow, Finset.mem_Icc]
  obtain ⟨hlo, hhi⟩ := abs_le.mp hz
  constructor
  · have h : (⌊c⌋ : ℝ) - D ≤ z := by linarith [Int.floor_le c]
    exact_mod_cast h
  · have h : (z : ℝ) ≤ ⌊c⌋ + D + 1 := by linarith [Int.lt_floor_add_one c]
    exact_mod_cast h

/-- A slice perpendicular to coordinate `j`, with two sheared windows. -/
def shearedSlice (j : Fin 3) (v : Fin 3 → ℝ) (D : ℕ) (m : ℤ) : Finset Wavevector :=
  Fintype.piFinset fun i ↦ if i = j then {m} else realWindow (v i * m) D

theorem card_shearedSlice (j : Fin 3) (v : Fin 3 → ℝ) (D : ℕ) (m : ℤ) :
    (shearedSlice j v D m).card = (2 * D + 2) ^ 2 := by
  rw [shearedSlice, Fintype.card_piFinset]
  fin_cases j <;> simp [Fin.prod_univ_three, card_realWindow, pow_two]

theorem mem_shearedSlice {j : Fin 3} {v : Fin 3 → ℝ} {D : ℕ} {q : Wavevector}
    (hq : ∀ i, i ≠ j → |(q i : ℝ) - v i * q j| ≤ D) :
    q ∈ shearedSlice j v D (q j) := by
  rw [shearedSlice, Fintype.mem_piFinset]
  intro i
  split_ifs with hi
  · simp [hi]
  · exact mem_realWindow (hq i hi)

/-- All slices whose distinguished integer coordinate lies between `-R` and `R`. -/
def shearedBox (j : Fin 3) (v : Fin 3 → ℝ) (R D : ℕ) : Finset Wavevector :=
  (Finset.Icc (-(R : ℤ)) R).biUnion (shearedSlice j v D)

theorem card_shearedBox_le (j : Fin 3) (v : Fin 3 → ℝ) (R D : ℕ) :
    (shearedBox j v R D).card ≤ (2 * R + 1) * (2 * D + 2) ^ 2 := by
  have hc : (Finset.Icc (-(R : ℤ)) R).card = 2 * R + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ (Finset.Icc (-(R : ℤ)) R).card * (2 * D + 2) ^ 2 :=
      Finset.card_biUnion_le_card_mul _ _ _ fun m _ ↦ (card_shearedSlice j v D m).le
    _ = _ := by rw [hc]

theorem mem_shearedBox {j : Fin 3} {v : Fin 3 → ℝ} {R D : ℕ} {q : Wavevector}
    (hR : (q j).natAbs ≤ R)
    (hq : ∀ i, i ≠ j → |(q i : ℝ) - v i * q j| ≤ D) :
    q ∈ shearedBox j v R D := by
  apply Finset.mem_biUnion.mpr
  refine ⟨q j, ?_, mem_shearedSlice hq⟩
  rw [Finset.mem_Icc]
  have h : |q j| ≤ (R : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hR
  exact abs_le.mp h

theorem card_le_of_shear (s : Finset Wavevector) (j : Fin 3) (v : Fin 3 → ℝ)
    (R D : ℕ) (hR : ∀ q ∈ s, (q j).natAbs ≤ R)
    (hq : ∀ q ∈ s, ∀ i, i ≠ j → |(q i : ℝ) - v i * q j| ≤ D) :
    s.card ≤ (2 * R + 1) * (2 * D + 2) ^ 2 :=
  (Finset.card_le_card fun q hq' ↦ mem_shearedBox (hR q hq') (hq q hq')).trans
    (card_shearedBox_le j v R D)

/-- Two slices suffice when only the absolute value of the distinguished coordinate is fixed. -/
theorem card_abs_slice_le (s : Finset Wavevector) (j : Fin 3) (v : Fin 3 → ℝ)
    (D m : ℕ) (hm : ∀ q ∈ s, (q j).natAbs = m)
    (hq : ∀ q ∈ s, ∀ i, i ≠ j → |(q i : ℝ) - v i * q j| ≤ D) :
    s.card ≤ 2 * (2 * D + 2) ^ 2 := by
  have hsub : s ⊆ shearedSlice j v D (m : ℤ) ∪ shearedSlice j v D (-(m : ℤ)) := by
    intro q hqs
    have hm' : (q j).natAbs = (m : ℤ).natAbs := by simpa using hm q hqs
    have hmem := mem_shearedSlice (hq q hqs)
    rcases Int.natAbs_eq_natAbs_iff.mp hm' with h | h
    · exact Finset.mem_union_left _ (h ▸ hmem)
    · exact Finset.mem_union_right _ (h ▸ hmem)
  calc
    s.card ≤ (shearedSlice j v D (m : ℤ) ∪ shearedSlice j v D (-(m : ℤ))).card :=
      Finset.card_le_card hsub
    _ ≤ (shearedSlice j v D (m : ℤ)).card + (shearedSlice j v D (-(m : ℤ))).card :=
      Finset.card_union_le _ _
    _ = _ := by rw [card_shearedSlice, card_shearedSlice]; omega

/-- A short segment of a tube lies in an ordinary coordinate box. -/
theorem supRadius_le_of_shear {q : Wavevector} {j : Fin 3} {v : Fin 3 → ℝ}
    {R D : ℕ} (hv : ∀ i, |v i| ≤ 1) (hR : (q j).natAbs ≤ R)
    (hq : ∀ i, i ≠ j → |(q i : ℝ) - v i * q j| ≤ D) :
    supRadius q ≤ R + D := by
  rw [supRadius, Finset.sup_le_iff]
  intro i _
  by_cases hij : i = j
  · subst i
    omega
  have hj : |(q j : ℝ)| ≤ R := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    exact_mod_cast hR
  have hi : |(q i : ℝ)| ≤ (R : ℝ) + D := by
    calc
      _ = |((q i : ℝ) - v i * q j) + v i * q j| := by congr 1; ring
      _ ≤ |(q i : ℝ) - v i * q j| + |v i * q j| := abs_add_le _ _
      _ ≤ D + 1 * R := add_le_add (hq i hij)
        (by rw [abs_mul]; exact mul_le_mul (hv i) hj (abs_nonneg _) (by positivity))
      _ = _ := by ring
  rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast] at hi
  exact_mod_cast hi

/-- The coordinate form of a tube of width `W` about a real axis. -/
def InTube (n : Fin 3 → ℝ) (W : ℝ) (q : Wavevector) : Prop :=
  ∃ t : ℝ, ∀ i, |(q i : ℝ) - t * n i| ≤ W

theorem InTube.add {n : Fin 3 → ℝ} {W V : ℝ} {p r : Wavevector}
    (hp : InTube n W p) (hr : InTube n V r) : InTube n (W + V) (p + r) := by
  obtain ⟨t, ht⟩ := hp
  obtain ⟨s, hs⟩ := hr
  refine ⟨t + s, fun i ↦ ?_⟩
  have heq : (((p + r) i : ℤ) : ℝ) - (t + s) * n i =
      ((p i : ℝ) - t * n i) + ((r i : ℝ) - s * n i) := by
    simp only [Pi.add_apply, Int.cast_add]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add (ht i) (hs i))

theorem exists_dominant_coordinate (n : Fin 3 → ℝ) (hn : n ≠ 0) :
    ∃ j : Fin 3, n j ≠ 0 ∧ ∀ i, |n i| ≤ |n j| := by
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i ↦ |n i|)
    Finset.univ_nonempty
  have hdom : ∀ i, |n i| ≤ |n j| := fun i ↦ hj i (Finset.mem_univ i)
  refine ⟨j, ?_, hdom⟩
  intro hz
  apply hn
  funext i
  have hi := hdom i
  rw [hz, abs_zero] at hi
  exact abs_nonpos_iff.mp hi

/-- A dominant axis coordinate turns a tube into uniformly bounded shear windows. -/
theorem tube_shear {n : Fin 3 → ℝ} {j : Fin 3} (hj : n j ≠ 0)
    (hdom : ∀ i, |n i| ≤ |n j|) {W : ℝ} (hW : 0 ≤ W)
    {q : Wavevector} (hq : InTube n W q) (i : Fin 3) :
    |(q i : ℝ) - (n i / n j) * q j| ≤ 2 * W := by
  obtain ⟨t, ht⟩ := hq
  have hv : |n i / n j| ≤ 1 := by
    rw [abs_div, div_le_one (abs_pos.mpr hj)]
    exact hdom i
  have heq : (q i : ℝ) - (n i / n j) * q j =
      ((q i : ℝ) - t * n i) - (n i / n j) * ((q j : ℝ) - t * n j) := by
    field_simp [hj]
    ring
  rw [heq]
  calc
    _ ≤ |(q i : ℝ) - t * n i| + |(n i / n j) * ((q j : ℝ) - t * n j)| :=
      by simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le ((q i : ℝ) - t * n i) (-(n i / n j * ((q j : ℝ) - t * n j)))
    _ = |(q i : ℝ) - t * n i| + |n i / n j| * |(q j : ℝ) - t * n j| := by
      rw [abs_mul]
    _ ≤ W + 1 * W := add_le_add (ht i)
      ((mul_le_mul_of_nonneg_left (ht j) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hv hW))
    _ = 2 * W := by ring

/-- Uniform tube count for every real axis, without any lattice rotation. -/
theorem card_tube_le (s : Finset Wavevector) (n : Fin 3 → ℝ) (hn : n ≠ 0)
    (R N : ℕ) (hR : ∀ q ∈ s, supRadius q ≤ R)
    (hTube : ∀ q ∈ s, InTube n N q) :
    s.card ≤ (2 * R + 1) * (4 * N + 2) ^ 2 := by
  obtain ⟨j, hj, hdom⟩ := exists_dominant_coordinate n hn
  have hs := card_le_of_shear s j (fun i ↦ n i / n j) R (2 * N)
    (fun q hq ↦ (natAbs_le_supRadius q j).trans (hR q hq))
    (fun q hq i _ ↦ by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        tube_shear hj hdom (Nat.cast_nonneg N) (hTube q hq) i)
  convert hs using 1
  ring

end Mettapedia.FluidDynamics.NavierStokes.FourierShearedLatticeCount
