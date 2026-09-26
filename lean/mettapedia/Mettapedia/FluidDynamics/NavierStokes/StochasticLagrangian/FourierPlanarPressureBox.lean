import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPlanarPressureSign

/-!
# Explicit boxes for coherent axial pressure production

Two narrow boxes near the first two coordinate axes and their negatives
give real transverse data in a critical Fourier belt. A box of sum
frequencies has many parents with a uniformly large planar area.
The construction concerns the initial unforced vector field.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPlanarPressureBox

open scoped BigOperators
open PeriodicFourierTriad PancakeFrequencyProjectorCommutator
  PancakeViscousMisalignmentAbsorption FourierBeltKernel FourierPlanarPressureSign
  FourierAxialLeraySource PancakeLowPressureBudget PancakeCoefficientLimitEquation
  FourierSingleConeStretch

def integerBox (a : Wavevector) (length : Fin 3 → ℕ) : Finset Wavevector :=
  Fintype.piFinset fun i ↦ Finset.Icc (a i) (a i + length i)

theorem mem_integerBox (a : Wavevector) (length : Fin 3 → ℕ) (k : Wavevector) :
    k ∈ integerBox a length ↔ ∀ i, a i ≤ k i ∧ k i ≤ a i + length i := by
  simp only [integerBox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem card_integerBox (a : Wavevector) (length : Fin 3 → ℕ) :
    (integerBox a length).card = ∏ i : Fin 3, (length i + 1) := by
  rw [integerBox, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Int.card_Icc]
  omega

def scale (m : ℕ) : ℕ := 10000 * m ^ 2
def width (m : ℕ) : ℕ := 100 * m ^ 2
def beltScale (m : ℕ) : ℕ := 100 * m

def swap (k : Wavevector) : Wavevector := ![k 1, k 0, k 2]

theorem swap_involutive : Function.Involutive swap := by
  intro k
  ext i
  fin_cases i <;> rfl

theorem swap_injective : Function.Injective swap := swap_involutive.injective

def firstBox (m : ℕ) : Finset Wavevector :=
  integerBox ![(scale m : ℤ), -2 * (width m : ℤ), (m : ℤ)]
    ![4 * width m, 4 * width m, 4 * m]

def secondBox (m : ℕ) : Finset Wavevector := (firstBox m).image swap

def support (m : ℕ) : Finset Wavevector :=
  (firstBox m ∪ secondBox m) ∪ (firstBox m ∪ secondBox m).image Neg.neg

def parentBox (m : ℕ) : Finset Wavevector :=
  integerBox ![(scale m : ℤ), 0, (m : ℤ)] ![width m, width m, m]

def outputBox (m : ℕ) : Finset Wavevector :=
  integerBox ![(scale m : ℤ) + width m, (scale m : ℤ) + width m, 4 * (m : ℤ)]
    ![width m, width m, m]

theorem mem_firstBox (m : ℕ) (k : Wavevector) :
    k ∈ firstBox m ↔
      (scale m : ℤ) ≤ k 0 ∧ k 0 ≤ (scale m : ℤ) + 4 * width m ∧
      -2 * (width m : ℤ) ≤ k 1 ∧ k 1 ≤ 2 * width m ∧
      (m : ℤ) ≤ k 2 ∧ k 2 ≤ 5 * m := by
  simp [firstBox, mem_integerBox, Fin.forall_fin_succ]
  omega

theorem mem_parentBox (m : ℕ) (k : Wavevector) :
    k ∈ parentBox m ↔
      (scale m : ℤ) ≤ k 0 ∧ k 0 ≤ (scale m : ℤ) + width m ∧
      0 ≤ k 1 ∧ k 1 ≤ width m ∧ (m : ℤ) ≤ k 2 ∧ k 2 ≤ 2 * m := by
  simp [parentBox, mem_integerBox, Fin.forall_fin_succ]
  omega

theorem mem_outputBox (m : ℕ) (k : Wavevector) :
    k ∈ outputBox m ↔
      (scale m : ℤ) + width m ≤ k 0 ∧ k 0 ≤ (scale m : ℤ) + 2 * width m ∧
      (scale m : ℤ) + width m ≤ k 1 ∧ k 1 ≤ (scale m : ℤ) + 2 * width m ∧
      4 * (m : ℤ) ≤ k 2 ∧ k 2 ≤ 5 * m := by
  simp [outputBox, mem_integerBox, Fin.forall_fin_succ]
  omega

theorem mem_secondBox (m : ℕ) (k : Wavevector) :
    k ∈ secondBox m ↔ swap k ∈ firstBox m := by
  constructor
  · intro hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    simpa only [swap_involutive p] using hp
  · intro hk
    exact Finset.mem_image.mpr ⟨swap k, hk, swap_involutive k⟩

theorem mem_neg_image (s : Finset Wavevector) (k : Wavevector) :
    k ∈ s.image Neg.neg ↔ -k ∈ s := by
  constructor
  · rintro hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    simpa only [neg_neg] using hp
  · intro hk
    exact Finset.mem_image.mpr ⟨-k, hk, neg_neg k⟩

theorem support_neg (m : ℕ) (k : Wavevector) : -k ∈ support m ↔ k ∈ support m := by
  simp only [support, Finset.mem_union, mem_neg_image, neg_neg, or_comm]

theorem card_firstBox (m : ℕ) :
    (firstBox m).card = (4 * width m + 1) ^ 2 * (4 * m + 1) := by
  simp [firstBox, card_integerBox, Fin.prod_univ_three, pow_two]

theorem card_secondBox (m : ℕ) : (secondBox m).card = (firstBox m).card :=
  Finset.card_image_of_injective _ swap_injective

theorem card_parentBox (m : ℕ) : (parentBox m).card = (width m + 1) ^ 2 * (m + 1) := by
  simp [parentBox, card_integerBox, Fin.prod_univ_three, pow_two]

theorem card_outputBox (m : ℕ) : (outputBox m).card = (width m + 1) ^ 2 * (m + 1) := by
  simp [outputBox, card_integerBox, Fin.prod_univ_three, pow_two]

theorem card_support_le (m : ℕ) :
    (support m).card ≤ 4 * ((4 * width m + 1) ^ 2 * (4 * m + 1)) := by
  have hbase := Finset.card_union_le (firstBox m) (secondBox m)
  have hneg := Finset.card_image_le (s := firstBox m ∪ secondBox m) (f := Neg.neg)
  have hall := Finset.card_union_le (firstBox m ∪ secondBox m)
    ((firstBox m ∪ secondBox m).image Neg.neg)
  rw [card_secondBox, card_firstBox] at hbase
  change (support m).card ≤ _ at hall
  omega

theorem parent_mem_first (m : ℕ) (p : Wavevector) (hp : p ∈ parentBox m) :
    p ∈ firstBox m := by
  rw [mem_parentBox] at hp
  rw [mem_firstBox]
  omega

theorem receiver_mem_second (m : ℕ) (p q : Wavevector)
    (hp : p ∈ parentBox m) (hq : q ∈ outputBox m) : q - p ∈ secondBox m := by
  rw [mem_parentBox] at hp
  rw [mem_outputBox] at hq
  rw [mem_secondBox, mem_firstBox]
  simp [swap]
  omega

theorem scale_eq_hundred_width (m : ℕ) : scale m = 100 * width m := by
  simp [scale, width]
  ring

theorem scale_eq_beltScale_sq (m : ℕ) : scale m = beltScale m ^ 2 := by
  simp [scale, beltScale]
  ring

theorem scale_pos (m : ℕ) (hm : 0 < m) : 0 < scale m := by unfold scale; positivity

theorem width_pos (m : ℕ) (hm : 0 < m) : 0 < width m := by unfold width; positivity

theorem m_le_width (m : ℕ) : m ≤ width m := by
  unfold width
  nlinarith [Nat.zero_le m]

theorem inBelt_axis_iff (N : ℕ) (k : Wavevector) :
    InBeltShell N axis k ↔ (N : ℝ) ^ 2 ≤ ‖frequencyVec k‖ ∧
      ‖frequencyVec k‖ ≤ 2 * (N : ℝ) ^ 2 ∧ |(k 2 : ℝ)| ≤ ‖frequencyVec k‖ / N := by
  simp [InBeltShell, FourierSlabKernel.InSlab, axis, Fin.sum_univ_three]

/-- A common coordinate envelope contains the input and output boxes inside the critical belt. -/
theorem inBelt_of_coordinate_bounds (m : ℕ) (hm : 0 < m) (k : Wavevector)
    (hxlo : (scale m : ℝ) ≤ k 0)
    (hxhi : (k 0 : ℝ) ≤ scale m + 4 * (width m : ℝ))
    (hy : |(k 1 : ℝ)| ≤ scale m + 4 * (width m : ℝ))
    (hz : |(k 2 : ℝ)| ≤ 5 * (m : ℝ)) : InBeltShell (beltScale m) axis k := by
  have hL : (0 : ℝ) < scale m := by exact_mod_cast scale_pos m hm
  have hN : (0 : ℝ) < beltScale m := by unfold beltScale; positivity
  have hw : (0 : ℝ) ≤ width m := by positivity
  have hmw : (m : ℝ) ≤ width m := by exact_mod_cast m_le_width m
  have hLw : (scale m : ℝ) = 100 * (width m : ℝ) := by
    exact_mod_cast scale_eq_hundred_width m
  have hNL : (beltScale m : ℝ) ^ 2 = scale m := by
    exact_mod_cast (scale_eq_beltScale_sq m).symm
  have hx0 : (0 : ℝ) ≤ k 0 := hL.le.trans hxlo
  have hx2 := pow_le_pow_left₀ hx0 hxhi 2
  have hy2 := pow_le_pow_left₀ (abs_nonneg (k 1 : ℝ)) hy 2
  have hz2 := pow_le_pow_left₀ (abs_nonneg (k 2 : ℝ))
    (hz.trans (mul_le_mul_of_nonneg_left hmw (by norm_num : (0 : ℝ) ≤ 5))) 2
  rw [sq_abs] at hy2 hz2
  have hs := norm_frequencyVec_sq k
  simp only [Fin.sum_univ_three] at hs
  have hlower : (scale m : ℝ) ≤ ‖frequencyVec k‖ := by
    nlinarith only [hs, hxlo, hx0, hL, norm_nonneg (frequencyVec k),
      sq_nonneg (k 1 : ℝ), sq_nonneg (k 2 : ℝ)]
  have hupper : ‖frequencyVec k‖ ≤ 2 * (scale m : ℝ) := by
    nlinarith only [hs, hx2, hy2, hz2, hLw, hL, hw, norm_nonneg (frequencyVec k)]
  rw [inBelt_axis_iff, hNL]
  refine ⟨hlower, hupper, ?_⟩
  rw [le_div_iff₀ hN]
  calc
    _ ≤ (5 * (m : ℝ)) * beltScale m := mul_le_mul_of_nonneg_right hz hN.le
    _ ≤ (scale m : ℝ) := by simp [beltScale, scale]; nlinarith [sq_nonneg (m : ℝ)]
    _ ≤ _ := hlower

theorem firstBox_inBelt (m : ℕ) (hm : 0 < m) (k : Wavevector) (hk : k ∈ firstBox m) :
    InBeltShell (beltScale m) axis k := by
  obtain ⟨hxlo, hxhi, hylo, hyhi, hzlo, hzhi⟩ := (mem_firstBox m k).mp hk
  apply inBelt_of_coordinate_bounds m hm k
  · exact_mod_cast hxlo
  · exact_mod_cast hxhi
  · exact_mod_cast (abs_le.mpr ⟨by omega, by omega⟩ :
      |k 1| ≤ (scale m : ℤ) + 4 * width m)
  · exact_mod_cast (abs_le.mpr ⟨by omega, hzhi⟩ : |k 2| ≤ 5 * (m : ℤ))

theorem outputBox_inBelt (m : ℕ) (hm : 0 < m) (k : Wavevector) (hk : k ∈ outputBox m) :
    InBeltShell (beltScale m) axis k := by
  obtain ⟨hxlo, hxhi, hylo, hyhi, hzlo, hzhi⟩ := (mem_outputBox m k).mp hk
  apply inBelt_of_coordinate_bounds m hm k
  · exact_mod_cast (show (scale m : ℤ) ≤ k 0 by omega)
  · exact_mod_cast (show k 0 ≤ (scale m : ℤ) + 4 * width m by omega)
  · exact_mod_cast (abs_le.mpr ⟨by omega, by omega⟩ :
      |k 1| ≤ (scale m : ℤ) + 4 * width m)
  · exact_mod_cast (abs_le.mpr ⟨by omega, hzhi⟩ : |k 2| ≤ 5 * (m : ℤ))

theorem inBelt_swap_iff (N : ℕ) (k : Wavevector) :
    InBeltShell N axis (swap k) ↔ InBeltShell N axis k := by
  have hn : ‖frequencyVec (swap k)‖ = ‖frequencyVec k‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [norm_frequencyVec_sq, swap, Fin.sum_univ_three]
    ring
  simp only [inBelt_axis_iff, hn, show swap k 2 = k 2 from rfl]

theorem inBelt_neg_iff (N : ℕ) (k : Wavevector) :
    InBeltShell N axis (-k) ↔ InBeltShell N axis k := by
  have hn : ‖frequencyVec (-k)‖ = ‖frequencyVec k‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [norm_frequencyVec_sq]
  simp [inBelt_axis_iff, hn]

theorem secondBox_inBelt (m : ℕ) (hm : 0 < m) (k : Wavevector) (hk : k ∈ secondBox m) :
    InBeltShell (beltScale m) axis k :=
  (inBelt_swap_iff _ _).mp (firstBox_inBelt m hm _ ((mem_secondBox m k).mp hk))

theorem support_inBelt (m : ℕ) (hm : 0 < m) (k : Wavevector) (hk : k ∈ support m) :
    InBeltShell (beltScale m) axis k := by
  simp only [support, Finset.mem_union, mem_neg_image] at hk
  rcases hk with (h | h) | (h | h)
  · exact firstBox_inBelt m hm k h
  · exact secondBox_inBelt m hm k h
  · exact (inBelt_neg_iff _ _).mp (firstBox_inBelt m hm (-k) h)
  · exact (inBelt_neg_iff _ _).mp (secondBox_inBelt m hm (-k) h)

theorem support_frequency_ne_zero (m : ℕ) (hm : 0 < m) (k : Wavevector)
    (hk : k ∈ support m) : frequencyVec k ≠ 0 := by
  intro hz
  have h := (support_inBelt m hm k hk).1
  rw [hz, norm_zero] at h
  have hN : (0 : ℝ) < beltScale m := by unfold beltScale; positivity
  nlinarith

theorem card_support_le_coarse (m : ℕ) (hm : 0 < m) :
    (support m).card ≤ 500 * width m ^ 2 * m := by
  have hw := width_pos m hm
  calc
    _ ≤ 4 * ((4 * width m + 1) ^ 2 * (4 * m + 1)) := card_support_le m
    _ ≤ 4 * ((5 * width m) ^ 2 * (5 * m)) := by gcongr <;> omega
    _ = _ := by ring

/-- The belt radius supplies a uniform coefficient-energy bound for the constructed datum. -/
theorem mode_energy_le_four (m : ℕ) (hm : 0 < m) (k : Wavevector) (hk : k ∈ support m) :
    ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2) / (scale m : ℝ) ^ 2 ≤ 4 := by
  have hL : (0 : ℝ) < scale m := by exact_mod_cast scale_pos m hm
  have hNL : (beltScale m : ℝ) ^ 2 = scale m := by
    exact_mod_cast (scale_eq_beltScale_sq m).symm
  have hr := (support_inBelt m hm k hk).2.1
  rw [hNL] at hr
  have hr2 := pow_le_pow_left₀ (norm_nonneg (frequencyVec k)) hr 2
  rw [norm_frequencyVec_sq] at hr2
  simp only [Fin.sum_univ_three] at hr2
  apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
  nlinarith only [hr2, sq_nonneg (k 2 : ℝ)]

theorem fullEnergy_le (m : ℕ) (hm : 0 < m) :
    fullEnergy (support m) (velocity (support m) (scale m)) ≤
      2000 * (width m : ℝ) ^ 2 * m := by
  rw [fullEnergy_eq]
  calc
    _ ≤ ∑ _k ∈ support m, (4 : ℝ) :=
      Finset.sum_le_sum fun k hk ↦ mode_energy_le_four m hm k hk
    _ = 4 * ((support m).card : ℝ) := by simp [mul_comm]
    _ ≤ 4 * (500 * (width m : ℝ) ^ 2 * m) := by
      gcongr
      exact_mod_cast card_support_le_coarse m hm
    _ = _ := by ring

theorem parent_card_lower (m : ℕ) : width m ^ 2 * m ≤ (parentBox m).card := by
  rw [card_parentBox]
  gcongr <;> omega

theorem output_card_lower (m : ℕ) : width m ^ 2 * m ≤ (outputBox m).card := by
  rw [card_outputBox]
  gcongr <;> omega

theorem parent_area_lower (m : ℕ) (p q : Wavevector)
    (hp : p ∈ parentBox m) (hq : q ∈ outputBox m) :
    (scale m : ℝ) ^ 2 / 2 ≤ planarArea p q := by
  obtain ⟨hp0lo, hp0hi, hp1lo, hp1hi, hp2lo, hp2hi⟩ := (mem_parentBox m p).mp hp
  obtain ⟨hq0lo, hq0hi, hq1lo, hq1hi, hq2lo, hq2hi⟩ := (mem_outputBox m q).mp hq
  have hp0 : (scale m : ℝ) ≤ p 0 := by exact_mod_cast hp0lo
  have hp1 : (p 1 : ℝ) ≤ width m := by exact_mod_cast hp1hi
  have hq0 : (q 0 : ℝ) ≤ scale m + 2 * (width m : ℝ) := by exact_mod_cast hq0hi
  have hq1 : (scale m : ℝ) + width m ≤ q 1 := by exact_mod_cast hq1lo
  have hp0nonneg : (0 : ℝ) ≤ p 0 := (by positivity : (0 : ℝ) ≤ scale m).trans hp0
  have hq0nonneg : (0 : ℝ) ≤ q 0 := by exact_mod_cast (show 0 ≤ q 0 by omega)
  have hmain := mul_le_mul hp0 hq1 (by positivity : (0 : ℝ) ≤ scale m + width m) hp0nonneg
  have hbad := mul_le_mul hp1 hq0 hq0nonneg (by positivity : (0 : ℝ) ≤ width m)
  have hLw : (scale m : ℝ) = 100 * (width m : ℝ) := by
    exact_mod_cast scale_eq_hundred_width m
  unfold planarArea
  rw [hLw] at hmain hbad ⊢
  nlinarith only [hmain, hbad, sq_nonneg (width m : ℝ)]

theorem parent_area_square_lower (m : ℕ) (hm : 0 < m) (p q : Wavevector)
    (hp : p ∈ parentBox m) (hq : q ∈ outputBox m) :
    (scale m : ℝ) ^ 2 / 4 ≤ planarArea p q ^ 2 / (scale m : ℝ) ^ 2 := by
  have hL : (0 : ℝ) < scale m := by exact_mod_cast scale_pos m hm
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (scale m : ℝ) ^ 2 / 2)
    (parent_area_lower m p q hp hq) 2
  apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
  nlinarith only [h]

def selectedPairs (m : ℕ) (q : Wavevector) : Finset (Wavevector × Wavevector) :=
  (parentBox m).image (fun p ↦ (p, q - p)) ∪
    (parentBox m).image (fun p ↦ (q - p, p))

theorem first_mem_support (m : ℕ) (p : Wavevector) (hp : p ∈ firstBox m) :
    p ∈ support m := Finset.mem_union_left _ (Finset.mem_union_left _ hp)

theorem second_mem_support (m : ℕ) (p : Wavevector) (hp : p ∈ secondBox m) :
    p ∈ support m := Finset.mem_union_left _ (Finset.mem_union_right _ hp)

theorem selectedPairs_subset (m : ℕ) (q : Wavevector) (hq : q ∈ outputBox m) :
    selectedPairs m q ⊆ interactionPairs (support m) q := by
  intro pr hpr
  rcases Finset.mem_union.mp hpr with hpr | hpr
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpr
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨first_mem_support m p (parent_mem_first m p hp),
        second_mem_support m (q - p) (receiver_mem_second m p q hp hq)⟩,
      by change p + (q - p) = q; abel⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpr
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨second_mem_support m (q - p) (receiver_mem_second m p q hp hq),
        first_mem_support m p (parent_mem_first m p hp)⟩,
      by change (q - p) + p = q; abel⟩

theorem selectedPairs_disjoint (m : ℕ) (hm : 0 < m) (q : Wavevector)
    (hq : q ∈ outputBox m) :
    Disjoint ((parentBox m).image (fun p ↦ (p, q - p)))
      ((parentBox m).image (fun p ↦ (q - p, p))) := by
  apply Finset.disjoint_left.mpr
  intro pr hl hr
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hr
  have hx := congrArg (fun z : Wavevector × Wavevector ↦ z.1 0) he
  have hp0 := ((mem_parentBox m p).mp hp).1
  have hr0 := ((mem_parentBox m r).mp hr).1
  have hq0 := ((mem_outputBox m q).mp hq).2.1
  have hLw := scale_eq_hundred_width m
  have hw := width_pos m hm
  change q 0 - r 0 = p 0 at hx
  omega

theorem card_selectedPairs (m : ℕ) (hm : 0 < m) (q : Wavevector)
    (hq : q ∈ outputBox m) : (selectedPairs m q).card = 2 * (parentBox m).card := by
  rw [selectedPairs, Finset.card_union_of_disjoint (selectedPairs_disjoint m hm q hq)]
  rw [Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.fst h),
    Finset.card_image_of_injective _ (fun _ _ h ↦ congrArg Prod.snd h)]
  omega

theorem selectedPairs_area_lower (m : ℕ) (hm : 0 < m) (q : Wavevector)
    (hq : q ∈ outputBox m) (pr : Wavevector × Wavevector) (hpr : pr ∈ selectedPairs m q) :
    (scale m : ℝ) ^ 2 / 4 ≤ planarArea pr.1 q ^ 2 / (scale m : ℝ) ^ 2 := by
  rcases Finset.mem_union.mp hpr with hpr | hpr
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpr
    exact parent_area_square_lower m hm p q hp hq
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpr
    have he : planarArea (q - p) q = -planarArea p q := by
      simpa only [show p + (q - p) = q from by abel] using planarArea_other_parent p (q - p)
    change (scale m : ℝ) ^ 2 / 4 ≤ planarArea (q - p) q ^ 2 / (scale m : ℝ) ^ 2
    rw [he, neg_sq]
    exact parent_area_square_lower m hm p q hp hq

/-- Every output in the selected box has a quantitative axial pressure lower bound. -/
theorem pressure_output_lower (m : ℕ) (hm : 0 < m) (q : Wavevector)
    (hq : q ∈ outputBox m) :
    (m : ℝ) ^ 2 * (width m : ℝ) ^ 2 / (2 * scale m) ≤
      ‖axialPressureSource axis (support m) (velocity (support m) (scale m)) q‖ /
        ‖frequencyVec q‖ := by
  have hL : (0 : ℝ) < scale m := by exact_mod_cast scale_pos m hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hqw := (mem_outputBox m q).mp hq
  have hq2 : 4 * (m : ℝ) ≤ q 2 := by exact_mod_cast hqw.2.2.2.2.1
  have hq2pos : (0 : ℝ) ≤ q 2 := by linarith
  have hq2int : 0 ≤ q 2 := by exact_mod_cast hq2pos
  have hNL : (beltScale m : ℝ) ^ 2 = scale m := by
    exact_mod_cast (scale_eq_beltScale_sq m).symm
  have hqB := outputBox_inBelt m hm q hq
  have hqlo := hqB.1
  have hqhi := hqB.2.1
  rw [hNL] at hqlo hqhi
  have hqnorm : 0 < ‖frequencyVec q‖ := hL.trans_le hqlo
  have hcard : (width m : ℝ) ^ 2 * m ≤ (parentBox m).card := by
    exact_mod_cast parent_card_lower m
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h := axialPressureSource_lower (support m) (scale m) q hq2int
    (selectedPairs m q) (selectedPairs_subset m q hq) ((scale m : ℝ) ^ 2 / 4)
    (selectedPairs_area_lower m hm q hq)
  rw [card_selectedPairs m hm q hq] at h
  push_cast at h
  calc
    _ = ((2 * 1 * (4 * (m : ℝ)) / (2 * scale m) ^ 2) *
        ((2 * ((width m : ℝ) ^ 2 * m)) * ((scale m : ℝ) ^ 2 / 4))) / (2 * scale m) := by
      field_simp
    _ ≤ ((2 * Real.pi * (q 2 : ℝ) / ‖frequencyVec q‖ ^ 2) *
        ((2 * ((parentBox m).card : ℝ)) * ((scale m : ℝ) ^ 2 / 4))) / ‖frequencyVec q‖ := by
      gcongr
    _ ≤ _ := div_le_div_of_nonneg_right h hqnorm.le

/-- Squared inverse-frequency weighted axial component of the actual unforced vector field. -/
def axialDerivativeEnergy (m : ℕ) (ν L : ℝ) : ℝ :=
  ∑ q ∈ outputBox m,
    (‖coefficientDot (infiniteVelocityRHS ν (velocity (support m) L) q)
      (axisCoefficient axis)‖ / ‖frequencyVec q‖) ^ 2

theorem axialDerivativeEnergy_eq (m : ℕ) (hm : 0 < m) (ν L : ℝ) :
    axialDerivativeEnergy m ν L =
      ∑ q ∈ outputBox m,
        (‖axialPressureSource axis (support m) (velocity (support m) L) q‖ /
          ‖frequencyVec q‖) ^ 2 := by
  unfold axialDerivativeEnergy
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [infinite_rhs_axial (support m) L ν q (support_frequency_ne_zero m hm)]

theorem axialDerivativeEnergy_lower (m : ℕ) (hm : 0 < m) (ν : ℝ) :
    (m : ℝ) ^ 5 * (width m : ℝ) ^ 6 / (4 * (scale m : ℝ) ^ 2) ≤
      axialDerivativeEnergy m ν (scale m) := by
  have hL : (0 : ℝ) < scale m := by exact_mod_cast scale_pos m hm
  have hc : (width m : ℝ) ^ 2 * m ≤ (outputBox m).card := by
    exact_mod_cast output_card_lower m
  rw [axialDerivativeEnergy_eq m hm]
  calc
    _ = ((width m : ℝ) ^ 2 * m) *
        ((m : ℝ) ^ 2 * (width m : ℝ) ^ 2 / (2 * scale m)) ^ 2 := by
      field_simp
      ring
    _ ≤ ((outputBox m).card : ℝ) *
        ((m : ℝ) ^ 2 * (width m : ℝ) ^ 2 / (2 * scale m)) ^ 2 := by gcongr
    _ = ∑ _q ∈ outputBox m,
        ((m : ℝ) ^ 2 * (width m : ℝ) ^ 2 / (2 * scale m)) ^ 2 := by simp
    _ ≤ _ := Finset.sum_le_sum fun q hq ↦
      pow_le_pow_left₀ (by positivity) (pressure_output_lower m hm q hq) 2

/-- The kinetic energy is nonzero, with an explicit unit contribution. -/
theorem fullEnergy_ge_one (m : ℕ) (hm : 0 < m) :
    1 ≤ fullEnergy (support m) (velocity (support m) (scale m)) := by
  have hL : (scale m : ℝ) ≠ 0 := by exact_mod_cast (scale_pos m hm).ne'
  have hp : ![(scale m : ℤ), 0, (m : ℤ)] ∈ parentBox m := by
    simp [mem_parentBox]
    omega
  have hP := first_mem_support m _ (parent_mem_first m _ hp)
  rw [fullEnergy_eq]
  calc
    1 = (((![(scale m : ℤ), 0, (m : ℤ)]) 0 : ℝ) ^ 2 +
        (((![(scale m : ℤ), 0, (m : ℤ)]) 1 : ℤ) : ℝ) ^ 2) / (scale m : ℝ) ^ 2 := by
      simp [hL]
    _ ≤ _ := Finset.single_le_sum (s := support m)
      (f := fun k : Wavevector ↦ ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2) / (scale m : ℝ) ^ 2)
      (fun _ _ ↦ by positivity) hP

/-- The source-to-energy ratio grows at least cubically in the box parameter.
This is an instantaneous lower bound, with no assertion about a time integral. -/
theorem energy_relative_source_growth (m : ℕ) (hm : 0 < m) (ν : ℝ) :
    (m : ℝ) ^ 3 * (fullEnergy (support m) (velocity (support m) (scale m))) ^ 2 ≤
      160000000000 * axialDerivativeEnergy m ν (scale m) := by
  have hw : (width m : ℝ) ≠ 0 := by exact_mod_cast (width_pos m hm).ne'
  have hLw : (scale m : ℝ) = 100 * (width m : ℝ) := by
    exact_mod_cast scale_eq_hundred_width m
  calc
    _ ≤ (m : ℝ) ^ 3 * (2000 * (width m : ℝ) ^ 2 * m) ^ 2 := by
      gcongr
      · exact fullEnergy_nonneg _ _
      · exact fullEnergy_le m hm
    _ = 160000000000 * ((m : ℝ) ^ 5 * (width m : ℝ) ^ 6 /
        (4 * (scale m : ℝ) ^ 2)) := by
      rw [hLw]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (axialDerivativeEnergy_lower m hm ν) (by norm_num)

end Mettapedia.FluidDynamics.NavierStokes.FourierPlanarPressureBox
