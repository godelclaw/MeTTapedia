import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Uniform inverse-Fourier moments from compact smooth symbol families

Joint smoothness and a common compact spatial support give uniform
Schwartz seminorms over compact parameter sets. Fourier decay then gives
uniform moments of the actual inverse kernels, including their first
spatial moment. No continuity in the Schwartz topology is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.CompactSchwartzFamily

open MeasureTheory Set
open scoped FourierTransform SchwartzMap ContDiff

variable {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]

theorem norm_iteratedFDeriv_section_le
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : T × P → V) (hF : ContDiff ℝ ∞ F) (n : ℕ) (t : T) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y ↦ F (t, y)) x‖ ≤ ‖iteratedFDeriv ℝ n F (t, x)‖ := by
  let L : P →L[ℝ] T × P := ContinuousLinearMap.inr ℝ T P
  let a : T × P := (t, 0)
  let G : T × P → V := fun z ↦ F (a + z)
  have hG : ContDiff ℝ ∞ G := hF.comp (contDiff_const.add contDiff_id)
  have hderiv := L.iteratedFDeriv_comp_right hG x
    (show (n : ℕ∞) ≤ ∞ by exact_mod_cast le_top)
  have he : (fun y ↦ F (t, y)) = G ∘ L := by funext y; simp [G, L, a]
  rw [he, hderiv]
  rw [show iteratedFDeriv ℝ n G (L x) = iteratedFDeriv ℝ n F (t, x) by
    simp [G, L, a, iteratedFDeriv_comp_add_left]]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ T P)

theorem exists_uniform_weighted_derivative_bound
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : T × P → V) (hF : ContDiff ℝ ∞ F)
    (A : Set T) (hA : IsCompact A) (L : Set P) (hL : IsCompact L)
    (hs : ∀ t, tsupport (fun x ↦ F (t, x)) ⊆ L) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ A, ∀ x : P,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y ↦ F (t, y)) x‖ ≤ C := by
  let H : T × P → ℝ := fun z ↦ ‖z.2‖ ^ k * ‖iteratedFDeriv ℝ n F z‖
  have hderiv : Continuous (fun z ↦ iteratedFDeriv ℝ n F z) :=
    hF.continuous_iteratedFDeriv (show (n : ℕ∞) ≤ ∞ by exact_mod_cast le_top)
  have hH : Continuous H := ((continuous_norm.comp continuous_snd).pow k).mul hderiv.norm
  obtain ⟨M, hM⟩ := (hA.prod hL).bddAbove_image hH.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ L
  · exact ((mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_section_le F hF n t x)
      (pow_nonneg (norm_nonneg _) _)).trans
        (hM (mem_image_of_mem H ⟨ht, hx⟩))).trans (le_max_left _ _)
  · have hzero : iteratedFDeriv ℝ n (fun y ↦ F (t, y)) x = 0 := by
      apply Function.notMem_support.mp
      exact fun h ↦ hx (hs t (support_iteratedFDeriv_subset n h))
    rw [hzero, norm_zero, mul_zero]
    exact le_max_right _ _

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_uniform_seminorm_bound (S : T → 𝓢(E, ℂ))
    (hS : ContDiff ℝ ∞ (fun z : T × E ↦ S z.1 z.2))
    (A : Set T) (hA : IsCompact A) (L : Set E) (hL : IsCompact L)
    (hs : ∀ t, tsupport (S t) ⊆ L) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ A, SchwartzMap.seminorm ℂ k n (S t) ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_weighted_derivative_bound
    (fun z : T × E ↦ S z.1 z.2) hS A hA L hL hs k n
  exact ⟨C, hC, fun t ht ↦ SchwartzMap.seminorm_le_bound ℂ k n _ hC (hb t ht)⟩

theorem exists_uniform_derivative_integral_bound (S : T → 𝓢(E, ℂ))
    (hS : ContDiff ℝ ∞ (fun z : T × E ↦ S z.1 z.2))
    (A : Set T) (hA : IsCompact A) (L : Set E) (hL : IsCompact L)
    (hs : ∀ t, tsupport (S t) ⊆ L) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ A,
      (∫ x : E, ‖iteratedFDeriv ℝ n (S t) x‖) ≤ C := by
  let p : ℕ := (volume : Measure E).integrablePower
  obtain ⟨C0, hC0, hb0⟩ := exists_uniform_seminorm_bound S hS A hA L hL hs 0 n
  obtain ⟨Cp, hCp, hbp⟩ := exists_uniform_seminorm_bound S hS A hA L hL hs p n
  let a : ℝ := 2 ^ p * ∫ x : E, (1 + ‖x‖) ^ (-(p : ℝ))
  have ha : 0 ≤ a := by unfold a; positivity
  refine ⟨a * (C0 + Cp), mul_nonneg ha (add_nonneg hC0 hCp), ?_⟩
  intro t ht
  have hmass : (∫ x : E, ‖iteratedFDeriv ℝ n (S t) x‖) ≤
      a * (SchwartzMap.seminorm ℂ 0 n (S t) + SchwartzMap.seminorm ℂ p n (S t)) := by
    simpa [a, p] using (S t).integral_pow_mul_iteratedFDeriv_le ℂ (volume : Measure E) 0 n
  exact hmass.trans (mul_le_mul_of_nonneg_left (add_le_add (hb0 t ht) (hbp t ht)) ha)

theorem pow_mul_norm_fourierInv_le (s : 𝓢(E, ℂ)) (m : ℕ) (x : E) :
    ‖x‖ ^ m * ‖(𝓕⁻ s) x‖ ≤ 2 ^ m * ∑ r ∈ Finset.range (m + 1),
      ∫ y : E, ‖iteratedFDeriv ℝ r s y‖ := by
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le (s.smooth ⊤)
    (fun k n _ _ ↦ s.integrable_pow_mul_iteratedFDeriv (volume : Measure E) k n)
    (k := 0) (n := m) le_top le_top (-x)
  simp only [norm_neg, norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero,
    zero_add, Finset.range_one] at h
  change ‖x‖ ^ m * ‖𝓕 s (-x)‖ ≤ _ at h
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, ← SchwartzMap.fourier_coe]
  simpa [Finset.sum_product] using h

theorem exists_uniform_fourierInv_decay (S : T → 𝓢(E, ℂ))
    (hS : ContDiff ℝ ∞ (fun z : T × E ↦ S z.1 z.2))
    (A : Set T) (hA : IsCompact A) (L : Set E) (hL : IsCompact L)
    (hs : ∀ t, tsupport (S t) ⊆ L) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ A, ∀ x : E, ‖x‖ ^ m * ‖(𝓕⁻ (S t)) x‖ ≤ C := by
  classical
  choose C hC hb using fun n ↦ exists_uniform_derivative_integral_bound S hS A hA L hL hs n
  refine ⟨2 ^ m * ∑ r ∈ Finset.range (m + 1), C r,
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun r _ ↦ hC r)), ?_⟩
  intro t ht x
  exact (pow_mul_norm_fourierInv_le (S t) m x).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun r _ ↦ hb r t ht)) (by positivity))

theorem exists_uniform_fourierInv_moment (S : T → 𝓢(E, ℂ))
    (hS : ContDiff ℝ ∞ (fun z : T × E ↦ S z.1 z.2))
    (A : Set T) (hA : IsCompact A) (L : Set E) (hL : IsCompact L)
    (hs : ∀ t, tsupport (S t) ⊆ L) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ A, (∫ x : E, ‖x‖ ^ m * ‖(𝓕⁻ (S t)) x‖) ≤ C := by
  let p : ℕ := (volume : Measure E).integrablePower
  obtain ⟨C0, hC0, hb0⟩ := exists_uniform_fourierInv_decay S hS A hA L hL hs 0
  obtain ⟨Cp, hCp, hbp⟩ := exists_uniform_fourierInv_decay S hS A hA L hL hs (m + p)
  let a : ℝ := 2 ^ p * ∫ x : E, (1 + ‖x‖) ^ (-(p : ℝ))
  have ha : 0 ≤ a := by unfold a; positivity
  refine ⟨a * (C0 + Cp), mul_nonneg ha (add_nonneg hC0 hCp), ?_⟩
  intro t ht
  have h := integral_pow_mul_le_of_le_of_pow_mul_le (μ := (volume : Measure E))
    (f := (𝓕⁻ (S t) : 𝓢(E, ℂ))) (k := m)
    (by simpa using hb0 t ht) (by simpa [p] using hbp t ht)
  simpa [a, p] using h

end Mettapedia.Analysis.CompactSchwartzFamily
