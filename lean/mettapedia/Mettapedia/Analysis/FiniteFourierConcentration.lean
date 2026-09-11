import Mettapedia.Analysis.FiniteMultiplierLocalization
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.Complex.Basic

/-!
# Concentration of finite Fourier products

Unit coefficients on a long interval have a quadratic product of input
energies but cubic convolution energy. Consequently no universal constant bounds the
product energy by the product of the two input square energies. The
construction works along any embedded integer frequency axis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteFourierConcentration

open scoped BigOperators
open FiniteMultiplierLocalization

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def intervalModes (e : ℤ →+ G) (n : ℕ) : Finset G :=
  (Finset.Icc (0 : ℤ) (2 * n)).image e

theorem card_intervalModes (e : ℤ →+ G) (he : Function.Injective e) (n : ℕ) :
    (intervalModes e n).card = 2 * n + 1 := by
  rw [intervalModes, Finset.card_image_of_injective _ he]
  rw [Int.card_Icc]
  omega

theorem scalarEnergy_intervalModes (e : ℤ →+ G) (he : Function.Injective e) (n : ℕ) :
    scalarEnergy (intervalModes e n) (fun _ ↦ (1 : ℂ)) = 2 * n + 1 := by
  simp [scalarEnergy, card_intervalModes e he]

theorem norm_intervalConvolution_ge (e : ℤ →+ G) (he : Function.Injective e)
    (n : ℕ) (q : ℤ) (hq : q ∈ Finset.Icc (n : ℤ) (2 * n)) :
    (n : ℝ) + 1 ≤ ‖scalarConvolution (intervalModes e n) (intervalModes e n)
      (fun _ ↦ (1 : ℂ)) (fun _ ↦ (1 : ℂ)) (e q)‖ := by
  let F := ((intervalModes e n) ×ˢ (intervalModes e n)).filter (fun p ↦ p.1 + p.2 = e q)
  have hc : (Finset.Icc (0 : ℤ) n).card ≤ F.card := by
    apply Finset.card_le_card_of_injOn (fun k : ℤ ↦ (e k, e (q - k)))
    · intro k hk
      have hk' := Finset.mem_Icc.mp hk
      have hq' := Finset.mem_Icc.mp hq
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨q - k, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
      · rw [← map_add]
        congr 1
        omega
    · intro k _ l _ h
      exact he (congrArg Prod.fst h)
  have hn : (Finset.Icc (0 : ℤ) n).card = n + 1 := by
    simp [Int.card_Icc]
  rw [hn] at hc
  have hval : scalarConvolution (intervalModes e n) (intervalModes e n)
      (fun _ ↦ (1 : ℂ)) (fun _ ↦ (1 : ℂ)) (e q) = (F.card : ℂ) := by
    simp [scalarConvolution, F]
  rw [hval, Complex.norm_natCast]
  exact_mod_cast hc

theorem scalarEnergy_intervalConvolution_ge (e : ℤ →+ G) (he : Function.Injective e) (n : ℕ) :
    ((n : ℝ) + 1) ^ 3 ≤
      scalarEnergy (((intervalModes e n) ×ˢ (intervalModes e n)).image (fun p ↦ p.1 + p.2))
        (scalarConvolution (intervalModes e n) (intervalModes e n) (fun _ ↦ (1 : ℂ)) (fun _ ↦ (1 : ℂ))) := by
  let Q := (Finset.Icc (n : ℤ) (2 * n)).image e
  have hQ : Q ⊆ ((intervalModes e n) ×ˢ (intervalModes e n)).image (fun p ↦ p.1 + p.2) := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
    have hk' := Finset.mem_Icc.mp hk
    refine Finset.mem_image.mpr ⟨(e 0, e k), Finset.mem_product.mpr ⟨?_, ?_⟩, by simp⟩
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_Icc.mpr ⟨le_refl _, by positivity⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩, rfl⟩
  have hcard : Q.card = n + 1 := by
    dsimp only [Q]
    rw [Finset.card_image_of_injective _ he]
    have h : (2 * (n : ℤ) + 1 - n) = (n + 1 : ℕ) := by omega
    simp [Int.card_Icc, h]
  have hlow : ∑ _q ∈ Q, ((n : ℝ) + 1) ^ 2 ≤
      ∑ q ∈ Q, ‖scalarConvolution (intervalModes e n) (intervalModes e n)
        (fun _ ↦ (1 : ℂ)) (fun _ ↦ (1 : ℂ)) q‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro q hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
    exact pow_le_pow_left₀ (by positivity) (norm_intervalConvolution_ge e he n k hk) 2
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg hQ
    (fun q _ _ ↦ sq_nonneg ‖scalarConvolution (intervalModes e n) (intervalModes e n)
      (fun _ ↦ (1 : ℂ)) (fun _ ↦ (1 : ℂ)) q‖)
  have h := hlow.trans hsub
  simp only [Finset.sum_const, hcard, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  unfold scalarEnergy
  nlinarith only [h]

theorem exists_intervalConvolution_energy_gt (e : ℤ →+ G) (he : Function.Injective e) (C : ℝ) :
    ∃ n : ℕ,
      C * scalarEnergy (intervalModes e n) (fun _ ↦ (1 : ℂ)) ^ 2 <
        scalarEnergy (((intervalModes e n) ×ˢ (intervalModes e n)).image (fun p ↦ p.1 + p.2))
          (scalarConvolution (intervalModes e n) (intervalModes e n) (fun _ ↦ (1 : ℂ)) (fun _ ↦ (1 : ℂ))) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * max C 0)
  refine ⟨n, ?_⟩
  rw [scalarEnergy_intervalModes e he]
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hC := le_max_left C 0
  have hC0 := le_max_right C 0
  have hsq : (2 * (n : ℝ) + 1) ^ 2 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right hC (sq_nonneg (2 * (n : ℝ) + 1))
  have h2 := mul_le_mul_of_nonneg_left hsq hC0
  have h3 : 4 * max C 0 * ((n : ℝ) + 1) ^ 2 < ((n : ℝ) + 1) ^ 3 := by
    have h := mul_lt_mul_of_pos_right (show 4 * max C 0 < (n : ℝ) + 1 by linarith)
      (show 0 < ((n : ℝ) + 1) ^ 2 by positivity)
    nlinarith only [h]
  exact (lt_of_le_of_lt h1 (lt_of_le_of_lt (by nlinarith only [h2]) h3)).trans_le
    (scalarEnergy_intervalConvolution_ge e he n)

end Mettapedia.Analysis.FiniteFourierConcentration
