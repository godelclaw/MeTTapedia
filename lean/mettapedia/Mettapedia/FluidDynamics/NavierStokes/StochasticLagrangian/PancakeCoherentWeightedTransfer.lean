import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCoherentPairEstimate
import Mathlib.Algebra.Order.Chebyshev

/-!
# Amplitude-weighted transfer of the coherent pancake estimate

`PancakeCoherentPairEstimate` proves an aperture gain for one normalized
source/receiver pair.  An unweighted sum of those coefficients necessarily
acquires a mode-count factor and is not a field estimate.  This module carries
the pair estimate through the first genuinely field-facing operation: arbitrary
Fourier amplitudes and a finite source convolution.

Write `coherentP k` for the Leray projection of the fixed reference direction
`e_x` onto `kᗮ`; it is the normalized version of `coherentW k`.  For cone
apertures `delta₁`, `delta₂`, the checked estimates below give

`l1Norm (stretchAmp k₁ (a * coherentP k₁) (b * coherentP k₂))
    ≤ 6 (delta₁ + delta₂) |a| |b|`

and, after summing arbitrary coherent source amplitudes,

`l1Norm (Σᵢ stretchᵢ)
    ≤ 6 (delta₁ + delta₂) (Σᵢ |aᵢ|) |b|`.

There is no cardinality factor: the correct source quantity is its Fourier
`ℓ¹` amplitude.  This is the finite Young/convolution step needed before a
conical Bernstein estimate can connect the mode calculation to a dyadic field
norm.  The module does not assume that such a Bernstein estimate has already
been proved, and therefore does not yet instantiate `coherent_le`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeCoherentWeightedTransfer

open PancakeConeDirectionDichotomy
open PancakeCoherentPairEstimate

/-- Coordinate `ℓ¹` norm on the exact rational three-vector model. -/
def l1Norm (v : Vec3) : ℚ := |v.1| + |v.2.1| + |v.2.2|

/-- The normalized coherent polarization `P_k e_x`. -/
def coherentP (k : Vec3) : Vec3 :=
  smul (1 / normSq k) (coherentW k)

theorem normSq_nonneg (v : Vec3) : 0 ≤ normSq v := by
  obtain ⟨x, y, z⟩ := v
  simp only [normSq, dot]
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]

theorem normSq_pos {v : Vec3} (hv : normSq v ≠ 0) : 0 < normSq v := by
  exact lt_of_le_of_ne (normSq_nonneg v) (Ne.symm hv)

theorem normSq_smul (a : ℚ) (v : Vec3) :
    normSq (smul a v) = a ^ 2 * normSq v := by
  simp only [normSq, dot, smul]
  ring

theorem l1Norm_nonneg (v : Vec3) : 0 ≤ l1Norm v := by
  simp only [l1Norm]
  positivity

theorem l1Norm_smul (a : ℚ) (v : Vec3) :
    l1Norm (smul a v) = |a| * l1Norm v := by
  simp only [l1Norm, smul, abs_mul]
  ring

theorem l1Norm_sq_le_three_normSq (v : Vec3) :
    l1Norm v ^ 2 ≤ 3 * normSq v := by
  obtain ⟨x, y, z⟩ := v
  simp only [l1Norm, normSq, dot]
  nlinarith [sq_nonneg (|x| - |y|), sq_nonneg (|x| - |z|),
    sq_nonneg (|y| - |z|), sq_abs x, sq_abs y, sq_abs z]

theorem stretchAmp_smul_smul (k w₁ w₂ : Vec3) (a b : ℚ) :
    stretchAmp k (smul a w₁) (smul b w₂) =
      smul (a * b) (stretchAmp k w₁ w₂) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [stretchAmp, biotSavartAmp, normSq, dot, cross, smul, add] <;>
    ring

theorem normSq_coherentP {k : Vec3} (hk : normSq k ≠ 0) :
    normSq (coherentP k) = 1 - k.1 ^ 2 / normSq k := by
  rw [coherentP, normSq_smul, normSq_coherentW]
  field_simp [hk]

theorem normSq_coherentP_le_one {k : Vec3} (hk : normSq k ≠ 0) :
    normSq (coherentP k) ≤ 1 := by
  rw [normSq_coherentP hk]
  have hN := normSq_pos hk
  have hx : 0 ≤ k.1 ^ 2 / normSq k := div_nonneg (sq_nonneg _) (le_of_lt hN)
  linarith

/-- In a pancake cone of squared aperture at most `1/4`, the normalized
coherent polarization is nonzero (indeed its squared norm is at least `3/4`). -/
theorem normSq_coherentP_pos {k : Vec3} {d : ℚ}
    (hk : normSq k ≠ 0)
    (hcone : k.1 ^ 2 + k.2.1 ^ 2 ≤ d * normSq k)
    (hd : d ≤ 1 / 4) :
    0 < normSq (coherentP k) := by
  have hN := normSq_pos hk
  have hx : k.1 ^ 2 ≤ (1 / 4 : ℚ) * normSq k := by
    have hdN : d * normSq k ≤ (1 / 4 : ℚ) * normSq k :=
      mul_le_mul_of_nonneg_right hd (le_of_lt hN)
    nlinarith [hcone, sq_nonneg k.2.1]
  rw [normSq_coherentP hk]
  rw [sub_pos, div_lt_iff₀ hN]
  nlinarith

theorem sigmaSq_coherentP_eq {k₁ k₂ : Vec3} {d₁ d₂ : ℚ}
    (hk₁ : normSq k₁ ≠ 0) (hk₂ : normSq k₂ ≠ 0)
    (hcone₁ : k₁.1 ^ 2 + k₁.2.1 ^ 2 ≤ d₁ * normSq k₁)
    (hcone₂ : k₂.1 ^ 2 + k₂.2.1 ^ 2 ≤ d₂ * normSq k₂)
    (hd₁ : d₁ ≤ 1 / 4) (hd₂ : d₂ ≤ 1 / 4) :
    sigmaSq k₁ (coherentP k₁) (coherentP k₂) =
      sigmaSq k₁ (coherentW k₁) (coherentW k₂) := by
  have hP₁ := normSq_coherentP_pos hk₁ hcone₁ hd₁
  have hP₂ := normSq_coherentP_pos hk₂ hcone₂ hd₂
  have hW₁ : normSq (coherentW k₁) ≠ 0 := by
    rw [coherentP, normSq_smul] at hP₁
    exact fun h => by rw [h, mul_zero] at hP₁; linarith
  have hW₂ : normSq (coherentW k₂) ≠ 0 := by
    rw [coherentP, normSq_smul] at hP₂
    exact fun h => by rw [h, mul_zero] at hP₂; linarith
  simp only [sigmaSq, coherentP]
  rw [stretchAmp_smul_smul,
    normSq_smul, normSq_smul, normSq_smul]
  field_simp [hk₁, hk₂, hW₁, hW₂]

/-- Pairwise coherent stretching with actual scalar Fourier amplitudes.  The
bound is linear in aperture (rather than squared aperture) because it controls
an amplitude norm rather than its square. -/
theorem l1Norm_stretchAmp_coherentP_le
    (k₁ k₂ : Vec3) (delta₁ delta₂ a b : ℚ)
    (hk₁ : normSq k₁ ≠ 0) (hk₂ : normSq k₂ ≠ 0)
    (hdelta₁ : 0 ≤ delta₁) (hdelta₂ : 0 ≤ delta₂)
    (hcone₁ : k₁.1 ^ 2 + k₁.2.1 ^ 2 ≤ delta₁ ^ 2 * normSq k₁)
    (hcone₂ : k₂.1 ^ 2 + k₂.2.1 ^ 2 ≤ delta₂ ^ 2 * normSq k₂)
    (hd₁ : delta₁ ^ 2 ≤ 1 / 4) (hd₂ : delta₂ ^ 2 ≤ 1 / 4) :
    l1Norm (stretchAmp k₁ (smul a (coherentP k₁))
      (smul b (coherentP k₂))) ≤
      6 * (delta₁ + delta₂) * |a| * |b| := by
  have hsigma := sigmaSq_coherent_le k₁ k₂ (delta₁ ^ 2) (delta₂ ^ 2)
    hk₁ hk₂ hcone₁ hcone₂ hd₁ hd₂
  rw [← sigmaSq_coherentP_eq hk₁ hk₂ hcone₁ hcone₂ hd₁ hd₂] at hsigma
  have hP₁ := normSq_coherentP_pos hk₁ hcone₁ hd₁
  have hP₂ := normSq_coherentP_pos hk₂ hcone₂ hd₂
  have hden : 0 < normSq (coherentP k₁) * normSq (coherentP k₂) :=
    mul_pos hP₁ hP₂
  have hstretch : normSq (stretchAmp k₁ (coherentP k₁) (coherentP k₂)) ≤
      6 * (delta₁ ^ 2 + delta₂ ^ 2) := by
    rw [sigmaSq, div_le_iff₀ hden] at hsigma
    have hP₁le := normSq_coherentP_le_one hk₁
    have hP₂le := normSq_coherentP_le_one hk₂
    have hK : 0 ≤ 6 * (delta₁ ^ 2 + delta₂ ^ 2) := by positivity
    have hprod : normSq (coherentP k₁) * normSq (coherentP k₂) ≤ 1 := by
      nlinarith [hP₁, hP₂, hP₁le, hP₂le]
    nlinarith
  have hl1sq := l1Norm_sq_le_three_normSq
    (stretchAmp k₁ (coherentP k₁) (coherentP k₂))
  have hap : delta₁ ^ 2 + delta₂ ^ 2 ≤ (delta₁ + delta₂) ^ 2 := by
    nlinarith
  have hl1 : l1Norm (stretchAmp k₁ (coherentP k₁) (coherentP k₂)) ≤
      6 * (delta₁ + delta₂) := by
    have hl1nn := l1Norm_nonneg
      (stretchAmp k₁ (coherentP k₁) (coherentP k₂))
    nlinarith [hl1sq]
  rw [stretchAmp_smul_smul, l1Norm_smul, abs_mul]
  have hab : 0 ≤ |a| * |b| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  nlinarith

/-- Coordinate `ℓ¹` triangle inequality for a finite vector sum. -/
theorem l1Norm_sum_le_sum_l1Norm {ι : Type*} (s : Finset ι) (f : ι → Vec3) :
    l1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Norm (f i) := by
  have hx := Finset.abs_sum_le_sum_abs (fun i => (f i).1) s
  have hy := Finset.abs_sum_le_sum_abs (fun i => (f i).2.1) s
  have hz := Finset.abs_sum_le_sum_abs (fun i => (f i).2.2) s
  simp only [l1Norm, Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib]
  linarith

/-- **Cardinality-free finite convolution estimate.**  A coherent receiver
interacting with arbitrary coherent source amplitudes pays the source Fourier
`ℓ¹` mass, not the number of modes. -/
theorem l1Norm_sum_stretchAmp_coherentP_le {ι : Type*} (s : Finset ι)
    (k : ι → Vec3) (k₂ : Vec3) (delta₁ delta₂ : ℚ)
    (a : ι → ℚ) (b : ℚ)
    (hk : ∀ i ∈ s, normSq (k i) ≠ 0) (hk₂ : normSq k₂ ≠ 0)
    (hdelta₁ : 0 ≤ delta₁) (hdelta₂ : 0 ≤ delta₂)
    (hcone : ∀ i ∈ s,
      (k i).1 ^ 2 + (k i).2.1 ^ 2 ≤ delta₁ ^ 2 * normSq (k i))
    (hcone₂ : k₂.1 ^ 2 + k₂.2.1 ^ 2 ≤ delta₂ ^ 2 * normSq k₂)
    (hd₁ : delta₁ ^ 2 ≤ 1 / 4) (hd₂ : delta₂ ^ 2 ≤ 1 / 4) :
    l1Norm (∑ i ∈ s, stretchAmp (k i) (smul (a i) (coherentP (k i)))
      (smul b (coherentP k₂))) ≤
      6 * (delta₁ + delta₂) * (∑ i ∈ s, |a i|) * |b| := by
  calc
    l1Norm (∑ i ∈ s, stretchAmp (k i) (smul (a i) (coherentP (k i)))
        (smul b (coherentP k₂)))
      ≤ ∑ i ∈ s, l1Norm (stretchAmp (k i)
          (smul (a i) (coherentP (k i))) (smul b (coherentP k₂))) :=
        l1Norm_sum_le_sum_l1Norm s _
    _ ≤ ∑ i ∈ s, 6 * (delta₁ + delta₂) * |a i| * |b| := by
      apply Finset.sum_le_sum
      intro i hi
      exact l1Norm_stretchAmp_coherentP_le (k i) k₂ delta₁ delta₂ (a i) b
        (hk i hi) hk₂ hdelta₁ hdelta₂ (hcone i hi) hcone₂ hd₁ hd₂
    _ = 6 * (delta₁ + delta₂) * (∑ i ∈ s, |a i|) * |b| := by
      rw [Finset.mul_sum, Finset.sum_mul]

/-- Finite Fourier `ℓ¹` mass is controlled by mode count times quadratic
energy.  This is the exact place where pancake-cone lattice counting enters
the subsequent Bernstein step. -/
theorem sq_sum_abs_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (a : ι → ℚ) :
    (∑ i ∈ s, |a i|) ^ 2 ≤ s.card * ∑ i ∈ s, a i ^ 2 := by
  simpa only [sq_abs] using
    (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => |a i|))

/-- Abstract conical Bernstein estimate once the lattice-point count of the
shell has been supplied.  The following module proves that count for the
square-dyadic pancake boxes used by the exact lattice model. -/
theorem sq_sum_abs_le_of_card_bound {ι : Type*} (s : Finset ι) (a : ι → ℚ)
    (modeBound : ℚ) (hcard : (s.card : ℚ) ≤ modeBound) :
    (∑ i ∈ s, |a i|) ^ 2 ≤ modeBound * ∑ i ∈ s, a i ^ 2 := by
  have hcs := sq_sum_abs_le_card_mul_sum_sq s a
  have henergy : 0 ≤ ∑ i ∈ s, a i ^ 2 := by positivity
  exact hcs.trans (mul_le_mul_of_nonneg_right hcard henergy)

/-- Energy-facing form of the convolution estimate.  It records exactly how
the coherent aperture gain combines with the number of active source modes;
the conical lattice count turns this into the improved Bernstein scaling. -/
theorem sq_l1Norm_sum_stretchAmp_coherentP_le {ι : Type*} (s : Finset ι)
    (k : ι → Vec3) (k₂ : Vec3) (delta₁ delta₂ : ℚ)
    (a : ι → ℚ) (b : ℚ)
    (hk : ∀ i ∈ s, normSq (k i) ≠ 0) (hk₂ : normSq k₂ ≠ 0)
    (hdelta₁ : 0 ≤ delta₁) (hdelta₂ : 0 ≤ delta₂)
    (hcone : ∀ i ∈ s,
      (k i).1 ^ 2 + (k i).2.1 ^ 2 ≤ delta₁ ^ 2 * normSq (k i))
    (hcone₂ : k₂.1 ^ 2 + k₂.2.1 ^ 2 ≤ delta₂ ^ 2 * normSq k₂)
    (hd₁ : delta₁ ^ 2 ≤ 1 / 4) (hd₂ : delta₂ ^ 2 ≤ 1 / 4) :
    l1Norm (∑ i ∈ s, stretchAmp (k i) (smul (a i) (coherentP (k i)))
      (smul b (coherentP k₂))) ^ 2 ≤
      36 * (delta₁ + delta₂) ^ 2 * s.card *
        (∑ i ∈ s, a i ^ 2) * b ^ 2 := by
  have hlin := l1Norm_sum_stretchAmp_coherentP_le s k k₂ delta₁ delta₂ a b
    hk hk₂ hdelta₁ hdelta₂ hcone hcone₂ hd₁ hd₂
  have hcs := sq_sum_abs_le_card_mul_sum_sq s a
  have hlhs := l1Norm_nonneg
    (∑ i ∈ s, stretchAmp (k i) (smul (a i) (coherentP (k i)))
      (smul b (coherentP k₂)))
  have hrhs : 0 ≤ 6 * (delta₁ + delta₂) * (∑ i ∈ s, |a i|) * |b| := by
    positivity
  have hsq : l1Norm (∑ i ∈ s,
      stretchAmp (k i) (smul (a i) (coherentP (k i)))
        (smul b (coherentP k₂))) ^ 2 ≤
      (6 * (delta₁ + delta₂) * (∑ i ∈ s, |a i|) * |b|) ^ 2 := by
    nlinarith
  calc
    l1Norm (∑ i ∈ s,
        stretchAmp (k i) (smul (a i) (coherentP (k i)))
          (smul b (coherentP k₂))) ^ 2
      ≤ (6 * (delta₁ + delta₂) * (∑ i ∈ s, |a i|) * |b|) ^ 2 := hsq
    _ = 36 * (delta₁ + delta₂) ^ 2 *
        (∑ i ∈ s, |a i|) ^ 2 * b ^ 2 := by
          rw [mul_pow, sq_abs]
          ring
    _ ≤ 36 * (delta₁ + delta₂) ^ 2 *
        (s.card * ∑ i ∈ s, a i ^ 2) * b ^ 2 := by
          gcongr
    _ = 36 * (delta₁ + delta₂) ^ 2 * s.card *
        (∑ i ∈ s, a i ^ 2) * b ^ 2 := by ring

end PancakeCoherentWeightedTransfer
end NavierStokes
end FluidDynamics
end Mettapedia
