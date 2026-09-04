import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeCoherentWeightedTransfer

/-!
# Lattice count for square-dyadic pancake cones

At physical frequency `lambda = N^2`, the pancake aperture used by the repair
is `delta = lambda^(-1/2) = 1/N`.  A lattice vector in the ball
`|k| < 2 lambda` and this cone obeys

* `|k_x|, |k_y| ≤ 2 N`,
* `|k_z| ≤ 2 N^2`.

Consequently the number of possible modes is at most
`(4 N + 1)^2 (4 N^2 + 1) = O(lambda^2)`, rather than the ambient
`O(lambda^3)` count.  This is the exact counting input which combines with
`sq_sum_abs_le_card_mul_sum_sq` to give the improved pancake Bernstein
scaling for the coherent source field.

The square-dyadic parameterization avoids any rounding convention for square
roots.  Every ordinary dyadic shell is comparable to one of these boxes; that
comparison, and the analytic smooth-cutoff multiplier bound, are separate
steps.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeConeLatticeCount

open PancakeConeDirectionDichotomy
open PancakeCoherentWeightedTransfer

/-- Integer frequency vectors, with the same right-associated coordinate
layout as the exact rational mode model. -/
abbrev Lattice3 := ℤ × ℤ × ℤ

def latticeNormSq (k : Lattice3) : ℤ :=
  k.1 ^ 2 + k.2.1 ^ 2 + k.2.2 ^ 2

/-- Transverse coordinate range forced by aperture `1/N` inside radius
`2 N^2`. -/
def transverseRange (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))

/-- Axial coordinate range forced by radius `2 N^2`. -/
def axialRange (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(2 * (N : ℤ) ^ 2)) (2 * (N : ℤ) ^ 2)

/-- The anisotropic lattice box containing the square-dyadic pancake cone. -/
def pancakeBox (N : ℕ) : Finset Lattice3 :=
  (transverseRange N).product ((transverseRange N).product (axialRange N))

theorem card_transverseRange (N : ℕ) :
    (transverseRange N).card = 4 * N + 1 := by
  rw [transverseRange, Int.card_Icc]
  norm_num
  omega

theorem card_axialRange (N : ℕ) :
    (axialRange N).card = 4 * N ^ 2 + 1 := by
  rw [axialRange, Int.card_Icc]
  have hEq : 2 * (N : ℤ) ^ 2 + 1 - -(2 * (N : ℤ) ^ 2) =
      ((4 * N ^ 2 + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hEq, Int.toNat_natCast]

/-- Exact cardinality of the containing anisotropic box. -/
theorem card_pancakeBox (N : ℕ) :
    (pancakeBox N).card = (4 * N + 1) ^ 2 * (4 * N ^ 2 + 1) := by
  change (transverseRange N ×ˢ (transverseRange N ×ˢ axialRange N)).card = _
  rw [Finset.card_product, Finset.card_product, card_transverseRange,
    card_axialRange]
  ring

/-- A lattice mode lies in the square-dyadic pancake cone ball when it has
radius `< 2 N^2` and squared transverse aperture at most `1/N^2`. -/
def InSquarePancakeConeBall (N : ℕ) (k : Lattice3) : Prop :=
  0 < N ∧
  0 < latticeNormSq k ∧
  latticeNormSq k < 4 * (N : ℤ) ^ 4 ∧
  (N : ℤ) ^ 2 * (k.1 ^ 2 + k.2.1 ^ 2) ≤ latticeNormSq k

/-- The cone and radial inequalities force membership in the anisotropic
box. -/
theorem mem_pancakeBox_of_mem_coneBall {N : ℕ} {k : Lattice3}
    (hk : InSquarePancakeConeBall N k) :
    k ∈ pancakeBox N := by
  obtain ⟨x, y, z⟩ := k
  rcases hk with ⟨hN, _hnorm, houter, hcone⟩
  have hNZ : 0 < (N : ℤ) := by exact_mod_cast hN
  have hN2 : 0 < (N : ℤ) ^ 2 := sq_pos_of_pos hNZ
  have hxprod : (N : ℤ) ^ 2 * x ^ 2 <
      (N : ℤ) ^ 2 * (4 * (N : ℤ) ^ 2) := by
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    simp only [latticeNormSq] at houter hcone
    nlinarith
  have hyprod : (N : ℤ) ^ 2 * y ^ 2 <
      (N : ℤ) ^ 2 * (4 * (N : ℤ) ^ 2) := by
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    simp only [latticeNormSq] at houter hcone
    nlinarith
  have hx2 : x ^ 2 < 4 * (N : ℤ) ^ 2 :=
    (Int.mul_lt_mul_left hN2).mp hxprod
  have hy2 : y ^ 2 < 4 * (N : ℤ) ^ 2 :=
    (Int.mul_lt_mul_left hN2).mp hyprod
  have hz2 : z ^ 2 < 4 * (N : ℤ) ^ 4 := by
    simp only [latticeNormSq] at houter
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hxlo : -(2 * (N : ℤ)) ≤ x := by nlinarith
  have hxhi : x ≤ 2 * (N : ℤ) := by nlinarith
  have hylo : -(2 * (N : ℤ)) ≤ y := by nlinarith
  have hyhi : y ≤ 2 * (N : ℤ) := by nlinarith
  have hzlo : -(2 * (N : ℤ) ^ 2) ≤ z := by
    nlinarith [sq_nonneg ((N : ℤ) ^ 2)]
  have hzhi : z ≤ 2 * (N : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((N : ℤ) ^ 2)]
  change (x, y, z) ∈ transverseRange N ×ˢ (transverseRange N ×ˢ axialRange N)
  rw [Finset.mem_product, Finset.mem_product, transverseRange, axialRange,
    Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨⟨hxlo, hxhi⟩, ⟨⟨hylo, hyhi⟩, ⟨hzlo, hzhi⟩⟩⟩

/-- **Pancake lattice count.**  Every finite family of distinct lattice modes
inside the square-dyadic cone ball has `O(N^4) = O(lambda^2)` elements. -/
theorem card_le_pancakeBox {N : ℕ} (s : Finset Lattice3)
    (hs : ∀ k ∈ s, InSquarePancakeConeBall N k) :
    s.card ≤ (4 * N + 1) ^ 2 * (4 * N ^ 2 + 1) := by
  rw [← card_pancakeBox N]
  apply Finset.card_le_card
  intro k hk
  exact mem_pancakeBox_of_mem_coneBall (hs k hk)

/-! ## Transfer to the exact rational Fourier-symbol model -/

/-- Cast an integer lattice frequency into the rational three-vector model. -/
def toRatVec (k : Lattice3) : Vec3 :=
  ((k.1 : ℚ), (k.2.1 : ℚ), (k.2.2 : ℚ))

theorem normSq_toRatVec (k : Lattice3) :
    normSq (toRatVec k) = (latticeNormSq k : ℚ) := by
  simp only [normSq, dot, toRatVec, latticeNormSq]
  push_cast
  ring

theorem normSq_toRatVec_ne_zero {N : ℕ} {k : Lattice3}
    (hk : InSquarePancakeConeBall N k) :
    normSq (toRatVec k) ≠ 0 := by
  rw [normSq_toRatVec]
  exact ne_of_gt (by exact_mod_cast hk.2.1)

/-- The integer cone condition is exactly the rational squared-aperture
condition with `delta = 1/N`. -/
theorem toRatVec_mem_cone {N : ℕ} {k : Lattice3}
    (hk : InSquarePancakeConeBall N k) :
    (toRatVec k).1 ^ 2 + (toRatVec k).2.1 ^ 2 ≤
      (1 / (N : ℚ)) ^ 2 * normSq (toRatVec k) := by
  have hNQ : 0 < (N : ℚ) := by exact_mod_cast hk.1
  have hN2Q : 0 < (N : ℚ) ^ 2 := sq_pos_of_pos hNQ
  have hconeQ : (N : ℚ) ^ 2 *
      ((toRatVec k).1 ^ 2 + (toRatVec k).2.1 ^ 2) ≤
      normSq (toRatVec k) := by
    have hconeZ := hk.2.2.2
    simp only [latticeNormSq] at hconeZ
    simp only [pow_two] at hconeZ ⊢
    simp only [normSq, dot, toRatVec]
    exact_mod_cast hconeZ
  have heq : (1 / (N : ℚ)) ^ 2 * normSq (toRatVec k) =
      normSq (toRatVec k) / (N : ℚ) ^ 2 := by
    field_simp
  rw [heq]
  exact (le_div_iff₀ hN2Q).2 (by simpa [mul_comm] using hconeQ)

theorem inv_nat_sq_le_quarter {N : ℕ} (hN : 2 ≤ N) :
    (1 / (N : ℚ)) ^ 2 ≤ 1 / 4 := by
  have hNQ : (2 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  have h4 : (4 : ℚ) ≤ (N : ℚ) ^ 2 := by
    nlinarith [sq_nonneg ((N : ℚ) - 2)]
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 4) h4
  norm_num at hinv ⊢
  simpa [div_pow] using hinv

/-- **Square-dyadic coherent Bernstein/convolution bound.**  The pairwise
coherence estimate, amplitude-weighted convolution inequality, Cauchy–Schwarz,
and the exact `O(lambda^2)` cone count combine into one energy-facing theorem.
No mode-count hypothesis remains. -/
theorem sq_coherentConvolution_le_squareDyadicEnergy
    {N₁ N₂ : ℕ} (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    (s : Finset Lattice3) (k₂ : Lattice3) (a : Lattice3 → ℚ) (b : ℚ)
    (hs : ∀ k ∈ s, InSquarePancakeConeBall N₁ k)
    (hk₂ : InSquarePancakeConeBall N₂ k₂) :
    l1Norm (∑ k ∈ s, stretchAmp (toRatVec k)
      (smul (a k) (coherentP (toRatVec k)))
      (smul b (coherentP (toRatVec k₂)))) ^ 2 ≤
      36 * (1 / (N₁ : ℚ) + 1 / (N₂ : ℚ)) ^ 2 *
        ((4 * N₁ + 1) ^ 2 * (4 * N₁ ^ 2 + 1) : ℕ) *
        (∑ k ∈ s, a k ^ 2) * b ^ 2 := by
  have hraw := sq_l1Norm_sum_stretchAmp_coherentP_le s toRatVec
    (toRatVec k₂) (1 / (N₁ : ℚ)) (1 / (N₂ : ℚ)) a b
    (fun k hk => normSq_toRatVec_ne_zero (hs k hk))
    (normSq_toRatVec_ne_zero hk₂)
    (by positivity) (by positivity)
    (fun k hk => toRatVec_mem_cone (hs k hk))
    (toRatVec_mem_cone hk₂)
    (inv_nat_sq_le_quarter hN₁) (inv_nat_sq_le_quarter hN₂)
  have hcardNat := card_le_pancakeBox s hs
  have hcard : (s.card : ℚ) ≤
      (((4 * N₁ + 1) ^ 2 * (4 * N₁ ^ 2 + 1) : ℕ) : ℚ) := by
    exact_mod_cast hcardNat
  have hfactor : 0 ≤
      36 * (1 / (N₁ : ℚ) + 1 / (N₂ : ℚ)) ^ 2 := by positivity
  have henergy : 0 ≤ ∑ k ∈ s, a k ^ 2 := by positivity
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  calc
    l1Norm (∑ k ∈ s, stretchAmp (toRatVec k)
        (smul (a k) (coherentP (toRatVec k)))
        (smul b (coherentP (toRatVec k₂)))) ^ 2
      ≤ 36 * (1 / (N₁ : ℚ) + 1 / (N₂ : ℚ)) ^ 2 * s.card *
          (∑ k ∈ s, a k ^ 2) * b ^ 2 := hraw
    _ ≤ 36 * (1 / (N₁ : ℚ) + 1 / (N₂ : ℚ)) ^ 2 *
          (((4 * N₁ + 1) ^ 2 * (4 * N₁ ^ 2 + 1) : ℕ) : ℚ) *
          (∑ k ∈ s, a k ^ 2) * b ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcard hfactor) henergy) hb

end PancakeConeLatticeCount
end NavierStokes
end FluidDynamics
end Mettapedia
