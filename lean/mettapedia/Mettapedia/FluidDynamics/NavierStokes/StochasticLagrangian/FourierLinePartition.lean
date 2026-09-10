import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeQuadraticProjectionLocalization
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralTiltFreezing

/-!
# Quadratic Fourier partitions with a cell-count-free line error

Approximation accuracy is chosen after the finite partition is known.
Coverage remains between one half and three halves. Off-cell Fourier
tails contribute at most twice the prescribed squared tolerance to the
total unoriented-line error, independently of the number of cells.
The Fourier bandwidth may depend on the partition and tolerance.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierLinePartition

open scoped BigOperators
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization SpectralTiltFreezing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

theorem sum_quadraticWeight_lineDistanceSq_le {ι : Type*} [Fintype ι]
    (weight : PartitionOfUnity ι T3) (c : ι → FourierCoeff (Fin 3))
    (e : T3 → R3) (f : ι → R3) (he : ∀ x, ‖e x‖ = 1) (hf : ∀ i, ‖f i‖ = 1)
    (rho epsilon C : ℝ)
    (hactive : ∀ i x, weight i x ≠ 0 → lineDistanceSq (e x) (f i) ≤ rho ^ 2)
    (hleak : ∀ i x, weight i x = 0 → quadraticWeight (c i) x ≤ epsilon ^ 2)
    (hcover : ∀ x, ∑ i, quadraticWeight (c i) x ≤ C) (x : T3) :
    (∑ i, quadraticWeight (c i) x * lineDistanceSq (e x) (f i)) ≤
      C * rho ^ 2 + 2 * (Fintype.card ι : ℝ) * epsilon ^ 2 := by
  have h (i : ι) : quadraticWeight (c i) x * lineDistanceSq (e x) (f i) ≤
      quadraticWeight (c i) x * rho ^ 2 + 2 * epsilon ^ 2 := by
    have hw : 0 ≤ quadraticWeight (c i) x := Complex.normSq_nonneg _
    by_cases hz : weight i x = 0
    · have hd := lineDistanceSq_le_two (e x) (f i) (he x) (hf i)
      have hm := mul_le_mul_of_nonneg_left hd hw
      nlinarith only [hm, hleak i x hz, mul_nonneg hw (sq_nonneg rho), sq_nonneg epsilon]
    · have hm := mul_le_mul_of_nonneg_left (hactive i x hz) hw
      nlinarith only [hm, sq_nonneg epsilon]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ h i)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hs
  have hc := mul_le_mul_of_nonneg_right (hcover x) (sq_nonneg rho)
  nlinarith only [hs, hc]

/-- One common tolerance simultaneously pays coverage and the sum of
off-cell squared tails. Its size is allowed to depend on the cell count. -/
theorem exists_approximation_tolerance (n : ℕ) (delta : ℝ) (hd : 0 < delta) :
    ∃ epsilon > (0 : ℝ),
      (n : ℝ) * (epsilon * (epsilon + 2)) ≤ 1 / 2 ∧
      (n : ℝ) * epsilon ^ 2 ≤ delta ^ 2 := by
  let epsilon := min (1 / 6 : ℝ) delta / ((n : ℝ) + 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have he : 0 < epsilon := div_pos (lt_min (by norm_num) hd) hden
  have hp : epsilon * ((n : ℝ) + 1) = min (1 / 6 : ℝ) delta :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have hsmall : epsilon * ((n : ℝ) + 1) ≤ 1 / 6 := hp.le.trans (min_le_left _ _)
  have hdelt : epsilon * ((n : ℝ) + 1) ≤ delta := hp.le.trans (min_le_right _ _)
  have hne := mul_nonneg hn he.le
  have heone : epsilon ≤ 1 := by nlinarith only [hsmall, hne]
  have hns : (n : ℝ) * epsilon ≤ 1 / 6 := by nlinarith only [hsmall, he.le]
  have hnd : (n : ℝ) * epsilon ≤ delta := by nlinarith only [hdelt, he.le]
  have hed : epsilon ≤ delta := by nlinarith only [hdelt, hne]
  refine ⟨epsilon, he, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left (by linarith : epsilon + 2 ≤ 3) hne
    nlinarith only [h, hns]
  · have h := mul_le_mul hnd hed he.le hd.le
    nlinarith only [h]

/-- Construct Fourier weights with positive coverage and an arbitrarily
small total tail cost from a partition subordinate to nearby lines. -/
theorem exists_quadraticFourier_line_partition {ι : Type*} [Fintype ι]
    (weight : PartitionOfUnity ι T3) (e : T3 → R3) (f : ι → R3)
    (he : ∀ x, ‖e x‖ = 1) (hf : ∀ i, ‖f i‖ = 1) (rho delta : ℝ) (hd : 0 < delta)
    (hactive : ∀ i x, weight i x ≠ 0 → lineDistanceSq (e x) (f i) ≤ rho ^ 2) :
    ∃ c : ι → FourierCoeff (Fin 3),
      (∀ x, (1 / 2 : ℝ) ≤ ∑ i, quadraticWeight (c i) x) ∧
      (∀ x, (∑ i, quadraticWeight (c i) x) ≤ 3 / 2) ∧
      ∀ x, (∑ i, quadraticWeight (c i) x * lineDistanceSq (e x) (f i)) ≤
        (3 / 2 : ℝ) * rho ^ 2 + 2 * delta ^ 2 := by
  obtain ⟨epsilon, heps, hsmall, htail⟩ := exists_approximation_tolerance (Fintype.card ι) delta hd
  obtain ⟨c, _, _, _, hcover, hleak, _⟩ := exists_adaptiveQuadraticFourierPackage weight heps hsmall
  have hlow (x : T3) : (1 / 2 : ℝ) ≤ ∑ i, quadraticWeight (c i) x := (hcover x).1
  have hupp (x : T3) : (∑ i, quadraticWeight (c i) x) ≤ 3 / 2 := (hcover x).2
  refine ⟨c, hlow, hupp, ?_⟩
  intro x
  have h := sum_quadraticWeight_lineDistanceSq_le weight c e f he hf rho epsilon (3 / 2)
    hactive (fun i y hy ↦ (hleak i y hy).le) hupp x
  linarith only [h, htail]

end Mettapedia.FluidDynamics.NavierStokes.FourierLinePartition
