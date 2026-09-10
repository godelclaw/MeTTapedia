import Mettapedia.Analysis.FiniteConvolutionEnergy
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.BigOperators

/-!
# Finite localization of a scalar-to-vector multiplier

The localized multiplier splits exactly into the multiplier of the
localized scalar field and a commutator. Its energy retains a small
output-symbol bound in the main term and an explicit weighted source
sum for the symbol variation. All coincident output modes are collected.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.FiniteMultiplierLocalization

open scoped BigOperators

variable {G E 𝕜 : Type*} [AddCommGroup G] [DecidableEq G] [NormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

def scalarConvolution (P K : Finset G) (c b : G → 𝕜) (q : G) : 𝕜 :=
  ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, c pk.1 * b pk.2

def vectorConvolution (P K : Finset G) (c : G → 𝕜) (a : G → E) (q : G) : E :=
  ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, c pk.1 • a pk.2

def commutatorCoefficient (P K : Finset G) (c b : G → 𝕜) (m : G → E) (q : G) : E :=
  ∑ pk ∈ P ×ˢ K with pk.1 + pk.2 = q, (c pk.1 * b pk.2) • (m pk.2 - m (pk.1 + pk.2))

def scalarEnergy (K : Finset G) (b : G → 𝕜) : ℝ := ∑ k ∈ K, ‖b k‖ ^ 2

def vectorEnergy (K : Finset G) (a : G → E) : ℝ := ∑ k ∈ K, ‖a k‖ ^ 2

theorem vectorConvolution_multiplier_eq (P K : Finset G) (c b : G → 𝕜) (m : G → E) (q : G) :
    vectorConvolution P K c (fun k ↦ b k • m k) q =
      scalarConvolution P K c b q • m q + commutatorCoefficient P K c b m q := by
  unfold vectorConvolution scalarConvolution commutatorCoefficient
  rw [Finset.sum_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro pk hpk
  rw [(Finset.mem_filter.mp hpk).2, smul_smul, smul_sub]
  abel

theorem commutator_energy_le (P K Q : Finset G) (c b : G → 𝕜) (m : G → E) (d : G → ℝ)
    (hd : ∀ p ∈ P, 0 ≤ d p)
    (hm : ∀ p ∈ P, ∀ k ∈ K, ‖m k - m (p + k)‖ ≤ d p)
    (hQ : ∀ p ∈ P, ∀ k ∈ K, p + k ∈ Q) :
    vectorEnergy Q (commutatorCoefficient P K c b m) ≤
      (∑ p ∈ P, ‖c p‖ * d p) ^ 2 * scalarEnergy K b := by
  apply FiniteConvolutionEnergy.sum_norm_sq_le P K Q (fun p ↦ ‖c p‖ * d p) (fun k ↦ ‖b k‖)
    (fun p k ↦ (c p * b k) • (m k - m (p + k)))
    (fun p hp ↦ mul_nonneg (norm_nonneg _) (hd p hp)) _ hQ
  intro p hp k hk
  rw [norm_smul, norm_mul]
  have h := mul_le_mul_of_nonneg_left (hm p hp k hk) (by positivity : 0 ≤ ‖c p‖ * ‖b k‖)
  nlinarith only [h]

theorem localized_multiplier_energy_le (P K Q : Finset G) (c b : G → 𝕜) (m : G → E)
    (eta : ℝ) (hmain : ∀ q ∈ Q, ‖m q‖ ≤ eta) :
    vectorEnergy Q (vectorConvolution P K c (fun k ↦ b k • m k)) ≤
      2 * eta ^ 2 * scalarEnergy Q (scalarConvolution P K c b) +
        2 * vectorEnergy Q (commutatorCoefficient P K c b m) := by
  unfold vectorEnergy scalarEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  rw [vectorConvolution_multiplier_eq]
  have hn := norm_add_le (scalarConvolution P K c b q • m q) (commutatorCoefficient P K c b m q)
  have hn2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hm := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hmain q hq) 2) (sq_nonneg ‖scalarConvolution P K c b q‖)
  rw [norm_smul] at hn2
  nlinarith only [hn2, hm,
    sq_nonneg (‖scalarConvolution P K c b q‖ * ‖m q‖ - ‖commutatorCoefficient P K c b m q‖)]

theorem localized_multiplier_energy_le_of_variation (P K Q : Finset G)
    (c b : G → 𝕜) (m : G → E) (eta : ℝ) (d : G → ℝ)
    (hmain : ∀ q ∈ Q, ‖m q‖ ≤ eta) (hd : ∀ p ∈ P, 0 ≤ d p)
    (hm : ∀ p ∈ P, ∀ k ∈ K, ‖m k - m (p + k)‖ ≤ d p)
    (hQ : ∀ p ∈ P, ∀ k ∈ K, p + k ∈ Q) :
    vectorEnergy Q (vectorConvolution P K c (fun k ↦ b k • m k)) ≤
      2 * eta ^ 2 * scalarEnergy Q (scalarConvolution P K c b) +
        2 * (∑ p ∈ P, ‖c p‖ * d p) ^ 2 * scalarEnergy K b := by
  have h1 := localized_multiplier_energy_le P K Q c b m eta hmain
  have h2 := commutator_energy_le P K Q c b m d hd hm hQ
  linarith only [h1, h2]

/-- Modes above the desired symbol threshold are charged explicitly, rather
than excluded by a support assumption. The global symbol bound controls
only this tail; the main term retains the smaller threshold. -/
theorem localized_multiplier_energy_le_with_tail (P K Q : Finset G)
    (c b : G → 𝕜) (m : G → E) (eta M : ℝ) (heta : 0 ≤ eta)
    (hglobal : ∀ q ∈ Q, ‖m q‖ ≤ M) :
    vectorEnergy Q (vectorConvolution P K c (fun k ↦ b k • m k)) ≤
      2 * eta ^ 2 * scalarEnergy Q (scalarConvolution P K c b) +
        2 * M ^ 2 * scalarEnergy (Q.filter (fun q ↦ eta < ‖m q‖))
          (scalarConvolution P K c b) +
        2 * vectorEnergy Q (commutatorCoefficient P K c b m) := by
  classical
  unfold vectorEnergy scalarEnergy
  rw [Finset.sum_filter]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro q hq
  rw [vectorConvolution_multiplier_eq]
  have hn := pow_le_pow_left₀ (norm_nonneg _)
    (norm_add_le (scalarConvolution P K c b q • m q)
      (commutatorCoefficient P K c b m q)) 2
  rw [norm_smul] at hn
  have hs := sq_nonneg (‖scalarConvolution P K c b q‖ * ‖m q‖ -
    ‖commutatorCoefficient P K c b m q‖)
  by_cases hbad : eta < ‖m q‖
  · simp only [if_pos hbad]
    have hm := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hglobal q hq) 2)
      (sq_nonneg ‖scalarConvolution P K c b q‖)
    have he := mul_nonneg (sq_nonneg eta) (sq_nonneg ‖scalarConvolution P K c b q‖)
    nlinarith only [hn, hs, hm, he]
  · simp only [if_neg hbad, mul_zero, add_zero]
    have hm := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) heta).mpr (le_of_not_gt hbad))
      (sq_nonneg ‖scalarConvolution P K c b q‖)
    nlinarith only [hn, hs, hm]

end Mettapedia.Analysis.FiniteMultiplierLocalization
