import Mettapedia.Analysis.ODE.DampedGramEnergyEvolution
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Order.Filter.AtTopBot.Prod

/-!
# Absolutely convergent damped Gram series

A uniform positive lower bound on the damping rates and absolute
summability of the two Hilbert-space families suffice for the full
correlated pairing. Finite Gram energies converge to a nonnegative
infinite energy; orthogonality is not assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DampedGramEnergy

open scoped RealInnerProductSpace Topology
open Filter

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pairTerm (γ : ι → ℝ) (x y : ι → E) (p : ι × ι) : ℝ :=
  ⟪x p.1, y p.2⟫ / (γ p.1 + γ p.2)

def seriesPairing (γ : ι → ℝ) (x y : ι → E) : ℝ := ∑' p, pairTerm γ x y p

def seriesEnergy (γ : ι → ℝ) (x : ι → E) : ℝ := seriesPairing γ x x

theorem norm_pairTerm_le (γ : ι → ℝ) (x y : ι → E) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i) (p : ι × ι) :
    ‖pairTerm γ x y p‖ ≤ (‖x p.1‖ * ‖y p.2‖) / (2 * c) := by
  have hp : 0 < γ p.1 + γ p.2 := by linarith [hγ p.1, hγ p.2]
  rw [pairTerm, norm_div, Real.norm_of_nonneg hp.le]
  exact div_le_div₀ (by positivity) (norm_inner_le_norm _ _)
    (by positivity) (by linarith [hγ p.1, hγ p.2])

theorem summable_norm_pairTerm (γ : ι → ℝ) (x y : ι → E) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i)
    (hx : Summable (fun i ↦ ‖x i‖)) (hy : Summable (fun i ↦ ‖y i‖)) :
    Summable (fun p ↦ ‖pairTerm γ x y p‖) := by
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (norm_pairTerm_le γ x y hc hγ)
    ((hx.mul_of_nonneg hy (fun i ↦ norm_nonneg _) (fun i ↦ norm_nonneg _)).div_const (2 * c))

theorem tendsto_pairing (γ : ι → ℝ) (x y : ι → E) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i)
    (hx : Summable (fun i ↦ ‖x i‖)) (hy : Summable (fun i ↦ ‖y i‖)) :
    Tendsto (fun P : Finset ι ↦ pairing P γ x y) atTop (𝓝 (seriesPairing γ x y)) := by
  classical
  have h := (summable_norm_pairTerm γ x y hc hγ hx hy).of_norm.hasSum
  have hp : Tendsto (fun P : Finset ι ↦ P ×ˢ P) atTop atTop :=
    tendsto_finsetProd_atTop.comp tendsto_atTop_diagonal
  simpa only [Function.comp_def, pairing, seriesPairing, Finset.sum_product, pairTerm] using h.comp hp

theorem seriesEnergy_nonneg (γ : ι → ℝ) (x : ι → E) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i) (hx : Summable (fun i ↦ ‖x i‖)) :
    0 ≤ seriesEnergy γ x := by
  exact ge_of_tendsto (tendsto_pairing γ x x hc hγ hx hx)
    (Eventually.of_forall (fun P ↦ energy_nonneg P γ x (fun i _ ↦ hc.trans_le (hγ i))))

theorem norm_pairing_le (P : Finset ι) (γ : ι → ℝ) (x y : ι → E) {c : ℝ}
    (hc : 0 < c) (hγ : ∀ i, c ≤ γ i) :
    ‖pairing P γ x y‖ ≤ ((∑ i ∈ P, ‖x i‖) * (∑ j ∈ P, ‖y j‖)) / (2 * c) := by
  classical
  calc
    ‖pairing P γ x y‖ ≤ ∑ i ∈ P, ∑ j ∈ P, ‖pairTerm γ x y (i, j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ ↦ norm_sum_le _ _))
    _ ≤ ∑ i ∈ P, ∑ j ∈ P, (‖x i‖ * ‖y j‖) / (2 * c) :=
      Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ norm_pairTerm_le γ x y hc hγ (i, j)))
    _ = _ := by rw [Finset.sum_mul]; simp only [Finset.mul_sum, Finset.sum_div]

theorem norm_pairing_le_envelopes (P : Finset ι) (γ : ι → ℝ) (x y : ι → E)
    {c : ℝ} (hc : 0 < c) (hγ : ∀ i, c ≤ γ i)
    (a b : ι → ℝ) (ha : Summable a) (hb : Summable b)
    (hxa : ∀ i, ‖x i‖ ≤ a i) (hyb : ∀ i, ‖y i‖ ≤ b i) :
    ‖pairing P γ x y‖ ≤ ((∑' i, a i) * (∑' i, b i)) / (2 * c) := by
  have ha0 (i : ι) : 0 ≤ a i := (norm_nonneg _).trans (hxa i)
  have hb0 (i : ι) : 0 ≤ b i := (norm_nonneg _).trans (hyb i)
  have hsa : (∑ i ∈ P, ‖x i‖) ≤ ∑' i, a i :=
    (Finset.sum_le_sum (fun i _ ↦ hxa i)).trans (ha.sum_le_tsum P (fun i _ ↦ ha0 i))
  have hsb : (∑ i ∈ P, ‖y i‖) ≤ ∑' i, b i :=
    (Finset.sum_le_sum (fun i _ ↦ hyb i)).trans (hb.sum_le_tsum P (fun i _ ↦ hb0 i))
  exact (norm_pairing_le P γ x y hc hγ).trans (div_le_div_of_nonneg_right
    (mul_le_mul hsa hsb (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
      (tsum_nonneg ha0)) (by positivity))

end Mettapedia.Analysis.DampedGramEnergy
