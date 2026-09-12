import Mettapedia.Analysis.SignedCrossKernel
import Mathlib.MeasureTheory.Group.Prod

/-! # Signed exchange for integrable, possibly unbounded kernels -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.SignedCrossKernel

open MeasureTheory EuclideanCrossProduct RadialPower
open scoped RealInnerProductSpace
local notation "R3" => EuclideanSpace ℝ (Fin 3)

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
  (H : X → X → R3 →L[ℝ] R3) (w : X → R3)

/-- Almost-everywhere exchange symmetry suffices; no representative on the
exceptional set is chosen or evaluated along a trajectory. -/
theorem integral_weightedStretch_eq_half_pair_of_integrable_of_ae_symmetry (n : ℕ)
    (hi : Integrable (fun p : X × X ↦ weightedStretch n (H p.1 p.2) (w p.1) (w p.2)) (μ.prod μ))
    (hs : ∀ᵐ p : X × X ∂μ.prod μ, H p.2 p.1 = H p.1 p.2) :
    (∫ x, ∫ y, weightedStretch n (H x y) (w x) (w y) ∂μ ∂μ) =
      (1 / 2 : ℝ) * ∫ x, ∫ y, pairedStretch n (H x y) (w x) (w y) ∂μ ∂μ := by
  have hj := hi.swap
  change Integrable (fun p : X × X ↦
    weightedStretch n (H p.2 p.1) (w p.2) (w p.1)) (μ.prod μ) at hj
  have he : (fun p : X × X ↦ pairedStretch n (H p.1 p.2) (w p.1) (w p.2)) =ᵐ[μ.prod μ]
      (fun p ↦ weightedStretch n (H p.1 p.2) (w p.1) (w p.2) +
        weightedStretch n (H p.2 p.1) (w p.2) (w p.1)) := by
    filter_upwards [hs] with p hp
    rw [hp, weightedStretch_add_swap]
  have hp := (hi.add hj).congr he.symm
  rw [← integral_prod _ hi, ← integral_prod _ hp, integral_congr_ae he]
  have hswap := integral_prod_swap (μ := μ) (ν := μ)
    (fun p : X × X ↦ weightedStretch n (H p.1 p.2) (w p.1) (w p.2))
  simp only [Prod.fst_swap, Prod.snd_swap] at hswap
  rw [integral_add hi hj, hswap]
  ring

theorem integral_weightedStretch_eq_half_pair_of_integrable (n : ℕ)
    (hi : Integrable (fun p : X × X ↦ weightedStretch n (H p.1 p.2) (w p.1) (w p.2)) (μ.prod μ))
    (hs : ∀ x y, H y x = H x y) :
    (∫ x, ∫ y, weightedStretch n (H x y) (w x) (w y) ∂μ ∂μ) =
      (1 / 2 : ℝ) * ∫ x, ∫ y, pairedStretch n (H x y) (w x) (w y) ∂μ ∂μ := by
  have hj := hi.swap
  change Integrable (fun p : X × X ↦
    weightedStretch n (H p.2 p.1) (w p.2) (w p.1)) (μ.prod μ) at hj
  have he (p : X × X) : pairedStretch n (H p.1 p.2) (w p.1) (w p.2) =
      weightedStretch n (H p.1 p.2) (w p.1) (w p.2) +
        weightedStretch n (H p.2 p.1) (w p.2) (w p.1) := by
    rw [hs p.1 p.2, weightedStretch_add_swap]
  have hp : Integrable (fun p : X × X ↦ pairedStretch n (H p.1 p.2) (w p.1) (w p.2)) (μ.prod μ) := by
    simp_rw [he]
    exact hi.add hj
  rw [← integral_prod _ hi, ← integral_prod _ hp]
  simp_rw [he]
  have hswap := integral_prod_swap (μ := μ) (ν := μ)
    (fun p : X × X ↦ weightedStretch n (H p.1 p.2) (w p.1) (w p.2))
  simp only [Prod.fst_swap, Prod.snd_swap] at hswap
  rw [integral_add hi hj, hswap]
  ring

/-- Integrability, rather than continuity of the kernel, suffices for the signed split. -/
theorem abs_integral_paired_sub_high_le_of_integrable (n : ℕ) (L : ℝ) (hL : 0 < L)
    (hp : Integrable (fun p : X × X ↦ pairedStretch (2 * n) (H p.1 p.2)
      (w p.1) (w p.2)) (μ.prod μ))
    (hh : Integrable (fun p : X × X ↦ highAmplitudeStretch (2 * n) L (H p.1 p.2)
      (w p.1) (w p.2)) (μ.prod μ))
    (hb : Integrable (fun p : X × X ↦ ‖H p.1 p.2‖ *
      ‖radialPower n (w p.1) - radialPower n (w p.2)‖ ^ 2) (μ.prod μ)) :
    |(∫ x, ∫ y, pairedStretch (2 * n) (H x y) (w x) (w y) ∂μ ∂μ) -
      (∫ x, ∫ y, highAmplitudeStretch (2 * n) L (H x y) (w x) (w y) ∂μ ∂μ)| ≤
      4 * L * ∫ x, ∫ y, ‖H x y‖ * ‖radialPower n (w x) - radialPower n (w y)‖ ^ 2 ∂μ ∂μ := by
  rw [← integral_prod _ hp, ← integral_prod _ hh, ← integral_prod _ hb, ← integral_sub hp hh]
  apply abs_integral_le_integral_abs.trans
  rw [← integral_const_mul]
  apply integral_mono (hp.sub hh).abs (hb.const_mul (4 * L))
  intro p
  change |pairedStretch (2 * n) (H p.1 p.2) (w p.1) (w p.2) -
    highAmplitudeStretch (2 * n) L (H p.1 p.2) (w p.1) (w p.2)| ≤ _
  rw [pairedStretch_sub_highAmplitudeStretch]
  simpa only [mul_assoc] using
    abs_lowAmplitudeWeight_mul_pairedStretch_double_le n L hL (H p.1 p.2) (w p.1) (w p.2)

end Mettapedia.Analysis.SignedCrossKernel
