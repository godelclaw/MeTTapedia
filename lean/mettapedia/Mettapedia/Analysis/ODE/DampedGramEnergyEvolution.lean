import Mettapedia.Analysis.ODE.DampedGramEnergy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A correlated time budget for differently damped components

The Gram energy dissipates the squared norm of the entire sum. Its
nonlinear work remains signed. This handles arbitrary interference
without replacing the sum by a mode-count times the diagonal energy.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.DampedGramEnergy

open scoped RealInnerProductSpace
open MeasureTheory

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuous_pairing {X : Type*} [TopologicalSpace X]
    (P : Finset ι) (γ : ι → ℝ) (x y : X → ι → E)
    (hx : ∀ i ∈ P, Continuous (fun t ↦ x t i))
    (hy : ∀ i ∈ P, Continuous (fun t ↦ y t i)) :
    Continuous (fun t ↦ pairing P γ (x t) (y t)) := by
  unfold pairing
  exact continuous_finsetSum P (fun i hi ↦ continuous_finsetSum P (fun j hj ↦
    ((hx i hi).inner (hy j hj)).div_const _))

theorem hasDerivAt_pairing (P : Finset ι) (γ : ι → ℝ)
    (x y : ℝ → ι → E) (dx dy : ι → E) (t : ℝ)
    (hx : ∀ i ∈ P, HasDerivAt (fun τ ↦ x τ i) (dx i) t)
    (hy : ∀ i ∈ P, HasDerivAt (fun τ ↦ y τ i) (dy i) t) :
    HasDerivAt (fun τ ↦ pairing P γ (x τ) (y τ))
      (pairing P γ dx (y t) + pairing P γ (x t) dy) t := by
  have h := HasDerivAt.fun_sum (fun i hi ↦ HasDerivAt.fun_sum
    (fun j hj ↦ ((hx i hi).inner ℝ (hy j hj)).div_const (γ i + γ j)))
  apply h.congr_deriv
  simp only [pairing, add_div, Finset.sum_add_distrib]
  ring

/-- The dissipation is the squared norm of the sum, including every cross term. -/
theorem hasDerivAt_energy_of_damped (P : Finset ι) (γ : ι → ℝ)
    (hγ : ∀ i ∈ P, 0 < γ i) (x : ℝ → ι → E) (r : ι → E) (t : ℝ)
    (hx : ∀ i ∈ P, HasDerivAt (fun τ ↦ x τ i) (r i - γ i • x t i) t) :
    HasDerivAt (fun τ ↦ energy P γ (x τ))
      (2 * pairing P γ r (x t) - ‖∑ i ∈ P, x t i‖ ^ 2) t := by
  have h := hasDerivAt_pairing P γ x x _ _ t hx hx
  apply h.congr_deriv
  change pairing P γ (r - fun i ↦ γ i • x t i) (x t) +
    pairing P γ (x t) (r - fun i ↦ γ i • x t i) = _
  rw [pairing_sub_left, pairing_sub_right, pairing_symmetric P γ (x t) r]
  have hd := pairing_damping_add P γ (x t) (x t) hγ
  rw [real_inner_self_eq_norm_sq] at hd
  linarith

theorem energy_identity_of_damped (P : Finset ι) (γ : ι → ℝ)
    (hγ : ∀ i ∈ P, 0 < γ i) (x r : ℝ → ι → E)
    (t : ℝ) (ht : 0 ≤ t)
    (hx : ∀ i ∈ P, ContinuousOn (fun τ ↦ x τ i) (Set.Icc 0 t))
    (hr : ∀ i ∈ P, ContinuousOn (fun τ ↦ r τ i) (Set.Icc 0 t))
    (he : ∀ τ ∈ Set.Ioo 0 t, ∀ i ∈ P,
      HasDerivAt (fun s ↦ x s i) (r τ i - γ i • x τ i) τ) :
    energy P γ (x t) + (∫ τ in (0 : ℝ)..t, ‖∑ i ∈ P, x τ i‖ ^ 2) =
      energy P γ (x 0) + 2 * (∫ τ in (0 : ℝ)..t, pairing P γ (r τ) (x τ)) := by
  have hE : ContinuousOn (fun τ ↦ energy P γ (x τ)) (Set.Icc 0 t) :=
    continuousOn_iff_continuous_restrict.mpr (continuous_pairing P γ _ _
      (fun i hi ↦ continuousOn_iff_continuous_restrict.mp (hx i hi))
      (fun i hi ↦ continuousOn_iff_continuous_restrict.mp (hx i hi)))
  have hW : ContinuousOn (fun τ ↦ pairing P γ (r τ) (x τ)) (Set.Icc 0 t) :=
    continuousOn_iff_continuous_restrict.mpr (continuous_pairing P γ _ _
      (fun i hi ↦ continuousOn_iff_continuous_restrict.mp (hr i hi))
      (fun i hi ↦ continuousOn_iff_continuous_restrict.mp (hx i hi)))
  have hD : ContinuousOn (fun τ ↦ ‖∑ i ∈ P, x τ i‖ ^ 2) (Set.Icc 0 t) :=
    (continuousOn_finsetSum P hx).norm.pow 2
  have hiW := hW.intervalIntegrable_of_Icc ht (μ := volume)
  have hiD := hD.intervalIntegrable_of_Icc ht (μ := volume)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hE
    (fun τ hτ ↦ hasDerivAt_energy_of_damped P γ hγ x (r τ) τ (he τ hτ))
    ((hiW.const_mul 2).sub hiD)
  rw [intervalIntegral.integral_sub (hiW.const_mul 2) hiD,
    intervalIntegral.integral_const_mul] at h
  linarith

theorem integral_norm_sum_sq_le_of_damped (P : Finset ι) (γ : ι → ℝ)
    (hγ : ∀ i ∈ P, 0 < γ i) (x r : ℝ → ι → E)
    (t : ℝ) (ht : 0 ≤ t)
    (hx : ∀ i ∈ P, ContinuousOn (fun τ ↦ x τ i) (Set.Icc 0 t))
    (hr : ∀ i ∈ P, ContinuousOn (fun τ ↦ r τ i) (Set.Icc 0 t))
    (he : ∀ τ ∈ Set.Ioo 0 t, ∀ i ∈ P,
      HasDerivAt (fun s ↦ x s i) (r τ i - γ i • x τ i) τ) :
    (∫ τ in (0 : ℝ)..t, ‖∑ i ∈ P, x τ i‖ ^ 2) ≤
      energy P γ (x 0) + 2 * (∫ τ in (0 : ℝ)..t, pairing P γ (r τ) (x τ)) := by
  have h := energy_identity_of_damped P γ hγ x r t ht hx hr he
  have hn := energy_nonneg P γ (x t) hγ
  linarith

end Mettapedia.Analysis.DampedGramEnergy
