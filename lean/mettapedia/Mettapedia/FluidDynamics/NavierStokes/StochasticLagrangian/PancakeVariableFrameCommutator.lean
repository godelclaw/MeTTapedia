import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFrameCovariance
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicOperatorKernel

/-!
# Freezing a spatially varying pancake-frame multiplier

The strain eigendirections defining the actual pancake sector depend on
space.  Thus the field projector is a pseudodifferential operator rather than
the translation-invariant fixed-frame multiplier.  This module records the
exact finite-Fourier freezing identity.

At a base point `x₀`, the variable-symbol action is the frozen multiplier
plus a frame-variation remainder.  The latter is bounded by the frequencywise
operator oscillation times the actual Fourier amplitudes.  The identity makes
the additional analytic obligation explicit: slow Littlewood--Paley
variation or a near-degeneracy alternative must control this remainder.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeVariableFrameCommutator

open scoped BigOperators
open PeriodicFourierTriad
open PancakePeriodicOperatorKernel

/-- Finite Fourier action of an operator symbol depending on the observation
point as well as frequency. -/
def finiteVariableSymbolAction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Torus3 → Wavevector → (E →L[ℂ] E))
    (coeff : Wavevector → E) (x : Torus3) : E :=
  ∑ k ∈ s, UnitAddTorus.mFourier k x • symbol x k (coeff k)

/-- Translation-invariant symbol obtained by freezing the spatial parameter
at `x₀`, evaluated at an arbitrary observation point `x`. -/
def finiteFrozenSymbolAction {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Torus3 → Wavevector → (E →L[ℂ] E))
    (coeff : Wavevector → E) (x₀ x : Torus3) : E :=
  ∑ k ∈ s, UnitAddTorus.mFourier k x • symbol x₀ k (coeff k)

/-- Exact frame-freezing remainder. -/
def finiteFrameVariationRemainder {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Torus3 → Wavevector → (E →L[ℂ] E))
    (coeff : Wavevector → E) (x₀ x : Torus3) : E :=
  ∑ k ∈ s, UnitAddTorus.mFourier k x •
    (symbol x k - symbol x₀ k) (coeff k)

/-- **Exact variable/frozen split.** -/
theorem variable_eq_frozen_add_remainder {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Torus3 → Wavevector → (E →L[ℂ] E))
    (coeff : Wavevector → E) (x₀ x : Torus3) :
    finiteVariableSymbolAction s symbol coeff x =
      finiteFrozenSymbolAction s symbol coeff x₀ x +
        finiteFrameVariationRemainder s symbol coeff x₀ x := by
  unfold finiteVariableSymbolAction finiteFrozenSymbolAction
    finiteFrameVariationRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← smul_add]
  congr 1
  simp

/-- Quantitative bound for the exact frame-variation remainder. -/
theorem norm_frameVariationRemainder_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Torus3 → Wavevector → (E →L[ℂ] E))
    (coeff : Wavevector → E) (x₀ x : Torus3) :
    ‖finiteFrameVariationRemainder s symbol coeff x₀ x‖ ≤
      ∑ k ∈ s, ‖symbol x k - symbol x₀ k‖ * ‖coeff k‖ := by
  unfold finiteFrameVariationRemainder
  calc
    ‖∑ k ∈ s, UnitAddTorus.mFourier k x •
        (symbol x k - symbol x₀ k) (coeff k)‖ ≤
        ∑ k ∈ s, ‖UnitAddTorus.mFourier k x •
          (symbol x k - symbol x₀ k) (coeff k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ s, ‖symbol x k - symbol x₀ k‖ * ‖coeff k‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_smul]
      simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk,
        norm_prod, Circle.norm_coe, Finset.prod_const_one, one_mul]
      exact ContinuousLinearMap.le_opNorm _ _

/-- Uniform symbol oscillation converts the remainder to the actual
frequency-amplitude mass. -/
theorem norm_frameVariationRemainder_le_of_oscillation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset Wavevector) (symbol : Torus3 → Wavevector → (E →L[ℂ] E))
    (coeff : Wavevector → E) (x₀ x : Torus3) (epsilon : ℝ)
    (hosc : ∀ k ∈ s, ‖symbol x k - symbol x₀ k‖ ≤ epsilon) :
    ‖finiteFrameVariationRemainder s symbol coeff x₀ x‖ ≤
      epsilon * ∑ k ∈ s, ‖coeff k‖ := by
  refine (norm_frameVariationRemainder_le s symbol coeff x₀ x).trans ?_
  calc
    ∑ k ∈ s, ‖symbol x k - symbol x₀ k‖ * ‖coeff k‖ ≤
        ∑ k ∈ s, epsilon * ‖coeff k‖ := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hosc k hk) (norm_nonneg _)
    _ = epsilon * ∑ k ∈ s, ‖coeff k‖ := by rw [Finset.mul_sum]

end PancakeVariableFrameCommutator
end NavierStokes
end FluidDynamics
end Mettapedia
