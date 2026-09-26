import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierVorticitySupContinuation

/-!
# Restarting and lowering the order of tame solutions

A tame solution of a higher order is a tame solution of every lower order
(`TameSolutionOn.ofLe`), and a tame solution restarted at a later time is a tame
solution from its value there (`TameSolutionOn.shift`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierTameRestart

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakeHigherSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeSobolevVelocityRate PancakeCurlOutputTail PancakeFrequencyProjectorCommutator
open FourierContinuation FourierTameContinuation FourierVorticitySupContinuation
open FourierInfiniteTameRate

section Constructions

variable {nu : ℝ} {u₀ : FourierVelocity} {T : ℝ}

/-- A tame solution of a higher order is a tame solution of every lower order. -/
def _root_.Mettapedia.FluidDynamics.NavierStokes.FourierTameContinuation.TameSolutionOn.ofLe {m m' : ℕ} (hmm' : m ≤ m') (c : TameSolutionOn nu m' u₀ T) :
    TameSolutionOn nu m u₀ T where
  toSolutionOn := c.toSolutionOn
  order_local := fun S hS ↦ by
    obtain ⟨B, hB⟩ := c.order_local S hS
    exact ⟨B, fun τ hτ F ↦ (velocityEnergy_le_of_order_le hmm' _ F).trans (hB τ hτ F)⟩
  dissipation_local := fun S hS ↦ by
    obtain ⟨X, hX⟩ := c.dissipation_local S hS
    refine ⟨max X 0, fun G ↦ ?_⟩
    rcases le_or_gt 0 S with hS0 | hS0
    · have hmono : ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients τ) ≤
          ∫ τ in (0 : ℝ)..S, velocityDissipation m' G (c.coefficients τ) := by
        refine intervalIntegral.integral_mono_on hS0
          ((continuous_velocityDissipation_along m G c.continuous).intervalIntegrable 0 S)
          ((continuous_velocityDissipation_along m' G c.continuous).intervalIntegrable 0 S)
          fun τ _ ↦ ?_
        unfold velocityDissipation orderDissipation orderEnergy
        refine Finset.sum_le_sum fun k _ ↦ ?_
        have hw : orderWeight m k ≤ orderWeight m' k :=
          pow_le_pow_right₀ (by linarith [norm_nonneg (frequencyVec k)]) hmm'
        have h0 : 0 ≤ orderWeight m k := by unfold orderWeight; positivity
        have ha : 0 ≤ ‖frequencyVec k‖ * amplitude (c.coefficients τ) k := by
          unfold amplitude; positivity
        exact pow_le_pow_left₀ (mul_nonneg h0 ha) (mul_le_mul_of_nonneg_right hw ha) 2
      exact hmono.trans ((hX G).trans (le_max_left _ _))
    · have h : ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients τ) ≤ 0 := by
        rw [intervalIntegral.integral_symm]
        have : 0 ≤ ∫ τ in S..(0 : ℝ), velocityDissipation m G (c.coefficients τ) :=
          intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hS0.le fun τ _ ↦
            orderDissipation_nonneg m G (amplitude (c.coefficients τ))
        change -(∫ τ in S..(0 : ℝ), velocityDissipation m G (c.coefficients τ)) ≤ 0
        linarith
      exact h.trans (le_max_right _ _)

/-- **Restarting a tame solution at a later time.** -/
def _root_.Mettapedia.FluidDynamics.NavierStokes.FourierTameContinuation.TameSolutionOn.shift {m : ℕ} (c : TameSolutionOn nu m u₀ T) {T₀ : ℝ} (h0 : 0 ≤ T₀) : TameSolutionOn nu m (c.coefficients T₀) (T - T₀) where
  coefficients := fun t ↦ c.coefficients (t + T₀)
  continuous := fun q i ↦ (c.continuous q i).comp (continuous_id.add continuous_const)
  initial := by simp
  reality := fun t q ↦ c.reality _ q
  transverse := fun t q ↦ c.transverse _ q
  zero := fun t ↦ c.zero _
  sobolev_local := fun S hS ↦ by
    obtain ⟨B, hB⟩ := c.sobolev_local (S + T₀) (by linarith)
    exact ⟨B, fun t ht F ↦ hB (t + T₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩ F⟩
  equation := fun t ht q i ↦ by
    have h := c.equation (t + T₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩ q i
    exact h.comp_add_const t T₀
  order_local := fun S hS ↦ by
    obtain ⟨B, hB⟩ := c.order_local (S + T₀) (by linarith)
    exact ⟨B, fun t ht F ↦ hB (t + T₀) ⟨by linarith [ht.1], by linarith [ht.2]⟩ F⟩
  dissipation_local := fun S hS ↦ by
    obtain ⟨X, hX⟩ := c.dissipation_local (S + T₀) (by linarith)
    refine ⟨max X 0, fun G ↦ ?_⟩
    have hc := continuous_velocityDissipation_along m G c.continuous
    have hsh : (∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients (τ + T₀))) =
        ∫ τ in T₀..(S + T₀), velocityDissipation m G (c.coefficients τ) := by
      have h := intervalIntegral.integral_comp_add_right
        (fun τ ↦ velocityDissipation m G (c.coefficients τ)) (a := 0) (b := S) T₀
      simpa only [zero_add] using h
    have hsplit : (∫ τ in T₀..(S + T₀), velocityDissipation m G (c.coefficients τ)) =
        (∫ τ in (0 : ℝ)..(S + T₀), velocityDissipation m G (c.coefficients τ)) -
          ∫ τ in (0 : ℝ)..T₀, velocityDissipation m G (c.coefficients τ) := by
      rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
    have hT₀ : 0 ≤ ∫ τ in (0 : ℝ)..T₀, velocityDissipation m G (c.coefficients τ) :=
      intervalIntegral.integral_nonneg h0 fun τ _ ↦
        orderDissipation_nonneg m G (amplitude (c.coefficients τ))
    change (∫ τ in (0 : ℝ)..S, velocityDissipation m G (c.coefficients (τ + T₀))) ≤ max X 0
    rw [hsh, hsplit]
    linarith [hX G, le_max_left X 0]

end Constructions

end Mettapedia.FluidDynamics.NavierStokes.FourierTameRestart
