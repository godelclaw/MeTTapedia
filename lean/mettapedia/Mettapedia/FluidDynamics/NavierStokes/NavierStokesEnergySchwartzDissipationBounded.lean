import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyIdentities

/-!
# Navier-Stokes Energy: Schwartz Dissipation Bounded Energy

Semantic layer split from `NavierStokesEnergySchwartzDissipation`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- Uniformly bounded scalar coefficients keep a two-profile Schwartz
superposition in the concrete bounded-energy class. -/
theorem boundedKineticEnergy_of_add_scalar_smul_schwartz_of_abs_le
    (a b : ℝ → ℝ) (f g : 𝓢(NSSpace, NSSpace)) (A B : ℝ)
    (haBound : ∀ t, |a t| ≤ A)
    (hbBound : ∀ t, |b t| ≤ B) :
    boundedKineticEnergy (fun s y => a s • f y + b s • g y) := by
  let u : NSVelocityField := fun s y => a s • f y + b s • g y
  have hA : 0 ≤ A := by
    nlinarith [abs_nonneg (a 0), haBound 0]
  have hB : 0 ≤ B := by
    nlinarith [abs_nonneg (b 0), hbBound 0]
  let C : ℝ :=
    (2 * A ^ (2 : ℕ)) * ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume +
      (2 * B ^ (2 : ℕ)) * ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume
  have hIntF :
      Integrable (fun x : NSSpace => (2 * A ^ (2 : ℕ)) * ‖f x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz f).const_mul (2 * A ^ (2 : ℕ))
  have hIntG :
      Integrable (fun x : NSSpace => (2 * B ^ (2 : ℕ)) * ‖g x‖ ^ (2 : ℕ)) := by
    exact (integrable_norm_sq_of_schwartz g).const_mul (2 * B ^ (2 : ℕ))
  have hIntF_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℕ) ∂volume := by
    refine integral_nonneg_of_ae ?_
    filter_upwards with x
    positivity
  have hIntG_nonneg : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume := by
    refine integral_nonneg_of_ae ?_
    filter_upwards with x
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    nlinarith [hIntF_nonneg, hIntG_nonneg]
  refine ⟨C, hC, ?_⟩
  intro t
  have hPointwise :
      ∀ x : NSSpace,
        kineticEnergyDensity u t x ≤
          (2 * A ^ (2 : ℕ)) * ‖f x‖ ^ (2 : ℕ) +
            (2 * B ^ (2 : ℕ)) * ‖g x‖ ^ (2 : ℕ) := by
    intro x
    have hMulF : |a t| * ‖f x‖ ≤ A * ‖f x‖ := by
      nlinarith [haBound t, norm_nonneg (f x)]
    have hMulG : |b t| * ‖g x‖ ≤ B * ‖g x‖ := by
      nlinarith [hbBound t, norm_nonneg (g x)]
    have hNorm :
        ‖a t • f x + b t • g x‖ ≤ A * ‖f x‖ + B * ‖g x‖ := by
      calc
        ‖a t • f x + b t • g x‖ ≤ ‖a t • f x‖ + ‖b t • g x‖ := norm_add_le _ _
        _ = |a t| * ‖f x‖ + |b t| * ‖g x‖ := by simp [norm_smul]
        _ ≤ A * ‖f x‖ + B * ‖g x‖ := by linarith
    have hX_nonneg : 0 ≤ A * ‖f x‖ := by positivity
    have hY_nonneg : 0 ≤ B * ‖g x‖ := by positivity
    have hSq :
        ‖a t • f x + b t • g x‖ ^ (2 : ℕ) ≤
          (A * ‖f x‖ + B * ‖g x‖) ^ (2 : ℕ) := by
      nlinarith [hNorm, norm_nonneg (a t • f x + b t • g x), hX_nonneg, hY_nonneg]
    have hSumSq :
        (A * ‖f x‖ + B * ‖g x‖) ^ (2 : ℕ) ≤
          2 * (A * ‖f x‖) ^ (2 : ℕ) + 2 * (B * ‖g x‖) ^ (2 : ℕ) := by
      nlinarith [two_mul_le_add_sq (A * ‖f x‖) (B * ‖g x‖)]
    calc
      kineticEnergyDensity u t x = ‖a t • f x + b t • g x‖ ^ (2 : ℕ) := by rfl
      _ ≤ (A * ‖f x‖ + B * ‖g x‖) ^ (2 : ℕ) := hSq
      _ ≤ 2 * (A * ‖f x‖) ^ (2 : ℕ) + 2 * (B * ‖g x‖) ^ (2 : ℕ) := hSumSq
      _ = (2 * A ^ (2 : ℕ)) * ‖f x‖ ^ (2 : ℕ) +
            (2 * B ^ (2 : ℕ)) * ‖g x‖ ^ (2 : ℕ) := by
            ring
  have hMeas :
      AEStronglyMeasurable (kineticEnergyDensity u t) (volume : Measure NSSpace) := by
    have hCont :
        Continuous (fun x : NSSpace => kineticEnergyDensity u t x) := by
      simpa [u, kineticEnergyDensity] using
        (((f.continuous.const_smul (a t)).add (g.continuous.const_smul (b t))).norm.pow 2)
    exact hCont.aestronglyMeasurable
  have hIntDensity : Integrable (kineticEnergyDensity u t) := by
    refine Integrable.mono' (hIntF.add hIntG) hMeas ?_
    filter_upwards with x
    have hDensity_nonneg : 0 ≤ kineticEnergyDensity u t x := by
      simp [u, kineticEnergyDensity]
    simpa [Real.norm_eq_abs, abs_of_nonneg hDensity_nonneg] using hPointwise x
  refine ⟨hIntDensity, ?_⟩
  calc
    kineticEnergyAt u t = ∫ x, kineticEnergyDensity u t x ∂volume := by rfl
    _ ≤ ∫ x,
          ((2 * A ^ (2 : ℕ)) * ‖f x‖ ^ (2 : ℕ) +
            (2 * B ^ (2 : ℕ)) * ‖g x‖ ^ (2 : ℕ)) ∂volume := by
          exact integral_mono hIntDensity (hIntF.add hIntG) hPointwise
    _ = C := by
          dsimp [C]
          rw [integral_add hIntF hIntG, integral_const_mul, integral_const_mul]

end NavierStokes
end FluidDynamics
end Mettapedia
