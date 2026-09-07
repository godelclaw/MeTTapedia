import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalMaterialStrain
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePeriodicLipschitz

/-!
# Compatibility of the material flow with the torus quotient

Trajectories whose initial lifts represent the same torus point continue
to represent the same particle. Uniqueness, not a chosen representative,
supplies this compatibility.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeMaterialFlowQuotient

open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeLocalInfiniteVelocity
open PancakeLocalMaterialTrajectories PancakeLocalMaterialFlow PancakeFourierMaterialPaths
open PancakePeriodicLipschitz PancakeCurlOutputTail

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

theorem torusPoint_add (x y : X3) : torusPoint (x + y) = torusPoint x + torusPoint y := rfl

theorem torusPoint_sub (x y : X3) : torusPoint (x - y) = torusPoint x - torusPoint y := rfl

theorem liftedVelocity_period {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B) (t : ℝ) (x d : X3)
    (hd : torusPoint d = 0) :
    liftedVelocity s t (x + d) = liftedVelocity s t x := by
  change (fun i ↦ (PancakeLocalSpatialVelocity.spatialField s t (torusPoint (x + d)) i).re) = _
  rw [torusPoint_add, hd, add_zero]
  rfl

theorem materialTrajectory_quotient {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients τ) q ≤ g q)
    (X Y : ℝ → X3)
    (hX : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt X (liftedVelocity s t (X t)) (Set.Icc (0 : ℝ) T) t)
    (hY : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt Y (liftedVelocity s t (Y t)) (Set.Icc (0 : ℝ) T) t)
    (h0 : torusPoint (X 0) = torusPoint (Y 0)) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    torusPoint (X t) = torusPoint (Y t) := by
  let d : X3 := Y 0 - X 0
  have hd : torusPoint d = 0 := by simp only [d, torusPoint_sub, h0, sub_self]
  have hs : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun r ↦ X r + d) (liftedVelocity s τ (X τ + d)) (Set.Icc (0 : ℝ) T) τ := by
    intro τ hτ
    rw [liftedVelocity_period s τ (X τ) d hd]
    exact (hX τ hτ).add_const d
  have he := materialTrajectory_unique s g hg hSum hu (fun r ↦ X r + d) Y hs hY
    (by dsimp [d]; abel) ht
  have hp := congrArg torusPoint he
  simpa only [torusPoint_add, hd, add_zero] using hp

theorem exists_torus_materialFlow {nu T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients τ) q ≤ g q)
    (Φ : X3 → ℝ → X3) (h0 : ∀ x, Φ x 0 = x)
    (hΦ : ∀ x t, t ∈ Set.Icc (0 : ℝ) T →
      HasDerivWithinAt (Φ x) (liftedVelocity s t (Φ x t)) (Set.Icc (0 : ℝ) T) t) :
    ∃ Ψ : T3 → ℝ → T3, (∀ x, Ψ x 0 = x) ∧
      ∀ x t, t ∈ Set.Icc (0 : ℝ) T → Ψ (torusPoint x) t = torusPoint (Φ x t) := by
  choose rep hrep _hnorm using torusPoint_bounded_rep
  refine ⟨fun x t ↦ torusPoint (Φ (rep x) t), fun x ↦ by
    change torusPoint (Φ (rep x) 0) = x
    rw [h0, hrep], ?_⟩
  intro x t ht
  exact materialTrajectory_quotient s g hg hSum hu (Φ (rep (torusPoint x))) (Φ x)
    (hΦ _) (hΦ _) (by rw [h0, h0, hrep]) t ht

end Mettapedia.FluidDynamics.NavierStokes.PancakeMaterialFlowQuotient
