import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalMaterialFlow
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMaterialFlowQuotient
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierUniqueness

/-!
# The stochastic Lagrangian flow of the actual solution, path by path

In the stochastic Lagrangian formulation of Constantin and Iyer a particle
obeys `dX = u(X, t) dt + √(2ν) dW`. The noise is additive and the same at every
point, so for each continuous path `a = √(2ν) W` the equation is solved by
`X = Y + a`, where `Y` follows the velocity seen at the displaced position:

```text
Y' = u(Y + a(t), t),   Y(0) = x.
```

For the actual local solution this velocity is bounded and uniformly Lipschitz
in space on the local interval, and continuous in time whenever the path is.
Picard–Lindelöf constructs `Y` from every initial point for every continuous
path (`exists_noisyTrajectory`), Grönwall's inequality makes it unique and
Lipschitz in the initial point (`noisyTrajectory_unique`,
`noisyTrajectory_dist_le`), and Lipschitz in the path in the uniform distance
(`noisyTrajectory_dist_path_le`). Composed with any process with continuous
paths, for instance a Brownian motion, this gives the stochastic Lagrangian
trajectories of the actual solution realization by realization.

No Brownian motion is constructed here, and neither the Constantin–Iyer
representation nor Itô's formula is claimed; those need a path measure and
stochastic calculus.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangianFlow

open scoped BigOperators NNReal
open PeriodicFourierTriad PancakeLocalInfiniteVelocity PancakeLocalMaterialTrajectories
open PancakeLocalSpatialVelocity PancakeFourierMaterialPaths PancakeCurlOutputTail
open Set Metric

local notation "T3" => UnitAddTorus (Fin 3)
local notation "X3" => Fin 3 → ℝ

theorem continuous_torusPoint : Continuous (torusPoint : X3 → T3) :=
  continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- The velocity at the noise-displaced position `y + a(t)`. -/
def noisyVelocity (s : LocalInfiniteVelocitySolution nu u₀ T B) (a : ℝ → X3) (t : ℝ) (y : X3) :
    X3 :=
  liftedVelocity s t (y + a t)

theorem noisyVelocity_continuousOn (s : LocalInfiniteVelocitySolution nu u₀ T B) {a : ℝ → X3}
    (ha : ContinuousOn a (Icc (0 : ℝ) T)) (y : X3) :
    ContinuousOn (fun t ↦ noisyVelocity s a t y) (Icc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_pi
  intro i
  have hpath : Continuous (fun t : Icc (0 : ℝ) T ↦ torusPoint (y + a t)) :=
    continuous_torusPoint.comp (continuous_const.add (continuousOn_iff_continuous_domRestrict.mp ha))
  have hjoint : Continuous (fun t : Icc (0 : ℝ) T ↦ spatialField s t (torusPoint (y + a t))) :=
    (spatialField_joint_continuous s).comp (continuous_id.prodMk hpath)
  exact Complex.continuous_re.comp ((continuous_apply i).comp hjoint)

section Main

variable (s : LocalInfiniteVelocitySolution nu u₀ T B)
  (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
  (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients t) q ≤ g q)

include hg hSum hu

theorem norm_noisyVelocity_le (a : ℝ → X3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (y : X3) :
    ‖noisyVelocity s a t y‖ ≤ ∑' q, g q :=
  norm_liftedVelocity_le s g hg hSum hu t ht (y + a t)

theorem lipschitzWith_noisyVelocity (a : ℝ → X3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    LipschitzWith (Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q)) (noisyVelocity s a t) := by
  have hL := lipschitzWith_liftedVelocity s g hg hSum hu t ht
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hL.dist_le_mul (x + a t) (y + a t)
  rwa [dist_add_right] at h

/-- **The velocity seen by the particle depends Lipschitz on the path.** -/
theorem dist_noisyVelocity_path_le (a a' : ℝ → X3) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (y : X3) :
    dist (noisyVelocity s a' t y) (noisyVelocity s a t y) ≤
      (3 * (2 * Real.pi) * ∑' q, g q) * dist (a' t) (a t) := by
  have hL := lipschitzWith_liftedVelocity s g hg hSum hu t ht
  have hgn : 0 ≤ 3 * (2 * Real.pi) * ∑' q, g q := mul_nonneg (by positivity) (tsum_nonneg hg)
  have h := hL.dist_le_mul (y + a' t) (y + a t)
  rw [dist_add_left, Real.coe_toNNReal _ hgn] at h
  exact h

/-- **Existence of the noisy trajectories.** For every continuous path and every
initial point there is a trajectory on the whole local interval. -/
theorem exists_noisyTrajectory (hT : 0 ≤ T) {a : ℝ → X3} (ha : ContinuousOn a (Icc (0 : ℝ) T))
    (x : X3) :
    ∃ Y : ℝ → X3, Y 0 = x ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (noisyVelocity s a t (Y t)) (Icc (0 : ℝ) T) t := by
  let L : ℝ≥0 := ⟨∑' q, g q, tsum_nonneg hg⟩
  let K : ℝ≥0 := Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q)
  let r : ℝ≥0 := ⟨(L : ℝ) * T, mul_nonneg L.2 hT⟩
  have hp : IsPicardLindelof (noisyVelocity s a) (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T)
      x r 0 L K := {
    lipschitzOnWith := fun t ht ↦
      (lipschitzWith_noisyVelocity s g hg hSum hu a t ht).lipschitzOnWith
    continuousOn := fun y _ ↦ noisyVelocity_continuousOn s ha y
    norm_le := fun t ht y _ ↦ norm_noisyVelocity_le s g hg hSum hu a t ht y
    mul_max_le := by simp only [sub_zero, sub_self, max_eq_left hT, NNReal.coe_zero]; exact le_rfl }
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- **Noisy trajectories depend Lipschitz on the initial point.** -/
theorem noisyTrajectory_dist_le (a : ℝ → X3) (Y Y' : ℝ → X3)
    (hY : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (noisyVelocity s a t (Y t)) (Icc (0 : ℝ) T) t)
    (hY' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y' (noisyVelocity s a t (Y' t)) (Icc (0 : ℝ) T) t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    dist (Y t) (Y' t) ≤ dist (Y 0) (Y' 0) *
      Real.exp ((Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q) : ℝ) * t) := by
  have h := dist_le_of_trajectories_ODE_of_mem
    (s := fun _ ↦ (univ : Set X3))
    (fun τ hτ ↦ (lipschitzWith_noisyVelocity s g hg hSum hu a τ ⟨hτ.1, hτ.2.le⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hY)
    (fun τ hτ ↦ (hY τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ))
    (fun _ _ ↦ mem_univ _) (HasDerivWithinAt.continuousOn hY')
    (fun τ hτ ↦ (hY' τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ))
    (fun _ _ ↦ mem_univ _) (le_refl (dist (Y 0) (Y' 0))) t ht
  simpa only [sub_zero] using h

/-- **Uniqueness of the noisy trajectories.** -/
theorem noisyTrajectory_unique (a : ℝ → X3) (Y Y' : ℝ → X3)
    (hY : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (noisyVelocity s a t (Y t)) (Icc (0 : ℝ) T) t)
    (hY' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y' (noisyVelocity s a t (Y' t)) (Icc (0 : ℝ) T) t)
    (h0 : Y 0 = Y' 0) : EqOn Y Y' (Icc (0 : ℝ) T) := by
  intro t ht
  have h := noisyTrajectory_dist_le s g hg hSum hu a Y Y' hY hY' t ht
  rw [h0, dist_self, zero_mul] at h
  exact dist_le_zero.mp h

/-- **Noisy trajectories depend Lipschitz on the path.** Two trajectories from the
same point, driven by paths that stay within `δ` of each other on the local
interval, stay within the Grönwall bound of `K δ` over the elapsed time. -/
theorem noisyTrajectory_dist_path_le (a a' : ℝ → X3) {δ : ℝ}
    (hδ : ∀ t ∈ Icc (0 : ℝ) T, dist (a' t) (a t) ≤ δ) (Y Y' : ℝ → X3)
    (hY : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (noisyVelocity s a t (Y t)) (Icc (0 : ℝ) T) t)
    (hY' : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Y' (noisyVelocity s a' t (Y' t)) (Icc (0 : ℝ) T) t)
    (h0 : Y 0 = Y' 0) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    dist (Y t) (Y' t) ≤ gronwallBound 0 (Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q) : ℝ)
      (0 + (3 * (2 * Real.pi) * ∑' q, g q) * δ) (t - 0) := by
  have hgn : 0 ≤ 3 * (2 * Real.pi) * ∑' q, g q := mul_nonneg (by positivity) (tsum_nonneg hg)
  refine dist_le_of_approx_trajectories_ODE_of_mem
    (s := fun _ ↦ (univ : Set X3)) (v := noisyVelocity s a)
    (fun τ hτ ↦ (lipschitzWith_noisyVelocity s g hg hSum hu a τ ⟨hτ.1, hτ.2.le⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hY)
    (fun τ hτ ↦ (hY τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ))
    (fun τ _ ↦ by rw [dist_self])
    (fun _ _ ↦ mem_univ _) (HasDerivWithinAt.continuousOn hY')
    (fun τ hτ ↦ (hY' τ ⟨hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hτ))
    (fun τ hτ ↦ (dist_noisyVelocity_path_le s g hg hSum hu a a' τ ⟨hτ.1, hτ.2.le⟩ (Y' τ)).trans
      (mul_le_mul_of_nonneg_left (hδ τ ⟨hτ.1, hτ.2.le⟩) hgn))
    (fun _ _ ↦ mem_univ _) (by rw [h0, dist_self]) t ht

omit hg hSum hu in
/-- The stochastic Lagrangian trajectory `X = Y + a`: with `a = √(2ν) W` it solves
`dX = u(X, t) dt + √(2ν) dW` path by path, since the noise is additive. -/
theorem hasDerivWithinAt_stochasticTrajectory {a : ℝ → X3} {a' : ℝ → X3} {Y : ℝ → X3}
    {t : ℝ} (hY : HasDerivWithinAt Y (noisyVelocity s a t (Y t)) (Icc (0 : ℝ) T) t)
    (ha : HasDerivWithinAt a (a' t) (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt (fun r ↦ Y r + a r) (liftedVelocity s t (Y t + a t) + a' t)
      (Icc (0 : ℝ) T) t :=
  hY.add ha

end Main

section Tame

open FourierTameContinuation FourierUniqueness PancakeHigherDerivativeMoments

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity} {T : ℝ}

/-- **The stochastic Lagrangian trajectories of every tame solution.** For a tame
solution of order at least seven from admissible data, every earlier time `S`,
every continuous path `a` and every initial point, the noisy trajectory
`Y' = u(Y + a(t), t)` exists on `[0, S]` and is unique there; `X = Y + a` is the
stochastic Lagrangian trajectory driven by `a`. -/
theorem existsUnique_noisyTrajectory_of_tame (hm : 7 ≤ m) (c : TameSolutionOn nu m u₀ T)
    {S : ℝ} (hS : 0 ≤ S) (hST : S < T) :
    ∃ B, ∃ s : LocalInfiniteVelocitySolution nu u₀ S B, s.coefficients = c.coefficients ∧
      ∀ a : ℝ → X3, ContinuousOn a (Icc (0 : ℝ) S) → ∀ x : X3,
        ∃ Y : ℝ → X3, Y 0 = x ∧
          (∀ t ∈ Icc (0 : ℝ) S, HasDerivWithinAt Y (noisyVelocity s a t (Y t)) (Icc (0 : ℝ) S) t) ∧
          ∀ Y' : ℝ → X3, Y' 0 = x →
            (∀ t ∈ Icc (0 : ℝ) S,
              HasDerivWithinAt Y' (noisyVelocity s a t (Y' t)) (Icc (0 : ℝ) S) t) →
            EqOn Y Y' (Icc (0 : ℝ) S) := by
  obtain ⟨B, s, hs, g, hg, hSum, hu3⟩ := local_envelope_at hm c hST
  have hu1 : ∀ t ∈ Icc (0 : ℝ) S, ∀ q, fourierMoment 1 (s.coefficients t) q ≤ g q :=
    fun t ht q ↦ (fourierMoment_mono _ (by omega : 1 ≤ 3) q).trans (hu3 t ht q)
  refine ⟨B, s, hs, fun a ha x ↦ ?_⟩
  obtain ⟨Y, hY0, hY⟩ := exists_noisyTrajectory s g hg hSum hu1 hS ha x
  exact ⟨Y, hY0, hY, fun Y' hY'0 hY' ↦
    noisyTrajectory_unique s g hg hSum hu1 a Y Y' hY hY' (by rw [hY0, hY'0])⟩

end Tame

section Paths

variable {nu T B : ℝ} {u₀ : FourierVelocity}

/-- **Realization by realization.** For any process with continuous paths, for
instance `√(2ν)` times a Brownian motion, every realization drives a unique noisy
trajectory of the actual local solution from every initial point. -/
theorem existsUnique_noisyTrajectory_of_process {Ω : Type*}
    (s : LocalInfiniteVelocitySolution nu u₀ T B)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Icc (0 : ℝ) T, ∀ q, fourierMoment 1 (s.coefficients t) q ≤ g q)
    (hT : 0 ≤ T) (W : ℝ → Ω → X3) (hW : ∀ ω, Continuous (fun t ↦ W t ω)) (ω : Ω) (x : X3) :
    ∃ Y : ℝ → X3, Y 0 = x ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt Y (noisyVelocity s (fun t ↦ W t ω) t (Y t)) (Icc (0 : ℝ) T) t) ∧
      ∀ Y' : ℝ → X3, Y' 0 = x →
        (∀ t ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt Y' (noisyVelocity s (fun t ↦ W t ω) t (Y' t)) (Icc (0 : ℝ) T) t) →
        EqOn Y Y' (Icc (0 : ℝ) T) := by
  obtain ⟨Y, hY0, hY⟩ := exists_noisyTrajectory s g hg hSum hu hT (hW ω).continuousOn x
  exact ⟨Y, hY0, hY, fun Y' hY'0 hY' ↦
    noisyTrajectory_unique s g hg hSum hu _ Y Y' hY hY' (by rw [hY0, hY'0])⟩

end Paths

end Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangianFlow
