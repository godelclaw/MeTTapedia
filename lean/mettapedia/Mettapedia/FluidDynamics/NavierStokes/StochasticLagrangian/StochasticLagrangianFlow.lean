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

Picard–Lindelöf also solves from any intermediate time
(`exists_noisyTrajectory_through`), and two trajectories that meet once coincide
(`noisyTrajectory_unique_of_eq_at`). So the flow map at each time is a bijection
of space, and its inverse is the back-to-labels map `A_t` of the Constantin–Iyer
representation `u = P 𝔼[(∇A)ᵀ u₀(A)]`. Grönwall's bound also runs backward
(`noisyTrajectory_dist_le_backward`), so both maps are Lipschitz, and the periodic
velocity makes both commute with integer translations, so they descend to the
torus (`exists_noisyFlow`, `exists_stochasticFlow`).

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

/-- Integer translations do not move points of the torus. -/
theorem torusPoint_add_intVec (x : X3) (k : Fin 3 → ℤ) :
    torusPoint (x + fun i ↦ (k i : ℝ)) = torusPoint x := by
  funext i
  simp only [torusPoint, Pi.add_apply, AddCircle.coe_add, add_eq_left]
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k i, by simp⟩

/-- The velocity seen at the displaced position is periodic. -/
theorem noisyVelocity_add_intVec (s : LocalInfiniteVelocitySolution nu u₀ T B) (a : ℝ → X3)
    (t : ℝ) (y : X3) (k : Fin 3 → ℤ) :
    noisyVelocity s a t (y + fun i ↦ (k i : ℝ)) = noisyVelocity s a t y := by
  unfold noisyVelocity liftedVelocity
  rw [add_right_comm, torusPoint_add_intVec]

/-- **Trajectories commute with the lattice.** A trajectory shifted by a vector of
integers is again a trajectory, since the velocity is periodic. -/
theorem noisyTrajectory_add_intVec (s : LocalInfiniteVelocitySolution nu u₀ T B)
    {a : ℝ → X3} {Y : ℝ → X3}
    (hY : ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (noisyVelocity s a τ (Y τ)) (Icc (0 : ℝ) T) τ)
    (k : Fin 3 → ℤ) :
    ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun σ ↦ Y σ + fun i ↦ (k i : ℝ))
      (noisyVelocity s a τ (Y τ + fun i ↦ (k i : ℝ))) (Icc (0 : ℝ) T) τ := fun τ hτ ↦ by
  rw [noisyVelocity_add_intVec]
  exact (hY τ hτ).add_const _

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

/-- **Trajectories through a prescribed point at a prescribed time.** For every time
`t` of the local interval and every point `z` there is a trajectory on the whole
local interval that passes through `z` at time `t`. Read backward, it names the
label that arrives at `z`. -/
theorem exists_noisyTrajectory_through (hT : 0 ≤ T) {a : ℝ → X3}
    (ha : ContinuousOn a (Icc (0 : ℝ) T)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (z : X3) :
    ∃ Z : ℝ → X3, Z t = z ∧
      ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt Z (noisyVelocity s a τ (Z τ)) (Icc (0 : ℝ) T) τ := by
  let L : ℝ≥0 := ⟨∑' q, g q, tsum_nonneg hg⟩
  let K : ℝ≥0 := Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q)
  let r : ℝ≥0 := ⟨(L : ℝ) * T, mul_nonneg L.2 hT⟩
  have hp : IsPicardLindelof (noisyVelocity s a) (⟨t, ht⟩ : Icc (0 : ℝ) T)
      z r 0 L K := {
    lipschitzOnWith := fun τ hτ ↦
      (lipschitzWith_noisyVelocity s g hg hSum hu a τ hτ).lipschitzOnWith
    continuousOn := fun y _ ↦ noisyVelocity_continuousOn s ha y
    norm_le := fun τ hτ y _ ↦ norm_noisyVelocity_le s g hg hSum hu a τ hτ y
    mul_max_le := by
      show (L : ℝ) * max (T - t) (t - 0) ≤ (L : ℝ) * T - ((0 : ℝ≥0) : ℝ)
      rw [NNReal.coe_zero, sub_zero, sub_zero]
      exact mul_le_mul_of_nonneg_left (max_le (by linarith [ht.1]) ht.2) L.2 }
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- **Existence of the noisy trajectories.** For every continuous path and every
initial point there is a trajectory on the whole local interval. -/
theorem exists_noisyTrajectory (hT : 0 ≤ T) {a : ℝ → X3} (ha : ContinuousOn a (Icc (0 : ℝ) T))
    (x : X3) :
    ∃ Y : ℝ → X3, Y 0 = x ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (noisyVelocity s a t (Y t)) (Icc (0 : ℝ) T) t :=
  exists_noisyTrajectory_through s g hg hSum hu hT ha ⟨le_rfl, hT⟩ x

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

/-- **Trajectories that meet once coincide.** Two trajectories that pass through the
same point at any one time of the local interval agree on the whole interval,
before that time as well as after it. -/
theorem noisyTrajectory_unique_of_eq_at (a : ℝ → X3) (Y Y' : ℝ → X3)
    (hY : ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (noisyVelocity s a τ (Y τ)) (Icc (0 : ℝ) T) τ)
    (hY' : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Y' (noisyVelocity s a τ (Y' τ)) (Icc (0 : ℝ) T) τ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (heq : Y t = Y' t) : EqOn Y Y' (Icc (0 : ℝ) T) := by
  have hK : ∀ τ ∈ Icc (0 : ℝ) T,
      LipschitzOnWith (Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q))
        (noisyVelocity s a τ) univ :=
    fun τ hτ ↦ (lipschitzWith_noisyVelocity s g hg hSum hu a τ hτ).lipschitzOnWith
  rw [← Icc_union_Icc_eq_Icc ht.1 ht.2]
  apply EqOn.union
  · exact ODE_solution_unique_of_mem_Icc_left (s := fun _ ↦ univ)
      (fun τ hτ ↦ hK τ ⟨hτ.1.le, hτ.2.trans ht.2⟩)
      ((HasDerivWithinAt.continuousOn hY).mono (Icc_subset_Icc_right ht.2))
      (fun τ hτ ↦ (hY τ ⟨hτ.1.le, hτ.2.trans ht.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨hτ.1, hτ.2.trans ht.2⟩))
      (fun _ _ ↦ mem_univ _)
      ((HasDerivWithinAt.continuousOn hY').mono (Icc_subset_Icc_right ht.2))
      (fun τ hτ ↦ (hY' τ ⟨hτ.1.le, hτ.2.trans ht.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨hτ.1, hτ.2.trans ht.2⟩))
      (fun _ _ ↦ mem_univ _) heq
  · exact ODE_solution_unique_of_mem_Icc_right (s := fun _ ↦ univ)
      (fun τ hτ ↦ hK τ ⟨ht.1.trans hτ.1, hτ.2.le⟩)
      ((HasDerivWithinAt.continuousOn hY).mono (Icc_subset_Icc_left ht.1))
      (fun τ hτ ↦ (hY τ ⟨ht.1.trans hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht.1.trans hτ.1, hτ.2⟩))
      (fun _ _ ↦ mem_univ _)
      ((HasDerivWithinAt.continuousOn hY').mono (Icc_subset_Icc_left ht.1))
      (fun τ hτ ↦ (hY' τ ⟨ht.1.trans hτ.1, hτ.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht.1.trans hτ.1, hτ.2⟩))
      (fun _ _ ↦ mem_univ _) heq

/-- **Labels depend Lipschitz on the arrival point.** Two trajectories that are close
at a time `t` of the local interval started close: Grönwall's bound also runs
backward in time. -/
theorem noisyTrajectory_dist_le_backward (a : ℝ → X3) (Y Y' : ℝ → X3)
    (hY : ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt Y (noisyVelocity s a τ (Y τ)) (Icc (0 : ℝ) T) τ)
    (hY' : ∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt Y' (noisyVelocity s a τ (Y' τ)) (Icc (0 : ℝ) T) τ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    dist (Y 0) (Y' 0) ≤ dist (Y t) (Y' t) *
      Real.exp ((Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q) : ℝ) * t) := by
  have hmaps : MapsTo (fun τ : ℝ ↦ t - τ) (Icc (0 : ℝ) t) (Icc (0 : ℝ) T) :=
    fun τ hτ ↦ ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
  -- run each trajectory backward from time `t`
  have hrev : ∀ Z : ℝ → X3,
      (∀ τ ∈ Icc (0 : ℝ) T,
        HasDerivWithinAt Z (noisyVelocity s a τ (Z τ)) (Icc (0 : ℝ) T) τ) →
      ContinuousOn (fun τ ↦ Z (t - τ)) (Icc (0 : ℝ) t) ∧
      ∀ τ ∈ Ico (0 : ℝ) t, HasDerivWithinAt (fun τ ↦ Z (t - τ))
        (-noisyVelocity s a (t - τ) (Z (t - τ))) (Ici τ) τ := by
    intro Z hZ
    refine ⟨(HasDerivWithinAt.continuousOn hZ).comp
      (continuous_const.sub continuous_id).continuousOn hmaps, fun τ hτ ↦ ?_⟩
    have hmem : t - τ ∈ Ioc (0 : ℝ) T := ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
    have hZ' : HasDerivWithinAt Z (noisyVelocity s a (t - τ) (Z (t - τ))) (Iic (t - τ))
        (t - τ) :=
      (hZ (t - τ) (Ioc_subset_Icc_self hmem)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem hmem)
    have hh : HasDerivWithinAt (fun σ : ℝ ↦ t - σ) (-1) (Ici τ) τ :=
      ((hasDerivAt_id' τ).const_sub t).hasDerivWithinAt
    have hcomp := hZ'.scomp τ hh (fun σ hσ ↦ by
      simp only [mem_Iic, mem_Ici] at hσ ⊢
      linarith)
    simpa [Function.comp_def] using hcomp
  obtain ⟨hfc, hfd⟩ := hrev Y hY
  obtain ⟨hgc, hgd⟩ := hrev Y' hY'
  have h := dist_le_of_trajectories_ODE_of_mem
    (v := fun τ y ↦ -noisyVelocity s a (t - τ) y) (s := fun _ ↦ (univ : Set X3))
    (fun τ hτ ↦ (lipschitzWith_noisyVelocity s g hg hSum hu a (t - τ)
      (hmaps (Ico_subset_Icc_self hτ))).neg.lipschitzOnWith)
    hfc hfd (fun _ _ ↦ mem_univ _) hgc hgd (fun _ _ ↦ mem_univ _)
    (le_refl (dist (Y (t - 0)) (Y' (t - 0)))) t ⟨ht.1, le_rfl⟩
  simpa only [sub_self, sub_zero] using h

/-- **The flow map at each time is a bi-Lipschitz bijection that commutes with the
lattice.** For every continuous path and every time `t` of the local interval there
is a bijection `e` of space that sends each label to the position of its trajectory
at time `t`. Its inverse sends each position to the label that arrives there. Both
are Lipschitz with the Grönwall constant, and both commute with integer
translations, so they descend to the torus. -/
theorem exists_noisyFlow (hT : 0 ≤ T) {a : ℝ → X3} (ha : ContinuousOn a (Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ e : X3 ≃ X3,
      (∀ Y : ℝ → X3, (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt Y (noisyVelocity s a τ (Y τ)) (Icc (0 : ℝ) T) τ) →
        e (Y 0) = Y t) ∧
      LipschitzWith (Real.toNNReal (Real.exp
        ((Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q) : ℝ) * t))) e ∧
      LipschitzWith (Real.toNNReal (Real.exp
        ((Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q) : ℝ) * t))) e.symm ∧
      ∀ x (k : Fin 3 → ℤ), e (x + fun i ↦ (k i : ℝ)) = e x + fun i ↦ (k i : ℝ) := by
  -- the trajectory from each label, and the trajectory through each point at time `t`
  choose Y hY0 hY using fun x ↦ exists_noisyTrajectory s g hg hSum hu hT ha x
  choose Z hZt hZ using fun z ↦ exists_noisyTrajectory_through s g hg hSum hu hT ha ht z
  have hflow : ∀ W : ℝ → X3, (∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt W (noisyVelocity s a τ (W τ)) (Icc (0 : ℝ) T) τ) → Y (W 0) t = W t :=
    fun W hW ↦ noisyTrajectory_unique s g hg hSum hu a _ _ (hY (W 0)) hW (hY0 _) ht
  have hlabel : ∀ W : ℝ → X3, (∀ τ ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt W (noisyVelocity s a τ (W τ)) (Icc (0 : ℝ) T) τ) → Z (W t) 0 = W 0 :=
    fun W hW ↦ noisyTrajectory_unique_of_eq_at s g hg hSum hu a _ _ (hZ (W t)) hW ht (hZt _)
      ⟨le_rfl, hT⟩
  let e : X3 ≃ X3 :=
    { toFun := fun x ↦ Y x t
      invFun := fun z ↦ Z z 0
      left_inv := fun x ↦ by
        show Z (Y x t) 0 = x
        rw [hlabel (Y x) (hY x), hY0]
      right_inv := fun z ↦ by
        show Y (Z z 0) t = z
        rw [hflow (Z z) (hZ z), hZt] }
  have hexp : 0 ≤ Real.exp ((Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q) : ℝ) * t) :=
    (Real.exp_pos _).le
  refine ⟨e, fun W hW ↦ hflow W hW, ?_, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x x'
    rw [Real.coe_toNNReal _ hexp]
    have h := noisyTrajectory_dist_le s g hg hSum hu a (Y x) (Y x') (hY x) (hY x') t ht
    rw [hY0, hY0] at h
    exact h.trans_eq (mul_comm _ _)
  · apply LipschitzWith.of_dist_le_mul
    intro z z'
    rw [Real.coe_toNNReal _ hexp]
    have h := noisyTrajectory_dist_le_backward s g hg hSum hu a (Z z) (Z z') (hZ z) (hZ z') ht
    rw [hZt, hZt] at h
    exact h.trans_eq (mul_comm _ _)
  · intro x k
    show Y (x + fun i ↦ (k i : ℝ)) t = Y x t + fun i ↦ (k i : ℝ)
    have h := hflow (fun σ ↦ Y x σ + fun i ↦ (k i : ℝ)) (noisyTrajectory_add_intVec s (hY x) k)
    simpa only [hY0] using h

/-- **The stochastic Lagrangian flow and its back-to-labels map, path by path.** For
every continuous path `a`, for instance `√(2ν)` times a Brownian path, and every time
`t` of the local interval, the stochastic flow `X_t`, which sends each label to the
position `Y(t) + a(t)` of its stochastic trajectory, is a bijection of space. Its
inverse is the back-to-labels map `A_t` of the Constantin–Iyer representation. Both
are Lipschitz with the Grönwall constant and commute with integer translations. -/
theorem exists_stochasticFlow (hT : 0 ≤ T) {a : ℝ → X3} (ha : ContinuousOn a (Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ X : X3 ≃ X3,
      (∀ Y : ℝ → X3, (∀ τ ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt Y (noisyVelocity s a τ (Y τ)) (Icc (0 : ℝ) T) τ) →
        X (Y 0) = Y t + a t) ∧
      LipschitzWith (Real.toNNReal (Real.exp
        ((Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q) : ℝ) * t))) X ∧
      LipschitzWith (Real.toNNReal (Real.exp
        ((Real.toNNReal (3 * (2 * Real.pi) * ∑' q, g q) : ℝ) * t))) X.symm ∧
      ∀ x (k : Fin 3 → ℤ), X (x + fun i ↦ (k i : ℝ)) = X x + fun i ↦ (k i : ℝ) := by
  obtain ⟨e, he, hL, hL', hk⟩ := exists_noisyFlow s g hg hSum hu hT ha ht
  refine ⟨e.trans (Equiv.addRight (a t)), fun Y hY ↦ ?_, ?_, ?_, fun x k ↦ ?_⟩
  · simp only [Equiv.trans_apply, Equiv.coe_addRight, he Y hY]
  · apply LipschitzWith.of_dist_le_mul
    intro x x'
    simp only [Equiv.trans_apply, Equiv.coe_addRight, dist_add_right]
    exact hL.dist_le_mul x x'
  · apply LipschitzWith.of_dist_le_mul
    intro z z'
    simp only [Equiv.symm_trans_apply, Equiv.addRight_symm, Equiv.coe_addRight]
    exact (hL'.dist_le_mul _ _).trans_eq (by rw [dist_add_right])
  · simp only [Equiv.trans_apply, Equiv.coe_addRight, hk]
    abel

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
