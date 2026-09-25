import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierUniqueness

/-!
# Global Fourier solutions

A `GlobalSolution` is a solution on `[0, ∞)` with local order-`m` bounds. If
tame solutions of order at least seven exist on every interval `[0, H)`,
uniqueness glues them into a single global solution, and every global
solution restricts to a tame solution on each finite interval. Its kinetic
energy never exceeds that of the data.

Each continuation theorem of the lane therefore upgrades to global existence:
`nonempty_globalSolution_of_vorticitySup` and its companions assume
finite-horizon bounds on `∫ ‖ω‖_∞`, `∫ D_Q`, the eighth moment, or the
order-one energy of every tame solution. Those bounds are the open dynamical
input.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierGlobalSolution

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeSobolevVelocityRate PancakeHigherSobolevWeights
open PancakeHigherSobolevVelocityRate PancakeCurlOutputTail PancakeLocalInfiniteVelocity
open PancakeCoefficientLimitEquation PancakeBlockReality PancakeGalerkinKineticEnergy
open PancakeHigherDerivativeMoments InfiniteConvectionEnergy InfiniteKineticCancellation
open FourierTameTriad FourierContinuation FourierTameContinuation FourierEighthMomentControl
open FourierVorticitySupContinuation FourierDyadicBlockContinuation FourierUniqueness
open LocalVorticityEighthMoment (meanEnergy)

/-- A solution on `[0, ∞)`: the constraints at every time, local Sobolev,
order-`m` and dissipation bounds on every finite interval, and the infinite
equation at every positive time. -/
structure GlobalSolution (nu : ℝ) (m : ℕ) (u₀ : FourierVelocity) where
  coefficients : ℝ → FourierVelocity
  continuous : ∀ q i, Continuous (fun t ↦ coefficients t q i)
  initial : coefficients 0 = u₀
  reality : ∀ t q, coefficients t (-q) = coefficientConjugate (coefficients t q)
  transverse : ∀ t q, modeDot q (coefficients t q) = 0
  zero : ∀ t, coefficients t 0 = 0
  sobolev_local : ∀ S, ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) S, ∀ F : Finset Wavevector,
    sobolevEnergy F (coefficients t) ≤ B
  order_local : ∀ S, ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) S, ∀ F : Finset Wavevector,
    velocityEnergy m F (coefficients t) ≤ B
  dissipation_local : ∀ S, ∃ X : ℝ, ∀ G : Finset Wavevector,
    ∫ τ in (0 : ℝ)..S, velocityDissipation m G (coefficients τ) ≤ X
  equation : ∀ t, 0 < t → ∀ q i,
    HasDerivAt (fun τ ↦ coefficients τ q i) (infiniteVelocityRHS nu (coefficients t) q i) t

variable {nu : ℝ} {m : ℕ} {u₀ : FourierVelocity}

/-- A global solution restricts to a tame solution on every finite interval. -/
def GlobalSolution.toTame (g : GlobalSolution nu m u₀) (H : ℝ) : TameSolutionOn nu m u₀ H where
  coefficients := g.coefficients
  continuous := g.continuous
  initial := g.initial
  reality := g.reality
  transverse := g.transverse
  zero := g.zero
  sobolev_local := fun S _ ↦ g.sobolev_local S
  equation := fun t ht ↦ g.equation t ht.1
  order_local := fun S _ ↦ g.order_local S
  dissipation_local := fun S _ ↦ g.dissipation_local S

/-- Tame solutions on different intervals agree on their common part. -/
theorem coefficients_eq_of_lt (hm : 7 ≤ m) (hnu : 0 < nu) {T T' : ℝ}
    (c : TameSolutionOn nu m u₀ T) (d : TameSolutionOn nu m u₀ T') {t : ℝ} (ht0 : 0 ≤ t)
    (hT : t < T) (hT' : t < T') : c.coefficients t = d.coefficients t :=
  FourierUniqueness.TameSolutionOn.coefficients_eq hm hnu (c.restrict (min_le_left T T'))
    (d.restrict (min_le_right T T')) t ⟨ht0, lt_min hT hT'⟩

/-- Global solutions are unique. -/
theorem GlobalSolution.coefficients_eq (hm : 7 ≤ m) (hnu : 0 < nu)
    (g g' : GlobalSolution nu m u₀) {t : ℝ} (ht : 0 ≤ t) :
    g.coefficients t = g'.coefficients t :=
  coefficients_eq_of_lt hm hnu (g.toTame (t + 1)) (g'.toTame (t + 1)) ht (by linarith)
    (by linarith)

section Glue

/-- The index of the solution used at time `t`. -/
def glueIndex (t : ℝ) : ℕ := ⌊max t 0⌋₊

theorem max_lt_glueIndex (t : ℝ) : max t 0 < (glueIndex t : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem lt_glueIndex (t : ℝ) : t < (glueIndex t : ℝ) + 1 :=
  (le_max_left t 0).trans_lt (max_lt_glueIndex t)

variable (c : ∀ n : ℕ, TameSolutionOn nu m u₀ ((n : ℝ) + 1))

/-- The glued coefficient curve; it is constant before time zero. -/
def glue (t : ℝ) : FourierVelocity := (c (glueIndex t)).coefficients (max t 0)

theorem glue_eq (hm : 7 ≤ m) (hnu : 0 < nu) (n : ℕ) {t : ℝ} (ht : t < (n : ℝ) + 1) :
    glue c t = (c n).coefficients (max t 0) :=
  coefficients_eq_of_lt hm hnu (c (glueIndex t)) (c n) (le_max_right t 0) (max_lt_glueIndex t)
    (max_lt ht (by positivity))

theorem glue_eq_of_nonneg (hm : 7 ≤ m) (hnu : 0 < nu) (n : ℕ) {t : ℝ} (h0 : 0 ≤ t)
    (ht : t < (n : ℝ) + 1) : glue c t = (c n).coefficients t := by
  rw [glue_eq c hm hnu n ht, max_eq_left h0]

/-- **Gluing.** Tame solutions on the intervals `[0, n + 1)` combine into one
global solution. -/
def glueSolution (hm : 7 ≤ m) (hnu : 0 < nu) : GlobalSolution nu m u₀ where
  coefficients := glue c
  continuous := by
    intro q i
    refine continuous_iff_continuousAt.mpr fun t ↦ ?_
    set n := glueIndex t
    have hcont : Continuous (fun s : ℝ ↦ (c n).coefficients (max s 0) q i) :=
      ((c n).continuous q i).comp (continuous_id.max continuous_const)
    refine hcont.continuousAt.congr ?_
    filter_upwards [Iio_mem_nhds (lt_glueIndex t)] with s hs
    rw [glue_eq c hm hnu n hs]
  initial := by
    rw [glue_eq_of_nonneg c hm hnu 0 le_rfl (by norm_num)]
    exact (c 0).initial
  reality := fun t q ↦ (c (glueIndex t)).reality (max t 0) q
  transverse := fun t q ↦ (c (glueIndex t)).transverse (max t 0) q
  zero := fun t ↦ (c (glueIndex t)).zero (max t 0)
  sobolev_local := by
    intro S
    obtain ⟨B, hB⟩ := (c (glueIndex S)).sobolev_local S (lt_glueIndex S)
    refine ⟨B, fun t ht F ↦ ?_⟩
    rw [glue_eq_of_nonneg c hm hnu (glueIndex S) ht.1 (ht.2.trans_lt (lt_glueIndex S))]
    exact hB t ht F
  order_local := by
    intro S
    obtain ⟨B, hB⟩ := (c (glueIndex S)).order_local S (lt_glueIndex S)
    refine ⟨B, fun t ht F ↦ ?_⟩
    rw [glue_eq_of_nonneg c hm hnu (glueIndex S) ht.1 (ht.2.trans_lt (lt_glueIndex S))]
    exact hB t ht F
  dissipation_local := by
    intro S
    rcases le_or_gt 0 S with hS | hS
    · obtain ⟨X, hX⟩ := (c (glueIndex S)).dissipation_local S (lt_glueIndex S)
      refine ⟨X, fun G ↦ le_of_eq_of_le ?_ (hX G)⟩
      refine intervalIntegral.integral_congr fun τ hτ ↦ ?_
      rw [uIcc_of_le hS] at hτ
      rw [glue_eq_of_nonneg c hm hnu (glueIndex S) hτ.1 (hτ.2.trans_lt (lt_glueIndex S))]
    · obtain ⟨X, hX⟩ := (c 0).dissipation_local 0 (by norm_num)
      refine ⟨0, fun G ↦ ?_⟩
      rw [intervalIntegral.integral_of_ge hS.le]
      have h : 0 ≤ ∫ τ in Ioc S 0, velocityDissipation m G (glue c τ) :=
        setIntegral_nonneg measurableSet_Ioc fun τ _ ↦ orderDissipation_nonneg m G _
      linarith
  equation := by
    intro t ht q i
    set n := glueIndex t
    have htn : t < (n : ℝ) + 1 := lt_glueIndex t
    have hd := (c n).equation t ⟨ht, htn⟩ q i
    rw [glue_eq_of_nonneg c hm hnu n ht.le htn]
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht htn] with s hs
    rw [glue_eq_of_nonneg c hm hnu n hs.1.le hs.2]

end Glue

/-- **Global existence from existence on every finite interval.** -/
theorem nonempty_globalSolution (hm : 7 ≤ m) (hnu : 0 < nu)
    (h : ∀ H, 0 < H → Nonempty (TameSolutionOn nu m u₀ H)) :
    Nonempty (GlobalSolution nu m u₀) :=
  ⟨glueSolution (fun n ↦ Classical.choice (h ((n : ℝ) + 1) (by positivity))) hm hnu⟩

/-- **Bounded kinetic energy.** The kinetic energy of a global solution never
exceeds that of its data. -/
theorem GlobalSolution.kineticEnergy_le (hm : 7 ≤ m) (hnu : 0 < nu)
    (g : GlobalSolution nu m u₀) {t : ℝ} (ht : 0 ≤ t) :
    kineticEnergy (g.coefficients t) ≤ kineticEnergy u₀ := by
  obtain ⟨B, s, hs, e, he, hSum, hu⟩ :=
    local_envelope_at hm (g.toTame (t + 1)) (show t < t + 1 by linarith)
  have hu2 : ∀ τ ∈ Icc (0 : ℝ) t, ∀ k, fourierMoment 2 (s.coefficients τ) k ≤ e k :=
    fun τ hτ k ↦ (fourierMoment_mono _ (by omega : 2 ≤ 3) k).trans (hu τ hτ k)
  have h := LocalKineticEnergy.energy_le_initial s hnu.le e he hSum hu2 t ⟨ht, le_rfl⟩
  rw [hs] at h
  exact h

section Assembly

variable (hm : 7 ≤ m) (hnu : 0 < nu) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
  (hd : ∀ q, modeDot q (u₀ q) = 0) (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀)
  (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀)
include hm hnu hr hd hz hE₀0 hE₀

/-- A unique global solution under a finite-horizon bound on `∫ ‖ω‖_∞`. -/
theorem nonempty_globalSolution_of_vorticitySup
    (hsup : ∀ H, 0 < H → ∃ A, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
      ∀ τ ∈ Ico (0 : ℝ) T, ∫ t in (0 : ℝ)..τ, vorticitySup (c.coefficients t) ≤ A) :
    Nonempty (GlobalSolution nu m u₀) :=
  nonempty_globalSolution hm hnu
    (exists_tameSolutionOn_of_vorticitySup m hm hnu u₀ hr hd hz hE₀0 hE₀ hsup)

/-- A unique global solution under a finite-horizon bound on `∫ D_Q`. -/
theorem nonempty_globalSolution_of_highBlockSum (Q : ℕ)
    (hhigh : ∀ H, 0 < H → ∃ A, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
      ∀ τ ∈ Ico (0 : ℝ) T, ∫ t in (0 : ℝ)..τ, highBlockSum Q (c.coefficients t) ≤ A) :
    Nonempty (GlobalSolution nu m u₀) :=
  nonempty_globalSolution hm hnu
    (exists_tameSolutionOn_of_highBlockSum m hm hnu u₀ hr hd hz hE₀0 hE₀ Q hhigh)

/-- A unique global solution under a finite-horizon eighth-moment bound. -/
theorem nonempty_globalSolution_of_meanEnergy
    (heighth : ∀ H, 0 < H → ∃ K₈, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
      ∀ τ ∈ Ico (0 : ℝ) T, meanEnergy (c.coefficients τ) ≤ K₈) :
    Nonempty (GlobalSolution nu m u₀) :=
  nonempty_globalSolution hm hnu
    (exists_tameSolutionOn_of_meanEnergy m (by omega) hnu u₀ hr hd hz hE₀0 hE₀ heighth)

end Assembly

end Mettapedia.FluidDynamics.NavierStokes.FourierGlobalSolution
