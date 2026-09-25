import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierOfficialEquation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierRegularityEquivalence
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPlanarRegularity

/-!
# Global solutions of every order

A solution of order `m'` is a solution of every lower order `m ≤ m'`: the
energies and dissipations grow with the order. Conversely, a global solution of
order `m ≥ 7` controls `∫ ‖ω‖_∞` on every finite horizon, a quantity that does
not depend on the order, so data admissible of a higher order `m'` have a
global solution of order `m'` too. For data admissible of every order the
coefficients are therefore bounded in every Sobolev order on bounded time
intervals, which is the rapid decay the physical fields need.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierAllOrders

open scoped BigOperators Topology
open MeasureTheory Set Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeHigherSobolevVelocityRate
open PancakeHigherSobolevWeights PancakeCurlOutputTail PancakeBlockReality
open PancakeHigherDerivativeMoments PancakeFrequencyProjectorCommutator
open FourierContinuation FourierTameContinuation FourierInfiniteTameRate
open FourierUniqueness FourierGlobalSolution FourierRegularityEquivalence
open FourierVorticitySupContinuation FourierTimeRegularity FourierOfficialEquation

variable {nu : ℝ} {m m' : ℕ} {u₀ : FourierVelocity}

theorem orderWeight_sq_mono (h : m ≤ m') (k : Wavevector) :
    orderWeight m k ^ 2 ≤ orderWeight m' k ^ 2 := by
  unfold orderWeight
  gcongr
  linarith [norm_nonneg (frequencyVec k)]

theorem velocityEnergy_mono (h : m ≤ m') (F : Finset Wavevector) (u : FourierVelocity) :
    velocityEnergy m F u ≤ velocityEnergy m' F u := by
  rw [velocityEnergy_eq, velocityEnergy_eq]
  exact Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right (orderWeight_sq_mono h k)
    (FourierSmallData.coefficientEnergy_nonneg' _)

theorem velocityDissipation_mono (h : m ≤ m') (F : Finset Wavevector) (u : FourierVelocity) :
    velocityDissipation m F u ≤ velocityDissipation m' F u := by
  rw [velocityDissipation_eq, velocityDissipation_eq]
  exact Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (orderWeight_sq_mono h k) (by positivity))
    (FourierSmallData.coefficientEnergy_nonneg' _)

/-- Integrated dissipation of a lower order is bounded by that of a higher
order, and is nonpositive on negative horizons. -/
theorem integral_dissipation_le {c : ℝ → FourierVelocity}
    (hc : ∀ q i, Continuous (fun t ↦ c t q i)) (h : m ≤ m') (G : Finset Wavevector) {S X : ℝ}
    (hX : ∫ τ in (0 : ℝ)..S, velocityDissipation m' G (c τ) ≤ X) :
    ∫ τ in (0 : ℝ)..S, velocityDissipation m G (c τ) ≤ max X 0 := by
  rcases le_total 0 S with hS | hS
  · refine le_trans ?_ (hX.trans (le_max_left _ _))
    exact intervalIntegral.integral_mono_on hS
      ((continuous_velocityDissipation_along m G hc).intervalIntegrable 0 S)
      ((continuous_velocityDissipation_along m' G hc).intervalIntegrable 0 S)
      fun τ _ ↦ velocityDissipation_mono h G _
  · rw [intervalIntegral.integral_symm]
    have h0 : 0 ≤ ∫ τ in S..0, velocityDissipation m G (c τ) :=
      intervalIntegral.integral_nonneg hS fun τ _ ↦ orderDissipation_nonneg m G _
    linarith [le_max_right X 0]

/-- A tame solution of order `m'` is a tame solution of every lower order. -/
def TameSolutionOn.lower {T : ℝ} (c : TameSolutionOn nu m' u₀ T) (h : m ≤ m') :
    TameSolutionOn nu m u₀ T where
  toSolutionOn := c.toSolutionOn
  order_local S hS := by
    obtain ⟨B, hB⟩ := c.order_local S hS
    exact ⟨B, fun τ hτ F ↦ (velocityEnergy_mono h F _).trans (hB τ hτ F)⟩
  dissipation_local S hS := by
    obtain ⟨X, hX⟩ := c.dissipation_local S hS
    exact ⟨max X 0, fun G ↦ integral_dissipation_le c.continuous h G (hX G)⟩

/-- A global solution of order `m'` is a global solution of every lower order. -/
def GlobalSolution.lower (g : GlobalSolution nu m' u₀) (h : m ≤ m') : GlobalSolution nu m u₀ where
  coefficients := g.coefficients
  continuous := g.continuous
  initial := g.initial
  reality := g.reality
  transverse := g.transverse
  zero := g.zero
  sobolev_local := g.sobolev_local
  order_local S := by
    obtain ⟨B, hB⟩ := g.order_local S
    exact ⟨B, fun τ hτ F ↦ (velocityEnergy_mono h F _).trans (hB τ hτ F)⟩
  dissipation_local S := by
    obtain ⟨X, hX⟩ := g.dissipation_local S
    exact ⟨max X 0, fun G ↦ integral_dissipation_le g.continuous h G (hX G)⟩
  equation := g.equation

/-- **Raising the order.** A global solution of order `m ≥ 7` gives a global
solution of every higher order for which the data are admissible. -/
theorem nonempty_globalSolution_of_le (hm : 7 ≤ m) (hmm' : m ≤ m') (hnu : 0 < nu)
    (g : GlobalSolution nu m u₀) (hu : Admissible m' u₀) : Nonempty (GlobalSolution nu m' u₀) := by
  obtain ⟨hr, hd, hz, E₀, hE₀⟩ := hu
  have hE₀0 : 0 ≤ E₀ := le_trans (by simp [velocityEnergy_eq]) (hE₀ ∅)
  have hEm : ∀ F, velocityEnergy m F u₀ ≤ E₀ := fun F ↦ (velocityEnergy_mono hmm' F u₀).trans (hE₀ F)
  have hg := (nonempty_globalSolution_iff_vorticitySup hm hnu hr hd hz hE₀0 hEm).mp ⟨g⟩
  refine (nonempty_globalSolution_iff_vorticitySup (hm.trans hmm') hnu hr hd hz hE₀0 hE₀).mpr
    fun H hH ↦ ?_
  obtain ⟨A, hA⟩ := hg H hH
  exact ⟨A, fun T hT c τ hτ ↦ hA T hT (TameSolutionOn.lower c hmm') τ hτ⟩

theorem fourierMoment_le_sqrt {u : FourierVelocity} {B : ℝ}
    (hB : ∀ F : Finset Wavevector, velocityEnergy m F u ≤ B) (k : Wavevector) :
    fourierMoment m u k ≤ Real.sqrt B := by
  have h := hB {k}
  rw [velocityEnergy_eq, Finset.sum_singleton, ← norm_coefficientVec_sq] at h
  have e : fourierMoment m u k ^ 2 = orderWeight m k ^ 2 * ‖coefficientVec (u k)‖ ^ 2 := by
    unfold fourierMoment orderWeight
    ring
  rw [← e] at h
  exact Real.le_sqrt_of_sq_le h

/-- **Rapid decay of the solutions.** For data admissible of every order, a
global solution of order `m ≥ 7` is a Fourier solution: its coefficients have
bounded Fourier moments of every order on bounded time intervals. -/
theorem fourierSolution_of_globalSolution (hm : 7 ≤ m) (hnu : 0 < nu)
    (g : GlobalSolution nu m u₀) (hu : ∀ n, Admissible n u₀) :
    FourierSolution nu g.coefficients where
  continuous := g.continuous
  reality := g.reality
  transverse := g.transverse
  equation := g.equation
  rapid S _ n := by
    obtain ⟨g'⟩ := nonempty_globalSolution_of_le hm (le_max_right n m) hnu g (hu (max n m))
    obtain ⟨B, hB⟩ := g'.order_local S
    refine ⟨Real.sqrt B, fun t ht k ↦ ?_⟩
    have heq : g.coefficients t = g'.coefficients t :=
      GlobalSolution.coefficients_eq hm hnu g (GlobalSolution.lower g' (le_max_right n m)) ht.1
    rw [heq]
    exact (fourierMoment_mono _ (le_max_left n m) k).trans
      (fourierMoment_le_sqrt (hB t ht) k)

end Mettapedia.FluidDynamics.NavierStokes.FourierAllOrders
