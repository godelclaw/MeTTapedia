import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierInitialData

/-!
# Fourier regularity in the form of the official periodic statement

Every smooth, divergence-free, one-periodic initial velocity has Fourier data
admissible of every order after its mean is removed. A global solution of the
Fourier system of one order `m ≥ 7` for these data therefore gives, through
rapid decay, the Galilean frame of the mean and the physical fields, a smooth
periodic solution of the official statement with zero force.

Consequences:

* `periodicStatementB_of_periodicRegularity`: global regularity of the Fourier
  class of one order `m ≥ 7` implies the official periodic statement
  (`PeriodicStatementB`). The hypothesis is open; it is equivalent to a bound
  on `∫ ‖ω‖_∞` over finite horizons (`periodicRegularity_iff_vorticitySup`).
* `exists_official_of_small`: data whose fluctuation is small in the Sobolev
  energy of order `m ≥ 5` have smooth periodic solutions in the official sense,
  unconditionally.
* `exists_official_of_planar`: planar data (independent of the third
  coordinate, with no third component) of any size have smooth periodic
  solutions in the official sense, unconditionally.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierOfficialTheorems

open scoped BigOperators Topology ContDiff
open Set Filter
open PeriodicFourierTriad PancakeHigherSobolevVelocityRate PancakePeriodicVorticityEquation
open FourierTimeRegularity FourierPhysicalFields FourierSpatialCalculus FourierOfficialEquation
open FourierGalilean FourierAllOrders FourierInitialData FourierGlobalSolution
open FourierRegularityEquivalence FourierPlanarRegularity OfficialPeriodicProblem

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {nu : ℝ} {u₀ : ℝ³ → ℝ³}

/-- **From a global Fourier solution to the official statement.** A global
solution of order `m ≥ 7` for the fluctuation data of a smooth periodic initial
velocity gives a smooth periodic solution of the official statement. -/
theorem exists_official_of_globalSolution (hnu : 0 < nu)
    (hu₀ : InitialVelocityConditionPeriodic u₀) {m : ℕ} (hm : 7 ≤ m)
    (g : GlobalSolution nu m (fluctuation u₀)) :
    ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ (fun _ _ ↦ 0) v p := by
  have hF := fourierSolution_galilean
    (fourierSolution_of_globalSolution hm hnu g (admissible_fluctuation hu₀)) g.zero (meanOf u₀)
  have h0 : Rapid (g.coefficients 0) := by
    rw [g.initial]
    exact rapid_fluctuation hu₀.smooth hu₀.isOnePeriodic
  have hinit : (fun x ↦ physVelocity (galilean (meanOf u₀) g.coefficients) x 0) = u₀ := by
    funext x
    rw [physVelocity_galilean_zero h0, physVelocity_eq, g.initial,
      ← eq_mean_add_realField hu₀.smooth hu₀.isOnePeriodic x]
  refine ⟨physVelocity (galilean (meanOf u₀) g.coefficients),
    physPressure (galilean (meanOf u₀) g.coefficients), ?_⟩
  have h := navierStokesPeriodic_of_fourierSolution hF
  rwa [hinit] at h

/-- **The conditional theorem.** Global regularity of the Fourier class of one
order `m ≥ 7` implies the official periodic existence-and-smoothness statement
with zero force. -/
theorem periodicStatementB_of_periodicRegularity {m : ℕ} (hm : 7 ≤ m)
    (h : PeriodicRegularity m) : PeriodicStatementB := by
  intro nu hnu u₀ hu₀
  obtain ⟨g⟩ := h nu hnu (fluctuation u₀) (admissible_fluctuation hu₀ m)
  exact exists_official_of_globalSolution hnu hu₀ hm g

/-- **Small data, official form.** If the fluctuation of a smooth periodic
initial velocity is small in the Sobolev energy of order `m ≥ 5`, relative to
the viscosity, there is a smooth periodic solution for all time. -/
theorem exists_official_of_small (m : ℕ) (hm : 5 ≤ m) (hnu : 0 < nu)
    (hu₀ : InitialVelocityConditionPeriodic u₀)
    (hsmall : ∀ F, velocityEnergy m F (fluctuation u₀) ≤ FourierSmallData.smallRadius m nu ^ 2 / 8) :
    ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ (fun _ _ ↦ 0) v p := by
  obtain ⟨g⟩ := admissible_small_regular m hm hnu (admissible_fluctuation hu₀ (m + 2)) hsmall
  exact exists_official_of_globalSolution hnu hu₀ (by omega) g

/-- A planar velocity field: independent of the third coordinate, with no third
component. -/
def IsPlanarVelocity (u : ℝ³ → ℝ³) : Prop :=
  (∀ x, u x 2 = 0) ∧ ∀ x (s : ℝ), u (x + s • EuclideanSpace.single 2 1) = u x

theorem partialDeriv_eq_zero_of_invariant {g : ℝ³ → ℝ} (hg : Differentiable ℝ g) (j : Fin 3)
    (hinv : ∀ x (s : ℝ), g (x + s • EuclideanSpace.single j 1) = g x) (x : ℝ³) :
    partialDeriv j g x = 0 := by
  have hd : HasDerivAt (fun s : ℝ ↦ x + s • EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single j (1 : ℝ))).const_add x
  have hg' : HasFDerivAt g (fderiv ℝ g (x + (0 : ℝ) • EuclideanSpace.single j 1))
      (x + (0 : ℝ) • EuclideanSpace.single j 1) := (hg _).hasFDerivAt
  have h := hg'.comp_hasDerivAt (0 : ℝ) hd
  simp only [zero_smul, add_zero] at h
  have hc : (g ∘ fun s : ℝ ↦ x + s • EuclideanSpace.single j (1 : ℝ)) = fun _ ↦ g x :=
    funext fun s ↦ hinv x s
  rw [hc] at h
  exact h.unique (hasDerivAt_const 0 (g x))

theorem coeff_eq_zero_of_invariant {g : ℝ³ → ℝ} (hg : ContDiff ℝ ∞ g) (hu : IsOnePeriodic g)
    (hinv : ∀ x (s : ℝ), g (x + s • EuclideanSpace.single 2 1) = g x) {k : Wavevector}
    (hk : k 2 ≠ 0) : coeff g k = 0 := by
  have h := coeff_partialDeriv hg hu 2 k
  have hz : partialDeriv 2 g = fun _ ↦ (0 : ℝ) :=
    funext (partialDeriv_eq_zero_of_invariant (hg.differentiable (by simp)) 2 hinv)
  rw [hz, coeff_zero_fun] at h
  have hph := unitTorusDerivativePhase_ne_zero
  have hk' : (k 2 : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
  exact ((mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero hph hk'))

theorem isPlanar_fluctuation (hu₀ : InitialVelocityConditionPeriodic u₀)
    (hpl : IsPlanarVelocity u₀) : IsPlanar (fluctuation u₀) := by
  have hs := hu₀.smooth
  have hp := hu₀.isOnePeriodic
  have hthird : ∀ k, coeffVec u₀ k 2 = 0 := by
    intro k
    have e : (fun x ↦ u₀ x 2) = fun _ ↦ (0 : ℝ) := funext hpl.1
    change coeff (fun x ↦ u₀ x 2) k = 0
    rw [e, coeff_zero_fun]
  refine ⟨fun k hk ↦ ?_, fun k ↦ ?_⟩
  · have hk0 : k ≠ 0 := fun h ↦ hk (by simp [h])
    rw [fluctuation_of_ne hk0]
    ext i
    exact coeff_eq_zero_of_invariant (contDiff_component hs i) (isOnePeriodic_component hp i)
      (fun x s ↦ by simp only [hpl.2 x s]) hk
  · by_cases hk : k = 0
    · simp [hk, fluctuation_zero]
    · rw [fluctuation_of_ne hk]
      exact hthird k

/-- **Planar data of any size, official form.** A smooth, divergence-free,
one-periodic planar initial velocity has a smooth periodic solution for all
time. -/
theorem exists_official_of_planar (hnu : 0 < nu) (hu₀ : InitialVelocityConditionPeriodic u₀)
    (hpl : IsPlanarVelocity u₀) :
    ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ (fun _ _ ↦ 0) v p := by
  obtain ⟨hr, hd, hz, E₀, hE₀⟩ := admissible_fluctuation hu₀ 7
  have hE₀0 : 0 ≤ E₀ := le_trans (by simp [velocityEnergy_eq]) (hE₀ ∅)
  obtain ⟨g⟩ := nonempty_globalSolution_of_planar 7 le_rfl hnu _ hr hd hz hE₀0 hE₀
    (isPlanar_fluctuation hu₀ hpl)
  exact exists_official_of_globalSolution hnu hu₀ le_rfl g

end Mettapedia.FluidDynamics.NavierStokes.FourierOfficialTheorems
