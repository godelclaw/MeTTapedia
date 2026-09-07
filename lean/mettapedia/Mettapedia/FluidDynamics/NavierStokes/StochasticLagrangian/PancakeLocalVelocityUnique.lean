import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalVelocityEnergy

/-!
# Uniqueness on the constructed local interval

The physical energy ball is compact in the retained Hilbert space. Smoothness
of the actual vector field gives a Lipschitz constant on that ball. ODE
uniqueness therefore identifies any two local physical solutions with the
same retained initial data. No uniform-in-frequency Lipschitz bound is claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeLocalVelocityUnique

open scoped BigOperators ContDiff
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeFiniteLocalizedEvolution
open PancakeFiniteVelocitySmooth PancakeLocalVelocityExistence PancakeLocalVelocityEnergy
open PancakeViscousMisalignmentAbsorption

variable {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}

def finiteCurve (s : LocalVelocitySolution M nu u₀ T) (t : ℝ) : FiniteField M :=
  restrictCoefficients M (s.coefficients t)

theorem extend_finiteCurve (s : LocalVelocitySolution M nu u₀ T) (t : ℝ) :
    extendCoefficients M (finiteCurve s t) = s.coefficients t := by
  funext q i
  by_cases hq : q ∈ M
  · simp [finiteCurve, extendCoefficients, hq]
  · simp [extendCoefficients, hq, s.support t q hq]

theorem hasDerivAt_finiteCurve (s : LocalVelocitySolution M nu u₀ T)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasDerivAt (finiteCurve s) (finiteVelocityRHS M nu (finiteCurve s t)) t := by
  have h : HasDerivAt (fun tau (p : M × Fin 3) ↦ s.coefficients tau p.1 p.2)
      (fun p ↦ velocityRHS M (s.coefficients t) nu p.1 p.2) t :=
    hasDerivAt_pi.mpr (fun p ↦ s.equation t ht p.1 p.1.2 p.2)
  have h' := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : M × Fin 3 ↦ ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h
  change HasDerivAt (finiteCurve s)
    (restrictCoefficients M (velocityRHS M (s.coefficients t) nu)) t at h'
  simpa [finiteVelocityRHS, extend_finiteCurve] using h'

theorem continuousOn_finiteCurve (s : LocalVelocitySolution M nu u₀ T) :
    ContinuousOn (finiteCurve s) (Set.Icc (0 : ℝ) T) :=
  fun t ht ↦ (hasDerivAt_finiteCurve s t ht).continuousAt.continuousWithinAt

theorem finiteCurve_mem_energyBall (s : LocalVelocitySolution M nu u₀ T) (hnu : 0 ≤ nu)
    (hs : ∀ q, -q ∈ M ↔ q ∈ M) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    finiteCurve s t ∈ Metric.closedBall (0 : FiniteField M) (Real.sqrt (fullEnergy M u₀)) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  have hb : ‖finiteCurve s t‖ ^ 2 ≤ fullEnergy M u₀ := by
    rw [finiteCurve, norm_restrictCoefficients_sq]
    exact kinetic_bound s hnu hs t ht
  have he := Real.sq_sqrt (fullEnergy_nonneg M u₀)
  have hn := Real.sqrt_nonneg (fullEnergy M u₀)
  nlinarith [norm_nonneg (finiteCurve s t)]

theorem localVelocitySolution_unique (s r : LocalVelocitySolution M nu u₀ T)
    (hnu : 0 ≤ nu) (hs : ∀ q, -q ∈ M ↔ q ∈ M) :
    Set.EqOn s.coefficients r.coefficients (Set.Icc (0 : ℝ) T) := by
  let B := Metric.closedBall (0 : FiniteField M) (Real.sqrt (fullEnergy M u₀))
  obtain ⟨K, hK⟩ := (contDiff_finiteVelocityRHS M nu).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall (0 : FiniteField M) _) (isCompact_closedBall _ _)
  have hinit : finiteCurve s 0 = finiteCurve r 0 := by
    ext p
    exact congrFun ((s.initial p.1 p.1.2).trans (r.initial p.1 p.1.2).symm) p.2
  have heq := ODE_solution_unique_of_mem_Icc_right
    (v := fun _ ↦ finiteVelocityRHS M nu) (s := fun _ ↦ B)
    (fun _ _ ↦ hK) (continuousOn_finiteCurve s)
    (fun t ht ↦ (hasDerivAt_finiteCurve s t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (fun t ht ↦ finiteCurve_mem_energyBall s hnu hs t ⟨ht.1, ht.2.le⟩)
    (continuousOn_finiteCurve r)
    (fun t ht ↦ (hasDerivAt_finiteCurve r t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (fun t ht ↦ finiteCurve_mem_energyBall r hnu hs t ⟨ht.1, ht.2.le⟩) hinit
  intro t ht
  rw [← extend_finiteCurve s t, ← extend_finiteCurve r t, heq ht]

end Mettapedia.FluidDynamics.NavierStokes.PancakeLocalVelocityUnique
