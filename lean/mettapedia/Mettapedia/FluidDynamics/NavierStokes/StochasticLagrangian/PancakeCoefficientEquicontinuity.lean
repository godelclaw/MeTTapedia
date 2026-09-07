import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFixedOutputVelocityBound
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Uniform time regularity of retained Fourier coefficients

A common kinetic-energy bound controls every fixed output coefficient
and its time derivative, independently of the retained set.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeCoefficientEquicontinuity

open scoped BigOperators NNReal
open PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakeViscousMisalignmentAbsorption
open PancakeLocalVelocityExistence PancakeLocalVelocityEnergy
open PancakeFixedOutputVelocityBound PancakeGalerkinKineticEnergy

def outputSpeed (nu U : ℝ) (q : Wavevector) : ℝ :=
  (2 * Real.pi) * ‖frequencyVec q‖ * U +
    |nu| * (2 * Real.pi)^2 * ‖frequencyVec q‖^2 * Real.sqrt U

theorem outputSpeed_nonneg (nu U : ℝ) (q : Wavevector) (hU : 0 ≤ U) :
    0 ≤ outputSpeed nu U q := by
  unfold outputSpeed
  positivity

variable {M : Finset Wavevector} {nu T : ℝ} {u₀ : FourierVelocity}

theorem coefficient_norm_le_of_energy (s : LocalVelocitySolution M nu u₀ T)
    (t U : ℝ) (hE : fullEnergy M (s.coefficients t) ≤ U) (q : Wavevector) :
    ‖coefficientVec (s.coefficients t q)‖ ≤ Real.sqrt U := by
  by_cases hq : q ∈ M
  · have hp : coefficientEnergy (s.coefficients t q) ≤ fullEnergy M (s.coefficients t) :=
      Finset.single_le_sum (f := fun k ↦ coefficientEnergy (s.coefficients t k))
        (fun k _ ↦ by rw [← norm_coefficientVec_sq]; positivity) hq
    rw [← norm_coefficientVec_sq] at hp
    have hU : 0 ≤ U := (fullEnergy_nonneg M (s.coefficients t)).trans hE
    nlinarith [Real.sq_sqrt hU, Real.sqrt_nonneg U, norm_nonneg (coefficientVec (s.coefficients t q))]
  · rw [s.support t q hq]
    simp [coefficientVec]

theorem coefficient_component_le_of_energy (s : LocalVelocitySolution M nu u₀ T)
    (t U : ℝ) (hE : fullEnergy M (s.coefficients t) ≤ U) (q : Wavevector) (i : Fin 3) :
    ‖s.coefficients t q i‖ ≤ Real.sqrt U :=
  (PiLp.norm_apply_le (coefficientVec (s.coefficients t q)) i).trans
    (coefficient_norm_le_of_energy s t U hE q)

theorem velocity_component_le_outputSpeed (s : LocalVelocitySolution M nu u₀ T)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (t U : ℝ)
    (hE : fullEnergy M (s.coefficients t) ≤ U) (q : Wavevector) (i : Fin 3) :
    ‖velocityRHS M (s.coefficients t) nu q i‖ ≤ outputSpeed nu U q := by
  apply (PiLp.norm_apply_le (coefficientVec (velocityRHS M (s.coefficients t) nu q)) i).trans
  apply (norm_velocityRHS_le M (s.coefficients t) nu hk (s.transverse t) q).trans
  unfold outputSpeed
  exact add_le_add
    (mul_le_mul_of_nonneg_left hE (by positivity))
    (mul_le_mul_of_nonneg_left (coefficient_norm_le_of_energy s t U hE q) (by positivity))

/-- Every fixed Fourier component has the same time Lipschitz constant
for every retained set obeying the common kinetic bound. -/
theorem coefficient_lipschitzOn (s : LocalVelocitySolution M nu u₀ T)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (U : ℝ) (hU : 0 ≤ U)
    (hE : ∀ t ∈ Set.Icc (0 : ℝ) T, fullEnergy M (s.coefficients t) ≤ U)
    (q : Wavevector) (i : Fin 3) :
    LipschitzOnWith ⟨outputSpeed nu U q, outputSpeed_nonneg nu U q hU⟩
      (fun t ↦ s.coefficients t q i) (Set.Icc (0 : ℝ) T) := by
  by_cases hq : q ∈ M
  · apply (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht ↦ (s.equation t ht q hq i).hasDerivWithinAt)
    intro t ht
    exact_mod_cast velocity_component_le_outputSpeed s hk t U (hE t ht) q i
  · have he : (fun t ↦ s.coefficients t q i) = fun _ ↦ (0 : ℂ) := by
      funext t
      rw [s.support t q hq]
      rfl
    rw [he]
    exact (LipschitzWith.const' (0 : ℂ)).lipschitzOnWith

def coefficientPath (s : LocalVelocitySolution M nu u₀ T) (q : Wavevector) (i : Fin 3) :
    BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t ↦ s.coefficients t q i, (continuousOn_coefficients s q i).restrict⟩

theorem coefficientPath_lipschitz (s : LocalVelocitySolution M nu u₀ T)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (U : ℝ) (hU : 0 ≤ U)
    (hE : ∀ t ∈ Set.Icc (0 : ℝ) T, fullEnergy M (s.coefficients t) ≤ U)
    (q : Wavevector) (i : Fin 3) :
    LipschitzWith ⟨outputSpeed nu U q, outputSpeed_nonneg nu U q hU⟩
      (coefficientPath s q i) :=
  (coefficient_lipschitzOn s hk U hU hE q i).to_restrict

end Mettapedia.FluidDynamics.NavierStokes.PancakeCoefficientEquicontinuity
