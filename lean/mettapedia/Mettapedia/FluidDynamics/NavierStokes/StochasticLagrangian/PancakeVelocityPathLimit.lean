import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConvectionFiberIdentity

/-!
# Uniform convergence of the actual velocity right-hand sides

The Leray projection and viscous multiplier act on the constructed nonlinear
time paths. Evaluation is identified with the existing physical Galerkin
equation, including its unit-torus derivative factors.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeVelocityPathLimit

open scoped BigOperators Topology
open Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeGalerkinCoefficientLimit PancakeCoefficientLimitProperties
open PancakeConvectionPathLimit PancakeConvectionFiberIdentity PancakeSobolevVelocityRate
open PancakeLocalVelocityExistence PancakeGalerkinKineticEnergy PancakePeriodicVorticityEquation

def lerayPath {T : ℝ} (q : Wavevector)
    (v : Fin 3 → BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℂ) (i : Fin 3) :
    BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℂ :=
  if modeSquare q = 0 then v i
  else v i - ((q i : ℂ) / modeSquare q) • ∑ j : Fin 3, (q j : ℂ) • v j

theorem lerayPath_apply {T : ℝ} (q : Wavevector)
    (v : Fin 3 → BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℂ)
    (i : Fin 3) (t : Set.Icc (0 : ℝ) T) :
    lerayPath q v i t = lerayMode q (fun j ↦ v j t) i := by
  by_cases hq : modeSquare q = 0
  · simp [lerayPath, lerayMode, hq]
  · simp [lerayPath, lerayMode, hq, modeDot]
    ring

theorem tendsto_lerayPath {T : ℝ} (q : Wavevector)
    (vₙ : ℕ → Fin 3 → BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℂ)
    (v : Fin 3 → BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℂ)
    (h : ∀ i, Tendsto (fun n ↦ vₙ n i) atTop (𝓝 (v i))) (i : Fin 3) :
    Tendsto (fun n ↦ lerayPath q (vₙ n) i) atTop (𝓝 (lerayPath q v i)) := by
  by_cases hq : modeSquare q = 0
  · simpa only [lerayPath, if_pos hq] using h i
  · simp only [lerayPath, if_neg hq]
    exact (h i).sub ((tendsto_finsetSum _ (fun j _ ↦ (h j).const_smul (q j : ℂ))).const_smul _)

def velocityPath {T : ℝ} (nu : ℝ) (q : Wavevector) (a : CoefficientLimit T) (i : Fin 3) :
    BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℂ :=
  lerayPath q (fun j ↦ (-unitTorusDerivativePhase) • convectionPath q a j) i +
    ((nu : ℂ) * unitTorusDerivativePhase^2 * modeSquare q) • a q i

theorem solution_velocityPath_apply {nu T : ℝ} {u₀ : FourierVelocity}
    {M : Finset Wavevector} (s : LocalVelocitySolution M nu u₀ T)
    (hk : ∀ k ∈ M, frequencyVec k ≠ 0) (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ t, t ∈ Set.Icc (0 : ℝ) T → sobolevEnergy M (s.coefficients t) ≤ B)
    (q : Wavevector) (i : Fin 3) (t : Set.Icc (0 : ℝ) T) :
    velocityPath nu q (solutionPaths s) i t = velocityRHS M (s.coefficients t) nu q i := by
  simp only [velocityPath, BoundedContinuousFunction.add_apply, lerayPath_apply,
    BoundedContinuousFunction.smul_apply, solution_convectionPath_apply s B hB hE,
    velocityRHS, finiteTransport_fourierCurl_eq M _ hk (s.transverse t),
    Pi.add_apply, unitTorusViscousVorticityCoeff, Pi.smul_apply]
  rfl

theorem tendsto_velocityPath {T : ℝ} (nu : ℝ)
    (aₙ : ℕ → CoefficientLimit T) (a : CoefficientLimit T)
    (h : ∀ k i, Tendsto (fun n ↦ aₙ n k i) atTop (𝓝 (a k i)))
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ n t F, sobolevEnergy F (limitField (aₙ n) t) ≤ B)
    (q : Wavevector) (i : Fin 3) :
    Tendsto (fun n ↦ velocityPath nu q (aₙ n) i) atTop (𝓝 (velocityPath nu q a i)) := by
  apply Tendsto.add _ ((h q i).const_smul _)
  exact tendsto_lerayPath q _ _ (fun j ↦
    (tendsto_convectionPath aₙ a h B hB hE q j).const_smul _) i

/-- Uniform-in-time convergence of the physical finite velocity RHS at every fixed output. -/
theorem coefficientLimit_velocity_uniform {nu T : ℝ} {u₀ : FourierVelocity}
    (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
    (phi : ℕ → ℕ) (a : CoefficientLimit T) (h : IsCoefficientLimit s phi a)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ B)
    (q : Wavevector) (i : Fin 3) :
    TendstoUniformly
      (fun n (t : Set.Icc (0 : ℝ) T) ↦
        velocityRHS (galerkinModes (phi n)) ((s (phi n)).coefficients t) nu q i)
      (velocityPath nu q a i) atTop := by
  have hn := tendsto_velocityPath nu (fun n ↦ solutionPaths (s (phi n))) a
    (fun k j ↦ BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr (h k j))
    B hB (fun n t F ↦
      (sobolevEnergy_of_support_le _ F _ ((s (phi n)).support t)).trans
        (hE (phi n) t t.2)) q i
  have hu := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hn
  have he (n : ℕ) (t : Set.Icc (0 : ℝ) T) :
      velocityPath nu q (solutionPaths (s (phi n))) i t =
        velocityRHS (galerkinModes (phi n)) ((s (phi n)).coefficients t) nu q i :=
    solution_velocityPath_apply (s (phi n)) (galerkinModes_nonzero (phi n))
      B hB (hE (phi n)) q i t
  change TendstoUniformly
    (fun n t ↦ velocityPath nu q (solutionPaths (s (phi n))) i t) _ atTop at hu
  simpa only [he] using hu

end Mettapedia.FluidDynamics.NavierStokes.PancakeVelocityPathLimit
