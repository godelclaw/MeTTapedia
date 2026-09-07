import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSobolevFiberEnvelope
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Uniform-in-time convergence of fixed-output convection

The quadratic series is constructed in the Banach space of bounded continuous
time paths. Its summable majorant comes from the common second-order energy,
with the derivative on the fixed output frequency.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PancakeConvectionPathLimit

open scoped BigOperators Topology
open Filter
open PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeGalerkinCoefficientLimit PancakeCoefficientLimitProperties
open PancakeSobolevFiberEnvelope PancakeSobolevVelocityRate
open PancakeLocalVelocityExistence PancakeCoefficientEquicontinuity

def modeDotPath {T : ℝ} (q : Wavevector) (a : CoefficientLimit T) (k : Wavevector) :
    BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℂ :=
  ∑ i : Fin 3, (q i : ℂ) • a k i

def fiberPath {T : ℝ} (q : Wavevector) (a : CoefficientLimit T) (k : Wavevector)
    (i : Fin 3) : BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℂ :=
  modeDotPath q a k * a (q-k) i

theorem fiberPath_apply {T : ℝ} (q : Wavevector) (a : CoefficientLimit T)
    (k : Wavevector) (i : Fin 3) (t : Set.Icc (0 : ℝ) T) :
    fiberPath q a k i t = outputFiber q (limitField a t) k i := by
  simp [fiberPath, modeDotPath, outputFiber, modeDot, limitField]

theorem norm_fiberPath_le {T : ℝ} (q : Wavevector) (a : CoefficientLimit T)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ t F, sobolevEnergy F (limitField a t) ≤ B) (k : Wavevector) (i : Fin 3) :
    ‖fiberPath q a k i‖ ≤ fiberEnvelope B q k := by
  apply (BoundedContinuousFunction.norm_le (fiberEnvelope_nonneg B hB q k)).mpr
  intro t
  rw [fiberPath_apply]
  exact norm_outputFiber_le_envelope _ B (hE t) q k i

theorem summable_fiberPath {T : ℝ} (q : Wavevector) (a : CoefficientLimit T)
    (B : ℝ) (hB : 0 ≤ B) (hE : ∀ t F, sobolevEnergy F (limitField a t) ≤ B)
    (i : Fin 3) : Summable (fun k ↦ fiberPath q a k i) :=
  (summable_fiberEnvelope B q).of_norm_bounded (fun k ↦ norm_fiberPath_le q a B hB hE k i)

def convectionPath {T : ℝ} (q : Wavevector) (a : CoefficientLimit T) (i : Fin 3) :
    BoundedContinuousFunction (Set.Icc (0 : ℝ) T) ℂ :=
  ∑' k, fiberPath q a k i

theorem convectionPath_apply {T : ℝ} (q : Wavevector) (a : CoefficientLimit T)
    (B : ℝ) (hB : 0 ≤ B) (hE : ∀ t F, sobolevEnergy F (limitField a t) ≤ B)
    (i : Fin 3) (t : Set.Icc (0 : ℝ) T) :
    convectionPath q a i t = ∑' k, outputFiber q (limitField a t) k i := by
  have he := (BoundedContinuousFunction.evalCLM ℂ t).map_tsum
    (summable_fiberPath q a B hB hE i)
  simpa only [convectionPath, BoundedContinuousFunction.evalCLM_apply, fiberPath_apply] using he

theorem tendsto_fiberPath {T : ℝ} (aₙ : ℕ → CoefficientLimit T) (a : CoefficientLimit T)
    (h : ∀ k i, Tendsto (fun n ↦ aₙ n k i) atTop (𝓝 (a k i)))
    (q k : Wavevector) (i : Fin 3) :
    Tendsto (fun n ↦ fiberPath q (aₙ n) k i) atTop (𝓝 (fiberPath q a k i)) := by
  apply Tendsto.mul _ (h (q-k) i)
  exact tendsto_finsetSum _ (fun j _ ↦ (h k j).const_smul (q j : ℂ))

theorem tendsto_convectionPath {T : ℝ} (aₙ : ℕ → CoefficientLimit T) (a : CoefficientLimit T)
    (h : ∀ k i, Tendsto (fun n ↦ aₙ n k i) atTop (𝓝 (a k i)))
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ n t F, sobolevEnergy F (limitField (aₙ n) t) ≤ B)
    (q : Wavevector) (i : Fin 3) :
    Tendsto (fun n ↦ convectionPath q (aₙ n) i) atTop (𝓝 (convectionPath q a i)) := by
  have hn := tendsto_tsum_of_dominated_convergence (summable_fiberEnvelope B q)
    (fun k ↦ tendsto_fiberPath aₙ a h q k i)
    (Eventually.of_forall (fun n k ↦ norm_fiberPath_le q (aₙ n) B hB (hE n) k i))
  simpa only [tsum_apply, convectionPath] using hn

def solutionPaths {nu T : ℝ} {u₀ : FourierVelocity} {M : Finset Wavevector}
    (s : LocalVelocitySolution M nu u₀ T) : CoefficientLimit T :=
  fun q i ↦ coefficientPath s q i

theorem limitField_solutionPaths {nu T : ℝ} {u₀ : FourierVelocity} {M : Finset Wavevector}
    (s : LocalVelocitySolution M nu u₀ T) (t : Set.Icc (0 : ℝ) T) :
    limitField (solutionPaths s) t = s.coefficients t := rfl

/-- The actual Galerkin family has uniformly converging nonlinear output paths. -/
theorem coefficientLimit_convection_uniform {nu T : ℝ} {u₀ : FourierVelocity}
    (s : ∀ n, LocalVelocitySolution (galerkinModes n) nu u₀ T)
    (phi : ℕ → ℕ) (a : CoefficientLimit T) (h : IsCoefficientLimit s phi a)
    (B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      sobolevEnergy (galerkinModes n) ((s n).coefficients t) ≤ B)
    (q : Wavevector) (i : Fin 3) :
    TendstoUniformly
      (fun n ↦ convectionPath q (solutionPaths (s (phi n))) i)
      (convectionPath q a i) atTop := by
  apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
  apply tendsto_convectionPath _ a _ B hB _ q i
  · intro k j
    exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr (h k j)
  · intro n t F
    exact (sobolevEnergy_of_support_le _ F _ ((s (phi n)).support t)).trans
      (hE (phi n) t t.2)

end Mettapedia.FluidDynamics.NavierStokes.PancakeConvectionPathLimit
