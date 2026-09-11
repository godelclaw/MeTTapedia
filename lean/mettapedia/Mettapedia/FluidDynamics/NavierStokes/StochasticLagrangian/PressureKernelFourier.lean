import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureKernelAction
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureTwoInputReconstruction

/-!
# Exact finite Fourier identification of the physical pressure kernel

The kernel action equals the collected pressure-pair convolution, including
colliding output frequencies. Retained kernel frequency sets may strictly
contain the input supports, as needed when localizing the input fields.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureKernelFourier

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeBilinearPeriodization
open PressureBilinearOperator FinitePressureKernel PressureKernelAction
open PressureTwoInputReconstruction PancakeFiniteFourierLocalization PancakeFrequencyProjectorCommutator
open ComplexPressurePair ComplexPressureConvolution Mettapedia.Analysis
open PancakePeriodicCoherentSplit PancakeCurlOutputTail PancakeFourierPressureStrain
open PancakeGalerkinKineticEnergy
open FourierPressureTraceSymbol

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "T3" => UnitAddTorus (Fin 3)
local notation "T6" => UnitAddTorus (Fin 6)

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedAddCommGroup (C3 →L[ℂ] C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace (C3 →L[ℂ] C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem continuous_vectorPolynomial (P : Finset Wavevector) (w : Wavevector → C3) :
    Continuous (vectorPolynomial P w) := by
  unfold vectorPolynomial
  fun_prop

theorem kernelAction_vectorPolynomial (B : T6 → C3 →L[ℂ] C3 →L[ℂ] C3) (hB : Continuous B)
    (P K : Finset Wavevector) (w v : Wavevector → C3) (x : T3) :
    kernelAction B (vectorPolynomial P w) (vectorPolynomial K v) x =
      ∑ p ∈ P, ∑ k ∈ K, (UnitAddTorus.mFourier p x * UnitAddTorus.mFourier k x) •
        (UnitAddTorus.mFourierCoeff B (pairWavevector p k)) (w p) (v k) := by
  have hint (p k : Wavevector) : Integrable (fun q : T6 ↦
      B q (UnitAddTorus.mFourier p (x - firstTorusDisplacement q) • w p)
        (UnitAddTorus.mFourier k (x - secondTorusDisplacement q) • v k)) :=
    integrable_action_integrand B _ _ x hB
      ((UnitAddTorus.mFourier p).continuous.smul continuous_const)
      ((UnitAddTorus.mFourier k).continuous.smul continuous_const)
  unfold kernelAction
  simp only [vectorPolynomial, map_sum, sum_apply]
  conv_lhs => arg 2; ext q; rw [Finset.sum_comm]
  rw [integral_finsetSum P]
  · apply Finset.sum_congr rfl
    intro p _
    rw [integral_finsetSum K]
    · apply Finset.sum_congr rfl
      intro k _
      exact kernelAction_monomials B hB p k (w p) (v k) x
    · exact fun k _ ↦ hint p k
  · exact fun p _ ↦ integrable_finsetSum K (fun k _ ↦ hint p k)

theorem pressureKernelAction_vectorPolynomial_of_subset
    (e : R3) (he : ‖e‖ = 1) (P K S T : Finset Wavevector)
    (hPS : P ⊆ S) (hKT : K ⊆ T) (w v : Wavevector → C3) (x : T3) :
    kernelAction (pressureKernel e he S T) (vectorPolynomial P w) (vectorPolynomial K v) x =
      ∑ p ∈ P, ∑ k ∈ K, (UnitAddTorus.mFourier p x * UnitAddTorus.mFourier k x) •
        tiltPair e p k (WithLp.ofLp (w p)) (WithLp.ofLp (v k)) := by
  rw [kernelAction_vectorPolynomial _ (continuous_pressureKernel e he S T)]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro k hk
  rw [mFourierCoeff_pressureKernel, if_pos ⟨hPS hp, hKT hk⟩, pressurePairOperator_apply]

theorem vectorPolynomial_pairConvolution_eq (e : R3) (P K : Finset Wavevector)
    (w v : FourierVelocity) (x : T3) :
    vectorPolynomial (finiteCutoffOutputModes P K) (pairConvolution e P K w v) x =
      ∑ p ∈ P, ∑ k ∈ K, (UnitAddTorus.mFourier p x * UnitAddTorus.mFourier k x) •
        tiltPair e p k (w p) (v k) := by
  let L (q : Wavevector) : C3 →ₗ[ℂ] C3 := UnitAddTorus.mFourier q x • LinearMap.id
  have h := sum_apply_fiberwise (P ×ˢ K) (finiteCutoffOutputModes P K)
    (fun pk ↦ pk.1 + pk.2) (fun pk ↦ tiltPair e pk.1 pk.2 (w pk.1) (v pk.2)) L
    (fun pk hpk ↦ (mem_finiteCutoffOutputModes_iff P K _).mpr
      ⟨pk.1, (Finset.mem_product.mp hpk).1, pk.2, (Finset.mem_product.mp hpk).2, rfl⟩)
  have hL (q : Wavevector) (z : C3) : L q z = UnitAddTorus.mFourier q x • z := rfl
  simpa only [hL, vectorPolynomial, pairConvolution,
    Finset.sum_product, UnitAddTorus.mFourier_add] using h

theorem pressureKernelAction_eq_pairConvolution (e : R3) (he : ‖e‖ = 1)
    (P K S T : Finset Wavevector) (hPS : P ⊆ S) (hKT : K ⊆ T)
    (w v : FourierVelocity) (x : T3) :
    kernelAction (pressureKernel e he S T) (vectorPolynomial P (fun p ↦ coefficientVec (w p)))
        (vectorPolynomial K (fun k ↦ coefficientVec (v k))) x =
      vectorPolynomial (finiteCutoffOutputModes P K) (pairConvolution e P K w v) x := by
  rw [pressureKernelAction_vectorPolynomial_of_subset e he P K S T hPS hKT,
    vectorPolynomial_pairConvolution_eq]
  rfl

/-- The physical pressure Hessian carries the negative of the pressure-pair
kernel action. Incompressibility is required only of the original velocity
modes, not of any subsequently localized vorticity. -/
theorem pressureHessian_polynomial_eq_neg_kernelAction
    (e : R3) (he : ‖e‖ = 1) (M S T : Finset Wavevector)
    (hMS : M ⊆ S) (hMT : M ⊆ T) (u : FourierVelocity)
    (hu : ∀ k ∈ M, modeDot k (u k) = 0) (x : T3) :
    vectorPolynomial (finiteCutoffOutputModes M M)
        (fun q ↦ (pressureHessianCoeff M u q).trace • complexTiltSymbol e q) x =
      -kernelAction (pressureKernel e he S T)
        (vectorPolynomial M (fun k ↦ coefficientVec (fourierCurl u k)))
        (vectorPolynomial M (fun k ↦ coefficientVec (fourierCurl u k))) x := by
  rw [pressureKernelAction_eq_pairConvolution e he M M S T hMS hMT]
  simp only [vectorPolynomial, PhysicalPressurePair.pressureHessian_tilt_eq_pairConvolution e M u hu,
    smul_neg, Finset.sum_neg_distrib]

end Mettapedia.FluidDynamics.NavierStokes.PressureKernelFourier
