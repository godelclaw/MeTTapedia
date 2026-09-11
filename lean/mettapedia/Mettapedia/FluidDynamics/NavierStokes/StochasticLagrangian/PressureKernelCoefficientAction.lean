import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureKernelFourier
import Mettapedia.Analysis.FiniteTorusProduct
import Mettapedia.Analysis.UnitTorusFourierTranslation

/-!
# Finite pressure kernels select the coefficients of full continuous fields

Product-Haar integration identifies the two retained input coefficients
directly. Neither field is assumed to be a finite Fourier polynomial.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureKernelCoefficientAction

open MeasureTheory PeriodicFourierTriad PancakeBilinearPeriodization
open PressureBilinearOperator FinitePressureKernel PressureKernelAction PressureKernelFourier
open PressureTwoInputReconstruction PancakeFiniteFourierLocalization ComplexPressureConvolution
open Mettapedia.Analysis Mettapedia.Analysis.UnitTorusFourierTranslation

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

theorem pressureKernel_eq_sum (e : R3) (he : ‖e‖ = 1)
    (S T : Finset Wavevector) (q : T6) :
    pressureKernel e he S T q = ∑ k ∈ S, ∑ p ∈ T,
      UnitAddTorus.mFourier (pairWavevector k p) q • pressurePairOperator e he k p := by
  unfold pressureKernel FiniteTorusSymbolKernel.kernel pairModes
  rw [Finset.sum_image]
  · simp only [Finset.sum_product, first_pairWavevector, second_pairWavevector]
  · intro a _ b _ h
    apply Prod.ext
    · simpa only [first_pairWavevector] using congrArg firstWavevector h
    · simpa only [second_pairWavevector] using congrArg secondWavevector h

theorem kernelAction_character (B : C3 →L[ℂ] C3 →L[ℂ] C3)
    (f g : T3 → C3) (hf : Continuous f) (hg : Continuous g)
    (k p : Wavevector) (x : T3) :
    kernelAction (fun q ↦ UnitAddTorus.mFourier (pairWavevector k p) q • B) f g x =
      (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier p x) •
        B (UnitAddTorus.mFourierCoeff f k) (UnitAddTorus.mFourierCoeff g p) := by
  have heq (q : T6) : (UnitAddTorus.mFourier (pairWavevector k p) q • B)
      (f (x - firstTorusDisplacement q)) (g (x - secondTorusDisplacement q)) =
      B (UnitAddTorus.mFourier k (firstTorusDisplacement q) • f (x - firstTorusDisplacement q))
        (UnitAddTorus.mFourier p (secondTorusDisplacement q) • g (x - secondTorusDisplacement q)) := by
    simp only [mFourier_pairWavevector, smul_apply, map_smul, smul_smul]
    rw [mul_comm]
  unfold kernelAction
  simp_rw [heq]
  have hsecond (q : T6) : secondTorusDisplacement q = fun i ↦ q (Fin.natAdd 3 i) := by
    funext i
    change q ⟨i.val + 3, _⟩ = q (Fin.natAdd 3 i)
    apply congrArg q
    apply Fin.ext
    exact Nat.add_comm _ _
  have hfirst (q : T6) : firstTorusDisplacement q = fun i ↦ q (Fin.castAdd 3 i) := by
    funext i
    rfl
  simp only [hsecond, hfirst]
  rw [FiniteTorusProduct.integral_bilinear 3 3 B
    (fun y ↦ UnitAddTorus.mFourier k y • f (x - y))
    (fun z ↦ UnitAddTorus.mFourier p z • g (x - z)) (by fun_prop) (by fun_prop)]
  simp only [integral_character_smul_sub, map_smul, smul_apply, smul_smul]
  rw [mul_comm]

theorem pressureKernelAction_eq_coefficient_sum (e : R3) (he : ‖e‖ = 1)
    (S T : Finset Wavevector) (f g : T3 → C3) (hf : Continuous f) (hg : Continuous g) (x : T3) :
    kernelAction (pressureKernel e he S T) f g x =
      ∑ k ∈ S, ∑ p ∈ T, (UnitAddTorus.mFourier k x * UnitAddTorus.mFourier p x) •
        pressurePairOperator e he k p (UnitAddTorus.mFourierCoeff f k) (UnitAddTorus.mFourierCoeff g p) := by
  have hint (k p : Wavevector) : Integrable (fun q : T6 ↦
      (UnitAddTorus.mFourier (pairWavevector k p) q • pressurePairOperator e he k p)
        (f (x - firstTorusDisplacement q)) (g (x - secondTorusDisplacement q))) :=
    integrable_action_integrand _ f g x (by fun_prop) hf hg
  unfold kernelAction
  simp_rw [pressureKernel_eq_sum, sum_apply]
  rw [integral_finsetSum S]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_finsetSum T]
    · apply Finset.sum_congr rfl
      intro p _
      exact kernelAction_character _ f g hf hg k p x
    · exact fun p _ ↦ hint k p
  · exact fun k _ ↦ integrable_finsetSum T (fun p _ ↦ hint k p)

theorem pressureKernelAction_eq_coefficient_convolution (e : R3) (he : ‖e‖ = 1)
    (S T : Finset Wavevector) (f g : T3 → C3) (hf : Continuous f) (hg : Continuous g) (x : T3) :
    kernelAction (pressureKernel e he S T) f g x =
      vectorPolynomial (finiteCutoffOutputModes S T)
        (pairConvolution e S T (fun k ↦ WithLp.ofLp (UnitAddTorus.mFourierCoeff f k))
          (fun p ↦ WithLp.ofLp (UnitAddTorus.mFourierCoeff g p))) x := by
  rw [pressureKernelAction_eq_coefficient_sum e he S T f g hf hg,
    vectorPolynomial_pairConvolution_eq]
  rfl

end Mettapedia.FluidDynamics.NavierStokes.PressureKernelCoefficientAction
