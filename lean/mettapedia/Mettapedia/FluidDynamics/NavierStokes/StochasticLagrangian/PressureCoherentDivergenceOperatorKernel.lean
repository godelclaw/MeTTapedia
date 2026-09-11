import Mettapedia.Analysis.BilinearRankOne
import Mettapedia.Analysis.SchwartzBilinearKernel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ComplexTransverseMatrix
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceChannelKernel

/-!
# Complex bilinear kernels for coherent pressure channels

Each scalar output coordinate is lifted by the two longitudinal input
functionals. These are complex bilinear, not sesquilinear, in the two
input amplitudes. Unit directions give rank-one operators of norm one.
Only the three output coordinates enter the common-envelope bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceOperatorKernel

open Mettapedia.Analysis.BilinearRankOne Mettapedia.Analysis.SchwartzBilinearKernel
open ComplexTransverseMatrix (pairing pairing_eq_inner)
open FourierPressureTraceSymbol (complexifyVector norm_complexifyVector)
open PressureCoherentDivergenceChannel (Factor)
open PressureCoherentDivergenceChannelKernel
open scoped SchwartzMap FourierTransform

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "Op" => C3 →L[ℂ] C3 →L[ℂ] C3

local instance : NormedAddCommGroup (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ (C3 →L[ℂ] C3) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup Op := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℂ Op := ContinuousLinearMap.toNormedSpace
local instance : CompleteSpace C3 := PiLp.completeSpace 2 (fun _ : Fin 3 ↦ ℂ)
local instance : CompleteSpace (C3 →L[ℂ] C3) := ContinuousLinearMap.instCompleteSpace
local instance : CompleteSpace Op := ContinuousLinearMap.instCompleteSpace

def outputOperator (e : R3) (i : Fin 3) : Op :=
  rankOne (innerSL ℂ (complexifyVector e)) (innerSL ℂ (complexifyVector e))
    (EuclideanSpace.single i 1)

@[simp] theorem outputOperator_apply (e : R3) (i : Fin 3) (u v : C3) :
    outputOperator e i u v = (pairing e u * pairing e v) • EuclideanSpace.single i 1 := by
  simp [outputOperator, pairing_eq_inner]

theorem norm_outputOperator (e : R3) (i : Fin 3) : ‖outputOperator e i‖ = ‖e‖ ^ 2 := by
  simp [outputOperator, innerSL_apply_norm, norm_complexifyVector, pow_two]

theorem norm_outputOperator_unit (e : R3) (he : ‖e‖ = 1) (i : Fin 3) :
    ‖outputOperator e i‖ = 1 := by rw [norm_outputOperator, he, one_pow]

def operatorKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor) : 𝓢(E6, Op) :=
  ∑ i : Fin 3, lift (scaledKernel N hN (t, e) c i) (outputOperator e i)

theorem operatorKernel_apply (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor)
    (x : E6) (u v : C3) (i : Fin 3) :
    operatorKernel N hN t e c x u v i =
      scaledKernel N hN (t, e) c i x * pairing e u * pairing e v := by
  simp [operatorKernel, outputOperator_apply, Pi.single_apply, mul_assoc]

theorem fourier_operatorKernel (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor)
    (ξ : E6) (u v : C3) (i : Fin 3) :
    (𝓕 (operatorKernel N hN t e c)) ξ u v i =
      (𝓕 (scaledKernel N hN (t, e) c i)) ξ * pairing e u * pairing e v := by
  simp [operatorKernel, FourierTransform.fourier_sum, fourier_lift,
    outputOperator_apply, Pi.single_apply, mul_assoc]

theorem fourier_operatorKernel_factor (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (c : Factor)
    (ξ : E6) :
    (𝓕 (operatorKernel N hN t e c)) ξ =
      (scaledMultiplier N c (PressureLowOutputSymbol.pairEquiv ξ) : ℂ) •
        (𝓕 (operatorKernel N hN t e .undifferentiated)) ξ := by
  ext u v i
  simp only [smul_apply, PiLp.smul_apply, smul_eq_mul,
    fourier_operatorKernel, fourier_scaledKernel, scaledMultiplier_undifferentiated,
    Complex.ofReal_one, one_mul]
  ring

theorem norm_operatorKernel_le_sum (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (he : ‖e‖ = 1)
    (c : Factor) (x : E6) :
    ‖operatorKernel N hN t e c x‖ ≤ ∑ i : Fin 3, ‖scaledKernel N hN (t, e) c i x‖ := by
  simp only [operatorKernel, sum_apply, lift_apply]
  simpa only [norm_smul, norm_outputOperator_unit e he, mul_one] using
    norm_sum_le Finset.univ (fun i : Fin 3 ↦ scaledKernel N hN (t, e) c i x • outputOperator e i)

theorem norm_operatorKernel_le (N : ℝ) (hN : 0 < N) (t : ℝ) (e : R3) (he : ‖e‖ = 1)
    (c : Factor) (H : E6 → ℝ) (hH : ∀ i : Fin 3, ∀ x, ‖scaledKernel N hN (t, e) c i x‖ ≤ H x)
    (x : E6) : ‖operatorKernel N hN t e c x‖ ≤ 3 * H x := by
  apply (norm_operatorKernel_le_sum N hN t e he c x).trans
  calc
    _ ≤ ∑ _i : Fin 3, H x := Finset.sum_le_sum (fun i _ ↦ hH i x)
    _ = _ := by simp

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceOperatorKernel
