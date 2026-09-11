import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergenceChannel
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureCoherentDivergencePhysicalKernel

/-!
# Physical kernels for the coherent input-frequency channels

Transport and dilation preserve the exact input-coordinate multipliers.
The input factors are normalized by the input scale, not the output scale.
The undifferentiated channel agrees with the existing coherent kernel.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceChannelKernel

open Mettapedia.Analysis.SchwartzLinearChange Mettapedia.Analysis.SchwartzDilation
open PressureLowOutputCutoff (ratio receiver)
open PressureLowOutputSymbol (pairEquiv)
open PressureLowOutputChange
open PressureCoherentDivergenceChannel
open scoped FourierTransform SchwartzMap

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local notation "P" => R3 × R3
local notation "A" => ℝ × R3

def inputMultiplier : Factor → P → ℝ
  | .undifferentiated, _ => 1
  | .first j, p => p.1 j
  | .second j, p => p.2 j

theorem multiplier_frequencyChange (c : Factor) (t : ℝ) (hr : ratio t ≠ 0) (ξ : E6) :
    multiplier c t (pairEquiv (frequencyChange (ratio t) ξ)) =
      inputMultiplier c (pairEquiv ξ) := by
  cases c <;> simp [multiplier, inputMultiplier, frequencyChange,
    receiver, smul_smul, mul_inv_cancel₀ hr]

def retainedKernel (a : A) (c : Factor) (i : Fin 3) : 𝓢(E6, ℂ) :=
  ratio a.1 • kernel a c i

def physicalKernel (a : A) (c : Factor) (i : Fin 3) : 𝓢(E6, ℂ) :=
  if h : ratio a.1 = 0 then 0 else
    pullback (spatialChange (ratio a.1) h) (retainedKernel a c i)

def scaledKernel (N : ℝ) (hN : 0 < N) (a : A) (c : Factor) (i : Fin 3) : 𝓢(E6, ℂ) :=
  dilate N hN.ne' (physicalKernel a c i)

@[simp] theorem retainedKernel_undifferentiated (a : A) (i : Fin 3) :
    retainedKernel a .undifferentiated i = PressureCoherentDivergenceKernel.retainedKernel a i := by
  simp [retainedKernel, PressureCoherentDivergenceKernel.retainedKernel]

@[simp] theorem physicalKernel_undifferentiated (a : A) (i : Fin 3) :
    physicalKernel a .undifferentiated i =
      PressureCoherentDivergencePhysicalKernel.physicalKernel a i := by
  simp [physicalKernel, PressureCoherentDivergencePhysicalKernel.physicalKernel]

@[simp] theorem scaledKernel_undifferentiated (N : ℝ) (hN : 0 < N) (a : A) (i : Fin 3) :
    scaledKernel N hN a .undifferentiated i =
      PressureCoherentDivergencePhysicalKernel.scaledKernel N hN a i := by
  simp [scaledKernel, PressureCoherentDivergencePhysicalKernel.scaledKernel]

theorem fourier_retainedKernel (a : A) (c : Factor) (i : Fin 3) (ξ : E6) :
    (𝓕 (retainedKernel a c i)) ξ =
      (multiplier c a.1 (pairEquiv ξ) : ℂ) *
        (𝓕 (PressureCoherentDivergenceKernel.retainedKernel a i)) ξ := by
  simp [retainedKernel, PressureCoherentDivergenceKernel.retainedKernel,
    FourierTransform.fourier_smul, entry, mul_left_comm,
    Complex.real_smul]

theorem fourier_physicalKernel (a : A) (c : Factor) (i : Fin 3) (ξ : E6) :
    (𝓕 (physicalKernel a c i)) ξ =
      (inputMultiplier c (pairEquiv ξ) : ℂ) *
        (𝓕 (PressureCoherentDivergencePhysicalKernel.physicalKernel a i)) ξ := by
  by_cases hr : ratio a.1 = 0
  · simp [physicalKernel, PressureCoherentDivergencePhysicalKernel.physicalKernel, hr]
  · simp only [physicalKernel, PressureCoherentDivergencePhysicalKernel.physicalKernel,
      dif_neg hr, fourier_pullback, inverse_adjoint_eq_frequencyChange]
    rw [fourier_retainedKernel, multiplier_frequencyChange c a.1 hr]

def scaledMultiplier (N : ℝ) (c : Factor) (p : P) : ℝ :=
  inputMultiplier c (N⁻¹ • p)

@[simp] theorem scaledMultiplier_undifferentiated (N : ℝ) (p : P) :
    scaledMultiplier N .undifferentiated p = 1 := rfl

@[simp] theorem scaledMultiplier_first (N : ℝ) (j : Fin 3) (p : P) :
    scaledMultiplier N (.first j) p = N⁻¹ * p.1 j := rfl

@[simp] theorem scaledMultiplier_second (N : ℝ) (j : Fin 3) (p : P) :
    scaledMultiplier N (.second j) p = N⁻¹ * p.2 j := rfl

theorem fourier_scaledKernel (N : ℝ) (hN : 0 < N) (a : A) (c : Factor) (i : Fin 3) (ξ : E6) :
    (𝓕 (scaledKernel N hN a c i)) ξ =
      (scaledMultiplier N c (pairEquiv ξ) : ℂ) *
        (𝓕 (PressureCoherentDivergencePhysicalKernel.scaledKernel N hN a i)) ξ := by
  simp only [scaledKernel, PressureCoherentDivergencePhysicalKernel.scaledKernel,
    fourier_dilate, fourier_physicalKernel, scaledMultiplier, map_smul]

end Mettapedia.FluidDynamics.NavierStokes.PressureCoherentDivergenceChannelKernel
