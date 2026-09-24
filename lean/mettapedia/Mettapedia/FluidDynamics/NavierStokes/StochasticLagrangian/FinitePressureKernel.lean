import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressureBilinearOperator
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeBilinearPeriodization
import Mettapedia.Analysis.FiniteTorusSymbolKernel

/-!
# A genuine six-torus kernel for a finite pressure symbol

The kernel is constructed, and its Fourier coefficients are proved to be
the actual retained pressure-pair operators. This finite realization alone
does not supply a frequency-uniform kernel-mass estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FinitePressureKernel

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeBilinearPeriodization PressureBilinearOperator
open Mettapedia.Analysis

local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
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

def firstWavevector (n : Fin 6 → ℤ) : Wavevector := fun i ↦ n (Fin.castAdd 3 i)
def secondWavevector (n : Fin 6 → ℤ) : Wavevector := fun i ↦ n (Fin.natAdd 3 i)

theorem first_pairWavevector (k p : Wavevector) : firstWavevector (pairWavevector k p) = k := by
  ext i
  exact Fin.append_left _ _ _

theorem second_pairWavevector (k p : Wavevector) : secondWavevector (pairWavevector k p) = p := by
  ext i
  exact Fin.append_right _ _ _

def pairModes (P K : Finset Wavevector) : Finset (Fin 6 → ℤ) :=
  (P ×ˢ K).image (fun kp ↦ pairWavevector kp.1 kp.2)

theorem mem_pairModes_iff (P K : Finset Wavevector) (k p : Wavevector) :
    pairWavevector k p ∈ pairModes P K ↔ k ∈ P ∧ p ∈ K := by
  constructor
  · intro h
    obtain ⟨⟨k', p'⟩, hp, he⟩ := Finset.mem_image.mp h
    have hk := congrArg firstWavevector he
    have hl := congrArg secondWavevector he
    simp only [first_pairWavevector] at hk
    simp only [second_pairWavevector] at hl
    simpa only [hk, hl] using Finset.mem_product.mp hp
  · rintro ⟨hk, hp⟩
    exact Finset.mem_image.mpr ⟨(k, p), Finset.mem_product.mpr ⟨hk, hp⟩, rfl⟩

def pressureKernel (e : R3) (he : ‖e‖ = 1) (P K : Finset Wavevector) :
    T6 → C3 →L[ℂ] C3 →L[ℂ] C3 :=
  FiniteTorusSymbolKernel.kernel (pairModes P K)
    (fun n ↦ pressurePairOperator e he (firstWavevector n) (secondWavevector n))

theorem continuous_pressureKernel (e : R3) (he : ‖e‖ = 1) (P K : Finset Wavevector) :
    Continuous (pressureKernel e he P K) := FiniteTorusSymbolKernel.continuous_kernel _ _

theorem integrable_pressureKernel (e : R3) (he : ‖e‖ = 1) (P K : Finset Wavevector) :
    Integrable (pressureKernel e he P K) := by
  exact (continuous_pressureKernel e he P K).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem mFourierCoeff_pressureKernel (e : R3) (he : ‖e‖ = 1) (P K : Finset Wavevector)
    (k p : Wavevector) : UnitAddTorus.mFourierCoeff (pressureKernel e he P K) (pairWavevector k p) =
      if k ∈ P ∧ p ∈ K then pressurePairOperator e he k p else 0 := by
  simp only [pressureKernel, FiniteTorusSymbolKernel.mFourierCoeff_kernel,
    mem_pairModes_iff, first_pairWavevector, second_pairWavevector]

end Mettapedia.FluidDynamics.NavierStokes.FinitePressureKernel
