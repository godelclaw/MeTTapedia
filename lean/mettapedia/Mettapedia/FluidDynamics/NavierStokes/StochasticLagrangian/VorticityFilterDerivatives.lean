import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityFilterAdjoint
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeMappedFourierDiffusion

/-!
# Actual coordinate derivatives of the transferred finite filter

The multiplier is differentiated, not the input field. These are exact
finite Fourier derivatives without a bound on their size.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityFilterDerivatives

open Mettapedia.Analysis.UnitTorusFiniteFilter
open PeriodicFourierTriad PancakePeriodicVorticityEquation PancakeFourierTranslationCurve
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open FourierPressureTraceSymbol VorticityFilterAdjoint

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def filterCoefficients (χ : Wavevector → ℂ) (f : T3 → R3) (q : Wavevector) : VelocityCoefficient :=
  χ q • (fun i ↦ UnitAddTorus.mFourierCoeff (fun y ↦ complexifyVector (f y)) q i)

theorem realFilter_eq_mappedField (P : Finset Wavevector) (χ : Wavevector → ℂ) (f : T3 → R3) :
    realFilter P χ f = PancakeMappedFourierDiffusion.mappedField complexRealPartEuclideanCLM P
      (filterCoefficients χ f) := by
  funext x
  ext i
  simp [realFilter, VorticityFilterAdjoint.realPart, finiteFilter, filterCoefficients,
    PancakeMappedFourierDiffusion.mappedField, fourierField, modeField,
    complexRealPartEuclideanCLM_apply, complexRealPartEuclidean]

def filterDerivative (P : Finset Wavevector) (χ : Wavevector → ℂ) (f : T3 → R3)
    (j : Fin 3) : T3 → R3 :=
  realFilter P (fun q ↦ (unitTorusDerivativePhase * (q j : ℂ)) * χ q) f

theorem continuous_filterDerivative (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (f : T3 → R3) (j : Fin 3) : Continuous (filterDerivative P χ f j) :=
  continuous_realFilter P _ f

theorem hasDerivAt_realFilter_shift (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (f : T3 → R3) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ realFilter P χ f (x + coordinateShift j t))
      (filterDerivative P χ f j (x + coordinateShift j h)) h := by
  have he : derivativeCoeff j (filterCoefficients χ f) =
      filterCoefficients (fun q ↦ (unitTorusDerivativePhase * (q j : ℂ)) * χ q) f := by
    funext q
    simp only [derivativeCoeff, filterCoefficients, smul_smul]
  have hd := PancakeMappedFourierDiffusion.hasDerivAt_mappedField_shift
    complexRealPartEuclideanCLM P (filterCoefficients χ f) j h x
  rw [he, ← realFilter_eq_mappedField, ← realFilter_eq_mappedField] at hd
  exact hd

end Mettapedia.FluidDynamics.NavierStokes.VorticityFilterDerivatives
