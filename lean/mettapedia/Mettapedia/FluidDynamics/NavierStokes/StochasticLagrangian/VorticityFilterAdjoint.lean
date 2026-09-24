import Mettapedia.Analysis.UnitTorusFiniteFilter
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullVorticityFourierCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FiniteVorticityVariation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityStretchingKernel

/-!
# Moving the vorticity filter onto a real test field

The velocity has its full Fourier support. Only the output filter is
finite. Complex symbols are allowed: taking the real part gives the
actual real vorticity, and the adjoint conjugates the symbol.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityFilterAdjoint

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis.UnitTorusFiniteFilter
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakePeriodicCoherentSplit PancakeBlockReality
open LocalFilteredVorticity
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakeFilteredStrainDynamics PancakePhysicalSpectralDefect FourierFiniteSupport
open FourierPressureTraceSymbol FullVorticityFourierCoefficients LocalLowDiffusionBudget
open VorticityStretchingKernel

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def realPart (z : C3) : R3 := WithLp.toLp 2 (fun i ↦ (z i).re)

theorem continuous_realPart : Continuous realPart := by
  unfold realPart
  fun_prop

theorem inner_realPart (a : R3) (z : C3) :
    ⟪a, realPart z⟫_ℝ = (⟪complexifyVector a, z⟫_ℂ).re := by
  simp [realPart, complexifyVector, coefficientVec, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, Complex.mul_re]

def realFilter (P : Finset Wavevector) (χ : Wavevector → ℂ) (f : T3 → R3) (x : T3) : R3 :=
  realPart (finiteFilter P χ (fun y ↦ complexifyVector (f y)) x)

theorem continuous_realFilter (P : Finset Wavevector) (χ : Wavevector → ℂ) (f : T3 → R3) :
    Continuous (realFilter P χ f) :=
  continuous_realPart.comp (continuous_finiteFilter P χ _)

theorem continuous_complexify_field (f : T3 → R3) (hf : Continuous f) :
    Continuous (fun x ↦ complexifyVector (f x)) := by
  unfold complexifyVector coefficientVec
  fun_prop

theorem integral_inner_realFilter_eq_adjoint (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (f g : T3 → R3) (hf : Continuous f) (hg : Continuous g) :
    (∫ x : T3, ⟪f x, realFilter P χ g x⟫_ℝ) =
      ∫ x : T3, ⟪realFilter P (fun q ↦ conj (χ q)) f x, g x⟫_ℝ := by
  have hfc := continuous_complexify_field f hf
  have hgc := continuous_complexify_field g hg
  have hleft : Integrable (fun x : T3 ↦
      ⟪complexifyVector (f x), finiteFilter P χ (fun y ↦ complexifyVector (g y)) x⟫_ℂ) :=
    (hfc.inner (continuous_finiteFilter P χ _)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hright : Integrable (fun x : T3 ↦
      ⟪finiteFilter P (fun q ↦ conj (χ q)) (fun y ↦ complexifyVector (f y)) x,
        complexifyVector (g x)⟫_ℂ) :=
    ((continuous_finiteFilter P _ _).inner hgc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [realFilter, inner_realPart]
  have hl := integral_re hleft
  have hr := integral_re hright
  simp only [RCLike.re_to_complex] at hl hr
  rw [hl, integral_inner_finiteFilter_eq_adjoint P χ _ _ hfc hgc, ← hr]
  congr 1
  funext x
  have hs := inner_re_symm (𝕜 := ℂ)
    (finiteFilter P (fun q ↦ conj (χ q)) (fun y ↦ complexifyVector (f y)) x)
    (complexifyVector (g x))
  simp only [RCLike.re_to_complex] at hs
  rw [hs, ← inner_realPart, real_inner_comm]

theorem realFilter_fullVorticity (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (x : T3) :
    realFilter P χ (fullVorticity u) x = fullVorticity (filteredVelocity χ u) x := by
  have hs (q : Wavevector) (hq : q ∉ P) : filteredVelocity χ u q = 0 := by
    simp [filteredVelocity, hcut q hq]
  rw [fullVorticity_eq_spatialVorticity P _ hs]
  simp only [realFilter, finiteFilter, mFourierCoeff_fullVorticity u hu hr]
  ext i
  simp [realPart, coefficientVec, spatialVorticity, finiteFourierReconstruction,
    fourierCurl_filteredVelocity, filteredVelocity, complexRealPartEuclidean]

theorem integral_inner_filteredVorticity_eq_adjoint (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (hcut : ∀ q, q ∉ P → χ q = 0)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (f : T3 → R3) (hf : Continuous f) :
    (∫ x : T3, ⟪f x, fullVorticity (filteredVelocity χ u) x⟫_ℝ) =
      ∫ x : T3, ⟪realFilter P (fun q ↦ conj (χ q)) f x, fullVorticity u x⟫_ℝ := by
  simp_rw [← realFilter_fullVorticity P χ hcut u hu hr]
  exact integral_inner_realFilter_eq_adjoint P χ f _ hf (continuous_fullVorticity u hu)

end Mettapedia.FluidDynamics.NavierStokes.VorticityFilterAdjoint
