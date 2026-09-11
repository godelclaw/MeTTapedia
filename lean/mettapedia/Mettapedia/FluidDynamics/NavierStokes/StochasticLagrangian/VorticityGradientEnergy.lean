import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFourierParseval
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalSpatialVorticityJets
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeLocalStrainReality

/-!
# Parseval for the actual vorticity-gradient energy

Conjugate symmetry is retained explicitly: taking real parts of an
arbitrary complex field need not preserve its Fourier energy. The energy
here uses the ordinary full vorticity derivatives, without a mode cutoff.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityGradientEnergy

open MeasureTheory
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeInfiniteFourierDerivative PancakeInfiniteRealCurl PancakeBlockReality
open PancakeGalerkinKineticEnergy PancakeViscousMisalignmentAbsorption
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakeIndexedFourierMoments PancakeCurlOutputTail LocalSpatialVorticityJets
open InfiniteFourierParseval PancakeLocalStrainReality

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem hasSum_coefficientEnergy_real (u : FourierVelocity)
    (hu : Summable (fun q ↦ ‖u q‖))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    HasSum (fun q ↦ coefficientEnergy (u q))
      (∫ x : T3, ‖complexRealPartEuclidean (fullFourierField id u x)‖ ^ 2) := by
  have he (x : T3) : ‖coefficientVec (fullFourierField id u x)‖ ^ 2 =
      ‖complexRealPartEuclidean (fullFourierField id u x)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    change ‖fullFourierField id u x i‖ ^ 2 = ‖(fullFourierField id u x i).re‖ ^ 2
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, fullFourierField_im_zero u hu hr x i]
    simp [Real.norm_eq_abs, pow_two]
  simpa only [he] using hasSum_coefficientEnergy u hu

def coefficientGradientEnergy (u : FourierVelocity) (q : Wavevector) : ℝ :=
  ∑ j : Fin 3, coefficientEnergy (indexedDerivativeCoeff id j (fourierCurl u) q)

def gradientEnergy (u : FourierVelocity) : ℝ :=
  ∫ x : T3, ∑ j : Fin 3, ‖fullCurlGradient u j x‖ ^ 2

theorem coefficientGradientEnergy_nonneg (u : FourierVelocity) (q : Wavevector) :
    0 ≤ coefficientGradientEnergy u q :=
  Finset.sum_nonneg (fun _ _ ↦ PancakeArbitraryDataBlocks.coefficientEnergy_nonneg _)

theorem gradientEnergy_nonneg (u : FourierVelocity) : 0 ≤ gradientEnergy u :=
  integral_nonneg (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

theorem hasSum_coefficientGradientEnergy (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    HasSum (coefficientGradientEnergy u) (gradientEnergy u) := by
  have hw : Summable (indexedFirstMoment id (fourierCurl u)) := by
    simpa only [indexedFirstMoment_id] using summable_firstMoment_curl u hu
  have hs (j : Fin 3) : HasSum
      (fun q ↦ coefficientEnergy (indexedDerivativeCoeff id j (fourierCurl u) q))
      (∫ x : T3, ‖fullCurlGradient u j x‖ ^ 2) :=
    hasSum_coefficientEnergy_real _ (summable_norm_derivativeCoefficients id _ hw j)
      (indexedDerivativeCoeff_conjugate _ (fourierCurl_real u hr) j)
  have hi (j : Fin 3) : Integrable (fun x : T3 ↦ ‖fullCurlGradient u j x‖ ^ 2) :=
    (((complexRealPartEuclideanCLM.continuous.comp (fullFourierField id
      (indexedDerivativeCoeff id j (fourierCurl u))).continuous)).norm.pow 2
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold coefficientGradientEnergy gradientEnergy
  rw [integral_finsetSum _ (fun j _ ↦ hi j)]
  exact hasSum_sum (fun j _ ↦ hs j)

theorem sum_coefficientGradientEnergy_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) (modes : Finset Wavevector) :
    (∑ q ∈ modes, coefficientGradientEnergy u q) ≤ gradientEnergy u :=
  sum_le_hasSum modes (fun q _ ↦ coefficientGradientEnergy_nonneg u q)
    (hasSum_coefficientGradientEnergy u hu hr)

end Mettapedia.FluidDynamics.NavierStokes.VorticityGradientEnergy
