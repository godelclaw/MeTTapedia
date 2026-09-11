import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierMatrixEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityGradientEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeFourierStrainGradient

/-!
# Filter-uniform strain-gradient control by vorticity-gradient energy

For real divergence-free data, contractive finite Fourier filters cannot
increase the integrated strain-gradient energy beyond the full physical
vorticity-gradient energy. No absolute Fourier moment occurs in the bound;
the summability hypothesis identifies the actual continuous derivatives.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.StrainGradientEnergy

open MeasureTheory
open scoped Matrix.Norms.Elementwise
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeFourierStrainGradient
open PancakeFilteredStrainDynamics PancakePeriodicVorticityEquation PancakeBlockReality
open PancakeViscousMisalignmentAbsorption PancakeGalerkinKineticEnergy
open PancakeInfiniteFourierDerivative PancakeIndexedFourierMoments PancakeCurlOutputTail
open FourierMatrixEnergy VorticityGradientEnergy

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem matrixEnergy_gradientCoeff (u : FourierVelocity) (q : Wavevector) :
    matrixEnergy (gradientCoeff u q) =
      ‖unitTorusDerivativePhase‖ ^ 2 * ‖frequencyVec q‖ ^ 2 * coefficientEnergy (u q) := by
  simp only [matrixEnergy, gradientCoeff, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp [norm_frequencyVec_sq, coefficientEnergy, Complex.normSq_eq_norm_sq]

theorem matrixEnergy_strainDerivativeCoeff_le (u : FourierVelocity) (q : Wavevector)
    (hd : modeDot q (u q) = 0) (j : Fin 3) :
    matrixEnergy (strainDerivativeCoeff j u q) ≤
      coefficientEnergy (indexedDerivativeCoeff id j (fourierCurl u) q) := by
  rw [strainDerivativeCoeff, matrixEnergy_smul]
  calc
    _ ≤ ‖unitTorusDerivativePhase * (q j : ℂ)‖ ^ 2 * matrixEnergy (gradientCoeff u q) :=
      mul_le_mul_of_nonneg_left (matrixEnergy_symmetrize_le _) (sq_nonneg _)
    _ = _ := by
      rw [matrixEnergy_gradientCoeff, indexedDerivativeCoeff, coefficientEnergy_smul,
        fourierCurl_energy q u hd]
      simp [unitTorusDerivativePhase, Real.pi_pos.le]

theorem strainDerivativeCoeff_filtered (chi : Wavevector → ℂ) (u : FourierVelocity)
    (q : Wavevector) (j : Fin 3) :
    strainDerivativeCoeff j (filteredVelocity chi u) q = chi q • strainDerivativeCoeff j u q := by
  ext a b
  simp [strainDerivativeCoeff, strainCoeff, gradientCoeff, filteredVelocity]
  ring

theorem matrixEnergy_filtered_strainDerivativeCoeff_le (chi : Wavevector → ℂ)
    (u : FourierVelocity) (q : Wavevector) (hchi : ‖chi q‖ ≤ 1)
    (hd : modeDot q (u q) = 0) (j : Fin 3) :
    matrixEnergy (strainDerivativeCoeff j (filteredVelocity chi u) q) ≤
      coefficientEnergy (indexedDerivativeCoeff id j (fourierCurl u) q) := by
  rw [strainDerivativeCoeff_filtered, matrixEnergy_smul]
  have hc : ‖chi q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (chi q)]
  exact (mul_le_of_le_one_left (matrixEnergy_nonneg _) hc).trans
    (matrixEnergy_strainDerivativeCoeff_le u q hd j)

theorem integral_sum_strainGradient_sq_le (chi : Wavevector → ℂ) (modes : Finset Wavevector)
    (hchi : ∀ q ∈ modes, ‖chi q‖ ≤ 1) (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u))
    (hr : ∀ q, u (-q) = coefficientConjugate (u q))
    (hd : ∀ q ∈ modes, modeDot q (u q) = 0) :
    (∫ x : T3, ∑ j : Fin 3, ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) ≤
      gradientEnergy u := by
  have hi (j : Fin 3) : Integrable (fun x : T3 ↦
      ‖strainGradient modes (filteredVelocity chi u) x j‖ ^ 2) :=
    ((continuous_operatorField modes (strainDerivativeCoeff j (filteredVelocity chi u))).norm.pow 2
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun j _ ↦ hi j)]
  calc
    _ ≤ ∑ j : Fin 3, ∑ q ∈ modes, matrixEnergy (strainDerivativeCoeff j (filteredVelocity chi u) q) :=
      Finset.sum_le_sum (fun j _ ↦ integral_operator_norm_sq_le modes _)
    _ ≤ ∑ j : Fin 3, ∑ q ∈ modes,
        coefficientEnergy (indexedDerivativeCoeff id j (fourierCurl u) q) :=
      Finset.sum_le_sum (fun j _ ↦ Finset.sum_le_sum (fun q hq ↦
        matrixEnergy_filtered_strainDerivativeCoeff_le chi u q (hchi q hq) (hd q hq) j))
    _ = ∑ q ∈ modes, coefficientGradientEnergy u q := Finset.sum_comm
    _ ≤ _ := sum_coefficientGradientEnergy_le u hu hr modes

end Mettapedia.FluidDynamics.NavierStokes.StrainGradientEnergy
