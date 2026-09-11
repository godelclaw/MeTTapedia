import Mettapedia.Analysis.SignedCrossKernel
import Mettapedia.Analysis.UnitTorusFourierTranslation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ComplexPressurePair
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullVorticityFourierCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakePhysicalNonlinearReconstruction

/-!
# The even periodic Biot--Savart kernel for signed stretching

The real part of each Fourier character gives an even, finite kernel.
Its quadratic action is identified with the actual reconstructed strain
using curl recovery and the reality of the full vorticity. The zero mode
is harmless because both its gradient and its projection symbol vanish.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel

open scoped RealInnerProductSpace ComplexConjugate Matrix
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeFrequencyProjectorCommutator PancakePeriodicComplexStretch PancakePeriodicVorticityEquation
open PancakeCurlOutputTail PancakeBlockReality
open PancakeFourierPressureStrain PancakeFourierMaterialPaths PancakeGalerkinKineticEnergy
open PancakePhysicalNonlinearReconstruction PancakeDyadicDirectionEvolution
open FourierPressureCommutator FourierPressureTraceSymbol ComplexPressurePair
open LocalLowDiffusionBudget FullVorticityFourierCoefficients
open Mettapedia.Analysis.EuclideanCrossProduct
open Mettapedia.Analysis.UnitTorusFourierTranslation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def projectionSymbol (k : Wavevector) : R3 →L[ℝ] R3 :=
  (‖realFrequency k‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (realFrequency k) (realFrequency k)

theorem projectionSymbol_apply (k : Wavevector) (a : R3) :
    projectionSymbol k a = (⟪realFrequency k, a⟫ / ‖realFrequency k‖ ^ 2) • realFrequency k := by
  simp only [projectionSymbol, smul_apply, InnerProductSpace.rankOne_apply, smul_smul]
  congr 1
  ring

def kernel (modes : Finset Wavevector) (z : T3) : R3 →L[ℝ] R3 :=
  ∑ k ∈ modes, (UnitAddTorus.mFourier k z).re • projectionSymbol k

theorem continuous_kernel (modes : Finset Wavevector) : Continuous (kernel modes) := by
  unfold kernel
  exact continuous_finsetSum _ (fun k _ ↦
    (Complex.continuous_re.comp (UnitAddTorus.mFourier k).continuous).smul continuous_const)

theorem real_character_sub_swap (k : Wavevector) (x y : T3) :
    (UnitAddTorus.mFourier k (y - x)).re = (UnitAddTorus.mFourier k (x - y)).re := by
  rw [mFourier_sub, mFourier_sub, UnitAddTorus.mFourier_neg, UnitAddTorus.mFourier_neg]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem kernel_sub_swap (modes : Finset Wavevector) (x y : T3) :
    kernel modes (y - x) = kernel modes (x - y) := by
  simp only [kernel, real_character_sub_swap]

def quadraticSymbol (k : Wavevector) (a : R3) : R3 := cross (projectionSymbol k a) a

theorem inner_quadraticSymbol (k : Wavevector) (a b : R3) :
    ⟪quadraticSymbol k a, b⟫ = ⟪cross a b, projectionSymbol k a⟫ := by
  rw [quadraticSymbol, real_inner_comm, inner_cross_cycle, real_inner_comm]

theorem coefficientDot_quadraticSymbol (k : Wavevector) (a : R3) (w : VelocityCoefficient) :
    coefficientDot (realCoefficient (quadraticSymbol k a)) w =
      coefficientDot (realCoefficient a) (unitTorusStrainStretchAmp k w (realCoefficient a)) := by
  rw [unitTorusStrainStretchAmp_eq_neg_complexStretchAmp]
  simp only [quadraticSymbol, projectionSymbol_apply, cross_smul_left]
  simp [coefficientDot, realCoefficient, complexStretchAmp, complexBiotSavartAmp,
    coefficientCross, wavevectorCoefficient, modeDot, modeSquare_eq_real,
    cross, realFrequency, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_three, crossProduct, Matrix.vecHead, Matrix.vecTail, Pi.smul_apply]
  ring

theorem inner_complexify_coefficientVec (a : R3) (v : VelocityCoefficient) :
    inner ℂ (complexifyVector a) (coefficientVec v) = coefficientDot (realCoefficient a) v := by
  simp [complexifyVector, coefficientVec, realCoefficient, coefficientDot,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem inner_complexify (a b : R3) :
    inner ℂ (complexifyVector a) (complexifyVector b) = (⟪a, b⟫ : ℝ) := by
  simp [complexifyVector, coefficientVec, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Complex.ofReal_sum, mul_comm]

theorem real_quadratic_form (A : MatrixCoefficient) (a : R3) :
    (coefficientDot (realCoefficient a) (A.mulVec (realCoefficient a))).re =
      ⟪a, realMatrixOperator A a⟫ := by
  simp [coefficientDot, realCoefficient, Matrix.mulVec, dotProduct, realMatrixOperator_apply,
    EuclideanSpace.inner_eq_star_dotProduct, Complex.mul_re, Finset.mul_sum,
    mul_comm, mul_left_comm]

theorem continuous_complexify (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (fun y : T3 ↦ complexifyVector (fullVorticity u y)) := by
  have hw := continuous_fullVorticity u hu
  unfold complexifyVector coefficientVec
  fun_prop

theorem integral_character_sub_vorticity (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (k : Wavevector) (x : T3) :
    (∫ y : T3, UnitAddTorus.mFourier k (x - y) • complexifyVector (fullVorticity u y)) =
      UnitAddTorus.mFourier k x • coefficientVec (fourierCurl u k) := by
  simp_rw [mFourier_sub, mul_smul]
  rw [integral_smul]
  exact congrArg (fun z : C3 ↦ UnitAddTorus.mFourier k x • z)
    (mFourierCoeff_fullVorticity u hu hr k)

/-- A real character selects the real part of the actual curl coefficient. -/
theorem integral_real_character_inner (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (k : Wavevector) (x : T3) (c : R3) :
    (∫ y : T3, (UnitAddTorus.mFourier k (x - y)).re * ⟪c, fullVorticity u y⟫) =
      (UnitAddTorus.mFourier k x * coefficientDot (realCoefficient c) (fourierCurl u k)).re := by
  have hc : Continuous (fun y : T3 ↦ UnitAddTorus.mFourier k (x - y) •
      complexifyVector (fullVorticity u y)) :=
    ((UnitAddTorus.mFourier k).continuous.comp (continuous_const.sub continuous_id)).smul
      (continuous_complexify u hu)
  have hi : Integrable (fun y : T3 ↦ UnitAddTorus.mFourier k (x - y) •
      complexifyVector (fullVorticity u y)) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := (innerSL ℂ (complexifyVector c)).integral_comp_comm hi
  rw [integral_character_sub_vorticity u hu hr] at h
  simp only [innerSL_apply_apply, inner_smul_right, inner_complexify, inner_complexify_coefficientVec] at h
  have hs : Integrable (fun y : T3 ↦ UnitAddTorus.mFourier k (x - y) *
      (⟪c, fullVorticity u y⟫ : ℝ)) := by
    have hcont : Continuous (fun y : T3 ↦ UnitAddTorus.mFourier k (x - y) *
        (⟪c, fullVorticity u y⟫ : ℝ)) :=
      ((UnitAddTorus.mFourier k).continuous.comp (continuous_const.sub continuous_id)).mul
        (Complex.continuous_ofReal.comp (continuous_const.inner (continuous_fullVorticity u hu)))
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre := integral_re hs
  simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hre
  exact hre.trans (congrArg Complex.re h)

/-- Curl recovery in the stretching symbol includes the zero mode. -/
theorem strainStretch_fourierCurl (k : Wavevector) (u : FourierVelocity)
    (w : VelocityCoefficient) (hd : modeDot k (u k) = 0) :
    unitTorusStrainStretchAmp k (fourierCurl u k) w = (strainCoeff u k).mulVec w := by
  by_cases hk : k = 0
  · subst k
    ext i
    simp [unitTorusStrainStretchAmp, strainCoeff, gradientCoeff, modeDot,
      wavevectorCoefficient, coefficientDot, Matrix.mulVec, dotProduct]
  · exact unitTorusStrainStretchAmp_fourierCurl k u w (frequencyVec_ne_zero hk) hd

theorem integral_singleMode_stretch (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (k : Wavevector)
    (hd : modeDot k (u k) = 0) (x : T3) (a : R3) :
    (∫ y : T3, (UnitAddTorus.mFourier k (x - y)).re *
      ⟪cross a (fullVorticity u y), projectionSymbol k a⟫) =
      ⟪a, realMatrixOperator (UnitAddTorus.mFourier k x • strainCoeff u k) a⟫ := by
  simp_rw [← inner_quadraticSymbol]
  rw [integral_real_character_inner u hu hr, coefficientDot_quadraticSymbol,
    strainStretch_fourierCurl k u _ hd]
  rw [← real_quadratic_form]
  congr 1
  simp only [Matrix.smul_mulVec, coefficientDot_smul_right]

/-- The receiver is the full physical vorticity, even when the strain is truncated. -/
theorem integral_kernel_stretch (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (x : T3) (a : R3) :
    (∫ y : T3, ⟪cross a (fullVorticity u y), kernel modes (x - y) a⟫) =
      ⟪a, (spatialStrain modes u x).1 a⟫ := by
  have hi (k : Wavevector) : Integrable (fun y : T3 ↦
      (UnitAddTorus.mFourier k (x - y)).re *
        ⟪cross a (fullVorticity u y), projectionSymbol k a⟫) := by
    have hc : Continuous (fun y : T3 ↦ (UnitAddTorus.mFourier k (x - y)).re *
        ⟪cross a (fullVorticity u y), projectionSymbol k a⟫) :=
      (Complex.continuous_re.comp ((UnitAddTorus.mFourier k).continuous.comp
        (continuous_const.sub continuous_id))).mul
        ((Mettapedia.Analysis.SignedCrossKernel.continuous_cross.comp
          (continuous_const.prodMk (continuous_fullVorticity u hu))).inner continuous_const)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [kernel, sum_apply, smul_apply, inner_sum,
    real_inner_smul_right]
  rw [integral_finsetSum _ (fun k _ ↦ hi k)]
  simp_rw [integral_singleMode_stretch u hu hr _ (hd _)]
  change _ = ⟪a, realMatrixOperator (∑ k ∈ modes,
    UnitAddTorus.mFourier k x • strainCoeff u k) a⟫
  change _ = ⟪a, realMatrixOperatorCLM (∑ k ∈ modes,
    UnitAddTorus.mFourier k x • strainCoeff u k) a⟫
  simp only [map_sum, sum_apply, inner_sum,
    realMatrixOperatorCLM_apply]

end Mettapedia.FluidDynamics.NavierStokes.VorticityStretchingKernel
