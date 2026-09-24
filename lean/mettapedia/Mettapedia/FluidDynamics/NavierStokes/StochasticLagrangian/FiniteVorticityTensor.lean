import Mettapedia.Analysis.QuarticTensorEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPolynomialDifferential
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedProjectionEvolution

/-!
# Polynomial tensors of actual finite-support vorticity

The real curl components and their quartic tensor are constructed from
the given Fourier velocity. Products enlarge the radius by at most four;
the support size never enters the energy bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FiniteVorticityTensor

open scoped RealInnerProductSpace
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeQuadraticFourierSupport FourierPolynomialRealAlgebra
open FourierPolynomialDifferential FourierFiniteSupport PancakeCurlOutputTail
open PancakeFrequencyProjectorCommutator PancakePeriodicVorticityEquation
open PancakeGalerkinKineticEnergy
open PancakeFourierTranslationCurve PancakeHaarTransportRate
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget
open PancakePhysicalSpectralDefect PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open LocalVorticityEighthMoment
local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def packCoeff (P : Finset Wavevector) (f : Wavevector → ℂ) : FourierCoeff (Fin 3) := by
  classical
  exact Finsupp.onFinset P (fun q ↦ if q ∈ P then f q else 0)
    (fun q hq ↦ by by_contra hn; simp [hn] at hq)

theorem packCoeff_apply (P : Finset Wavevector) (f : Wavevector → ℂ) (q : Wavevector) :
    packCoeff P f q = if q ∈ P then f q else 0 := by
  classical
  rfl

theorem support_packCoeff (P : Finset Wavevector) (f : Wavevector → ℂ) :
    (packCoeff P f).support ⊆ P := by
  intro q hq
  by_contra hn
  exact Finsupp.mem_support_iff.mp hq (by simp [packCoeff_apply, hn])

theorem fourierPolynomial_packCoeff (P : Finset Wavevector) (f : Wavevector → ℂ) (x : T3) :
    fourierPolynomial (packCoeff P f) x = ∑ q ∈ P, f q * UnitAddTorus.mFourier q x := by
  rw [fourierPolynomial_eq_sum_of_support_subset _ P (support_packCoeff P f)]
  exact Finset.sum_congr rfl (fun q hq ↦ by simp [packCoeff_apply, hq])

def curlCoeff (P : Finset Wavevector) (u : FourierVelocity) (i : Fin 3) : FourierCoeff (Fin 3) :=
  realPartCoeff (packCoeff P (fun q ↦ fourierCurl u q i))

theorem fourierPolynomial_curlCoeff (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (i : Fin 3) (x : T3) :
    fourierPolynomial (curlCoeff P u i) x = ((fullVorticity u x) i : ℂ) := by
  rw [curlCoeff, fourierPolynomial_realPartCoeff, fourierPolynomial_packCoeff,
    fullVorticity_eq_spatialVorticity P u hs]
  simp [spatialVorticity, complexRealPartEuclidean, Finset.sum_apply,
    PancakePeriodicCoherentSplit.finiteFourierReconstruction, mul_comm]

def normSquareCoeff (P : Finset Wavevector) (u : FourierVelocity) : FourierCoeff (Fin 3) :=
  productCoeff (curlCoeff P u 0) (curlCoeff P u 0) +
    productCoeff (curlCoeff P u 1) (curlCoeff P u 1) +
    productCoeff (curlCoeff P u 2) (curlCoeff P u 2)

def tensorCoeff (P : Finset Wavevector) (u : FourierVelocity) (i j : Fin 3) : FourierCoeff (Fin 3) :=
  productCoeff (normSquareCoeff P u) (productCoeff (curlCoeff P u i) (curlCoeff P u j))

theorem fourierPolynomial_normSquareCoeff (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (x : T3) :
    fourierPolynomial (normSquareCoeff P u) x = (‖fullVorticity u x‖ ^ 2 : ℝ) := by
  simp only [normSquareCoeff, fourierPolynomial_add, ContinuousMap.add_apply,
    fourierPolynomial_productCoeff, ContinuousMap.mul_apply, fourierPolynomial_curlCoeff P u hs]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_three, sq]

theorem fourierPolynomial_tensorCoeff (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (i j : Fin 3) (x : T3) :
    fourierPolynomial (tensorCoeff P u i j) x =
      (PeriodicRadialRiesz.quarticTensorEntry (fullVorticity u x) i j : ℂ) := by
  simp only [tensorCoeff, fourierPolynomial_productCoeff, ContinuousMap.mul_apply,
    fourierPolynomial_normSquareCoeff P u hs, fourierPolynomial_curlCoeff P u hs,
    PeriodicRadialRiesz.quarticTensorEntry, Complex.ofReal_mul]
  ring

theorem hasRadius_curlCoeff (P : Finset Wavevector) (u : FourierVelocity) (R : ℝ)
    (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R) (i : Fin 3) : HasRadius (curlCoeff P u i) R :=
  hasRadius_realPart (fun q hq ↦ hP q (support_packCoeff P _ hq))

theorem hasRadius_tensorCoeff (P : Finset Wavevector) (u : FourierVelocity) (R : ℝ)
    (hP : ∀ q ∈ P, ‖frequencyVec q‖ ≤ R) (i j : Fin 3) :
    HasRadius (tensorCoeff P u i j) (4 * R) := by
  have hc := hasRadius_curlCoeff P u R hP
  have hn : HasRadius (normSquareCoeff P u) (R + R) :=
    hasRadius_add (hasRadius_add (hasRadius_product (hc 0) (hc 0))
      (hasRadius_product (hc 1) (hc 1))) (hasRadius_product (hc 2) (hc 2))
  have h := hasRadius_product hn (hasRadius_product (hc i) (hc j))
  rw [show R + R + (R + R) = 4 * R by ring] at h
  exact h

theorem fourierPolynomial_tensorDerivative (P : Finset Wavevector) (u : FourierVelocity)
    (hs : ∀ q, q ∉ P → u q = 0) (i j k : Fin 3) (x : T3) :
    fourierPolynomial (ParallelHeatFlow.derivativeCoeff (tensorCoeff P u i j) k) x =
      (PeriodicRadialRiesz.quarticTensorRate (fullVorticity u x) (fullCurlGradient u k x) i j : ℂ) := by
  have hp := hasDerivAt_fourierPolynomial_shift (tensorCoeff P u i j) k x 0
  have hv := hasDerivAt_fullVorticity_shift u (summable_fourierMoment P u hs 3) k x 0
  have ht := (PeriodicRadialRiesz.hasDerivAt_quarticTensorEntry hv i j).ofReal_comp
  simp only [coordinateShift_zero, add_zero] at hp hv ht
  simp_rw [fourierPolynomial_tensorCoeff P u hs] at hp
  exact hp.unique ht

end Mettapedia.FluidDynamics.NavierStokes.FiniteVorticityTensor
