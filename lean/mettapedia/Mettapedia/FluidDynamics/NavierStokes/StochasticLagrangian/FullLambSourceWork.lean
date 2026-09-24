import Mettapedia.Analysis.ContinuousFieldInnerProduct
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullLambVector
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.VorticityFilterDerivatives
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalKineticEnergy

/-!
# Complete nonlinear work and the transverse curl of its transferred test

Periodic curl pairing puts the derivative on the explicitly constructed
finite test. The full velocity is then paired with `omega cross curl(test)`.
Its kinetic energy pays one factor in spatial Cauchy--Schwarz. The remaining
transverse-test square is explicit and has no assumed dynamical bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FullLambSourceWork

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis EuclideanCrossProduct WeightedCurlCancellation
open PeriodicFourierTriad PancakeCurlOutputTail PancakeBlockReality PancakeHigherDerivativeMoments
open PancakeCoefficientLimitEquation PancakeFilteredStrainDynamics PancakeGalerkinKineticEnergy
open PancakeInfiniteRealCurl PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakeFourierTranslationCurve PancakeFourierMaterialPaths
open PancakeLocalInfiniteVelocity LocalLowDiffusionBudget LocalKineticEnergy
open InfiniteConvectionEnergy
open FiniteAngularSourceWork FilteredAngularSourceBalance FullAngularSourceAdjoint
open FullLambVector VorticityFilterAdjoint VorticityFilterDerivatives

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def adjointDerivative (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (j : Fin 3) : T3 → R3 :=
  filterDerivative P (fun q ↦ conj (χ q)) (correctedGradient κ (filteredVelocity χ u)) j

def adjointCurl (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) : R3 := curlJet (fun j ↦ adjointDerivative κ P χ u j x)

theorem continuous_adjointCurl (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) : Continuous (adjointCurl κ P χ u) := by
  have hd (j : Fin 3) : Continuous (adjointDerivative κ P χ u j) :=
    continuous_filterDerivative P (fun q ↦ conj (χ q)) (correctedGradient κ (filteredVelocity χ u)) j
  unfold adjointCurl curlJet
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;>
    exact ((EuclideanSpace.proj _).continuous.comp (hd _)).sub
      ((EuclideanSpace.proj _).continuous.comp (hd _))

theorem realSpatialCurl_adjointTest (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) :
    realSpatialCurl (adjointTest κ P χ u) x = adjointCurl κ P χ u x := by
  have hd (j : Fin 3) : realCoordinateDerivative (adjointTest κ P χ u) j x =
      adjointDerivative κ P χ u j x := by
    simpa only [realCoordinateDerivative, adjointTest, adjointDerivative,
      PancakeHaarTransportRate.coordinateShift_zero, add_zero] using
      (hasDerivAt_realFilter_shift P (fun q ↦ conj (χ q))
        (correctedGradient κ (filteredVelocity χ u)) j x 0).deriv
  simp only [realSpatialCurl, hd, adjointCurl, curlJet]

theorem sourceWork_eq_lamb_pairing (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    sourceWork κ χ u = ∫ x : T3, ⟪adjointCurl κ P χ u x, lambVector u x⟫ := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  rw [sourceWork_eq_full_pairing κ P χ hcut u hu hr]
  simp_rw [fullVorticity_inviscidRHS_eq_curl_lambVector u hu hd hr,
    realSpatialCurl_lambVector u hu]
  have hshift (j : Fin 3) : UnitTorusWeakDerivative.coordinateShift j = coordinateShift j := by
    funext t i
    simp [UnitTorusWeakDerivative.coordinateShift, UnitTorusWeakDerivative.torusPoint,
      UnitTorusWeakDerivative.coordinateLine, coordinateShift, torusPoint,
      PancakeFourierStrainGradient.coordinateLine]
  apply UnitTorusCurlPairing.integral_inner_curl (adjointTest κ P χ u) (lambVector u)
    (adjointDerivative κ P χ u) (lambDerivative u)
    (continuous_adjointTest κ P χ u) (continuous_lambVector u hu1)
    (fun j ↦ continuous_filterDerivative P _ _ j) (continuous_lambDerivative u hu1)
  · simpa only [hshift, adjointTest, adjointDerivative] using
      (fun j x h ↦ hasDerivAt_realFilter_shift P (fun q ↦ conj (χ q))
        (correctedGradient κ (filteredVelocity χ u)) j x h)
  · simpa only [hshift] using hasDerivAt_lambVector_shift u hu

def transverseTest (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) : R3 := cross (fullVorticity u x) (adjointCurl κ P χ u x)

def transverseTestSquare (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) : ℝ := ∫ x : T3, ‖transverseTest κ P χ u x‖ ^ 2

theorem continuous_transverseTest (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (transverseTest κ P χ u) :=
  contDiff_cross.continuous.comp ((continuous_fullVorticity u hu).prodMk
    (continuous_adjointCurl κ P χ u))

theorem transverseTestSquare_nonneg (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) : 0 ≤ transverseTestSquare κ P χ u :=
  integral_nonneg (fun _ ↦ sq_nonneg _)

/-- The parallel component is removed before any norm is taken. -/
theorem transverseTest_sub_radial (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) (c : ℝ) :
    cross (fullVorticity u x) (adjointCurl κ P χ u x - c • fullVorticity u x) =
      transverseTest κ P χ u x := by
  simp [transverseTest, cross_sub_right, cross_smul_right]

theorem sourceWork_eq_velocity_pairing (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    sourceWork κ χ u = ∫ x : T3, ⟪realFullField u x, transverseTest κ P χ u x⟫ := by
  rw [sourceWork_eq_lamb_pairing κ P χ hcut u hu hd hr]
  congr 1
  funext x
  exact inner_cross_cycle _ _ _

theorem abs_sourceWork_le_kineticEnergy (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    |sourceWork κ χ u| ≤ Real.sqrt (kineticEnergy u) * Real.sqrt (transverseTestSquare κ P χ u) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hm : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu1
  have hE := InfiniteFourierParseval.integral_norm_realPart_fullFourierField_sq_le u
    (summable_norm_coefficients id u hm)
  rw [sourceWork_eq_velocity_pairing κ P χ hcut u hu hd hr]
  have h := ContinuousFieldInnerProduct.abs_integral_inner_le (volume : Measure T3)
    (realFullField u) (transverseTest κ P χ u) (continuous_realFullField u)
    (continuous_transverseTest κ P χ u hu1)
  exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hE) (Real.sqrt_nonneg _))

theorem abs_sourceWork_solution_le_initial {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 ≤ ν)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)
    (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    |sourceWork κ χ (s.coefficients t)| ≤
      Real.sqrt (kineticEnergy u₀) * Real.sqrt (transverseTestSquare κ P χ (s.coefficients t)) := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :=
    (fourierMoment_mono (s.coefficients τ) (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)
  exact (abs_sourceWork_le_kineticEnergy κ P χ hcut _ hm (s.transverse t) (s.reality t)).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (energy_le_initial s hν g hg hSum hu2 t ht))
      (Real.sqrt_nonneg _))

end Mettapedia.FluidDynamics.NavierStokes.FullLambSourceWork
