import Mettapedia.Analysis.OcticCurlCancellation
import Mettapedia.Analysis.UnitTorusDivergenceFreeTransport
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullLambSourceWork

/-!
# Complete source work after exact gradient removal

An actual periodic gradient pairs to zero with the full incompressible
velocity. Subtracting the gradient of `7/8 * ‖ω‖⁸` before Cauchy--Schwarz
retains the longitudinal radial derivative and the full test mismatch.
The resulting square is not assumed to have a dynamical bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FullLambGradientWork

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis EuclideanCrossProduct WeightedCurlCancellation
open RadialPower OcticCurlCancellation
open PeriodicFourierTriad PancakeCurlOutputTail PancakeBlockReality PancakeHigherDerivativeMoments
open PancakeInfiniteRealCurl PancakeIndexedFourierMoments PancakeInfiniteFourierDerivative
open PancakeFourierTranslationCurve PancakeFourierMaterialPaths PancakeHaarTransportRate
open PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing PancakeGalerkinKineticEnergy
open PancakeFilteredStrainDynamics PancakeLocalInfiniteVelocity PancakeCoefficientLimitEquation
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalKineticEnergy InfiniteConvectionEnergy
open FullLambVector FullLambSourceWork FilteredAngularSourceBalance FullAngularSourceAdjoint

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_velocity_gradient_eq_zero (u : FourierVelocity)
    (hu : Summable (fourierMoment 2 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (φ : T3 → ℝ) (D : Fin 3 → T3 → ℝ) (hφ : Continuous φ) (hD : ∀ j, Continuous (D j))
    (hdφ : ∀ j x h, HasDerivAt (fun t ↦ φ (x + coordinateShift j t))
      (D j (x + coordinateShift j h)) h) :
    (∫ x : T3, ⟪realFullField u x, WithLp.toLp 2 (fun j ↦ D j x)⟫) = 0 := by
  have hz := UnitTorusContinuousRate.integral_sum_mul_rate_eq_zero φ D
    (fun j x ↦ realFullField u x j) (fun j x ↦ velocityJet u j x j) coordinateShift hφ hD
    (fun j ↦ (EuclideanSpace.proj j).continuous.comp (continuous_realFullField u))
    (fun j ↦ (EuclideanSpace.proj j).continuous.comp (continuous_velocityJet u j))
    continuous_coordinateShift coordinateShift_zero hdφ
    (fun j x h ↦ by
      simpa [EuclideanSpace.inner_single_left] using
        (hasDerivAt_const h (EuclideanSpace.single j (1 : ℝ))).inner ℝ
          (hasDerivAt_realFullField_shift u (summable_firstMoment_of_second u hu) j x h))
    (sum_velocityJet_diagonal u hu hd)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
    PiLp.toLp_apply, mul_comm] using hz

def radialPotentialGradient (u : FourierVelocity) (x : T3) : R3 :=
  potentialGradient (fullVorticity u x) (fun j ↦ fullCurlGradient u j x)

theorem continuous_radialPotentialGradient (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) : Continuous (radialPotentialGradient u) := by
  have ha := continuous_fullVorticity u hu
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  unfold radialPotentialGradient potentialGradient potentialRate
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  exact continuous_pi (fun j ↦ (continuous_const.mul (ha.norm.pow 6)).mul (ha.inner (hD j)))

theorem integral_velocity_radialPotentialGradient (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0) :
    (∫ x : T3, ⟪realFullField u x, radialPotentialGradient u x⟫) = 0 := by
  have ha := continuous_fullVorticity u (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have hD := LocalSquaredGapGradient.continuous_fullCurlGradient u
  exact integral_velocity_gradient_eq_zero u
    (summable_fourierMoment_of_le u (by omega : 2 ≤ 3) hu) hd
    (fun x ↦ potential (fullVorticity u x))
    (fun j x ↦ potentialRate (fullVorticity u x) (fullCurlGradient u j x))
    (continuous_const.mul (ha.norm.pow 8))
    (fun j ↦ (continuous_const.mul (ha.norm.pow 6)).mul (ha.inner (hD j)))
    (fun j x h ↦ hasDerivAt_potential (hasDerivAt_fullVorticity_shift u hu j x h))

def remainder (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) : R3 :=
  transverseTest κ P χ u x - radialPotentialGradient u x

def remainderSquare (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) : ℝ := ∫ x : T3, ‖remainder κ P χ u x‖ ^ 2

def testMismatch (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (x : T3) : R3 :=
  adjointTest κ P χ u x - radialPower 6 (fullVorticity u x)

theorem hasDerivAt_testMismatch_shift (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (j : Fin 3) (x : T3) (h : ℝ) :
    HasDerivAt (fun t ↦ testMismatch κ P χ u (x + coordinateShift j t))
      (adjointDerivative κ P χ u j (x + coordinateShift j h) -
        evenRadialRate 2 (fullVorticity u (x + coordinateShift j h))
          (fullCurlGradient u j (x + coordinateShift j h))) h := by
  exact (VorticityFilterDerivatives.hasDerivAt_realFilter_shift P (fun q ↦ conj (χ q))
    (FiniteAngularSourceWork.correctedGradient κ (filteredVelocity χ u)) j x h).sub
      (hasDerivAt_radialPower_even 2 (hasDerivAt_fullVorticity_shift u hu j x h))

theorem realSpatialCurl_testMismatch (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (x : T3) :
    realSpatialCurl (testMismatch κ P χ u) x =
      curlJet (fun j ↦ adjointDerivative κ P χ u j x -
        evenRadialRate 2 (fullVorticity u x) (fullCurlGradient u j x)) := by
  have hd (j : Fin 3) : realCoordinateDerivative (testMismatch κ P χ u) j x =
      adjointDerivative κ P χ u j x - evenRadialRate 2 (fullVorticity u x) (fullCurlGradient u j x) := by
    simpa only [realCoordinateDerivative, coordinateShift_zero, add_zero] using
      (hasDerivAt_testMismatch_shift κ P χ u hu j x 0).deriv
  simp only [realSpatialCurl, hd, curlJet]

theorem continuous_remainder (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 1 u)) :
    Continuous (remainder κ P χ u) :=
  (continuous_transverseTest κ P χ u hu).sub (continuous_radialPotentialGradient u hu)

theorem remainderSquare_nonneg (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) : 0 ≤ remainderSquare κ P χ u := integral_nonneg (fun _ ↦ sq_nonneg _)

/-- The mismatch is the actual adjoint-test derivative minus the radial
vorticity derivative. No alignment of the nonlocal test is asserted. -/
theorem remainder_eq_longitudinal_add_mismatch (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (u : FourierVelocity) (x : T3) :
    remainder κ P χ u x =
      -longitudinalRate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) +
        cross (fullVorticity u x) (curlJet (fun j ↦ adjointDerivative κ P χ u j x -
          evenRadialRate 2 (fullVorticity u x) (fullCurlGradient u j x))) :=
  cross_curlJet_sub_gradient _ _ _

theorem remainder_eq_longitudinal_add_curl_mismatch (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (x : T3) :
    remainder κ P χ u x =
      -longitudinalRate (fullVorticity u x) (fun j ↦ fullCurlGradient u j x) +
        cross (fullVorticity u x) (realSpatialCurl (testMismatch κ P χ u) x) := by
  rw [remainder_eq_longitudinal_add_mismatch, realSpatialCurl_testMismatch κ P χ u hu]

theorem remainder_eq_angularJet_add_curl_mismatch (κ : ℝ) (P : Finset Wavevector)
    (χ : Wavevector → ℂ) (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (x : T3) :
    remainder κ P χ u x =
      -(‖fullVorticity u x‖ ^ 4 •
        ((∑ j, fullVorticity u x j • AngularCurlDecomposition.angularJet
            (fullVorticity u x) (fun k ↦ fullCurlGradient u k x) j) -
          (7 * ∑ j, AngularCurlDecomposition.angularJet
            (fullVorticity u x) (fun k ↦ fullCurlGradient u k x) j j) • fullVorticity u x)) +
        cross (fullVorticity u x) (realSpatialCurl (testMismatch κ P χ u) x) := by
  rw [remainder_eq_longitudinal_add_curl_mismatch κ P χ u hu,
    longitudinalRate_eq_angularJet _ _ (LocalWeightedCurlCancellation.sum_fullCurlGradient_diagonal_eq_zero u hu x)]

theorem sourceWork_eq_remainder_pairing (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    sourceWork κ χ u = ∫ x : T3, ⟪realFullField u x, remainder κ P χ u x⟫ := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hi : Integrable (fun x : T3 ↦ ⟪realFullField u x, transverseTest κ P χ u x⟫) :=
    ((continuous_realFullField u).inner (continuous_transverseTest κ P χ u hu1)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun x : T3 ↦ ⟪realFullField u x, radialPotentialGradient u x⟫) :=
    ((continuous_realFullField u).inner (continuous_radialPotentialGradient u hu1)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [remainder, inner_sub_right]
  rw [integral_sub hi hj, integral_velocity_radialPotentialGradient u hu hd, sub_zero]
  exact sourceWork_eq_velocity_pairing κ P χ hcut u hu hd hr

theorem norm_remainder_le (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (u : FourierVelocity) (hu : Summable (fourierMoment 3 u)) (x : T3) :
    ‖remainder κ P χ u x‖ ≤
      7 * ‖fullVorticity u x‖ ^ 6 * ‖∑ j, fullVorticity u x j • fullCurlGradient u j x‖ +
        ‖fullVorticity u x‖ * ‖realSpatialCurl (testMismatch κ P χ u) x‖ := by
  rw [realSpatialCurl_testMismatch κ P χ u hu]
  exact norm_cross_curlJet_sub_gradient_le _ _ _

theorem abs_sourceWork_le_remainderSquare (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    |sourceWork κ χ u| ≤ Real.sqrt (kineticEnergy u) * Real.sqrt (remainderSquare κ P χ u) := by
  have hu1 := summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu
  have hm : Summable (indexedFirstMoment id u) := by simpa only [indexedFirstMoment_id] using hu1
  have hE := InfiniteFourierParseval.integral_norm_realPart_fullFourierField_sq_le u
    (summable_norm_coefficients id u hm)
  rw [sourceWork_eq_remainder_pairing κ P χ hcut u hu hd hr]
  have h := ContinuousFieldInnerProduct.abs_integral_inner_le (volume : Measure T3)
    (realFullField u) (remainder κ P χ u) (continuous_realFullField u)
    (continuous_remainder κ P χ u hu1)
  exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hE) (Real.sqrt_nonneg _))

theorem abs_sourceWork_solution_le_initial (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) {ν T B : ℝ} {u₀ : FourierVelocity}
    (s : LocalInfiniteVelocitySolution ν u₀ T B) (hν : 0 ≤ ν)
    (g : Wavevector → ℝ) (hg : ∀ q, 0 ≤ g q) (hSum : Summable g)
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ q, fourierMoment 3 (s.coefficients t) q ≤ g q)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    |sourceWork κ χ (s.coefficients t)| ≤
      Real.sqrt (kineticEnergy u₀) * Real.sqrt (remainderSquare κ P χ (s.coefficients t)) := by
  have hu2 (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) T) (q : Wavevector) :=
    (fourierMoment_mono (s.coefficients τ) (by omega : 2 ≤ 3) q).trans (hu τ hτ q)
  have hm := hSum.of_nonneg_of_le (fourierMoment_nonneg _ _) (hu t ht)
  exact (abs_sourceWork_le_remainderSquare κ P χ hcut _ hm (s.transverse t) (s.reality t)).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (energy_le_initial s hν g hg hSum hu2 t ht))
      (Real.sqrt_nonneg _))

/-- Gradient subtraction is optional: a fixed gradient need not decrease
the norm for every filter. Both valid estimates remain available. -/
theorem abs_sourceWork_le_min (κ : ℝ) (P : Finset Wavevector) (χ : Wavevector → ℂ)
    (hcut : ∀ q, q ∉ P → χ q = 0) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (hd : ∀ q, modeDot q (u q) = 0)
    (hr : ∀ q, u (-q) = coefficientConjugate (u q)) :
    |sourceWork κ χ u| ≤ Real.sqrt (kineticEnergy u) *
      min (Real.sqrt (transverseTestSquare κ P χ u)) (Real.sqrt (remainderSquare κ P χ u)) := by
  rw [mul_min_of_nonneg _ _ (Real.sqrt_nonneg _)]
  exact le_min (abs_sourceWork_le_kineticEnergy κ P χ hcut u hu hd hr)
    (abs_sourceWork_le_remainderSquare κ P χ hcut u hu hd hr)

end Mettapedia.FluidDynamics.NavierStokes.FullLambGradientWork
