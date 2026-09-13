import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalLongitudinalVorticity
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatWitness

/-!
# Velocity curvature at a point with zero vorticity gradient

The smooth, real, mean-zero, divergence-free periodic snapshot is
`u = (-sin y + sin x sin z, 0, cos x cos z - cos(2x)/2)`, with
physical angles `2πx`, `2πy`, `2πz`. Its NS tangent is evaluated from
the full equation, not from an invariant finite-mode evolution.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.CoherenceCreationSnapshot

open scoped RealInnerProductSpace ComplexConjugate
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeBlockReality
open PancakeCurlOutputTail PancakeHigherDerivativeMoments PancakeIndexedFourierMoments
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open PancakeInfiniteRealCurl PancakeDyadicDirectionEvolution PancakeTransverseEnergyFreezing
open PancakeFourierTranslationCurve PancakeFourierMaterialPaths PancakePeriodicVorticityEquation
open LocalLowDiffusionBudget LocalSpatialVorticityJets FullLambVector FourierFiniteSupport
open FullVorticityGradientTransport LocalLongitudinalVorticity PancakePeriodicComplexStretch
open LocalVorticityGradientEvolution LocalJointDiffusionBudget LocalWeightedCurlCancellation
open Mettapedia.Analysis LongitudinalJetEvolution

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

def yMode : Wavevector := ![0, 1, 0]
def sumMode : Wavevector := ![1, 0, 1]
def differenceMode : Wavevector := ![1, 0, -1]
def doubleMode : Wavevector := ![2, 0, 0]
def modes : Finset Wavevector :=
  {yMode, -yMode, sumMode, -sumMode, differenceMode, -differenceMode, doubleMode, -doubleMode}

def cosineCoefficients (k : Wavevector) : Wavevector →₀ ℂ :=
  Finsupp.single k (1 / 2) + Finsupp.single (-k) (1 / 2)

def coefficients : FourierVelocity := fun q ↦
  ![-ParallelHeatFlow.sineCoefficients yMode 1 q +
      cosineCoefficients differenceMode q / 2 - cosineCoefficients sumMode q / 2,
    0, cosineCoefficients differenceMode q / 2 + cosineCoefficients sumMode q / 2 -
      cosineCoefficients doubleMode q / 2]

theorem supported (q : Wavevector) (hq : q ∉ modes) : coefficients q = 0 := by
  classical
  simp only [modes, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  rcases hq with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  ext i
  fin_cases i <;> simp [coefficients, ParallelHeatFlow.sineCoefficients, cosineCoefficients,
    h1, h2, h3, h4, h5, h6, h7, h8]

theorem transverse (q : Wavevector) : modeDot q (coefficients q) = 0 := by
  classical
  by_cases hq : q ∈ modes
  · simp only [modes, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [modeDot, coefficients, ParallelHeatFlow.sineCoefficients, cosineCoefficients,
        yMode, sumMode, differenceMode, doubleMode, Finsupp.single_apply,
        Fin.sum_univ_three, Matrix.vecCons_inj, Matrix.cons_val_two]
  · simp [supported q hq, modeDot]

theorem cosineCoefficients_neg (k q : Wavevector) :
    cosineCoefficients k (-q) = conj (cosineCoefficients k q) := by
  classical
  simp only [cosineCoefficients, Finsupp.add_apply, Finsupp.single_apply,
    neg_eq_iff_eq_neg, neg_neg]
  split_ifs <;> simp [map_ofNat]

theorem reality (q : Wavevector) : coefficients (-q) = coefficientConjugate (coefficients q) := by
  ext i
  fin_cases i <;> simp [coefficients, coefficientConjugate, cosineCoefficients_neg,
    ParallelHeatFlow.sineCoefficients_reality, map_div₀, map_ofNat]

theorem coefficients_zero : coefficients 0 = 0 := by
  apply supported
  norm_num [modes, yMode, sumMode, differenceMode, doubleMode, Matrix.vecCons_inj,
    funext_iff, Fin.forall_fin_succ]

theorem all_moments (n : ℕ) : Summable (fourierMoment n coefficients) :=
  summable_fourierMoment modes coefficients supported n

set_option maxHeartbeats 800000 in
theorem vorticity_origin : fullVorticity coefficients 0 =
    WithLp.toLp 2 ![0, 0, 2 * Real.pi] := by
  rw [fullVorticity_eq_realFullField coefficients (all_moments 1)]
  unfold realFullField
  rw [fullFourierField_eq_sum modes _ (fourierCurl_eq_zero modes coefficients supported)]
  ext i
  fin_cases i <;> norm_num [modes, coefficients, ParallelHeatFlow.sineCoefficients, cosineCoefficients,
    yMode, sumMode, differenceMode, doubleMode, Finsupp.single_apply, fourierCurl, coefficientCross,
    wavevectorCoefficient,
    unitTorusDerivativePhase, complexRealPartEuclideanCLM_apply, complexRealPartEuclidean,
    UnitAddTorus.mFourier, Fin.sum_univ_three, Matrix.vecCons_inj, Matrix.cons_val_two,
    PiLp.single_apply] <;> ring

set_option maxHeartbeats 800000 in
theorem vorticityGradient_origin (j : Fin 3) : fullCurlGradient coefficients j 0 = 0 := by
  have hs (q : Wavevector) (hq : q ∉ modes) :
      indexedDerivativeCoeff id j (fourierCurl coefficients) q = 0 := by
    simp [indexedDerivativeCoeff, fourierCurl_eq_zero modes coefficients supported q hq]
  unfold fullCurlGradient
  rw [fullFourierField_eq_sum modes _ hs]
  ext i
  fin_cases j <;> fin_cases i <;>
    norm_num [modes, coefficients, ParallelHeatFlow.sineCoefficients, cosineCoefficients,
      yMode, sumMode, differenceMode, doubleMode, Finsupp.single_apply, fourierCurl, coefficientCross,
      wavevectorCoefficient,
      indexedDerivativeCoeff, unitTorusDerivativePhase, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean, UnitAddTorus.mFourier, Fin.sum_univ_three,
      Matrix.vecCons_inj, Matrix.cons_val_two] <;> ring

set_option maxHeartbeats 800000 in
theorem velocityHessian_origin_zz : mixedGradient coefficients 2 2 0 =
    WithLp.toLp 2 ![0, 0, -(2 * Real.pi) ^ 2] := by
  have hs (q : Wavevector) (hq : q ∉ modes) :
      indexedDerivativeCoeff id 2 (indexedDerivativeCoeff id 2 coefficients) q = 0 := by
    simp [indexedDerivativeCoeff, supported q hq]
  unfold mixedGradient velocityJet
  rw [fullFourierField_eq_sum modes _ hs]
  ext i
  fin_cases i <;>
    norm_num [modes, coefficients, ParallelHeatFlow.sineCoefficients, cosineCoefficients,
      yMode, sumMode, differenceMode, doubleMode, Finsupp.single_apply,
      indexedDerivativeCoeff, unitTorusDerivativePhase, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean, UnitAddTorus.mFourier, Fin.sum_univ_three,
      Matrix.vecCons_inj, Matrix.cons_val_two, PiLp.single_apply] <;> ring

theorem longitudinal_origin : longitudinalVorticity coefficients 0 = 0 := by
  simp [longitudinalVorticity, longitudinal, vorticityGradient_origin]

theorem angularJet_origin (j : Fin 3) :
    AngularCurlDecomposition.angularJet (fullVorticity coefficients 0)
      (fun k ↦ fullCurlGradient coefficients k 0) j = 0 := by
  simp [AngularCurlDecomposition.angularJet, vorticityGradient_origin]

theorem angularDensity_origin :
    AngularCurlDecomposition.angularDensity (fullVorticity coefficients 0)
      (fun k ↦ fullCurlGradient coefficients k 0) = 0 := by
  simp [AngularCurlDecomposition.angularDensity, vorticityGradient_origin]

theorem curvatureSource_origin : curvatureSource coefficients 0 =
    WithLp.toLp 2 ![0, 0, -(2 * Real.pi) ^ 4] := by
  simp only [curvatureSource, velocityCurvature, vorticity_origin, Fin.sum_univ_three,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    zero_mul, mul_zero, zero_smul, zero_add, add_zero, velocityHessian_origin_zz]
  ext i
  fin_cases i <;> simp [PiLp.smul_apply] <;> ring

theorem curvatureSource_ne_zero : curvatureSource coefficients 0 ≠ 0 := by
  intro h
  have he := congrArg (fun v : R3 ↦ v 2) h
  rw [curvatureSource_origin] at he
  change (-(2 * Real.pi) ^ 4 : ℝ) = 0 at he
  have hp : 0 < (2 * Real.pi) ^ 4 := by positivity
  linarith

set_option maxHeartbeats 800000 in
theorem gradientLaplacian_origin_z : gradientLaplacian coefficients 2 0 = 0 := by
  have hm := summable_fourierMoment_derivative 2 (fourierCurl coefficients)
    (summable_fourierMoment_curl 3 coefficients (all_moments 4)) 2
  have hs (q : Wavevector) (hq : q ∉ modes) :
      laplacianCoeff (indexedDerivativeCoeff id 2 (fourierCurl coefficients)) q = 0 := by
    simp [laplacianCoeff, indexedDerivativeCoeff,
      fourierCurl_eq_zero modes coefficients supported q hq]
  unfold gradientLaplacian
  rw [spatialLaplacian_fullFourierField _ hm, fullFourierField_eq_sum modes _ hs]
  ext i
  fin_cases i <;>
    norm_num [modes, coefficients, ParallelHeatFlow.sineCoefficients, cosineCoefficients,
      yMode, sumMode, differenceMode, doubleMode, Finsupp.single_apply, fourierCurl, coefficientCross,
      wavevectorCoefficient, laplacianCoeff, modeSquare, indexedDerivativeCoeff,
      unitTorusDerivativePhase, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean, UnitAddTorus.mFourier, Fin.sum_univ_three,
      Matrix.vecCons_inj, Matrix.cons_val_two]

theorem viscousRate_origin : viscousRate coefficients 0 = 0 := by
  simp [viscousRate, rate, vorticityGradient_origin, vorticity_origin,
    Fin.sum_univ_three, gradientLaplacian_origin_z]

/-- The full unforced material tangent creates a longitudinal derivative at
this point for every viscosity, although the whole first vorticity jet vanishes. -/
theorem materialRate_origin (ν : ℝ) :
    materialRate ν coefficients (fun j ↦ realFullField coefficients 0 j) 0 =
      WithLp.toLp 2 ![0, 0, -(2 * Real.pi) ^ 4] := by
  rw [materialRate_eq ν coefficients (all_moments 4) transverse reality]
  simp [inviscidRate, longitudinal_origin, viscousRate_origin, curvatureSource_origin]

theorem materialRate_ne_zero (ν : ℝ) :
    materialRate ν coefficients (fun j ↦ realFullField coefficients 0 j) 0 ≠ 0 := by
  rw [materialRate_origin, ← curvatureSource_origin]
  exact curvatureSource_ne_zero

/-- Pointwise vanishing of the longitudinal derivative cannot control its
velocity-curvature source, even on admissible finite Fourier data. -/
theorem not_curvature_bound_by_longitudinal (C : ℝ) :
    ¬ ‖curvatureSource coefficients 0‖ ≤ C * ‖longitudinalVorticity coefficients 0‖ := by
  intro h
  have hh : ‖curvatureSource coefficients 0‖ ≤ 0 := by simpa [longitudinal_origin] using h
  exact curvatureSource_ne_zero (norm_le_zero_iff.mp hh)

end Mettapedia.FluidDynamics.NavierStokes.CoherenceCreationSnapshot
