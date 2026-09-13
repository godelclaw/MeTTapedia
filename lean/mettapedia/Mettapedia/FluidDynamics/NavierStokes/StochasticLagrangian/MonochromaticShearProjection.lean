import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ParallelHeatGeometry
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedProjectionEvolution
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalWeightedCurlCancellation

/-!
# Projection energy at the exact frequency of a monochromatic shear

The real, mean-zero field is `u = (0, 0, A sin(2πx))`. It belongs to the
exact unforced parallel heat-flow family. Its curl and double curl are
orthogonal, so regularization does not reduce its projection energy.
This tests simultaneous spectral matching and coercivity of the correction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.MonochromaticShearProjection

open scoped RealInnerProductSpace ComplexConjugate
open MeasureTheory Mettapedia.Analysis
open PeriodicFourierTriad PancakeGalerkinKineticEnergy PancakeCurlOutputTail
open PancakeBlockReality PancakePeriodicVorticityEquation
open PancakePhysicalSpectralDefect PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeInfiniteFourierDerivative PancakeInfiniteSpatialCurl PancakeInfiniteSpatialLaplacian
open PancakeIndexedFourierMoments PancakeFourierMaterialPaths PancakeDyadicDirectionEvolution
open PancakeLocalGradientEquation PancakeTransverseEnergyFreezing
open LocalLowDiffusionBudget LocalSpatialVorticityJets LocalJointDiffusionBudget LocalAlignmentForcing
open LocalVorticityEighthMoment LocalWeightedProjectionEvolution LocalHelicityProjectionEvolution
open FourierFiniteSupport

local notation "T3" => UnitAddTorus (Fin 3)
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def wave : Wavevector := ![1, 0, 0]
def modes : Finset Wavevector := {wave, -wave}
def scalarData (A : ℝ) : Wavevector →₀ ℂ := ParallelHeatFlow.sineCoefficients wave A
def velocity (A : ℝ) : FourierVelocity := fun q ↦ ParallelHeatFlow.vertical (scalarData A q)
def cosine (x : T3) : ℝ := (UnitAddTorus.mFourier wave x).re
def sine (x : T3) : ℝ := (UnitAddTorus.mFourier wave x).im
def eigenvalue : ℝ := (2 * Real.pi) ^ 2

theorem negative_wave_re (x : T3) : (UnitAddTorus.mFourier ![-1, 0, 0] x).re =
    (UnitAddTorus.mFourier ![1, 0, 0] x).re := by
  simpa [wave] using congrArg Complex.re (UnitAddTorus.mFourier_neg (n := wave) (x := x))

theorem negative_wave_im (x : T3) : (UnitAddTorus.mFourier ![-1, 0, 0] x).im =
    -(UnitAddTorus.mFourier ![1, 0, 0] x).im := by
  simpa [wave] using congrArg Complex.im (UnitAddTorus.mFourier_neg (n := wave) (x := x))

theorem eigenvalue_pos : 0 < eigenvalue := by unfold eigenvalue; positivity

theorem horizontal (A : ℝ) : ParallelHeatFlow.IsHorizontal (scalarData A) :=
  ParallelHeatFlow.sineCoefficients_horizontal wave (by simp [wave]) A

theorem transverse (A : ℝ) (q : Wavevector) : modeDot q (velocity A q) = 0 :=
  ParallelHeatFlow.transverse (horizontal A) q

theorem reality (A : ℝ) (q : Wavevector) : velocity A (-q) = coefficientConjugate (velocity A q) := by
  unfold velocity scalarData
  rw [ParallelHeatFlow.sineCoefficients_reality, ParallelHeatFlow.vertical_conj]

theorem supported (A : ℝ) (q : Wavevector) (hq : q ∉ modes) : velocity A q = 0 := by
  simp only [modes, Finset.mem_insert, Finset.mem_singleton, not_or] at hq
  simp [velocity, scalarData, ParallelHeatFlow.sineCoefficients, hq.1, hq.2]

theorem vorticity_eq (A : ℝ) (x : T3) : fullVorticity (velocity A) x =
    WithLp.toLp 2 ![0, -(2 * Real.pi) * A * cosine x, 0] := by
  rw [fullVorticity_eq_spatialVorticity modes _ (supported A)]
  ext i
  fin_cases i <;>
    norm_num [spatialVorticity, finiteFourierReconstruction, modes, velocity, scalarData, ParallelHeatFlow.sineCoefficients,
      ParallelHeatFlow.vertical, wave, fourierCurl, coefficientCross, wavevectorCoefficient, unitTorusDerivativePhase,
      Finsupp.single_apply, complexRealPartEuclideanCLM_apply, complexRealPartEuclidean,
      UnitAddTorus.mFourier_neg, cosine, Complex.mul_re, Complex.mul_im,
      Matrix.vecCons_inj, Matrix.cons_val_two, negative_wave_re, negative_wave_im]
  all_goals ring_nf
  all_goals simp +decide

theorem doubleCurl_eq (A : ℝ) (x : T3) : fullVorticity (fourierCurl (velocity A)) x =
    WithLp.toLp 2 ![0, 0, eigenvalue * A * sine x] := by
  rw [fullVorticity_eq_spatialVorticity modes _ (fourierCurl_eq_zero modes _ (supported A))]
  ext i
  fin_cases i <;>
    norm_num [spatialVorticity, finiteFourierReconstruction, modes, velocity, scalarData, ParallelHeatFlow.sineCoefficients,
      ParallelHeatFlow.vertical, wave, fourierCurl, coefficientCross, wavevectorCoefficient, unitTorusDerivativePhase,
      Finsupp.single_apply, complexRealPartEuclideanCLM_apply, complexRealPartEuclidean,
      UnitAddTorus.mFourier_neg, sine, eigenvalue, Complex.mul_re, Complex.mul_im,
      Matrix.vecCons_inj, Matrix.cons_val_two, negative_wave_re, negative_wave_im]
  all_goals ring_nf
  all_goals simp +decide

theorem vorticityGradient_eq (A : ℝ) (j : Fin 3) (x : T3) : fullCurlGradient (velocity A) j x =
    if j = 0 then WithLp.toLp 2 ![0, eigenvalue * A * sine x, 0] else 0 := by
  have hs (q : Wavevector) (hq : q ∉ modes) : indexedDerivativeCoeff id j (fourierCurl (velocity A)) q = 0 := by
    simp [indexedDerivativeCoeff, fourierCurl_eq_zero modes _ (supported A) q hq]
  rw [fullCurlGradient, fullFourierField_eq_sum modes _ hs]
  ext i
  fin_cases i <;> fin_cases j <;>
    norm_num [modes, velocity, scalarData, ParallelHeatFlow.sineCoefficients,
      ParallelHeatFlow.vertical, wave, indexedDerivativeCoeff, fourierCurl, coefficientCross, wavevectorCoefficient,
      unitTorusDerivativePhase, Finsupp.single_apply, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean, UnitAddTorus.mFourier_neg, sine, eigenvalue,
      Complex.mul_re, Complex.mul_im, Matrix.vecCons_inj, Matrix.cons_val_two,
      negative_wave_re, negative_wave_im]
  all_goals ring_nf
  all_goals simp +decide

theorem vorticityLaplacian_eq (A : ℝ) (x : T3) : fullVorticityLaplacian (velocity A) x =
    -eigenvalue • fullVorticity (velocity A) x := by
  have hs (q : Wavevector) (hq : q ∉ modes) : laplacianCoeff (fourierCurl (velocity A)) q = 0 := by
    simp [laplacianCoeff, fourierCurl_eq_zero modes _ (supported A) q hq]
  rw [fullVorticityLaplacian, spatialCurl_velocity _ (summable_fourierMoment modes _ (supported A) 1),
    spatialLaplacian_fullFourierField _ (summable_fourierMoment modes _
      (fourierCurl_eq_zero modes _ (supported A)) 2), fullFourierField_eq_sum modes _ hs, vorticity_eq]
  ext i
  fin_cases i <;>
    norm_num [modes, velocity, scalarData, ParallelHeatFlow.sineCoefficients,
      ParallelHeatFlow.vertical, wave, laplacianCoeff, modeSquare, fourierCurl, coefficientCross, wavevectorCoefficient,
      unitTorusDerivativePhase, Finsupp.single_apply, complexRealPartEuclideanCLM_apply,
      complexRealPartEuclidean, UnitAddTorus.mFourier_neg, cosine, eigenvalue,
      Complex.mul_re, Complex.mul_im, Matrix.vecCons_inj, Matrix.cons_val_two, Fin.sum_univ_three,
      negative_wave_re, negative_wave_im]
  all_goals ring_nf
  all_goals simp +decide [Complex.I_sq, Complex.mul_re, ← Complex.ofReal_pow] <;> ring

end Mettapedia.FluidDynamics.NavierStokes.MonochromaticShearProjection
