import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureLocalization

/-!
# Physical realization and aggregation of pressure trace patch energy

The scalar energy in the angular estimate is exactly the weighted square
of the real filtered Laplacian pressure. Summing patches retains their
coverage weight without a cell-count factor. The original pressure field,
not its cutoff product, is real-symmetrized.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureTracePatchEnergy

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit
open PancakeMisalignmentEnergyBridge PancakeFiniteFourierLocalization PancakeRealFourierProjection
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open FourierPressureTiltEnergy FourierPressureTraceSymbol FourierPressureLocalization
open Mettapedia.Analysis.FiniteMultiplierLocalization

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem scalarReconstruction_convolution (P K : Finset Wavevector) (c b : Wavevector → ℂ) (x : T3) :
    finiteScalarFourierReconstruction (finiteCutoffOutputModes P K) (scalarConvolution P K c b) x =
      finiteScalarFourierReconstruction P c x * finiteScalarFourierReconstruction K b x := by
  have h : finiteFourierReconstruction (finiteCutoffOutputModes P K)
      (finiteCutoffConvolutionCoeff P K c (fun k _ ↦ b k)) x =
      finiteScalarFourierReconstruction P c x • finiteFourierReconstruction K (fun k _ ↦ b k) x := by
    rw [finiteFourierReconstruction_convolutionCoeff, ← finiteScalar_mul_finiteFourierReconstruction]
  have hi := congrArg (fun v : VelocityCoefficient ↦ v 0) h
  simpa only [finiteFourierReconstruction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    finiteCutoffConvolutionCoeff, scalarConvolution, finiteScalarFourierReconstruction] using hi

theorem reconstruction_realTraceAmplitude (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (hs : ∀ q, -q ∈ outputs ↔ q ∈ outputs) (x : T3) :
    finiteScalarFourierReconstruction outputs (realTraceAmplitude chi u) x =
      ((finiteScalarFourierReconstruction outputs (traceAmplitude chi u) x).re : ℂ) := by
  have h := reconstruction_realSymmetricCoeff outputs (fun q _ ↦ traceAmplitude chi u q) hs x 0
  simpa only [finiteFourierReconstruction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    realSymmetricCoeff, realTraceAmplitude, finiteScalarFourierReconstruction] using h

def realPressureTrace (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (x : T3) : ℝ :=
  (finiteScalarFourierReconstruction outputs (traceAmplitude chi u) x).re

theorem continuous_realPressureTrace (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) : Continuous (realPressureTrace chi outputs u) :=
  Complex.continuous_re.comp (continuous_finiteScalarFourierReconstruction _ _)

/-- The scalar reconstructed from the Laplacian-pressure coefficients is
the actual trace of the filtered pressure Hessian. -/
theorem realPressureTrace_eq_sum_diagonal (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    realPressureTrace chi outputs u x = ∑ j : Fin 3,
      LocalPressureCommutator.filteredPressureOperator chi outputs u x
        ((EuclideanSpace.basisFun (Fin 3) ℝ) j) j := by
  simp_rw [FourierPressureHessianEnergy.pressure_apply_eq_real_reconstruction]
  simp only [realPressureTrace, finiteScalarFourierReconstruction,
    PancakeTransverseEnergyFreezing.complexRealPartEuclidean, PiLp.toLp_apply,
    finiteFourierReconstruction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  simp only [traceAmplitude, FourierPressureHessianEnergy.actionCoefficient,
    EuclideanSpace.inner_basisFun_real, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs,
    sq_abs, ← sq, Complex.ofReal_sum, ← Finset.mul_sum, ← Complex.re_sum, ← mul_assoc]

theorem tracePatchEnergy_eq_integral (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (hs : ∀ q, -q ∈ outputs ↔ q ∈ outputs) :
    tracePatchEnergy c chi outputs u =
      ∫ x : T3, quadraticWeight c x * realPressureTrace chi outputs u x ^ 2 := by
  have h := integral_normSq_finiteScalarFourierReconstruction (finiteCutoffOutputModes c.support outputs)
    (scalarConvolution c.support outputs c (realTraceAmplitude chi u))
  simp only [Complex.normSq_eq_norm_sq] at h
  change _ = tracePatchEnergy c chi outputs u at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [scalarReconstruction_convolution, reconstruction_realTraceAmplitude chi outputs u hs,
    scalarReconstruction_eq_fourierPolynomial, norm_mul, mul_pow]
  simp only [quadraticWeight, Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, realPressureTrace]

theorem integral_realPressureTrace_sq_le (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (hs : ∀ q, -q ∈ outputs ↔ q ∈ outputs) :
    (∫ x : T3, realPressureTrace chi outputs u x ^ 2) ≤ hessianEnergy chi outputs u := by
  have h := integral_normSq_finiteScalarFourierReconstruction outputs (realTraceAmplitude chi u)
  simp only [reconstruction_realTraceAmplitude chi outputs u hs, Complex.normSq_eq_norm_sq,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h.le.trans (scalarEnergy_realTraceAmplitude_le chi outputs u hs)

theorem sum_tracePatchEnergy_eq_integral {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (hs : ∀ q, -q ∈ outputs ↔ q ∈ outputs) :
    (∑ i, tracePatchEnergy (c i) chi outputs u) =
      ∫ x : T3, (∑ i, quadraticWeight (c i) x) * realPressureTrace chi outputs u x ^ 2 := by
  have hi (i : ι) : Integrable (fun x : T3 ↦ quadraticWeight (c i) x * realPressureTrace chi outputs u x ^ 2) :=
    ((continuous_quadraticWeight (c i)).mul ((continuous_realPressureTrace chi outputs u).pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [tracePatchEnergy_eq_integral _ chi outputs u hs, Finset.sum_mul]
  exact (integral_finsetSum _ (fun i _ ↦ hi i)).symm

/-- An approximate weighted partition leaves the original spatial weight
in the main energy. Only the coverage error uses unweighted Hessian energy. -/
theorem sum_tracePatchEnergy_le_weighted {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (hs : ∀ q, -q ∈ outputs ↔ q ∈ outputs)
    (a : T3 → ℝ) (ha : Continuous a) (delta : ℝ) (hd : 0 ≤ delta)
    (hcover : ∀ x, (∑ i, quadraticWeight (c i) x) ≤ a x + delta) :
    (∑ i, tracePatchEnergy (c i) chi outputs u) ≤
      (∫ x : T3, a x * realPressureTrace chi outputs u x ^ 2) + delta * hessianEnergy chi outputs u := by
  have ht := (continuous_realPressureTrace chi outputs u).pow 2
  have hi : Integrable (fun x : T3 ↦ a x * realPressureTrace chi outputs u x ^ 2) :=
    (ha.mul ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hT : Integrable (fun x : T3 ↦ realPressureTrace chi outputs u x ^ 2) :=
    ht.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hleft : Integrable (fun x : T3 ↦ (∑ i, quadraticWeight (c i) x) * realPressureTrace chi outputs u x ^ 2) :=
    ((continuous_finsetSum Finset.univ (fun i _ ↦ continuous_quadraticWeight (c i))).mul ht).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hright : Integrable (fun x : T3 ↦ a x * realPressureTrace chi outputs u x ^ 2 +
      delta * realPressureTrace chi outputs u x ^ 2) := hi.add (hT.const_mul delta)
  rw [sum_tracePatchEnergy_eq_integral c chi outputs u hs]
  have h := integral_mono hleft hright (fun x ↦ by
    have hx := mul_le_mul_of_nonneg_right (hcover x) (sq_nonneg (realPressureTrace chi outputs u x))
    simpa only [add_mul] using hx)
  rw [integral_add hi (hT.const_mul delta), integral_const_mul] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_realPressureTrace_sq_le chi outputs u hs) hd))

end Mettapedia.FluidDynamics.NavierStokes.PressureTracePatchEnergy
