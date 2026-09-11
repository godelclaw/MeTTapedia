import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressurePatchSmoothing

/-!
# Pressure localization with a charged L2 replacement error

Exact coverage and line localization belong to the continuous spatial
amplitudes. Finite Fourier cutoffs need only approximate those amplitudes
in total L2 error. The error is charged against actual pressure suprema;
no pointwise coverage of the Fourier cutoffs is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WeightedPressureL2Replacement

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeAnisotropyDepletion SpectralTiltFreezing
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open FourierPressureTiltEnergy FourierPressureHessianEnergy FourierPressurePatchEnergy
open LocalPressureCommutator WeightedProjectorTilt PressureTracePatchEnergy
open FourierPressureLocalization PressurePatchSmoothing
open Mettapedia.Analysis.QuadraticWeightStability

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {ι : Type*} [Fintype ι]

def approximationError (p : ι → C(T3, ℂ)) (c : ι → FourierCoeff (Fin 3)) : ℝ :=
  ∑ i, ∫ x : T3, ‖fourierPolynomial (c i) x - p i x‖ ^ 2

theorem approximationError_nonneg (p : ι → C(T3, ℂ)) (c : ι → FourierCoeff (Fin 3)) :
    0 ≤ approximationError p c :=
  Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))

theorem integral_spatial_patch_le_fourier (p : C(T3, ℂ)) (c : FourierCoeff (Fin 3))
    (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity)
    (hK : ∀ q, -q ∈ K ↔ q ∈ K) (e : R3) (he : ‖e‖ = 1) :
    (∫ x : T3, ‖p x‖ ^ 2 *
      ‖lineRemainder e (filteredPressureOperator chi K u x e)‖ ^ 2) ≤
        2 * frozenPatchEnergy c chi K u e +
          2 * ‖pressureField chi K u‖ ^ 2 * ∫ x : T3, ‖fourierPolynomial c x - p x‖ ^ 2 := by
  have h := integral_mul_le volume p (fourierPolynomial c)
    (fun x ↦ ‖lineRemainder e (filteredPressureOperator chi K u x e)‖ ^ 2)
    ((continuous_transverse_pressure chi K u e).norm.pow 2) (fun _ ↦ sq_nonneg _)
    (‖pressureField chi K u‖ ^ 2) (transverse_sq_le chi K u e he)
  simp_rw [norm_sub_rev (p _) (fourierPolynomial c _)] at h
  have hpoly (x : T3) : ‖fourierPolynomial c x‖ ^ 2 = quadraticWeight c x :=
    (Complex.normSq_eq_norm_sq _).symm
  simpa only [hpoly, integral_frozen_patch_eq c chi K u e hK] using h

theorem integral_weighted_tilt_le_fourier (p : ι → C(T3, ℂ)) (c : ι → FourierCoeff (Fin 3))
    (a : T3 → ℝ) (ha : Continuous a) (han : ∀ x, 0 ≤ a x)
    (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ Real.sqrt (a x) • InnerProductSpace.rankOne ℝ (e x) (e x)))
    (f : ι → R3) (hf : ∀ i, ‖f i‖ = 1) (rho : ℝ)
    (hmass : ∀ x, (∑ i, ‖p i x‖ ^ 2) = a x)
    (hline : ∀ x, (∑ i, ‖p i x‖ ^ 2 * lineDistanceSq (e x) (f i)) ≤ rho ^ 2)
    (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity)
    (hK : ∀ q, -q ∈ K ↔ q ∈ K) :
    (∫ x : T3, a x *
      ‖lineRemainder (e x) (filteredPressureOperator chi K u x (e x))‖ ^ 2) ≤
        4 * (∑ i, frozenPatchEnergy (c i) chi K u (f i)) +
          4 * ‖pressureField chi K u‖ ^ 2 * approximationError p c +
          32 * rho ^ 2 * hessianEnergy chi K u := by
  have hi (i : ι) : Integrable (fun x : T3 ↦ ‖p i x‖ ^ 2 *
      ‖lineRemainder (f i) (filteredPressureOperator chi K u x (f i))‖ ^ 2) :=
    (((p i).continuous.norm.pow 2).mul
      ((continuous_transverse_pressure chi K u (f i)).norm.pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hleft : Integrable (fun x : T3 ↦ a x *
      ‖lineRemainder (e x) (filteredPressureOperator chi K u x (e x))‖ ^ 2) :=
    (continuous_weighted_transverse_norm_sq a ha han _
      (continuous_filteredPressureOperator chi K u) e he hP).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hH := integrable_pressure_norm_sq chi K u
  have h := integral_mono hleft
    (((integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).const_mul 2).add
      (hH.const_mul (32 * rho ^ 2)))
    (fun x ↦ weighted_transverse_action_sq_le (filteredPressureOperator chi K u x)
      (e x) f (fun i ↦ ‖p i x‖ ^ 2) (he x) hf (fun _ ↦ sq_nonneg _) (a x) (rho ^ 2)
      (hmass x).ge (hline x))
  simp only [Pi.add_apply] at h
  rw [integral_add ((integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).const_mul 2)
    (hH.const_mul (32 * rho ^ 2)), integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun i _ ↦ hi i)] at h
  have hp := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦
    integral_spatial_patch_le_fourier (p i) (c i) chi K u hK (f i) (hf i))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hp
  have hE := mul_le_mul_of_nonneg_left (integral_pressure_norm_sq_le_hessianEnergy chi K u)
    (show 0 ≤ 32 * rho ^ 2 by positivity)
  unfold approximationError
  linarith only [h, hp, hE]

theorem trace_sq_le (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity) (x : T3) :
    realPressureTrace chi K u x ^ 2 ≤ ‖traceField chi K u‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) ((traceField chi K u).norm_coe_le_norm x) 2
  simpa only [traceField, ContinuousMap.coe_mk, Real.norm_eq_abs, sq_abs] using h

theorem sum_tracePatchEnergy_le_spatial (p : ι → C(T3, ℂ)) (c : ι → FourierCoeff (Fin 3))
    (a : T3 → ℝ) (hmass : ∀ x, (∑ i, ‖p i x‖ ^ 2) = a x)
    (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity)
    (hK : ∀ q, -q ∈ K ↔ q ∈ K) :
    (∑ i, tracePatchEnergy (c i) chi K u) ≤
      2 * (∫ x : T3, a x * realPressureTrace chi K u x ^ 2) +
        2 * ‖traceField chi K u‖ ^ 2 * approximationError p c := by
  have hi (i : ι) : Integrable (fun x : T3 ↦ ‖p i x‖ ^ 2 * realPressureTrace chi K u x ^ 2) :=
    (((p i).continuous.norm.pow 2).mul ((continuous_realPressureTrace chi K u).pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcell (i : ι) := integral_mul_le volume (fourierPolynomial (c i)) (p i)
    (fun x ↦ realPressureTrace chi K u x ^ 2) ((continuous_realPressureTrace chi K u).pow 2)
    (fun _ ↦ sq_nonneg _) (‖traceField chi K u‖ ^ 2) (trace_sq_le chi K u)
  have hpoly (b : FourierCoeff (Fin 3)) (x : T3) : ‖fourierPolynomial b x‖ ^ 2 = quadraticWeight b x :=
    (Complex.normSq_eq_norm_sq _).symm
  simp only [hpoly, ← tracePatchEnergy_eq_integral _ chi K u hK] at hcell
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ hcell i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  have hsum : (∑ i, ∫ x : T3, ‖p i x‖ ^ 2 * realPressureTrace chi K u x ^ 2) =
      ∫ x : T3, a x * realPressureTrace chi K u x ^ 2 := by
    rw [← integral_finsetSum _ (fun i _ ↦ hi i)]
    simp only [← Finset.sum_mul, hmass]
  rwa [hsum] at h

theorem integral_weighted_tilt_le_with_tail (p : ι → C(T3, ℂ)) (c : ι → FourierCoeff (Fin 3))
    (a : T3 → ℝ) (ha : Continuous a) (han : ∀ x, 0 ≤ a x)
    (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ Real.sqrt (a x) • InnerProductSpace.rankOne ℝ (e x) (e x)))
    (f : ι → R3) (hf : ∀ i, ‖f i‖ = 1) (rho : ℝ)
    (hmass : ∀ x, (∑ i, ‖p i x‖ ^ 2) = a x)
    (hline : ∀ x, (∑ i, ‖p i x‖ ^ 2 * lineDistanceSq (e x) (f i)) ≤ rho ^ 2)
    (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity)
    (hK : ∀ q, -q ∈ K ↔ q ∈ K) (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ x : T3, a x *
      ‖lineRemainder (e x) (filteredPressureOperator chi K u x (e x))‖ ^ 2) ≤
        16 * eta ^ 2 * (∫ x : T3, a x * realPressureTrace chi K u x ^ 2) +
          8 * (∑ i, tiltTailTraceEnergy (c i) chi K u (f i) eta) +
          8 * (∑ i, tiltCommutatorEnergy (c i) chi K u (f i)) +
          (4 * ‖pressureField chi K u‖ ^ 2 + 16 * eta ^ 2 * ‖traceField chi K u‖ ^ 2) *
            approximationError p c + 32 * rho ^ 2 * hessianEnergy chi K u := by
  have h := integral_weighted_tilt_le_fourier p c a ha han e he hP f hf rho hmass hline chi K u hK
  have hc := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦
    frozenPatchEnergy_le_with_tail (c i) chi K u (f i) (hf i) eta heta)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hc
  have ht := mul_le_mul_of_nonneg_left (sum_tracePatchEnergy_le_spatial p c a hmass chi K u hK)
    (show 0 ≤ 8 * eta ^ 2 by positivity)
  nlinarith only [h, hc, ht]

end Mettapedia.FluidDynamics.NavierStokes.WeightedPressureL2Replacement
