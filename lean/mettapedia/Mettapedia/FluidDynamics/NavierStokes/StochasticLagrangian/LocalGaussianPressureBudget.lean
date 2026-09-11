import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalGaussianFourierBudget
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SmoothedPressureL2Budget

/-!
# An actual Gaussian pressure budget with all replacement costs charged

The strain/vorticity field constructs the spatial cover once. Every
positive Fourier approximation error then gives finite coefficients,
independently of the pressure output truncation and smoothing parameter.
The cutoff derivative energy is bounded by the actual spatial density.

Angular tails, pressure suprema, inverse-gap costs and time/scale
uniformity are not assumed away. This is a spatial estimate, not an
unconditional regularity theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressureBudget

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeCurlOutputTail
open PancakePeriodicVorticityEquation PancakeHigherDerivativeMoments
open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeSpectralFiniteDifference
open PancakeAnisotropyDepletion PancakeQuadraticFourierSupport FourierEllipticProductEnergy
open FourierPressureTiltEnergy FourierPressureLocalization PressureTracePatchEnergy LocalPressureCommutator
open LocalSquaredGapPressure LocalGaussianPressurePartition LocalGaussianGradientBudget
open LocalGaussianFourierBudget AdaptiveGaussianLinePartition
open FourierResolventSmoothing WeightedPressureL2Replacement SmoothedPressureL2Budget

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_local_gaussian_pressure_budget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 3 u)) (rho : ℝ) (hr : 0 < rho) :
    ∃ centers : Finset T3, centers.Nonempty ∧
      let tau := temperature centers.card rho
      let a := localWeight gamma chi modes u
      let e := localDirection chi modes u
      0 < tau ∧ ∀ delta : ℝ, 0 < delta → ∃ c : ↑centers → FourierCoeff (Fin 3),
        (∑ i, ∫ x : T3, ‖fourierPolynomial (c i) x -
          (patch gamma chi modes u centers tau i x : ℂ)‖ ^ 2) < delta ∧
        ‖unitTorusDerivativePhase‖ ^ 2 * (∑ i, coordinateEnergy (c i).support (c i)) ≤
          (∫ x : T3, gradientDensity gamma chi modes u rho tau x) ∧
        ∀ epsilon : ℝ, 0 < epsilon → ∀ K : Finset Wavevector,
          (∀ q, -q ∈ K ↔ q ∈ K) → ∀ eta : ℝ, 0 ≤ eta →
          (∫ x : T3, a x *
            ‖lineRemainder (e x) (filteredPressureOperator chi K u x (e x))‖ ^ 2) ≤
              16 * eta ^ 2 * (∫ x : T3, a x * realPressureTrace chi K u x ^ 2) +
                8 * (∑ i, tiltTailTraceEnergy (smoothCutoff epsilon (c i)) chi K u (e i.1) eta) +
                derivativeCost epsilon eta chi K u / ‖unitTorusDerivativePhase‖ ^ 2 *
                  (∫ x : T3, gradientDensity gamma chi modes u rho tau x) +
                replacementCost eta chi K u * delta + 32 * rho ^ 2 * hessianEnergy chi K u := by
  obtain ⟨centers, hc, ht, hp, hmass, hline, hfamily⟩ :=
    exists_local_gaussian_fourier_family gamma hg chi modes u hu rho hr
  let tau := temperature centers.card rho
  let p : ↑centers → C(T3, ℂ) := fun i ↦
    ⟨fun x ↦ (patch gamma chi modes u centers tau i x : ℂ), Complex.continuous_ofReal.comp (hp i)⟩
  have hmass' (x : T3) : (∑ i, ‖p i x‖ ^ 2) = localWeight gamma chi modes u x := by
    simpa only [p, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hmass x
  have hline' (x : T3) : (∑ i, ‖p i x‖ ^ 2 *
      SpectralTiltFreezing.lineDistanceSq (localDirection chi modes u x) (localDirection chi modes u i.1)) ≤ rho ^ 2 := by
    simpa only [p, ContinuousMap.coe_mk, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hline x
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hw := LocalLowDiffusionBudget.continuous_fullVorticity u
    (summable_fourierMoment_of_le u (by omega : 1 ≤ 3) hu)
  have ha := SquaredGapTiltWeight.continuous_weight gamma hg _ _ hS hw
  have hP := SquaredGapTiltWeight.continuous_weightedProjector gamma hg _ _ hS hw
  simp_rw [SquaredGapTiltWeight.weightedProjector_eq gamma hg] at hP
  refine ⟨centers, hc, ht, ?_⟩
  intro delta hd
  obtain ⟨c, herr, hgrad⟩ := hfamily delta hd
  refine ⟨c, herr, hgrad, ?_⟩
  intro epsilon hepsilon K hK eta heta
  have h := integral_weighted_tilt_le_smoothed p c (localWeight gamma chi modes u) ha
    (fun _ ↦ sq_nonneg _) (localDirection chi modes u) (fun _ ↦ topVector_norm _) hP
    (fun i ↦ localDirection chi modes u i.1) (fun _ ↦ topVector_norm _) rho hmass' hline'
    epsilon hepsilon chi K u hK eta heta
  have herror : approximationError p c < delta := herr
  have hphase : 0 < ‖unitTorusDerivativePhase‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr unitTorusDerivativePhase_ne_zero) 2
  have hG : (∑ i, coordinateEnergy (c i).support (c i)) ≤
      (∫ x : T3, gradientDensity gamma chi modes u rho tau x) / ‖unitTorusDerivativePhase‖ ^ 2 :=
    (le_div_iff₀ hphase).mpr (by simpa only [mul_comm] using hgrad)
  have hcost := mul_le_mul_of_nonneg_left hG (derivativeCost_nonneg epsilon eta hepsilon.le chi K u)
  have herrorCost := mul_le_mul_of_nonneg_left herror.le (replacementCost_nonneg eta chi K u)
  simp only [div_eq_mul_inv] at hcost ⊢
  nlinarith only [h, hcost, herrorCost]

end Mettapedia.FluidDynamics.NavierStokes.LocalGaussianPressureBudget
