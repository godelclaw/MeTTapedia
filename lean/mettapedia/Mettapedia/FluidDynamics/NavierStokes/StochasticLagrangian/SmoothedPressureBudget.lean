import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PressurePatchSmoothing

/-!
# Weighted pressure budgets with one cutoff derivative energy

The original patch family is constructed once from the weighted
projector. Every positive resolvent parameter then gives actual smoothed
polynomials. Their angular tails remain in the estimate, and smoothing
error is charged against the physical Hessian and trace supremum norms.

Only the original first-derivative patch energy remains as a cutoff cost.
Its dynamical control, and uniform pressure bounds, are separate open
estimates; the existential construction does not provide them.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.SmoothedPressureBudget

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeAnisotropyDepletion
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open FourierPressureTiltEnergy FourierPressurePatchEnergy FourierPressureLocalization
open PressureTracePatchEnergy LocalPressureCommutator FourierEllipticProductEnergy
open LocalPressureEllipticBudget FourierResolventSmoothing PressurePatchSmoothing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def derivativeCost (epsilon eta : ℝ) (chi : Wavevector → ℂ) (K : Finset Wavevector)
    (u : FourierVelocity) : ℝ :=
  1536 * potentialCoordinateBound chi K u ^ 2 +
    72 / epsilon * ‖potentialField chi K u‖ ^ 2 +
    epsilon * ‖pressureField chi K u‖ ^ 2 +
    4 * epsilon * eta ^ 2 * ‖traceField chi K u‖ ^ 2

theorem exists_weighted_smoothed_pressure_budget
    (a : T3 → ℝ) (ha : Continuous a) (han : ∀ x, 0 ≤ a x)
    (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ Real.sqrt (a x) • InnerProductSpace.rankOne ℝ (e x) (e x)))
    (rho delta : ℝ) (hr : 0 < rho) (hd : 0 < delta) :
    ∃ (centers : Finset T3) (c : ↑centers → FourierCoeff (Fin 3)),
      (∀ x, |(∑ i, quadraticWeight (c i) x) - a x| ≤ delta) ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ (chi : Wavevector → ℂ) (K : Finset Wavevector) (u : FourierVelocity),
          (∀ q, -q ∈ K ↔ q ∈ K) → ∀ eta : ℝ, 0 ≤ eta →
          (∫ x : T3, a x *
            ‖lineRemainder (e x) (filteredPressureOperator chi K u x (e x))‖ ^ 2) ≤
              16 * eta ^ 2 * (∫ x : T3, a x * realPressureTrace chi K u x ^ 2) +
                8 * (∑ i, tiltTailTraceEnergy (smoothCutoff epsilon (c i)) chi K u (e i.1) eta) +
                derivativeCost epsilon eta chi K u * (∑ i, coordinateEnergy (c i).support (c i)) +
                (32 * rho ^ 2 + 2 * delta + 16 * eta ^ 2 * delta) * hessianEnergy chi K u := by
  obtain ⟨centers, c, hmass, henergy⟩ :=
    WeightedFourierPressurePatch.exists_weighted_pressure_patches a ha han e he hP rho delta hr hd
  refine ⟨centers, c, hmass, ?_⟩
  intro epsilon hepsilon chi K u hK eta heta
  have hf := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ↑centers)) ↦
    frozenPatchEnergy_le_smooth epsilon hepsilon.le (c i) chi K u hK (e i.1) (he i.1))
  have ha' := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ↑centers)) ↦
    frozenPatchEnergy_le_with_tail (smoothCutoff epsilon (c i)) chi K u (e i.1) (he i.1) eta heta)
  have ht := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ↑centers)) ↦
    tracePatchEnergy_smooth_le epsilon hepsilon.le (c i) chi K u hK)
  have hc := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ↑centers)) ↦
    tiltCommutatorEnergy_smooth_le epsilon hepsilon (c i) chi K u (e i.1) (he i.1))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hf ha' ht hc
  have ht0 := sum_tracePatchEnergy_le_weighted c chi K u hK a ha delta hd.le
    (fun x ↦ by have hx := (abs_le.mp (hmass x)).2; linarith only [hx])
  have ht1 := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 8 * eta ^ 2)
  have ht2 := mul_le_mul_of_nonneg_left ht0 (by positivity : 0 ≤ 16 * eta ^ 2)
  have h := henergy chi K u hK
  unfold derivativeCost
  simp only [div_eq_mul_inv] at hc ⊢
  nlinarith only [h, hf, ha', hc, ht1, ht2]

open PancakeFourierMaterialPaths PancakeFilteredStrainDynamics PancakeSpectralFiniteDifference
open PancakeCurlOutputTail LocalSquaredGapPressure

/-- The weight and line are those of the actual filtered strain and full
vorticity. No global eigenvector regularity or positive spectral gap is
added. The original patches are independent of epsilon, K, and eta. -/
theorem exists_local_smoothed_pressure_budget (gamma : ℝ) (hg : 0 < gamma)
    (chi : Wavevector → ℂ) (modes : Finset Wavevector) (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (rho delta : ℝ) (hr : 0 < rho) (hd : 0 < delta) :
    let a := localWeight gamma chi modes u
    let e := fun x ↦ topVector (spatialStrain modes (filteredVelocity chi u) x)
    ∃ (centers : Finset T3) (c : ↑centers → FourierCoeff (Fin 3)),
      (∀ x, |(∑ i, quadraticWeight (c i) x) - a x| ≤ delta) ∧
      ∀ epsilon : ℝ, 0 < epsilon →
        ∀ (K : Finset Wavevector), (∀ q, -q ∈ K ↔ q ∈ K) →
          ∀ eta : ℝ, 0 ≤ eta →
          (∫ x : T3, a x *
            ‖lineRemainder (e x) (filteredPressureOperator chi K u x (e x))‖ ^ 2) ≤
              16 * eta ^ 2 * (∫ x : T3, a x * realPressureTrace chi K u x ^ 2) +
                8 * (∑ i, tiltTailTraceEnergy (smoothCutoff epsilon (c i)) chi K u (e i.1) eta) +
                derivativeCost epsilon eta chi K u * (∑ i, coordinateEnergy (c i).support (c i)) +
                (32 * rho ^ 2 + 2 * delta + 16 * eta ^ 2 * delta) * hessianEnergy chi K u := by
  dsimp only
  have hS := PancakeMaterialDiffusionBudget.continuous_strain modes (filteredVelocity chi u)
  have hw := LocalLowDiffusionBudget.continuous_fullVorticity u hu
  have hP := SquaredGapTiltWeight.continuous_weightedProjector gamma hg _ _ hS hw
  simp_rw [SquaredGapTiltWeight.weightedProjector_eq gamma hg] at hP
  obtain ⟨centers, c, hmass, henergy⟩ := exists_weighted_smoothed_pressure_budget
    (localWeight gamma chi modes u) (SquaredGapTiltWeight.continuous_weight gamma hg _ _ hS hw)
    (fun _ ↦ sq_nonneg _) _ (fun _ ↦ topVector_norm _) hP rho delta hr hd
  exact ⟨centers, c, hmass, fun epsilon hepsilon K hK eta heta ↦
    henergy epsilon hepsilon chi K u hK eta heta⟩

end Mettapedia.FluidDynamics.NavierStokes.SmoothedPressureBudget
