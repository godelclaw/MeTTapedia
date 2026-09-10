import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressurePatchEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.WeightedLineFreezing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.WeightedProjectorTilt
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.QuadraticFourierWeightApproximation

/-!
# Pressure patches retaining a spatially varying weight

Approximate the square roots of the weighted partition, not just the
partition itself. The resulting frozen energies contain the original
spatial weight. Only the explicitly prescribed additive error is paid
against unweighted pressure Hessian energy. Neither a cell-count factor
nor the supremum of the spatial weight occurs in this estimate.

The patches and their bandwidth depend on the weight and projector. This
is not a time-integrated, scale-uniform bound for their frozen energies.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.WeightedFourierPressurePatch

open scoped BigOperators
open MeasureTheory
open PeriodicFourierTriad PancakeAnisotropyDepletion SpectralTiltFreezing
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open FourierPressureTiltEnergy FourierPressureHessianEnergy FourierPressurePatchEnergy
open LocalPressureCommutator WeightedProjectorTilt QuadraticFourierWeightApproximation

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem exists_weighted_patch_energy_bound {ι : Type*} [Fintype ι]
    (weight : PartitionOfUnity ι T3) (a : T3 → ℝ) (ha : Continuous a) (han : ∀ x, 0 ≤ a x)
    (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ Real.sqrt (a x) • InnerProductSpace.rankOne ℝ (e x) (e x)))
    (f : ι → R3) (hf : ∀ i, ‖f i‖ = 1) (rho delta : ℝ) (hd : 0 < delta)
    (hactive : ∀ i x, weight i x ≠ 0 → a x * lineDistanceSq (e x) (f i) ≤ rho ^ 2) :
    ∃ c : ι → FourierCoeff (Fin 3),
      (∀ x, |(∑ i, quadraticWeight (c i) x) - a x| ≤ delta) ∧
      ∀ (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity),
        (∀ q, -q ∈ outputs ↔ q ∈ outputs) →
        (∫ x : T3, a x *
          ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
            2 * (∑ i, frozenPatchEnergy (c i) chi outputs u (f i)) +
              (32 * rho ^ 2 + 2 * delta) * hessianEnergy chi outputs u := by
  let b : ι → C(T3, ℝ) := fun i ↦ ⟨fun x ↦ a x * weight i x, ha.mul (weight i).continuous⟩
  have hb (i : ι) (x : T3) : 0 ≤ b i x := mul_nonneg (han x) (weight.nonneg i x)
  obtain ⟨c, hc⟩ := exists_finite_quadraticWeight_approximation b hb delta hd
  have hsum (x : T3) : (∑ i, b i x) = a x := by
    have hw : (∑ i, weight i x) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using weight.sum_eq_one (Set.mem_univ x)
    change (∑ i, a x * weight i x) = a x
    rw [← Finset.mul_sum, hw, mul_one]
  have hframe (x : T3) : (∑ i, b i x * lineDistanceSq (e x) (f i)) ≤ rho ^ 2 := by
    have hcell (i : ι) : b i x * lineDistanceSq (e x) (f i) ≤ weight i x * rho ^ 2 := by
      by_cases hz : weight i x = 0
      · simp [b, hz]
      · have h := mul_le_mul_of_nonneg_left (hactive i x hz) (weight.nonneg i x)
        dsimp only [b, ContinuousMap.coe_mk]
        nlinarith only [h]
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hcell i)
    have hw : (∑ i, weight i x) = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using weight.sum_eq_one (Set.mem_univ x)
    simpa only [← Finset.sum_mul, hw, one_mul] using h
  refine ⟨c, ?_, ?_⟩
  · intro x
    rw [← hsum x, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (hc x)
  · intro chi outputs u hs
    have hi (i : ι) : Integrable (fun x : T3 ↦ quadraticWeight (c i) x *
        ‖lineRemainder (f i) (filteredPressureOperator chi outputs u x (f i))‖ ^ 2) :=
      ((continuous_quadraticWeight (c i)).mul
        ((continuous_transverse_pressure chi outputs u (f i)).norm.pow 2)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have heI : Integrable (fun x : T3 ↦ a x *
        ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) :=
      (continuous_weighted_transverse_norm_sq a ha han _
      (continuous_filteredPressureOperator chi outputs u) e he hP).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hH := integrable_pressure_norm_sq chi outputs u
    have h := integral_mono heI
      (((integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).const_mul 2).add
        (hH.const_mul (32 * rho ^ 2 + 2 * delta)))
      (fun x ↦ weighted_transverse_le_approximation (filteredPressureOperator chi outputs u x)
        (e x) f (he x) hf (fun i ↦ b i x) (fun i ↦ quadraticWeight (c i) x)
          (fun i ↦ hb i x) (a x) (rho ^ 2) delta (hsum x).ge (hframe x) (hc x))
    change (∫ x : T3, a x *
      ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
      ∫ x : T3, 2 * (∑ i, quadraticWeight (c i) x *
        ‖lineRemainder (f i) (filteredPressureOperator chi outputs u x (f i))‖ ^ 2) +
          (32 * rho ^ 2 + 2 * delta) * ‖filteredPressureOperator chi outputs u x‖ ^ 2 at h
    rw [integral_add ((integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).const_mul 2)
      (hH.const_mul (32 * rho ^ 2 + 2 * delta)), integral_const_mul, integral_const_mul,
      integral_finsetSum _ (fun i _ ↦ hi i)] at h
    simp_rw [integral_frozen_patch_eq _ chi outputs u _ hs] at h
    exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (integral_pressure_norm_sq_le_hessianEnergy chi outputs u) (by positivity)))

/-- Construct the weighted cells and Fourier cutoffs from a continuous
weighted projector, including across zeros of its scalar weight. -/
theorem exists_weighted_pressure_patches
    (a : T3 → ℝ) (ha : Continuous a) (han : ∀ x, 0 ≤ a x)
    (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ Real.sqrt (a x) • InnerProductSpace.rankOne ℝ (e x) (e x)))
    (rho delta : ℝ) (hr : 0 < rho) (hd : 0 < delta) :
    ∃ (centers : Finset T3) (c : ↑centers → FourierCoeff (Fin 3)),
      (∀ x, |(∑ i, quadraticWeight (c i) x) - a x| ≤ delta) ∧
      ∀ (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity),
        (∀ q, -q ∈ outputs ↔ q ∈ outputs) →
        (∫ x : T3, a x *
          ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
            2 * (∑ i, frozenPatchEnergy (c i) chi outputs u (e i.1)) +
              (32 * rho ^ 2 + 2 * delta) * hessianEnergy chi outputs u := by
  obtain ⟨centers, weight, hactive⟩ :=
    WeightedLineFreezing.exists_partition_of_continuous_weighted_projector a han e he hP rho hr
  obtain ⟨c, hmass, henergy⟩ := exists_weighted_patch_energy_bound weight a ha han e he hP
    (fun i ↦ e i.1) (fun i ↦ he i.1) rho delta hd hactive
  exact ⟨centers, c, hmass, henergy⟩

end Mettapedia.FluidDynamics.NavierStokes.WeightedFourierPressurePatch
