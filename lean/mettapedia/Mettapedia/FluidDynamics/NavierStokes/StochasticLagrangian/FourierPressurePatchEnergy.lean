import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTiltFreezing
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.RealFourierLocalizationEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierLinePartition
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.AdaptiveLinePartition

/-!
# Pressure tilt localized to a finite family of Fourier patches

The squared cutoff weights are realized exactly by collected Fourier
convolutions. Coverage and total line error control the patch sum without
a cell-count factor. Approximation tails are retained, not treated as
compact spatial support. The localized frozen-pressure energies remain
explicit on the right side and require their own angular estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressurePatchEnergy

open scoped BigOperators
open Filter MeasureTheory
open PeriodicFourierTriad PancakeAnisotropyDepletion
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open LocalPressureCommutator FourierPressureTiltEnergy FourierPressureHessianEnergy
open FourierPressureTiltFreezing SpectralTiltFreezing RealFourierLocalizationEnergy FourierLinePartition

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def frozenPatchEnergy (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (f : R3) : ℝ :=
  localizedEnergy c outputs (tiltCoefficient chi u f)

theorem integral_frozen_patch_eq (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (f : R3)
    (hs : ∀ q, -q ∈ outputs ↔ q ∈ outputs) :
    (∫ x : T3, quadraticWeight c x *
      ‖lineRemainder f (filteredPressureOperator chi outputs u x f)‖ ^ 2) =
      frozenPatchEnergy c chi outputs u f := by
  simp_rw [transverse_pressure_eq_real_reconstruction]
  exact integral_quadraticWeight_real_reconstruction_sq c outputs (tiltCoefficient chi u f) hs

theorem frozenPatchEnergy_nonneg (c : FourierCoeff (Fin 3)) (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (f : R3) :
    0 ≤ frozenPatchEnergy c chi outputs u f := localizedEnergy_nonneg _ _ _

theorem integral_variable_tilt_le_patch_energy_of_integrable {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (hs : ∀ q, -q ∈ outputs ↔ q ∈ outputs)
    (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1)
    (heI : Integrable (fun x : T3 ↦
      ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2))
    (f : ι → R3) (hf : ∀ i, ‖f i‖ = 1) (a B : ℝ) (hB : 0 ≤ B)
    (hcover : ∀ x, a ≤ ∑ i, quadraticWeight (c i) x)
    (hframe : ∀ x, (∑ i, quadraticWeight (c i) x * lineDistanceSq (e x) (f i)) ≤ B) :
    a * (∫ x : T3, ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
      2 * (∑ i, frozenPatchEnergy (c i) chi outputs u (f i)) + 32 * B * hessianEnergy chi outputs u := by
  have hi (i : ι) : Integrable (fun x : T3 ↦ quadraticWeight (c i) x *
      ‖lineRemainder (f i) (filteredPressureOperator chi outputs u x (f i))‖ ^ 2) :=
    ((continuous_quadraticWeight (c i)).mul
      ((continuous_transverse_pressure chi outputs u (f i)).norm.pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hH := integrable_pressure_norm_sq chi outputs u
  have h := integral_mono (heI.const_mul a)
    (((integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).const_mul 2).add (hH.const_mul (32 * B)))
    (fun x ↦ weighted_transverse_action_sq_le (filteredPressureOperator chi outputs u x)
      (e x) f (fun i ↦ quadraticWeight (c i) x) (he x) hf (fun _ ↦ Complex.normSq_nonneg _)
        a B (hcover x) (hframe x))
  change (∫ x : T3, a * ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
    ∫ x : T3, 2 * (∑ i, quadraticWeight (c i) x *
      ‖lineRemainder (f i) (filteredPressureOperator chi outputs u x (f i))‖ ^ 2) +
      (32 * B) * ‖filteredPressureOperator chi outputs u x‖ ^ 2 at h
  rw [integral_const_mul, integral_add
    ((integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).const_mul 2) (hH.const_mul (32 * B)),
    integral_const_mul, integral_const_mul, integral_finsetSum _ (fun i _ ↦ hi i)] at h
  simp_rw [integral_frozen_patch_eq _ chi outputs u _ hs] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (integral_pressure_norm_sq_le_hessianEnergy chi outputs u) (by positivity)))

theorem integral_variable_tilt_le_patch_energy {ι : Type*} [Fintype ι]
    (c : ι → FourierCoeff (Fin 3)) (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (hs : ∀ q, -q ∈ outputs ↔ q ∈ outputs)
    (e : T3 → R3) (hem : AEStronglyMeasurable e) (he : ∀ x, ‖e x‖ = 1)
    (f : ι → R3) (hf : ∀ i, ‖f i‖ = 1) (a B : ℝ) (hB : 0 ≤ B)
    (hcover : ∀ x, a ≤ ∑ i, quadraticWeight (c i) x)
    (hframe : ∀ x, (∑ i, quadraticWeight (c i) x * lineDistanceSq (e x) (f i)) ≤ B) :
    a * (∫ x : T3, ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
      2 * (∑ i, frozenPatchEnergy (c i) chi outputs u (f i)) + 32 * B * hessianEnergy chi outputs u :=
  integral_variable_tilt_le_patch_energy_of_integrable c chi outputs u hs e he
    (integrable_variable_transverse_sq chi outputs u e hem he) f hf a B hB hcover hframe

/-- A line-subordinate partition yields finite Fourier patches whose
coverage and tail costs are uniform in the number of cells. One family
works for every pressure field and every negation-closed output set. -/
theorem exists_pressure_patch_energy_bound {ι : Type*} [Fintype ι]
    (weight : PartitionOfUnity ι T3) (e : T3 → R3) (hem : AEStronglyMeasurable e)
    (f : ι → R3) (he : ∀ x, ‖e x‖ = 1) (hf : ∀ i, ‖f i‖ = 1)
    (rho delta : ℝ) (hd : 0 < delta)
    (hactive : ∀ i x, weight i x ≠ 0 → lineDistanceSq (e x) (f i) ≤ rho ^ 2) :
    ∃ c : ι → FourierCoeff (Fin 3),
      (∀ x, (1 / 2 : ℝ) ≤ ∑ i, quadraticWeight (c i) x) ∧
      (∀ x, (∑ i, quadraticWeight (c i) x) ≤ 3 / 2) ∧
      ∀ (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity),
        (∀ q, -q ∈ outputs ↔ q ∈ outputs) →
        (∫ x : T3, ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
          4 * (∑ i, frozenPatchEnergy (c i) chi outputs u (f i)) +
            (96 * rho ^ 2 + 128 * delta ^ 2) * hessianEnergy chi outputs u := by
  obtain ⟨c, hlow, hupp, hframe⟩ := exists_quadraticFourier_line_partition weight e f he hf rho delta hd hactive
  refine ⟨c, hlow, hupp, ?_⟩
  intro chi outputs u hs
  have h := integral_variable_tilt_le_patch_energy c chi outputs u hs e hem he f hf
    (1 / 2) ((3 / 2) * rho ^ 2 + 2 * delta ^ 2) (by positivity) hlow hframe
  nlinarith only [h]

/-- Construct both the adaptive cells and their Fourier cutoffs from the
continuous line projector. No measurable unit-vector selection is needed.
The finite family is chosen independently of the pressure coefficients. -/
theorem exists_pressure_patches_of_continuous_projector
    (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1)
    (hP : Continuous (fun x ↦ InnerProductSpace.rankOne ℝ (e x) (e x)))
    (rho delta : ℝ) (hr : 0 < rho) (hd : 0 < delta) :
    ∃ (centers : Finset T3) (c : ↑centers → FourierCoeff (Fin 3)),
      (∀ x, (1 / 2 : ℝ) ≤ ∑ i, quadraticWeight (c i) x) ∧
      (∀ x, (∑ i, quadraticWeight (c i) x) ≤ 3 / 2) ∧
      ∀ (chi : Wavevector → ℂ) (outputs : Finset Wavevector) (u : FourierVelocity),
        (∀ q, -q ∈ outputs ↔ q ∈ outputs) →
        (∫ x : T3, ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
          4 * (∑ i, frozenPatchEnergy (c i) chi outputs u (e i.1)) +
            (96 * rho ^ 2 + 128 * delta ^ 2) * hessianEnergy chi outputs u := by
  obtain ⟨centers, weight, hactive⟩ :=
    AdaptiveLinePartition.exists_partition_of_continuous_projector e he hP rho hr
  obtain ⟨c, hlow, hupp, hframe⟩ := exists_quadraticFourier_line_partition
    weight e (fun i ↦ e i.1) he (fun i ↦ he i.1) rho delta hd hactive
  refine ⟨centers, c, hlow, hupp, ?_⟩
  intro chi outputs u hs
  have heI : Integrable (fun x : T3 ↦
      ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) :=
    (LineProjectorTilt.continuous_transverse_norm_sq _
      (continuous_filteredPressureOperator chi outputs u) e he hP).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have h := integral_variable_tilt_le_patch_energy_of_integrable c chi outputs u hs e he heI
    (fun i ↦ e i.1) (fun i ↦ he i.1) (1 / 2) ((3 / 2) * rho ^ 2 + 2 * delta ^ 2)
      (by positivity) hlow hframe
  nlinarith only [h]

end Mettapedia.FluidDynamics.NavierStokes.FourierPressurePatchEnergy
