import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureHessianEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralTiltFreezing

/-!
# Pressure-tilt energy for a varying direction near a fixed frame

The frozen-direction angular gain survives with an explicit squared
unoriented-line error cost. Both terms are bounded using pressure coefficient
energy, not sums of coefficient magnitudes. A measurable unit direction
and its closeness to the fixed frame are explicit hypotheses.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltFreezing

open scoped RealInnerProductSpace
open Filter MeasureTheory
open PeriodicFourierTriad PancakeAnisotropyDepletion
open LocalPressureCommutator FourierPressureTiltEnergy FourierPressureHessianEnergy SpectralTiltFreezing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem norm_variable_transverse_le (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : T3 → R3) (he : ∀ x, ‖e x‖ = 1) (x : T3) :
    ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ≤
      ‖filteredPressureOperator chi outputs u x‖ :=
  (norm_lineRemainder_le _ _ (he x)).trans (by
    simpa only [he x, mul_one] using (filteredPressureOperator chi outputs u x).le_opNorm (e x))

theorem aestronglyMeasurable_variable_transverse (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : T3 → R3) (he : AEStronglyMeasurable e) :
    AEStronglyMeasurable (fun x ↦ lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))) := by
  have hH : AEStronglyMeasurable (filteredPressureOperator chi outputs u) volume :=
    (continuous_filteredPressureOperator chi outputs u).aestronglyMeasurable
  have happly : Continuous (fun p : (R3 →L[ℝ] R3) × R3 ↦ p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hv := happly.comp_aestronglyMeasurable (hH.prodMk he)
  exact hv.sub ((he.inner hv).smul he)

theorem integrable_variable_transverse_sq (chi : Wavevector → ℂ) (outputs : Finset Wavevector)
    (u : FourierVelocity) (e : T3 → R3) (hem : AEStronglyMeasurable e) (he : ∀ x, ‖e x‖ = 1) :
    Integrable (fun x : T3 ↦ ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) := by
  apply (integrable_pressure_norm_sq chi outputs u).mono'
    ((aestronglyMeasurable_variable_transverse chi outputs u e hem).norm.pow 2)
  filter_upwards [] with x
  dsimp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_variable_transverse_le chi outputs u e he x) 2

theorem integral_variable_transverse_sq_le_hessianEnergy (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : T3 → R3)
    (hem : AEStronglyMeasurable e) (he : ∀ x, ‖e x‖ = 1) :
    (∫ x : T3, ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
      hessianEnergy chi outputs u :=
  (integral_mono (integrable_variable_transverse_sq chi outputs u e hem he)
    (integrable_pressure_norm_sq chi outputs u)
    (fun x ↦ pow_le_pow_left₀ (norm_nonneg _) (norm_variable_transverse_le chi outputs u e he x) 2)).trans
      (integral_pressure_norm_sq_le_hessianEnergy chi outputs u)

theorem integral_variable_transverse_sq_le_frozen (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : T3 → R3)
    (hem : AEStronglyMeasurable e) (he : ∀ x, ‖e x‖ = 1)
    (f : R3) (hf : ‖f‖ = 1) (rho : ℝ) (hd : ∀ x, lineDistanceSq (e x) f ≤ rho ^ 2) :
    (∫ x : T3, ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
      2 * angularEnergy chi outputs u f + 32 * rho ^ 2 * hessianEnergy chi outputs u := by
  have hfI := ((continuous_transverse_pressure chi outputs u f).norm.pow 2
    ).integrable_of_hasCompactSupport (μ := (volume : Measure T3)) (HasCompactSupport.of_compactSpace _)
  have hH := integrable_pressure_norm_sq chi outputs u
  have h := integral_mono (integrable_variable_transverse_sq chi outputs u e hem he)
    ((hfI.const_mul 2).add (hH.const_mul (32 * rho ^ 2))) (fun x ↦ by
      have hp := norm_transverse_action_sq_le_lineDistance (filteredPressureOperator chi outputs u x)
        (e x) f (he x) hf
      have hq := mul_le_mul_of_nonneg_left (hd x) (by positivity :
        0 ≤ 32 * ‖filteredPressureOperator chi outputs u x‖ ^ 2)
      dsimp only [Pi.add_apply]
      nlinarith only [hp, hq])
  change (∫ x : T3, ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
    ∫ x : T3, 2 * ‖lineRemainder f (filteredPressureOperator chi outputs u x f)‖ ^ 2 +
      (32 * rho ^ 2) * ‖filteredPressureOperator chi outputs u x‖ ^ 2 at h
  rw [integral_add (hfI.const_mul 2) (hH.const_mul (32 * rho ^ 2)), integral_const_mul,
    integral_const_mul] at h
  exact h.trans (add_le_add
    (mul_le_mul_of_nonneg_left (integral_transverse_pressure_sq_le_angularEnergy chi outputs u f) (by norm_num))
    (mul_le_mul_of_nonneg_left (integral_pressure_norm_sq_le_hessianEnergy chi outputs u) (by positivity)))

theorem integral_variable_transverse_sq_le_of_cone (chi : Wavevector → ℂ)
    (outputs : Finset Wavevector) (u : FourierVelocity) (e : T3 → R3)
    (hem : AEStronglyMeasurable e) (he : ∀ x, ‖e x‖ = 1)
    (f : R3) (hf : ‖f‖ = 1) (rho eta : ℝ) (hd : ∀ x, lineDistanceSq (e x) f ≤ rho ^ 2)
    (hcone : ∀ q ∈ outputs, ‖pressureAmplitude chi u q‖ ≠ 0 →
      ⟪FourierPressureCommutator.realFrequency q, f⟫ ^ 2 ≤
        eta ^ 2 * ‖FourierPressureCommutator.realFrequency q‖ ^ 2) :
    (∫ x : T3, ‖lineRemainder (e x) (filteredPressureOperator chi outputs u x (e x))‖ ^ 2) ≤
      (2 * eta ^ 2 + 32 * rho ^ 2) * hessianEnergy chi outputs u := by
  have h := integral_variable_transverse_sq_le_frozen chi outputs u e hem he f hf rho hd
  have hc := angularEnergy_le_of_longitudinal_bound chi outputs u f hf eta hcone
  nlinarith only [h, hc]

end Mettapedia.FluidDynamics.NavierStokes.FourierPressureTiltFreezing
