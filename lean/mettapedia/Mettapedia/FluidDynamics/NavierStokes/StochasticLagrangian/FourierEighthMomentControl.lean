import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierTameContinuation
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalVorticityEighthEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FullVorticityFourierCoefficients
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.InfiniteFourierParseval
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressureTraceSymbol

/-!
# The eighth vorticity moment controls the order-one energy

For real, transverse, mean-zero Fourier data with an absolutely summable
first moment, Parseval for the actual curl (the complexified real vorticity
is the reconstructed curl series) gives

```text
∫ |ω|² = ∑ |ω̂_k|² = (2π)² ∑ |k|² |û_k|².
```

On nonzero modes `(1+|k|)² ≤ 4|k|²`, so every truncated order-one energy is at
most `π⁻² ∫ |ω|²`. The torus measure is a probability measure, and Jensen's
inequality gives `(∫ |ω|²)⁴ ≤ ∫ |ω|⁸`, the eighth moment of the lane's
eighth-moment identity.

Consequently a finite-horizon bound on the eighth moment of every tame
solution implies the order-one hypothesis of
`FourierTameContinuation.exists_tameSolutionOn_of_orderOne`, and hence
solutions on every finite interval. That eighth-moment bound is the open
dynamical input; it is not supplied here.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierEighthMomentControl

open scoped BigOperators
open MeasureTheory Set
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeSobolevWeights PancakeHigherSobolevWeights PancakeHigherSobolevVelocityRate
open PancakeCurlOutputTail PancakeLatticeDecayEnvelope PancakeHigherLocalVelocity
open PancakeGalerkinKineticEnergy PancakeBlockReality
open InfiniteConvectionEnergy InfiniteKineticCancellation InfiniteFourierParseval
open FullVorticityFourierCoefficients FourierPressureTraceSymbol LocalLowDiffusionBudget
open LocalVorticityEighthMoment FourierTameTriad FourierContinuation FourierTameContinuation
open PancakeInfinitePressureCoefficients

local notation "T3" => UnitAddTorus (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Parseval for the actual real vorticity of real data. -/
theorem integral_norm_fullVorticity_sq_eq (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hr : ∀ k, u (-k) = coefficientConjugate (u k)) :
    ∫ x : T3, ‖fullVorticity u x‖ ^ 2 = kineticEnergy (fourierCurl u) := by
  rw [← integral_norm_fullFourierField_sq (fourierCurl u)
    (FullVorticityFourierCoefficients.summable_norm_fourierCurl u hu)]
  congr 1
  funext x
  rw [← complexify_fullVorticity u hu hr x, norm_complexifyVector]

/-- Every truncated order-one energy is controlled by the vorticity energy. -/
theorem velocityEnergy_one_le (u : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (hr : ∀ k, u (-k) = coefficientConjugate (u k)) (hd : ∀ k, modeDot k (u k) = 0)
    (h0 : u 0 = 0) (F : Finset Wavevector) :
    velocityEnergy 1 F u ≤ (∫ x : T3, ‖fullVorticity u x‖ ^ 2) / Real.pi ^ 2 := by
  classical
  rw [integral_norm_fullVorticity_sq_eq u hu hr, kineticEnergy_eq_tsum_coefficientEnergy,
    le_div_iff₀ (by positivity)]
  have hsum : Summable (fun q ↦ coefficientEnergy (fourierCurl u q)) := by
    have h := (hasSum_coefficientEnergy (fourierCurl u)
      (FullVorticityFourierCoefficients.summable_norm_fourierCurl u hu))
    exact h.summable
  have hpt : ∀ q ∈ F, orderWeight 1 q ^ 2 * coefficientEnergy (u q) * Real.pi ^ 2 ≤
      coefficientEnergy (fourierCurl u q) := by
    intro q _
    rw [fourierCurl_energy q u (hd q)]
    have hE : 0 ≤ coefficientEnergy (u q) := by
      rw [← norm_coefficientVec_sq]
      positivity
    by_cases hq : q = 0
    · subst hq
      simp [h0, coefficientEnergy]
    · have h1 := one_le_norm_frequencyVec hq
      have hw : orderWeight 1 q ^ 2 ≤ 4 * ‖frequencyVec q‖ ^ 2 := by
        unfold orderWeight
        rw [pow_one]
        nlinarith
      have hπ : 0 ≤ Real.pi ^ 2 := by positivity
      calc orderWeight 1 q ^ 2 * coefficientEnergy (u q) * Real.pi ^ 2
          ≤ 4 * ‖frequencyVec q‖ ^ 2 * coefficientEnergy (u q) * Real.pi ^ 2 := by
            gcongr
        _ = (2 * Real.pi) ^ 2 * ‖frequencyVec q‖ ^ 2 * coefficientEnergy (u q) := by ring
  calc velocityEnergy 1 F u * Real.pi ^ 2
      = ∑ q ∈ F, orderWeight 1 q ^ 2 * coefficientEnergy (u q) * Real.pi ^ 2 := by
        rw [velocityEnergy_eq, Finset.sum_mul]
    _ ≤ ∑ q ∈ F, coefficientEnergy (fourierCurl u q) := Finset.sum_le_sum hpt
    _ ≤ ∑' q, coefficientEnergy (fourierCurl u q) :=
        hsum.sum_le_tsum F fun q _ ↦ by rw [← norm_coefficientVec_sq]; positivity

/-- Jensen's inequality on the probability torus. -/
theorem integral_norm_fullVorticity_sq_pow_le (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) :
    (∫ x : T3, ‖fullVorticity u x‖ ^ 2) ^ 4 ≤ meanEnergy u := by
  have hc : Continuous (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 2) :=
    (continuous_fullVorticity u hu).norm.pow 2
  have hint : Integrable (fun x : T3 ↦ ‖fullVorticity u x‖ ^ 2) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint4 : Integrable ((fun y : ℝ ↦ y ^ 4) ∘ fun x : T3 ↦ ‖fullVorticity u x‖ ^ 2) :=
    (hc.pow 4).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJ := (convexOn_pow 4).map_integral_le (μ := (volume : Measure T3))
    (continuous_pow 4).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun x ↦ (sq_nonneg ‖fullVorticity u x‖ : _))
    hint hint4
  simpa [meanEnergy, LocalVorticityEighthMoment.energy] using hJ

/-- **The eighth moment controls the order-one energy.** -/
theorem velocityEnergy_one_le_of_meanEnergy (u : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hr : ∀ k, u (-k) = coefficientConjugate (u k))
    (hd : ∀ k, modeDot k (u k) = 0) (h0 : u 0 = 0) {K₈ : ℝ} (hK : meanEnergy u ≤ K₈)
    (F : Finset Wavevector) :
    velocityEnergy 1 F u ≤ max 1 K₈ / Real.pi ^ 2 := by
  have h1 := velocityEnergy_one_le u hu hr hd h0 F
  have h4 := integral_norm_fullVorticity_sq_pow_le u hu
  set y := ∫ x : T3, ‖fullVorticity u x‖ ^ 2
  have hy0 : 0 ≤ y := integral_nonneg fun x ↦ sq_nonneg _
  have hy : y ≤ max 1 K₈ := by
    rcases le_or_gt y 1 with h | h
    · exact h.trans (le_max_left _ _)
    · have : y ≤ y ^ 4 := by nlinarith [sq_nonneg (y - 1), sq_nonneg y, sq_nonneg (y ^ 2 - 1)]
      exact (this.trans (h4.trans hK)).trans (le_max_right _ _)
  exact h1.trans (div_le_div_of_nonneg_right hy (by positivity))

/-- An order-five energy bound gives the absolutely summable first moment. -/
theorem summable_fourierMoment_one (u : FourierVelocity) {B : ℝ}
    (hB : ∀ F : Finset Wavevector, velocityEnergy 5 F u ≤ B) :
    Summable (fourierMoment 1 u) :=
  (summable_latticeDecayWeight.mul_left (Real.sqrt B)).of_nonneg_of_le
    (fourierMoment_nonneg 1 u) (orderMoment_le_latticeEnvelope 1 u B hB)

/-- **Global existence under eighth-moment control.** For order `m ≥ 5`, if on
every finite horizon the eighth vorticity moment of every tame solution from
`u₀` is bounded by a common constant, tame solutions exist on every interval
`[0, H)`. -/
theorem exists_tameSolutionOn_of_meanEnergy (m : ℕ) (hm : 5 ≤ m) {nu : ℝ} (hnu : 0 < nu)
    (u₀ : FourierVelocity) (hr : ∀ q, u₀ (-q) = coefficientConjugate (u₀ q))
    (hd : ∀ q, modeDot q (u₀ q) = 0) (hz : u₀ 0 = 0) {E₀ : ℝ} (hE₀0 : 0 ≤ E₀)
    (hE₀ : ∀ F, velocityEnergy m F u₀ ≤ E₀)
    (heighth : ∀ H, 0 < H → ∃ K₈, ∀ T, T ≤ H → ∀ c : TameSolutionOn nu m u₀ T,
      ∀ τ ∈ Ico (0 : ℝ) T, meanEnergy (c.coefficients τ) ≤ K₈) :
    ∀ H, 0 < H → Nonempty (TameSolutionOn nu m u₀ H) := by
  refine exists_tameSolutionOn_of_orderOne m (by omega) hnu u₀ hr hd hz hE₀0 hE₀ ?_
  intro H hH
  obtain ⟨K₈, hK₈⟩ := heighth H hH
  refine ⟨max 1 K₈ / Real.pi ^ 2, fun T hT c τ hτ F ↦ ?_⟩
  obtain ⟨B, hB⟩ := c.order_local τ hτ.2
  have hB5 : ∀ G : Finset Wavevector, velocityEnergy 5 G (c.coefficients τ) ≤ B := by
    intro G
    refine le_trans ?_ (hB τ ⟨hτ.1, le_rfl⟩ G)
    rw [velocityEnergy_eq, velocityEnergy_eq]
    refine Finset.sum_le_sum fun k _ ↦ ?_
    have hE : 0 ≤ coefficientEnergy (c.coefficients τ k) := by
      rw [← norm_coefficientVec_sq]
      positivity
    have hw : orderWeight 5 k ^ 2 ≤ orderWeight m k ^ 2 := by
      unfold orderWeight
      rw [← pow_mul, ← pow_mul]
      exact pow_le_pow_right₀ (by linarith [norm_nonneg (frequencyVec k)]) (by omega)
    exact mul_le_mul_of_nonneg_right hw hE
  exact velocityEnergy_one_le_of_meanEnergy (c.coefficients τ)
    (summable_fourierMoment_one _ hB5) (c.reality τ) (c.transverse τ) (c.zero τ)
    (hK₈ T hT c τ hτ) F

end Mettapedia.FluidDynamics.NavierStokes.FourierEighthMomentControl
