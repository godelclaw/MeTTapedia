import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.ExchangedFluxAdjointSeries

/-!
# Full signed coefficient pairing for the stretching variation

Absolute convergence permits regrouping the true three-input variation
by its velocity-rate frequency. The coefficient test is constructed from
the two adjoint double sums, rather than introduced as a hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointPairing

open scoped RealInnerProductSpace
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakeFrequencyProjectorCommutator
open PancakeCurlOutputTail PeriodicGradientFluxTriple ExchangedFluxVariation
open ExchangedFluxHeatRepresentation ExchangedFluxAdjoint ExchangedFluxVariationSeries
open ExchangedFluxAdjointSeries

local notation "H" => Mettapedia.Analysis.UnitTorusGradientProjection.TensorL2
  (Fin 3) (EuclideanSpace ℝ (Fin 3))

def firstSecondExchange : TripleIndex ≃ TripleIndex where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun p := (p.2.1, (p.1, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem summable_mixedPairing (u v w : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v))
    (hw : Summable (fourierMoment 1 w)) (F : H) :
    Summable (fun p : TripleIndex ↦ ⟪mixedMode u v w p, F⟫) :=
  ((summable_norm_mixedMode u v w hu hv hw).mul_right ‖F‖).of_norm_bounded
    (fun p ↦ norm_inner_le_norm (mixedMode u v w p) F)

theorem outer_pairing_sum (u v : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (F : H) (q : Wavevector) :
    (∑' p : Wavevector × Wavevector, ⟪mixedMode v u u (q, p), F⟫) =
      ⟪coefficientVec (v q), ∑' p : Wavevector × Wavevector, outerTest u F (q, p)⟫ := by
  have hi := (innerSL ℝ (coefficientVec (v q))).map_tsum
    (summable_norm_outerTest u hu F q).of_norm
  simp only [innerSL_apply_apply] at hi
  rw [hi]
  apply tsum_congr
  intro p
  simp only [outerTest, ContinuousLinearMap.adjoint_inner_right, outerSlot_apply]

theorem left_pairing_sum (u v : FourierVelocity) (hu : Summable (fourierMoment 1 u))
    (F : H) (q : Wavevector) :
    (∑' p : Wavevector × Wavevector, ⟪mixedMode u v u (p.1, (q, p.2)), F⟫) =
      ⟪coefficientVec (v q), ∑' p : Wavevector × Wavevector, leftTest u F (p.1, (q, p.2))⟫ := by
  have hi := (innerSL ℝ (coefficientVec (v q))).map_tsum
    (summable_norm_leftTest u hu F q).of_norm
  simp only [innerSL_apply_apply] at hi
  rw [hi]
  apply tsum_congr
  intro p
  simp only [leftTest, ContinuousLinearMap.adjoint_inner_right, leftSlot_apply]

theorem summable_coefficientPairing (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) (F : H) :
    Summable (fun q ↦ ⟪coefficientVec (v q), coefficientTest u F q⟫) := by
  have ho := (summable_mixedPairing v u u hv hu hu F).prod
  have hl := (firstSecondExchange.summable_iff.mpr (summable_mixedPairing u v u hu hv hu F)).prod
  simp only [outer_pairing_sum u v hu F] at ho
  change Summable (fun q ↦ ∑' p : Wavevector × Wavevector, ⟪mixedMode u v u (p.1, (q, p.2)), F⟫) at hl
  simp only [left_pairing_sum u v hu F] at hl
  simp only [coefficientTest, inner_sub_right, inner_neg_right, real_inner_smul_right]
  exact ho.neg.sub (hl.mul_left 2)

set_option synthInstance.maxHeartbeats 80000 in
/-- The actual infinite variation is paired with its constructed velocity test. -/
theorem inner_fluxVariation_eq_tsum (u v : FourierVelocity)
    (hu : Summable (fourierMoment 1 u)) (hv : Summable (fourierMoment 1 v)) (F : H) :
    ⟪fluxVariation u v, F⟫ = ∑' q, ⟪coefficientVec (v q), coefficientTest u F q⟫ := by
  have hO := (summable_norm_mixedMode v u u hv hu hu).of_norm
  have hL := (summable_norm_mixedMode u v u hu hv hu).of_norm
  have hOi : ⟪∑' p : TripleIndex, mixedMode v u u p, F⟫ =
      ∑' p : TripleIndex, ⟪mixedMode v u u p, F⟫ := by
    simpa only [innerSL_apply_apply, real_inner_comm] using (innerSL ℝ F).map_tsum hO
  have hLi : ⟪∑' p : TripleIndex, mixedMode u v u p, F⟫ =
      ∑' p : TripleIndex, ⟪mixedMode u v u p, F⟫ := by
    simpa only [innerSL_apply_apply, real_inner_comm] using (innerSL ℝ F).map_tsum hL
  have ho := (summable_mixedPairing v u u hv hu hu F).prod
  have hl := (firstSecondExchange.summable_iff.mpr (summable_mixedPairing u v u hu hv hu F)).prod
  have hlSum : (∑' p : TripleIndex, ⟪mixedMode u v u p, F⟫) =
      ∑' q, ∑' p : Wavevector × Wavevector, ⟪mixedMode u v u (p.1, (q, p.2)), F⟫ := by
    rw [← firstSecondExchange.tsum_eq (fun p ↦ ⟪mixedMode u v u p, F⟫)]
    exact (firstSecondExchange.summable_iff.mpr (summable_mixedPairing u v u hu hv hu F)).tsum_prod
  rw [fluxVariation_eq_outer_add_twice_inner u v hu hv, inner_sub_left, inner_neg_left,
    real_inner_smul_left, hOi, hLi, (summable_mixedPairing v u u hv hu hu F).tsum_prod, hlSum]
  simp only [outer_pairing_sum u v hu F] at ho ⊢
  change Summable (fun q ↦ ∑' p : Wavevector × Wavevector, ⟪mixedMode u v u (p.1, (q, p.2)), F⟫) at hl
  simp only [left_pairing_sum u v hu F] at hl ⊢
  simp only [coefficientTest, inner_sub_right, inner_neg_right, real_inner_smul_right]
  rw [ho.neg.tsum_sub (hl.mul_left 2), tsum_neg, tsum_mul_left]

end Mettapedia.FluidDynamics.NavierStokes.ExchangedFluxAdjointPairing
