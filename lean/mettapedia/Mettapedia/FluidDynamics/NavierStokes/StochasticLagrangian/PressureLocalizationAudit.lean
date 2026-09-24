import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.GaussianPressureCommutatorBudget

/-! Regression tests for input variation and actual pressure localization. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationAudit

open scoped BigOperators
open PeriodicFourierTriad PancakePeriodicCoherentSplit PancakePeriodicComplexStretch
open PancakeFrequencyProjectorCommutator ComplexPressurePair NormalizedPressureTrace
open PressureBilinearLocalization

local notation "R3" => EuclideanSpace ℝ (Fin 3)

@[simp] private theorem vector_last {α : Type*} (a b c : α) : ![a, b, c] (2 : Fin 3) = c := rfl

@[simp] private theorem triple_fiber (a p k : Wavevector) :
    ({((p, k), a)} : Finset ((Wavevector × Wavevector) × Wavevector)).filter
      (fun t ↦ t.1.1 + t.1.2 + t.2 = p + k + a) = {((p, k), a)} := by
  apply Finset.filter_eq_self.mpr
  intro t ht
  simp only [Finset.mem_singleton] at ht
  subst t
  rfl

example (p : Wavevector) (w v : VelocityCoefficient) : tracePair 0 p w v = 0 := by
  simp [tracePair, complexBiotSavartAmp, modeDot, modeSquare]

/-- The trace is unchanged by a positive radial rescaling of one input. -/
example : tracePair ![1, 0, 1] ![-1, 1, 0] ![-1, 0, 1] ![0, 0, 1] =
    tracePair ![2, 0, 2] ![-1, 1, 0] ![-1, 0, 1] ![0, 0, 1] := by
  norm_num [tracePair, complexBiotSavartAmp, modeDot, modeSquare, coefficientCross,
    wavevectorCoefficient, Fin.sum_univ_three]

/-- Complex bilinear dot product has the sharp dimension-free norm bound. -/
example : ‖coefficientDot ![1, Complex.I, 0] ![1, -Complex.I, 0]‖ ^ 2 =
    ‖coefficientVec ![1, Complex.I, 0]‖ ^ 2 * ‖coefficientVec ![1, -Complex.I, 0]‖ ^ 2 := by
  norm_num [coefficientDot, coefficientVec, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

/-- A constant spatial cutoff commutes exactly. -/
example (e : R3) (P K : Finset Wavevector) (c : Wavevector → ℂ) (w v : FourierVelocity) (q : Wavevector) :
    commutatorCoefficient e {0} P K c w v q = 0 := by
  unfold commutatorCoefficient
  apply Finset.sum_eq_zero
  intro t ht
  have ha : t.2 = 0 := Finset.mem_singleton.mp (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2
  simp only [ha, zero_add, sub_self, smul_zero]

/-- The one-mode case retains the difference of both actual kernels. -/
example (e : R3) (a p k : Wavevector) (c : ℂ) (w v : FourierVelocity) :
    commutatorCoefficient e {a} {p} {k} (fun _ ↦ c) w v (p + k + a) =
      c • (tiltPair e p k (w p) (v k) - tiltPair e (a + p) k (w p) (v k)) := by
  simp [commutatorCoefficient]

/-- Landing on source frequency zero is included, and leaves the original kernel as error. -/
example (e : R3) (p k : Wavevector) (c : ℂ) (w v : FourierVelocity) :
    commutatorCoefficient e {-p} {p} {k} (fun _ ↦ c) w v (p + k + (-p)) =
      c • tiltPair e p k (w p) (v k) := by
  have hz : tiltPair e 0 k (w p) (v k) = 0 := by
    simp [tiltPair, tracePair, complexBiotSavartAmp, modeDot, modeSquare]
  have ht : (({p} : Finset Wavevector) ×ˢ {k}) ×ˢ {-p} = {((p, k), -p)} := by simp
  rw [commutatorCoefficient, ht, triple_fiber, Finset.sum_singleton, neg_add_cancel, hz, sub_zero]

end Mettapedia.FluidDynamics.NavierStokes.PressureLocalizationAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.GaussianPressureCommutatorBudget.exists_local_gaussian_commutator_budget
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressureLocalization.physicalCommutatorCost_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressureLocalization.norm_curl_div_frequency_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressureLocalization.commutator_energy_fourierCurl_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressureLocalization.commutator_energy_le_physical_gradient
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressureLocalization.sum_commutator_energy_fourierCurl_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PhysicalPressureLocalization.physical_pressure_localization_identity
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureBilinearLocalization.localizedOutput_eq_triple_sum
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureBilinearLocalization.localizedSource_eq_triple_sum
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureBilinearLocalization.localizedOutput_sub_localizedSource
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureBilinearLocalization.norm_commutator_term_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressureBilinearLocalization.commutator_energy_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairInputStability.tiltPair_sub_decomposition
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairInputStability.norm_tiltPair_sub_left_mul_frequency_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairInputStability.tracePair_swap
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairInputStability.tiltPair_swap
#print axioms Mettapedia.FluidDynamics.NavierStokes.PressurePairInputStability.norm_tiltPair_sub_right_mul_frequency_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace.norm_coefficientDot_le_product
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace.norm_triple_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace.triple_sub_left
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace.triple_sub_right
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace.triple_smul_smul
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace.directionalTrace_sub_left
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace.norm_directionalTrace_sub_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace.coefficientVec_normalizedCoefficient
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace.norm_normalizedCoefficient_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace.tracePair_eq_directionalTrace
#print axioms Mettapedia.FluidDynamics.NavierStokes.NormalizedPressureTrace.norm_tracePair_sub_mul_frequency_le
