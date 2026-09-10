import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.FourierPressurePatchEnergy

/-! Regression and axiom audit for adaptive pressure localization. -/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.FourierPressurePatchAudit

open scoped BigOperators
open MeasureTheory PeriodicFourierTriad PancakeAnisotropyDepletion
open PancakeQuadraticFourierSupport PancakeQuadraticProjectionLocalization
open PancakeFiniteFourierLocalization PancakeRealFourierProjection PancakeViscousMisalignmentAbsorption
open RealFourierLocalizationEnergy FourierLinePartition FourierPressurePatchEnergy SpectralTiltFreezing

local notation "T3" => UnitAddTorus (Fin 3)
local notation "R3" => EuclideanSpace ℝ (Fin 3)

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

example (modes : Finset Wavevector) (a : FourierVelocity) :
    localizedEnergy 0 modes a = 0 := by
  simp [localizedEnergy, finiteCutoffOutputModes, fullEnergy]

/-- A purely imaginary cutoff preserves the real field's energy. Taking
the real part after multiplication would incorrectly erase this example. -/
example : localizedEnergy (Finsupp.single 0 Complex.I) {0} (fun _ _ ↦ 1) = 3 := by
  norm_num [localizedEnergy, localizedCoefficient, finiteCutoffOutputModes,
    finiteCutoffConvolutionCoeff, fullEnergy, coefficientEnergy, realSymmetricCoeff,
    Fin.sum_univ_succ]
  simp [Finset.sum_filter]

example (n : ℕ) (delta : ℝ) (hd : 0 < delta) :
    ∃ epsilon > (0 : ℝ), (n : ℝ) * (epsilon * (epsilon + 2)) ≤ 1 / 2 ∧
      (n : ℝ) * epsilon ^ 2 ≤ delta ^ 2 := exists_approximation_tolerance n delta hd

example (e : R3) (he : ‖e‖ = 1) :
    lineDistanceSq e (-e) ≤ 2 *
      ‖InnerProductSpace.rankOne ℝ e e - InnerProductSpace.rankOne ℝ (-e) (-e)‖ ^ 2 :=
  lineDistanceSq_le_two_mul_projector_sub_sq e (-e) he (by simpa using he)

/-- No regularity, including measurability, is imposed on the sign choice. -/
example (R : T3 → (R3 →L[ℝ] R3)) (hR : Continuous R) (e : R3) (he : ‖e‖ = 1)
    (sign : T3 → Bool) :
    Continuous (fun x ↦ ‖lineRemainder (if sign x then e else -e)
      (R x (if sign x then e else -e))‖ ^ 2) := by
  apply LineProjectorTilt.continuous_transverse_norm_sq R hR
  · intro x
    split <;> simpa using he
  · have hP : (fun x ↦ InnerProductSpace.rankOne ℝ (if sign x then e else -e)
        (if sign x then e else -e)) = fun _ : T3 ↦ InnerProductSpace.rankOne ℝ e e := by
      funext x
      split <;> simp
    rw [hP]
    exact continuous_const

/-- The existing spectral regularity theorem supplies the projector input
on a globally separated strain field. Positivity of the gap is explicit. -/
example (S : T3 → PancakeSpectralProjectorRegularity.SymmetricStrain) (hS : Continuous S)
    (hg : ∀ x, 0 < PancakeSpectralProjectorRegularity.SymmetricStrain.topGap (S x))
    (rho : ℝ) (hr : 0 < rho) :
    ∃ (centers : Finset T3) (weight : PartitionOfUnity (↑centers) T3),
      ∀ (center : ↑centers) (x : T3), weight center x ≠ 0 →
        lineDistanceSq (PancakeSpectralFiniteDifference.topVector (S x))
          (PancakeSpectralFiniteDifference.topVector (S center.1)) ≤ rho ^ 2 := by
  apply AdaptiveLinePartition.exists_partition_of_continuous_projector
    (fun x ↦ PancakeSpectralFiniteDifference.topVector (S x))
    (fun x ↦ PancakeSpectralFiniteDifference.topVector_norm (S x)) _ rho hr
  exact PancakeSpectralProjectorRegularity.SymmetricStrain.continuous_topEigenlineProjector_comp_of_topGap_pos S hS hg

end Mettapedia.FluidDynamics.NavierStokes.FourierPressurePatchAudit

#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing.lineDistanceSq_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing.lineDistanceSq_le_two
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing.lineDistanceSq_le_two_mul_remainder_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing.lineDistanceSq_le_two_mul_projector_sub_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralTiltFreezing.weighted_transverse_action_sq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LineProjectorTilt.transverse_projector_action_eq_rankOne
#print axioms Mettapedia.FluidDynamics.NavierStokes.LineProjectorTilt.norm_transverse_projector_action
#print axioms Mettapedia.FluidDynamics.NavierStokes.LineProjectorTilt.continuous_transverse_norm_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.AdaptiveLinePartition.exists_partition_of_continuous_projector
#print axioms Mettapedia.FluidDynamics.NavierStokes.RealFourierLocalizationEnergy.norm_realSymmetric_reconstruction_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.RealFourierLocalizationEnergy.localized_reconstruction_norm_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.RealFourierLocalizationEnergy.integral_quadraticWeight_real_reconstruction_sq
#print axioms Mettapedia.FluidDynamics.NavierStokes.RealFourierLocalizationEnergy.localizedEnergy_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.RealFourierLocalizationEnergy.localizedCoefficient_eq_zero_off_support
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierLinePartition.sum_quadraticWeight_lineDistanceSq_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierLinePartition.exists_approximation_tolerance
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierLinePartition.exists_quadraticFourier_line_partition
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressurePatchEnergy.integral_frozen_patch_eq
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressurePatchEnergy.frozenPatchEnergy_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressurePatchEnergy.integral_variable_tilt_le_patch_energy_of_integrable
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressurePatchEnergy.integral_variable_tilt_le_patch_energy
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressurePatchEnergy.exists_pressure_patch_energy_bound
#print axioms Mettapedia.FluidDynamics.NavierStokes.FourierPressurePatchEnergy.exists_pressure_patches_of_continuous_projector
