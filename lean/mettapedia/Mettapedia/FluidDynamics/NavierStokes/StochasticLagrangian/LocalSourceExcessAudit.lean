import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.LocalExcessAlignmentEnergy
import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.SpectralSourceCommutatorTests

/-!
# Regression and axiom audit for source absorption

Zero source and separated alignment have zero excess. A commuting source
at a collision can retain positive excess. Thus the absorption theorem
does not obtain a false global gain by dividing by a vanishing gap.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcessAudit

open PancakeSpectralProjectorRegularity PancakeSpectralProjectorRegularity.SymmetricStrain
open PancakeSpectralFiniteDifference PancakeSpectralDefectEvolution SpectralSourceCommutator

local notation "R3" => EuclideanSpace ℝ (Fin 3)

example (S : SymmetricStrain) (w : R3) : SpectralSourceExcess.excess S 0 w = 0 := by
  apply le_antisymm _ (SpectralSourceExcess.excess_nonneg S 0 w)
  simpa only [norm_zero, mul_zero, zero_mul] using SpectralSourceExcess.excess_le_coarse S 0 w

example (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (c : ℝ) (hg : 0 < topGap S) :
    SpectralSourceExcess.excess S R (c • topVector S) = 0 :=
  SpectralSourceExcess.excess_aligned S R c hg

example (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3)
    (hg : 0 < topGap S) (hc : commutator S R = 0) (hR : 16 * ‖R‖ ≤ topGap S ^ 2) :
    |remainderAnisotropy R (topVector S) w| ≤
      ‖spectralResidual S.1 (topEigenvalue S) w‖ ^ 2 / 4 := by
  have h := SpectralSourceExcess.envelope_le_quarter_residual_add_excess S R w
  rw [SpectralSourceExcess.excess_eq_zero_of_commutator_eq_zero S R w hg hc hR, add_zero] at h
  exact (SpectralCommutatorLimit.abs_remainderAnisotropy_le_limitingEnvelope S R w).trans h

theorem exists_commuting_source_with_positive_excess_at_collision :
    ∃ (S : SymmetricStrain) (R : R3 →L[ℝ] R3) (w : R3),
      topGap S = 0 ∧ commutator S R = 0 ∧
      remainderAnisotropy R (topVector S) w = 1 ∧ SpectralSourceExcess.excess S R w = 2 := by
  obtain ⟨S, R, w, hg, hc, _, hA, hE⟩ :=
    SpectralSourceCommutatorTests.exists_commuting_zero_gap_source_with_nonzero_anisotropy
  refine ⟨S, R, w, hg, hc, hA, ?_⟩
  rw [SpectralSourceExcess.excess_eq_coarse_of_topGap_zero S R w hg,
    ← SpectralCommutatorLimit.limitingEnvelope_eq_coarse_of_topGap_zero S R w hg, hE]

end Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcessAudit

#check Mettapedia.FluidDynamics.NavierStokes.LocalExcessAlignmentEnergy.exists_physical_localExcessAlignmentEnergy

#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.refinedCost_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.excess_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.excess_le_envelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.excess_le_coarse
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.tilt_le_eighth_residual_add_commutator_cost
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.envelope_le_quarter_residual_add_refinedCost
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.envelope_le_quarter_residual_add_excess
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.excess_eq_coarse_of_topGap_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.excess_aligned
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.excess_le_commutator_cost_of_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.excess_eq_zero_of_commutator_eq_zero
#print axioms Mettapedia.FluidDynamics.NavierStokes.SpectralSourceExcess.measurable_excess
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.sourceExcess_nonneg
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.sourceExcess_le_coarse
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.forcingEnvelope_le_previous
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.previous_le_quarter_residual_add_forcingEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.sourceExcess_eq_zero_of_commuting
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.norm_forcingEnvelope_le
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.measurable_sourceExcess
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.measurable_forcingEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.integrable_forcingEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.measurable_forcingEnvelope_spaceTime
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.intervalIntegrable_forcingEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.integral_previous_le_quarter_residual_add_forcingEnvelope
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcess.integral_source_le_quarter_residual_add_excess
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalExcessAlignmentEnergy.meanEnergy_add_quarter_integral_residual_le_initial
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalExcessAlignmentEnergy.exists_physical_localExcessAlignmentEnergy
#print axioms Mettapedia.FluidDynamics.NavierStokes.LocalSourceExcessAudit.exists_commuting_source_with_positive_excess_at_collision
