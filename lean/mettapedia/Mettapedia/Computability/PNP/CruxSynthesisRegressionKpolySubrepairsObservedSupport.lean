import Mettapedia.Computability.PNP.CruxKpolySubrepairCoverage

/-!
# Regression checks for PNP Kpoly subrepairs: observed-support subrepair membership checks

This module is part of the decomposed Kpoly subrepair regression ledger.
It keeps the historical `CruxSynthesisRegression` theorem namespace while
separating membership checks by mathematical role.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP

universe u v w z

theorem current_pnp_kpoly_covered_subrepairs_exact_regression
    (repair : PNPKpolySubrepairClass) :
    repair ∈ currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact repair

theorem current_pnp_kpoly_actual_observed_support_subrepair_regression :
    PNPKpolySubrepairClass.actualObservedSupportPayloadInsufficiency ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportPayloadInsufficiency

theorem current_pnp_kpoly_actual_observed_support_section_boundary_regression :
    PNPKpolySubrepairClass.actualObservedSupportUniformSectionBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportUniformSectionBoundary

theorem current_pnp_kpoly_actual_observed_support_quotient_loss_regression :
    PNPKpolySubrepairClass.actualObservedSupportQuotientLossBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportQuotientLossBoundary

theorem current_pnp_kpoly_actual_observed_support_decoder_recovery_regression :
    PNPKpolySubrepairClass.actualObservedSupportDecoderRecoveryBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportDecoderRecoveryBoundary

theorem current_pnp_kpoly_actual_observed_support_observable_property_regression :
    PNPKpolySubrepairClass.actualObservedSupportObservablePropertyBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportObservablePropertyBoundary

theorem current_pnp_kpoly_actual_observed_support_property_factor_regression :
    PNPKpolySubrepairClass.actualObservedSupportPropertyFactorBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportPropertyFactorBoundary

theorem current_pnp_kpoly_actual_observed_support_point_query_regression :
    PNPKpolySubrepairClass.actualObservedSupportPointQueryBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportPointQueryBoundary

theorem current_pnp_kpoly_actual_observed_support_query_family_regression :
    PNPKpolySubrepairClass.actualObservedSupportQueryFamilyBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportQueryFamilyBoundary

theorem current_pnp_kpoly_actual_observed_support_adaptive_query_regression :
    PNPKpolySubrepairClass.actualObservedSupportAdaptiveQueryBoundary ∈
      currentPNPKpolyCoveredSubrepairs := by
  exact currentPNPKpolyCoveredSubrepairs_exact
    PNPKpolySubrepairClass.actualObservedSupportAdaptiveQueryBoundary

end Mettapedia.Computability.PNP.CruxSynthesisRegression
