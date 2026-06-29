import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMHighNormContinuation

/-!
# Regression checks for the BKM high-norm continuation assembly
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

section BKMContinuation

theorem BKMAnalyticContinuationLemma_of_components_regression
    (hDefect : BKMResidualCurlExpansionDefectVanishes)
    (hLog : BKMLogSobolevGradientControlFromEnvelope)
    (hHigh : BKMHighNormContinuationFromLogControl) :
    BKMAnalyticContinuationLemma := by
  exact BKMAnalyticContinuationLemma_of_components hDefect hLog hHigh

theorem BKMAnalyticComponentsClosed_implies_BKMAnalyticContinuationLemma_regression
    (h : BKMAnalyticComponentsClosed) :
    BKMAnalyticContinuationLemma := by
  exact h.implies_BKMAnalyticContinuationLemma

theorem BKMAnalyticComponentsClosed_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons_regression
    (h : BKMAnalyticComponentsClosed) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons := by
  exact h.implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons

theorem BKMContinuation_reduced_to_analytic_components_regression :
    BKMVorticityStretchingEstimateClosed ∧
      BKMResidualCurlExpansionAlgebraClosed ∧
        BKMStandardVorticityGrowthEstimateClosed ∧
          BKMLogSobolevGrowthEstimateClosed ∧
            (BKMAnalyticComponentsClosed →
              ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) := by
  exact BKMContinuation_reduced_to_analytic_components

end BKMContinuation

end NavierStokes
end FluidDynamics
end Mettapedia
