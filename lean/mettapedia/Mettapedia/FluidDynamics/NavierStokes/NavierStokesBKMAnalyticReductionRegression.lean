import Mettapedia.FluidDynamics.NavierStokes.NavierStokesBKMAnalyticReduction

/-!
# Regression checks for the BKM one-lemma analytic reduction
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

namespace Regression

theorem bkm_vorticity_stretching_estimate_closed_regression :
    BKMVorticityStretchingEstimateClosed :=
  BKMVorticityStretchingEstimateClosed_proved

theorem bkm_single_analytic_lemma_implies_repaired_target_regression
    (hBKM : BKMAnalyticContinuationLemma) :
    ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons :=
  BKMAnalyticContinuationLemma_implies_finiteEnergyBKMContinuationTargetOnNonnegHorizons hBKM

theorem bkm_continuation_reduced_to_single_analytic_lemma_regression :
    BKMVorticityStretchingEstimateClosed ∧
      BKMResidualCurlExpansionAlgebraClosed ∧
        BKMStandardVorticityGrowthEstimateClosed ∧
          BKMVorticityEnstrophyBalanceAssemblyClosed ∧
            BKMVorticityEnstrophyAprioriEstimateClosed ∧
              BKMLogSobolevGrowthEstimateClosed ∧
                (BKMAnalyticContinuationLemma →
                  ExplicitFiniteEnergyBKMContinuationTargetOnNonnegHorizons) :=
  BKMContinuation_reduced_to_single_analytic_lemma

end Regression

end NavierStokes
end FluidDynamics
end Mettapedia
