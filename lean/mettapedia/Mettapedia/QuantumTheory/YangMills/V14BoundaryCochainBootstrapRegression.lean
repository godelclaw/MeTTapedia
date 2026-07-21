import Mettapedia.QuantumTheory.YangMills.V14BoundaryCochainBootstrap

/-!
# Regressions for the postponed-IBP boundary-cochain repair
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14BoundaryCochainBootstrapRegression

open V14BoundaryCochainComplex
open V14BoundaryCochainExtraction
open V14BoundaryCochainBootstrap

example :
    Module.finrank ℝ
      (TwoBlockBoundaryH0 V14ActionOperatorTemplate) = 5 :=
  displayedTemplateBoundaryH0_finrank

example :
    Module.finrank ℝ
      (TwoBlockBoundaryH0 (RetainedDisplayedTemplate .onShell)) = 4 :=
  onShellDisplayedBoundaryH0_finrank

example :
    Module.finrank ℝ
      (TwoBlockBoundaryH0 (RetainedDisplayedTemplate .offShell)) = 5 :=
  offShellDisplayedBoundaryH0_finrank

example :
    assembledActionLaplacianBulk 0 .actionLaplacian = 1 ∧
    assembledActionLaplacianBulk 1 .actionLaplacian = -1 ∧
    (LinearMap.range
        (sharedBoundaryCoboundaryLinear ActionLaplacianCensus)).mkQ
      assembledActionLaplacianBulk = 0 :=
  move5Witness_handled_by_postponedIBP

example : Fintype.card BoundaryCochainLow16 = 13 :=
  boundaryCochainLow16_card

example : RepairedBoundaryCochainExtractionCertificate :=
  repairedBoundaryCochainExtractionCertificate

example : boundaryCochainRouteStatus .fullDimensionSixteenCensus =
    .sameTargetRefuted := rfl

example :
    repairedBoundaryCochainRecursionBudget = (5544 : ℝ) / 5 :=
  repairedBoundaryCochainRecursionBudget_eq

example :
    HasTwoSourceBootstrapSlack
      repairedBoundaryCochainRecursionBudget 2 15 :=
  repairedBoundaryCochain_twoSourceSlack_fifteen

#print axioms range_sharedBoundaryCoboundary_eq_ker_globalRecombine
#print axioms twoBlockBoundaryH0_finrank
#print axioms onShellDisplayedBoundaryH0_finrank
#print axioms offShellDisplayedBoundaryH0_finrank
#print axioms witnessFields_interfaceCompatible
#print axioms move5Witness_handled_by_postponedIBP
#print axioms canonicalCoordinateJetMatrix_eq_one
#print axioms coefficientL1_canonicalDimensionProjection_le
#print axioms canonicalDimensionProjection_coefficientSup_le
#print axioms boundaryCochainProjection16_manuscriptCoefficientSup_le
#print axioms boundaryCochainProjection16_fixes_move5Vector
#print axioms boundaryCochainProjection16_kills_highDerivative
#print axioms repairedBoundaryCochainExtractionCertificate
#print axioms actualFactors_le_repairedBoundaryCochainBudget
#print axioms leastDepth_repairedBoundaryCochain_packet
#print axioms repairedBoundaryCochain_scalar_bootstrap_closure
#print axioms boundaryCochainRouteMatrix_agrees
#print axioms v14_postponedIBP_boundaryCochain_constructed_packet

end V14BoundaryCochainBootstrapRegression
end YangMills
end QuantumTheory
end Mettapedia
