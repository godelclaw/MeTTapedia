import Mettapedia.Computability.PNP.CruxResidualSideInformationCoverageRepairEquivalencesSpec

/-!
# PNP residual-side-information repair-equivalence coverage proofs

The public repair-equivalence package is factored through named subcoverages:
repair witnesses, visible-pair fiber imbalance, obstruction packages, and exact
supported success.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

@[simp] theorem residualSideInformationRepairWitnessCoverage :
    ResidualSideInformationRepairWitnessCoverage := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α Base Side _Fintypeα τ base side y w hτ hbase hy hw
    exact
      residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_resolving_witness
        τ base side y w hτ hbase hy hw
  · intro α Base Side _Fintypeα τ base side y w hτ hbase hy hw
    exact
      residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_resolving_witness
        τ base side y w hτ hbase hy hw
  · intro α Base Side _Fintypeα τ base side y w hτ hbase hy hw
    exact
      residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_resolving_witness_and_no_visible_pair_balancing
        τ base side y w hτ hbase hy hw
  · intro α Base Side _Fintypeα τ base side y w hτ hbase hy hw
    exact
      residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_resolving_witness_and_no_visible_pair_balancing
        τ base side y w hτ hbase hy hw

@[simp] theorem residualSideInformationRepairFiberImbalanceCoverage :
    ResidualSideInformationRepairFiberImbalanceCoverage := by
  refine ⟨?_, ?_⟩
  · intro α Base Side _Fintypeα _FintypeBase _FintypeSide _DecidableEqBase _DecidableEqSide
      base side y w
    exact
      residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_visible_pair_fiber_imbalance
        base side y w
  · intro α Base Side _Fintypeα _FintypeBase _FintypeSide _DecidableEqBase _DecidableEqSide
      base side y w
    exact
      residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_visible_pair_fiber_imbalance
        base side y w

@[simp] theorem residualSideInformationRepairObstructionPackageCoverage :
    ResidualSideInformationRepairObstructionPackageCoverage := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α Base Side _Fintypeα τ base side y w h hτ hbase hy hw hadv
    exact
      residualSideInformationCoverage_anchor_positive_advantage_forces_supported_obstruction_package
        τ base side y w h hτ hbase hy hw hadv
  · intro α Base Side _Fintypeα τ base side y w hτ hbase hy hw hsuccess
    exact
      residualSideInformationCoverage_anchor_existential_positive_advantage_repair_exposes_pure_residual_obstruction_package
        τ base side y w hτ hbase hy hw hsuccess
  · intro α Base Side _Fintypeα τ base side y w hτ hbase hy hw hsuccess
    exact
      residualSideInformationCoverage_anchor_existential_strict_half_repair_exposes_pure_residual_obstruction_package
        τ base side y w hτ hbase hy hw hsuccess
  · intro α Base Side _Fintypeα τ base side y w hτ hbase hy hw
    exact
      residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_supported_obstruction_package
        τ base side y w hτ hbase hy hw
  · intro α Base Side _Fintypeα τ base side y w hτ hbase hy hw
    exact
      residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_supported_obstruction_package
        τ base side y w hτ hbase hy hw
  · intro α Base Side _Fintypeα τ base side y w hτ hbase hy hw
    exact
      residualSideInformationCoverage_anchor_existential_positive_advantage_repair_iff_supported_obstruction_package_and_no_visible_pair_balancing
        τ base side y w hτ hbase hy hw
  · intro α Base Side _Fintypeα τ base side y w hτ hbase hy hw
    exact
      residualSideInformationCoverage_anchor_existential_strict_half_repair_iff_supported_obstruction_package_and_no_visible_pair_balancing
        τ base side y w hτ hbase hy hw

@[simp] theorem residualSideInformationRepairExactSuccessCoverage :
    ResidualSideInformationRepairExactSuccessCoverage := by
  intro α Base Side _Fintypeα τ base side y w hτ hbase hy hw
  exact
    residualSideInformationCoverage_anchor_existential_exact_supported_success_iff_full_resolution_budget_and_supported_obstruction_package_and_no_visible_pair_balancing
      τ base side y w hτ hbase hy hw

@[simp] theorem residualSideInformationRepairEquivalenceCoverage :
    ResidualSideInformationRepairEquivalenceCoverage := by
  exact
    ⟨residualSideInformationRepairWitnessCoverage,
      residualSideInformationRepairFiberImbalanceCoverage,
      residualSideInformationRepairObstructionPackageCoverage,
      residualSideInformationRepairExactSuccessCoverage⟩

end Mettapedia.Computability.PNP
