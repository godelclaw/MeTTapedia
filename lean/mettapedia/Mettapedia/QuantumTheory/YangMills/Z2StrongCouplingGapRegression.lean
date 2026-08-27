import Mettapedia.QuantumTheory.YangMills.Roadmap

/-!
# `Z₂` strong-coupling gap regression checks

Regression checks for the finite-lattice strong-coupling landmark and the
roadmap entries that keep it separate from the continuum endpoint.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace Z2StrongCouplingGapRegression

theorem finite_lattice_landmark_regression :
    ∃ _ : Z2StrongCouplingGapCanary,
      (∃ x y : Z2OneLinkConfig, x ≠ y) ∧
        OSReflectionPositive z2StrongCouplingKernel ∧
        z2StrongCouplingGap = 1 ∧
        (1 : ℝ) ≤ z2StrongCouplingGap ∧
        0 < z2StrongCouplingGap := by
  exact z2StrongCoupling_latticeYangMills_massGap_landmark

theorem finite_lattice_packet_regression :
    z2StrongCouplingGap = 1 ∧
      (1 : ℝ) ≤ z2StrongCouplingGap ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ a : ℝ,
          0 < a ∧ a < ε ∧ z2HeatTimePhysicalGap a (a ^ 2) < ε) := by
  exact
    ⟨z2StrongCouplingGap_eq_one,
      z2StrongCouplingGap_lower_bound_one,
      z2QuadraticHeatTime_physicalGap_closes⟩

theorem proof_state_node_checked_regression :
    yangMillsZ2StrongCouplingGapNode.status = .checked := by
  exact yangMillsZ2StrongCouplingGapNode_checked

theorem roadmap_records_z2_landmark_regression :
    ∃ entry : YangMillsRoadmapEntry,
      entry.nodeId = yangMillsZ2StrongCouplingGapNode.id ∧
        entry.status = .checked ∧
        entry.truthValue = ⟨100, 99⟩ ∧
        entry.progressPercent = 100 := by
  exact currentYangMillsRoadmap_records_z2_landmark

theorem roadmap_keeps_continuum_endpoint_open_regression :
    yangMillsContinuumMassGapEndpointRoadmapEntry.status = .openGoal ∧
      yangMillsContinuumMassGapEndpointRoadmapEntry.progressPercent = 0 ∧
      yangMillsMassGapEndpointNode.status = .openGoal := by
  exact currentYangMillsRoadmap_keeps_continuum_endpoint_open

end Z2StrongCouplingGapRegression
end YangMills
end QuantumTheory
end Mettapedia
