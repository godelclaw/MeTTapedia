import Mettapedia.QuantumTheory.YangMills.Roadmap

/-!
# Regression checks for the finite `Z3` strong-coupling gap

These checks keep the non-vacuous finite lattice canary and the half-scale
refinement diagnostic exposed through the public Yang-Mills roadmap.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

theorem z3StrongCoupling_landmark_regression :
    ∃ _ : Z3StrongCouplingGapCanary,
      (∃ x y : Z3OneLinkConfig, x ≠ y) ∧
        OSReflectionPositive z3StrongCouplingKernel ∧
        z3StrongCouplingGap = 1 ∧
        (1 : ℝ) ≤ z3StrongCouplingGap ∧
        0 < z3StrongCouplingGap := by
  exact z3StrongCoupling_latticeYangMills_massGap_landmark

theorem z3HalfScaleRG_canary_regression :
    ∃ _ : Z3HalfScaleRGCanary,
      z3HalfScaleKappa = 1 / 2 ∧
        0 < z3HalfScaleKappa ∧
        z3HalfScaleKappa < 1 ∧
        (1 : ℝ) ≤
          z3HeatTimePhysicalGap
            (z3HalfScaleKappa * 1) (1 * (z3HalfScaleKappa * 1)) := by
  exact
    ⟨z3HalfScaleRGPositiveCanary,
      rfl,
      z3HalfScaleKappa_pos,
      z3HalfScaleKappa_lt_one,
      z3LinearHeatTime_unitLowerBound
        (a := z3HalfScaleKappa * 1) (by norm_num [z3HalfScaleKappa])⟩

theorem z3HalfScaleRG_preservation_regression :
    z3HalfScaleKappa = 1 / 2 ∧
      z3HalfScaleKappa < 1 ∧
      (∀ {a κ : ℝ}, a ≠ 0 →
        z3HeatTimePhysicalGap
            (z3HalfScaleKappa * a) (κ * (z3HalfScaleKappa * a)) =
          z3HeatTimePhysicalGap a (κ * a)) := by
  exact
    ⟨rfl,
      z3HalfScaleKappa_lt_one,
      by
        intro a κ ha
        exact z3HalfScaleLinearRGStep_preserves_physicalGap (a := a) (κ := κ) ha⟩

theorem z3StrongCoupling_packet_regression :
    (∃ _ : Z3StrongCouplingGapCanary,
      (∃ x y : Z3OneLinkConfig, x ≠ y) ∧
        OSReflectionPositive z3StrongCouplingKernel ∧
        z3StrongCouplingGap = 1 ∧
        (1 : ℝ) ≤ z3StrongCouplingGap ∧
        0 < z3StrongCouplingGap) ∧
      (∃ _ : Z3HalfScaleRGCanary,
        z3HalfScaleKappa = 1 / 2 ∧
          0 < z3HalfScaleKappa ∧
          z3HalfScaleKappa < 1 ∧
          (1 : ℝ) ≤
            z3HeatTimePhysicalGap
              (z3HalfScaleKappa * 1) (1 * (z3HalfScaleKappa * 1))) ∧
      z3StrongCouplingGap = 1 ∧
      (1 : ℝ) ≤ z3StrongCouplingGap ∧
      (∀ {a κ : ℝ}, a ≠ 0 →
        z3HeatTimePhysicalGap
            (z3HalfScaleKappa * a) (κ * (z3HalfScaleKappa * a)) =
          z3HeatTimePhysicalGap a (κ * a)) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ a : ℝ,
          0 < a ∧ a < ε ∧ z3HeatTimePhysicalGap a (a ^ 2) < ε) := by
  exact currentYangMillsZ3StrongCouplingGap_packet

theorem z3Roadmap_landmark_regression :
    ∃ entry : YangMillsRoadmapEntry,
      entry.nodeId = yangMillsZ3StrongCouplingGapNode.id ∧
        entry.status = .checked ∧
        entry.truthValue = ⟨100, 99⟩ ∧
        entry.progressPercent = 100 ∧
        z3StrongCouplingGap = 1 ∧
        (1 : ℝ) ≤ z3StrongCouplingGap := by
  exact currentYangMillsRoadmap_records_z3_landmark

theorem z3Roadmap_half_scale_rg_regression :
    z3HalfScaleLinearRGStepRoadmapEntry.status = .checked ∧
      z3HalfScaleLinearRGStepRoadmapEntry.progressPercent = 100 ∧
      z3HalfScaleKappa = 1 / 2 ∧
      z3HalfScaleKappa < 1 ∧
      (∀ {a κ : ℝ}, a ≠ 0 →
        z3HeatTimePhysicalGap
            (z3HalfScaleKappa * a) (κ * (z3HalfScaleKappa * a)) =
          z3HeatTimePhysicalGap a (κ * a)) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ a : ℝ,
          0 < a ∧ a < ε ∧ z3HeatTimePhysicalGap a (a ^ 2) < ε) := by
  exact currentYangMillsRoadmap_records_z3_half_scale_rg_step

end YangMills
end QuantumTheory
end Mettapedia
