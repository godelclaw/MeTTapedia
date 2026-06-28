import Mettapedia.QuantumTheory.YangMills.ProofState
import Mettapedia.QuantumTheory.YangMills.Z3StrongCouplingGap

/-!
# Yang-Mills finite `Z3` strong-coupling proof state

This module records the checked three-configuration finite-lattice landmark and
its one-step refinement diagnostic.  The finite theorem is unconditional and
non-vacuous; the continuum endpoint remains open.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- The explicit finite `Z3` strong-coupling gap theorem checked in Lean. -/
def yangMillsZ3StrongCouplingGapNode : YangMillsProofNode where
  id := "yang-mills.finite-z3-strong-coupling-gap"
  status := .checked
  truthValue := ⟨100, 99⟩
  evidence := "z3StrongCoupling_latticeYangMills_massGap_landmark packages a nontrivial three-configuration finite lattice, reflection positivity, OS transfer reconstruction, two mean-zero eigenvectors, and z3StrongCouplingGap = 1."
  nextObligation := "Generalize the same non-vacuous canary pattern to reusable Z_N families and keep continuum scaling diagnostics separate from the finite lattice gap."

/-- A checked half-scale refinement diagnostic for linear heat-time schedules. -/
def yangMillsZ3HalfScaleRGStepNode : YangMillsProofNode where
  id := "yang-mills.z3-half-scale-linear-rg-step"
  status := .checked
  truthValue := ⟨100, 96⟩
  evidence := "z3HalfScaleRGPositiveCanary records kappa=1/2, kappa<1, a concrete refined spacing, and preservation of the physical gap for t(a)=k*a."
  nextObligation := "Classify which scaling schedules keep a positive physical lower bound; z3QuadraticHeatTime_physicalGap_closes remains the warning that not every refinement schedule preserves the gap."

/-- The focused finite-lattice and refinement proof-state node list. -/
def currentYangMillsZ3StrongCouplingProofNodes : List YangMillsProofNode :=
  [yangMillsZ3StrongCouplingGapNode, yangMillsZ3HalfScaleRGStepNode]

theorem yangMillsZ3StrongCouplingGapNode_checked :
    yangMillsZ3StrongCouplingGapNode.status = .checked := by
  rfl

theorem yangMillsZ3HalfScaleRGStepNode_checked :
    yangMillsZ3HalfScaleRGStepNode.status = .checked := by
  rfl

theorem currentYangMillsZ3StrongCouplingProofNodes_nonempty :
    currentYangMillsZ3StrongCouplingProofNodes ≠ [] := by
  simp [currentYangMillsZ3StrongCouplingProofNodes]

/-- Checked finite-lattice packet plus the non-vacuous half-scale refinement
diagnostic and the quadratic scaling warning. -/
theorem currentYangMillsZ3StrongCouplingGap_packet :
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
  exact
    ⟨z3StrongCoupling_latticeYangMills_massGap_landmark,
      ⟨z3HalfScaleRGPositiveCanary,
        rfl,
        z3HalfScaleKappa_pos,
        z3HalfScaleKappa_lt_one,
        z3LinearHeatTime_unitLowerBound
          (a := z3HalfScaleKappa * 1) (by norm_num [z3HalfScaleKappa])⟩,
      z3StrongCouplingGap_eq_one,
      z3StrongCouplingGap_lower_bound_one,
      by
        intro a κ ha
        exact z3HalfScaleLinearRGStep_preserves_physicalGap (a := a) (κ := κ) ha,
      z3QuadraticHeatTime_physicalGap_closes⟩

end YangMills
end QuantumTheory
end Mettapedia
