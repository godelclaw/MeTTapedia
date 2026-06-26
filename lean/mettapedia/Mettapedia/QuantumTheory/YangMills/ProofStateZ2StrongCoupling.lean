import Mettapedia.QuantumTheory.YangMills.ProofState
import Mettapedia.QuantumTheory.YangMills.Z2StrongCouplingGap

/-!
# Yang-Mills finite `Z₂` strong-coupling proof state

This module records the checked finite-lattice landmark separately from the
continuum mass-gap endpoint.  The finite theorem is unconditional and
non-vacuous; the continuum endpoint remains open.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-- The explicit finite `Z₂` strong-coupling gap theorem now checked in Lean. -/
def yangMillsZ2StrongCouplingGapNode : YangMillsProofNode where
  id := "yang-mills.finite-z2-strong-coupling-gap"
  status := .checked
  truthValue := ⟨100, 99⟩
  evidence := "z2StrongCoupling_latticeYangMills_massGap_landmark packages a nontrivial two-configuration finite lattice, reflection positivity, OS transfer reconstruction, constant/sign eigenvectors, and z2StrongCouplingGap = 1."
  nextObligation := "Keep z2QuadraticHeatTime_physicalGap_closes as the continuum-scaling obstruction; do not promote the finite gap to a continuum mass-gap endpoint."

/-- The focused finite-lattice proof-state node list for the strong-coupling canary. -/
def currentYangMillsZ2StrongCouplingProofNodes : List YangMillsProofNode :=
  [yangMillsZ2StrongCouplingGapNode]

theorem yangMillsZ2StrongCouplingGapNode_checked :
    yangMillsZ2StrongCouplingGapNode.status = .checked := by
  rfl

theorem currentYangMillsZ2StrongCouplingProofNodes_nonempty :
    currentYangMillsZ2StrongCouplingProofNodes ≠ [] := by
  simp [currentYangMillsZ2StrongCouplingProofNodes]

/-- Checked finite-lattice packet and its first continuum-scaling warning. -/
theorem currentYangMillsZ2StrongCouplingGap_packet :
    (∃ _ : Z2StrongCouplingGapCanary,
      (∃ x y : Z2OneLinkConfig, x ≠ y) ∧
        OSReflectionPositive z2StrongCouplingKernel ∧
        z2StrongCouplingGap = 1 ∧
        (1 : ℝ) ≤ z2StrongCouplingGap ∧
        0 < z2StrongCouplingGap) ∧
      z2StrongCouplingGap = 1 ∧
      (1 : ℝ) ≤ z2StrongCouplingGap ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ a : ℝ,
          0 < a ∧ a < ε ∧ z2HeatTimePhysicalGap a (a ^ 2) < ε) := by
  exact
    ⟨z2StrongCoupling_latticeYangMills_massGap_landmark,
      z2StrongCouplingGap_eq_one,
      z2StrongCouplingGap_lower_bound_one,
      z2QuadraticHeatTime_physicalGap_closes⟩

end YangMills
end QuantumTheory
end Mettapedia
