import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalCycleProfile

/-!
# Regression checks for OUR physical three-cut trace-cycle bridge

These checks retain the two policy instances of the semantic profile-kernel
theorem.  They do not turn the profile-coordinate result into a claim about
the full repaired correction or a complete relation census.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalCycleProfileRegression

open HypercubicDimension16FundamentalTracePhysicalFamily
open HypercubicDimension16FundamentalTracePhysicalCycleProfile
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair

/-- OUR off-shell physical three-cut family remains in the kernel of the
invariant trace-cycle-profile coordinate. -/
theorem ourInvariantTraceCycleProfileCoordinate_offShell_zero
    (cochain : OurFundamentalTraceCochainSpace) :
    ourInvariantTraceCycleProfileCoordinate
      ((ourFundamentalTraceToJointRelation .offShell cochain).1).1 = 0 :=
  ourInvariantTraceCycleProfileCoordinate_fundamentalTrace_zero .offShell cochain

/-- OUR on-shell physical three-cut family remains in the kernel of the
invariant trace-cycle-profile coordinate. -/
theorem ourInvariantTraceCycleProfileCoordinate_onShell_zero
    (cochain : OurFundamentalTraceCochainSpace) :
    ourInvariantTraceCycleProfileCoordinate
      ((ourFundamentalTraceToJointRelation .onShell cochain).1).1 = 0 :=
  ourInvariantTraceCycleProfileCoordinate_fundamentalTrace_zero .onShell cochain

#print axioms ourInvariantTraceCycleProfileCoordinate_offShell_zero
#print axioms ourInvariantTraceCycleProfileCoordinate_onShell_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalCycleProfileRegression
