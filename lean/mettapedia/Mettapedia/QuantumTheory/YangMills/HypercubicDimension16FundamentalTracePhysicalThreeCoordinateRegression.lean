import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalThreeCoordinate

/-!
# Regression checks for OUR physical three-coordinate bridge

These checks retain the complete finite physical fundamental-trace family
under both relation policies. They concern OUR current trace-order repair on
that family only and do not assert full coordinate-free relation-submodule
descent.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalThreeCoordinateRegression

open HypercubicDimension16FundamentalTracePhysicalFamily
open HypercubicDimension16FundamentalTracePhysicalThreeCoordinate
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair

/-- OUR off-shell physical three-cut family remains in the kernel of the
separate three-coordinate correction. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_offShell_zero
    (cochain : OurFundamentalTraceCochainSpace) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      ((ourFundamentalTraceToJointRelation .offShell cochain).1).1 = 0 :=
  ourThreeCoordinateInvariantTraceOrderCorrection_fundamentalTrace_zero
    .offShell cochain

/-- OUR on-shell physical three-cut family remains in the kernel of the
separate three-coordinate correction. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_onShell_zero
    (cochain : OurFundamentalTraceCochainSpace) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      ((ourFundamentalTraceToJointRelation .onShell cochain).1).1 = 0 :=
  ourThreeCoordinateInvariantTraceOrderCorrection_fundamentalTrace_zero
    .onShell cochain

/-- OUR off-shell physical three-cut family remains in the kernel of the
full current cycle-profile correction. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_offShell_zero
    (cochain : OurFundamentalTraceCochainSpace) :
    ourCycleProfileInvariantTraceOrderCorrection
      ((ourFundamentalTraceToJointRelation .offShell cochain).1).1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_fundamentalTrace_zero
    .offShell cochain

/-- OUR on-shell physical three-cut family remains in the kernel of the
full current cycle-profile correction. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_onShell_zero
    (cochain : OurFundamentalTraceCochainSpace) :
    ourCycleProfileInvariantTraceOrderCorrection
      ((ourFundamentalTraceToJointRelation .onShell cochain).1).1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_fundamentalTrace_zero
    .onShell cochain

#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_offShell_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_onShell_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_offShell_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_onShell_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalThreeCoordinateRegression
