import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceAnticommutatorPhysicalFamily

/-!
# Regression checks for OUR physical adjacent trace-anticommutator family

These checks retain the policy-indexed semantic boundary of the seven-site
physical family and the kernel statement for the full current correction.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceAnticommutatorPhysicalFamilyRegression

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16TraceAnticommutatorPhysicalFamily
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair

example (left : OurPhysicalTraceAnticommutatorLabel) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single
          (ourPhysicalTraceAnticommutatorGeneratorAt .offShell left) 1)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutator_row_zero
    .offShell left

example (left : OurPhysicalTraceAnticommutatorLabel) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single
          (ourPhysicalTraceAnticommutatorGeneratorAt .onShell left) 1)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutator_row_zero
    .onShell left

example (cochain : OurPhysicalTraceAnticommutatorCochainSpace) :
    ourCycleProfileInvariantTraceOrderCorrection
      ((ourPhysicalTraceAnticommutatorToJointRelation .offShell cochain).1).1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutator_zero
    .offShell cochain

example (cochain : OurPhysicalTraceAnticommutatorCochainSpace) :
    ourCycleProfileInvariantTraceOrderCorrection
      ((ourPhysicalTraceAnticommutatorToJointRelation .onShell cochain).1).1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutator_zero
    .onShell cochain

#print axioms HypercubicDimension16TraceAnticommutatorPhysicalFamily.ourPhysicalTraceAnticommutator_rowFormula
#print axioms HypercubicDimension16TraceAnticommutatorPhysicalFamily.ourPhysicalTraceAnticommutatorProfileValue_eq_neg_half
#print axioms HypercubicDimension16TraceAnticommutatorPhysicalFamily.ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutator_row_zero
#print axioms HypercubicDimension16TraceAnticommutatorPhysicalFamily.ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutator_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceAnticommutatorPhysicalFamilyRegression
