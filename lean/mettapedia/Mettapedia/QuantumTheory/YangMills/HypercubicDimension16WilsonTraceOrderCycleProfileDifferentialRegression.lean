import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileDifferential

/-!
# Regression checks for OUR cycle-profile differential compatibility packet

These checks retain the actual physical and Reynolds-averaged relation rows
on which the added trace-cycle profile term has been kernel-checked.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileDifferentialRegression

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantEOM
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileDifferential

example (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_ourCommutator_zero policy

example :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .offShell
        (Finsupp.single (ourFieldSevenIBPGenerator .offShell) 1)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_ourIBP_zero

example (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenSecondIBPGenerator policy) 1)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_zero policy

example (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenBianchiGenerator policy) 1)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_ourBianchi_zero policy

example :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator .onShell
        (Finsupp.single ourFieldSevenEOMGenerator 1)) = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_ourEOM_zero

example (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1)) =
      0 :=
  ourCycleProfileInvariantTraceOrderCorrection_liftedTraceGenerator_zero policy generator

example (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection (ourInvariantCommutatorRow policy).1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_invariantCommutator_zero policy

example :
    ourCycleProfileInvariantTraceOrderCorrection ourInvariantIBPRow.1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_invariantIBP_zero

example (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection (ourInvariantSecondIBPRow policy).1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_invariantSecondIBP_zero policy

example (policy : PhysicalRelationPolicy) :
    ourCycleProfileInvariantTraceOrderCorrection (ourInvariantBianchiRow policy).1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_invariantBianchi_zero policy

example :
    ourCycleProfileInvariantTraceOrderCorrection ourInvariantEOMRow.1 = 0 :=
  ourCycleProfileInvariantTraceOrderCorrection_invariantEOM_zero

#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourInvariantTraceCycleProfileCoordinate_fieldEightExactEmbed_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileRepair.ourCycleProfileInvariantTraceOrderCorrection_liftedTraceGenerator_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileDifferential.ourCycleProfileInvariantTraceOrderCorrection_ourCommutator_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileDifferential.ourCycleProfileInvariantTraceOrderCorrection_ourIBP_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileDifferential.ourCycleProfileInvariantTraceOrderCorrection_ourSecondIBP_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileDifferential.ourCycleProfileInvariantTraceOrderCorrection_ourBianchi_zero
#print axioms HypercubicDimension16WilsonTraceOrderCycleProfileDifferential.ourCycleProfileInvariantTraceOrderCorrection_ourEOM_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileDifferentialRegression
