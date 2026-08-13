import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FDIBPCochainJointBridge

/-! Regression checks for OUR semantic `F,D`/IBP cochain bridge. -/

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16FDIBPCochainJointBridge

example (policy : PhysicalRelationPolicy) :
    Function.Surjective (ourFDIBPCochainToJointRelation policy) :=
  ourFDIBPCochainToJointRelation_surjective policy

example (policy : PhysicalRelationPolicy) :
    LinearMap.range (ourFDIBPCochainToJointRelation policy) = ⊤ :=
  ourFDIBPCochainToJointRelation_range_eq_top policy

example (cochain : OurFDIBPCochainSpace .offShell) :
    ((ourFDIBPCochainToJointRelation .onShell
      (liftOffShellGeneratorSpace cochain)).1).1 =
      ((ourFDIBPCochainToJointRelation .offShell cochain).1).1 :=
  ourFDIBPCochainToJointRelation_liftOffShell_val cochain

#print axioms HypercubicDimension16FDIBPCochainJointBridge.ourFDIBPCochainToJointRelation_equivariant
#print axioms HypercubicDimension16FDIBPCochainJointBridge.ourFDIBPCochainToJointRelation_surjective
#print axioms HypercubicDimension16FDIBPCochainJointBridge.ourFDIBPCochainToJointRelation_range_eq_top
#print axioms HypercubicDimension16FDIBPCochainJointBridge.ourFDIBPCochainToJointRelation_liftOffShell_val

end YangMills
end QuantumTheory
end Mettapedia
