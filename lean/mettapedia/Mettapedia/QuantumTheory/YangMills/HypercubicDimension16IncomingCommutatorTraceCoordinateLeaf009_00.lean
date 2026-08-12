import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinateCore

/-!
# OUR atomic incoming trace-coordinate replay

This finite certificate verifies the listed entries of OUR incoming trace
column against the two certified standard columns.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf009_00

open HypercubicDimension16PhysicalTraceEvaluationExecutable
open HypercubicDimension16IncomingCommutatorTraceCoordinateCore

set_option maxHeartbeats 3000000 in
theorem replay_first :
    literalIncomingUnsignedEvaluation (⟨63, by decide⟩ : Fin 98) =
      (expectedUnsignedEvaluation (⟨63, by decide⟩ : Fin 98) ⟨6, by decide⟩ -
        expectedUnsignedEvaluation (⟨63, by decide⟩ : Fin 98) ⟨4, by decide⟩) / 4 := by
  set_option maxRecDepth 100000 in
    decide +kernel

#print axioms replay_first

set_option maxHeartbeats 3000000 in
theorem replay_second :
    literalIncomingUnsignedEvaluation (⟨64, by decide⟩ : Fin 98) =
      (expectedUnsignedEvaluation (⟨64, by decide⟩ : Fin 98) ⟨6, by decide⟩ -
        expectedUnsignedEvaluation (⟨64, by decide⟩ : Fin 98) ⟨4, by decide⟩) / 4 := by
  set_option maxRecDepth 100000 in
    decide +kernel

#print axioms replay_second

end HypercubicDimension16IncomingCommutatorTraceCoordinateLeaf009_00
end YangMills
end QuantumTheory
end Mettapedia

