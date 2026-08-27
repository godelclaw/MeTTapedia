import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceMismatch

/-!
# OUR exact-carrier projection of the incoming commutator pair

This file supplies the typed bridge from the isolated eight-field orbit
carrier to the exact field-indexed carrier used by the physical relation
operator.  It identifies only the eight-field projection of one concrete
covariant-commutator column.  No claim is made here about the complete
physical relation submodule or its quotient.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceProjection

open HypercubicRawFDDimension16Census
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch

/-- OUR typed inclusion of the isolated eight-field orbit carrier in the
exact field-indexed orbit carrier. -/
def fieldEightExactCarrier (target : FieldEightOrbitCarrier) :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourEightFieldCount, target⟩

/-- OUR linear inclusion of finite eight-field orbit combinations in the
exact field-indexed orbit space. -/
def fieldEightExactEmbed : FieldEightOrbitSpace →ₗ[ℚ]
    ExactFieldRelabelOrbitSpace :=
  Finsupp.lmapDomain ℚ ℚ fieldEightExactCarrier

@[simp] theorem fieldEightExactEmbed_single
    (target : FieldEightOrbitCarrier) (coefficient : ℚ) :
    fieldEightExactEmbed (Finsupp.single target coefficient) =
      Finsupp.single (fieldEightExactCarrier target) coefficient := by
  simp [fieldEightExactEmbed]

/-- OUR exact-carrier form of the literal incoming signed pair. -/
theorem fieldEightExactEmbed_literalIncoming :
    fieldEightExactEmbed literalIncomingCommutatorVector =
      -Finsupp.single (ourLiteralExactTarget incomingBeforeSource) 1 +
        Finsupp.single (ourLiteralExactTarget incomingAfterSource) 1 := by
  rw [literalIncomingCommutatorVector, map_add, map_neg]
  simp only [fieldEightExactEmbed_single]
  rfl

/-- The eight-field projection of OUR concrete covariant-commutator column
is exactly the embedded literal pair. -/
theorem actualIncomingProjection_eq_fieldEightExactEmbed
    (policy : PhysicalRelationPolicy) :
    orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) =
      fieldEightExactEmbed literalIncomingCommutatorVector := by
  rw [orbitPhysicalRelationOperator_ourCommutator_fieldEight_literal]
  exact fieldEightExactEmbed_literalIncoming.symm

#print axioms actualIncomingProjection_eq_fieldEightExactEmbed

end HypercubicDimension16IncomingCommutatorTraceProjection
end YangMills
end QuantumTheory
end Mettapedia
