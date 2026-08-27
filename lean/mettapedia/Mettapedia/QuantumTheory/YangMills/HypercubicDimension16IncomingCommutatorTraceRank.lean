import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceQuotient
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceMismatch

/-!
# OUR incoming commutator rank extension

The derivative-free eight-field standard trace quotient has a certified
`11556`-dimensional relation submodule inside its `11654`-dimensional signed
orbit coinvariant carrier.  The checked incoming covariant-commutator
projection has a literal eight-field class which survives that relation
submodule.

This module makes the resulting one-column calculation explicit: adjoining
that literal class raises the relation rank by one and reduces the quotient
dimension from `98` to `97`.  It is an OUR bounded cross-sector extension of
the isolated trace calculation, not a computation of the full joint physical
quotient.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceRank

open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceQuotient
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch

/-- OUR non-membership certificate for the literal eight-field projection of
the checked incoming covariant commutator. -/
theorem literalIncomingCommutatorCoinvariant_not_mem :
    literalIncomingCommutatorCoinvariant ∉
      fieldEightPhysicalTraceRelationSubmodule := by
  intro hmem
  apply actualIncomingLiteralTraceClass_ne_zero
  change Submodule.Quotient.mk literalIncomingCommutatorCoinvariant = 0
  exact (Submodule.Quotient.mk_eq_zero
    fieldEightPhysicalTraceRelationSubmodule).mpr hmem

/-- OUR relation submodule obtained by adjoining the literal incoming
commutator column to every ordinary derivative-free eight-field trace row. -/
def incomingAugmentedTraceRelationSubmodule :
    Submodule ℚ FieldEightSignedOrbitCoinvariant :=
  fieldEightPhysicalTraceRelationSubmodule ⊔
    Submodule.span ℚ {literalIncomingCommutatorCoinvariant}

/-- OUR quotient of the signed eight-field orbit coinvariants by the ordinary
trace rows together with the literal incoming commutator column. -/
abbrev IncomingAugmentedTraceQuotient :=
  FieldEightSignedOrbitCoinvariant ⧸ incomingAugmentedTraceRelationSubmodule

/-- OUR exact rank of the one-column augmented relation submodule. -/
theorem incomingAugmentedTraceRelationSubmodule_finrank :
    Module.finrank ℚ incomingAugmentedTraceRelationSubmodule = 11557 := by
  unfold incomingAugmentedTraceRelationSubmodule
  rw [Submodule.finrank_sup_span_singleton
    literalIncomingCommutatorCoinvariant_not_mem,
    physicalTraceRelationSubmodule_finrank]

/-- OUR exact dimension after imposing the literal projection of the checked
incoming covariant commutator. -/
theorem incomingAugmentedTraceQuotient_finrank :
    Module.finrank ℚ IncomingAugmentedTraceQuotient = 97 := by
  rw [Submodule.finrank_quotient,
    fieldEightSignedOrbitCoinvariant_finrank,
    incomingAugmentedTraceRelationSubmodule_finrank]

#print axioms literalIncomingCommutatorCoinvariant_not_mem
#print axioms incomingAugmentedTraceRelationSubmodule_finrank
#print axioms incomingAugmentedTraceQuotient_finrank

end HypercubicDimension16IncomingCommutatorTraceRank
end YangMills
end QuantumTheory
end Mettapedia
