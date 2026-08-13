import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonCartanJointMismatch

/-!
# OUR trace-order-faithful Cartan Wilson-coordinate obstruction

The existing actual Wilson eighth-jet calculation is a valid Cartan
calculation, but it forgets noncommutative trace order.  This module makes
that limitation an explicit finite no-go theorem rather than an informal
warning.

OUR certificate asks for a linear coordinate on the complete ordinary
eight-field trace quotient that (i) reproduces the actual Cartan Wilson jet
on every raw labelled input and (ii) is faithful, hence injective, on that
quotient.  The certified incoming commutator endpoints have a nonzero trace
class while their actual Cartan Wilson values agree.  Consequently no such
certificate exists, even before adding a signed-`H(4)` equivariance demand.

This does not rule out a repaired noncommutative Wilson coordinate system. It
isolates the necessary repair: it must retain trace-order data beyond the
existing Cartan coordinate.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16WilsonCartanTraceOrderFaithfulnessNoGo

open HypercubicDimension16WilsonCartanJointMismatch
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16FieldEightPhysicalTrace

/-- OUR raw labelled eight-field syntax mapped to its complete ordinary trace
class. -/
def ourRawLabeledToFieldEightTraceClass :
    OurLabeledFieldEightSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  exactFieldEightTraceClassMap.comp ourRawLabeledToFieldEightOrbit

/-- The certified incoming raw difference maps to its nonzero ordinary trace
class. -/
theorem ourRawLabeledToFieldEightTraceClass_incomingRawDifference :
    ourRawLabeledToFieldEightTraceClass ourIncomingRawDifference =
      literalIncomingCommutatorClass := by
  change exactFieldEightTraceClassMap
      (ourRawLabeledToFieldEightOrbit ourIncomingRawDifference) = _
  rw [ourRawLabeledToFieldEightOrbit_incomingRawDifference]
  exact exactFieldEightTraceClassMap_literalIncoming

/-- OUR proposed realization of the actual Cartan Wilson eighth jet that
retains the certified incoming trace-order class. `agrees` is its semantic
requirement on raw labelled inputs. -/
structure OurIncomingTraceOrderFaithfulCartanWilsonCoordinate (a : ℝ) where
  coordinate : FieldEightPhysicalTraceQuotient →ₗ[ℚ] ℝ
  agrees : coordinate.comp ourRawLabeledToFieldEightTraceClass =
    ourRawCartanWilsonEighthJet a
  detectsIncoming : coordinate literalIncomingCommutatorClass ≠ 0

/-- The actual Cartan Wilson eighth jet cannot retain even the single
certified incoming trace-order class after a quotient realization. -/
theorem no_ourIncomingTraceOrderFaithfulCartanWilsonCoordinate (a : ℝ) :
    ¬ Nonempty (OurIncomingTraceOrderFaithfulCartanWilsonCoordinate a) := by
  rintro ⟨candidate⟩
  apply candidate.detectsIncoming
  have hagrees := congrArg
    (fun coordinate : OurLabeledFieldEightSpace →ₗ[ℚ] ℝ =>
      coordinate ourIncomingRawDifference) candidate.agrees
  change candidate.coordinate
      (ourRawLabeledToFieldEightTraceClass ourIncomingRawDifference) =
    ourRawCartanWilsonEighthJet a ourIncomingRawDifference at hagrees
  rw [ourRawLabeledToFieldEightTraceClass_incomingRawDifference,
    ourRawCartanWilsonEighthJet_incomingRawDifference_zero] at hagrees
  exact hagrees

/-- OUR proposed globally faithful realization of the actual Cartan Wilson
eighth jet.  `agrees` is its semantic requirement on raw labelled inputs;
`injective` says that the resulting quotient coordinate does not erase a
nonzero ordinary trace class. -/
structure OurTraceOrderFaithfulCartanWilsonCoordinate (a : ℝ) where
  coordinate : FieldEightPhysicalTraceQuotient →ₗ[ℚ] ℝ
  agrees : coordinate.comp ourRawLabeledToFieldEightTraceClass =
    ourRawCartanWilsonEighthJet a
  injective : Function.Injective coordinate

/-- The existing actual Cartan Wilson eighth jet admits no trace-order-faithful
realization on the complete ordinary eight-field trace quotient.  Since this
already fails without an equivariance hypothesis, adding signed-`H(4)`
equivariance cannot repair this particular coordinate. -/
theorem no_ourTraceOrderFaithfulCartanWilsonCoordinate (a : ℝ) :
    ¬ Nonempty (OurTraceOrderFaithfulCartanWilsonCoordinate a) := by
  rintro ⟨candidate⟩
  apply no_ourIncomingTraceOrderFaithfulCartanWilsonCoordinate a
  refine ⟨candidate.coordinate, candidate.agrees, ?_⟩
  intro hzero
  apply literalIncomingCommutatorClass_ne_zero
  apply candidate.injective
  rw [hzero, map_zero]

#print axioms ourRawLabeledToFieldEightTraceClass_incomingRawDifference
#print axioms no_ourIncomingTraceOrderFaithfulCartanWilsonCoordinate
#print axioms no_ourTraceOrderFaithfulCartanWilsonCoordinate

end HypercubicDimension16WilsonCartanTraceOrderFaithfulnessNoGo
end YangMills
end QuantumTheory
end Mettapedia
