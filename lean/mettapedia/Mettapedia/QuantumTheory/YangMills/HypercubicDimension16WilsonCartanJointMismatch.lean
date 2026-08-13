import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceQuotient
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
import Mettapedia.QuantumTheory.YangMills.HypercubicWilsonSymanzikRestoration

/-!
# OUR Cartan-Wilson / joint-quotient mismatch at dimension sixteen

The actual Wilson eighth jet currently constructed in this development lives
on the derivative-free Cartan-octic chart.  This file compares that chart with
one explicit cross-sector relation witness on the exact `F,D` carrier.

The two literal eight-field endpoints of the certified incoming covariant
commutator have identical field-plane decorations and differ only in trace
order.  Their ordinary derivative-free trace-quotient class is nonzero, but
every Cartan restriction that forgets trace order sends their signed
difference to zero.  The actual Cartan Wilson eighth-jet coefficient is one
such restriction.  Independently, the complete ordinary trace quotient has
dimension `98`, so no `17`-coordinate Cartan chart can be an injective full
dual chart for it.

This is a semantic mismatch theorem for the existing Cartan calculation.  It
does not refute a genuinely noncommutative Wilson-coordinate construction:
such a construction must retain trace order and the coupled lower-field
commutator component.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16WilsonCartanJointMismatch

open HypercubicDimension16CartanCensus
open HypercubicWilsonSymanzikRestoration
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceQuotient
open HypercubicDimension16IncomingCommutatorTraceCertificate

/-! ## The raw Cartan restriction -/

/-- OUR raw labelled eight-field source space, before field relabeling,
hypercubic averaging, and relation quotienting. -/
abbrev OurLabeledFieldEightSpace := LabeledLocalWordSector 8 0 →₀ ℚ

/-- OUR unordered Cartan octic monomial underlying one labelled
derivative-free eight-field source.  It intentionally records only the eight
two-form planes, so it is insensitive to the trace permutation. -/
def ourCartanOcticRestriction
    (source : LabeledLocalWordSector 8 0) : OcticMonomial :=
  octicOfPlanes
    (source.decoration.1 0).plane
    (source.decoration.1 1).plane
    (source.decoration.1 2).plane
    (source.decoration.1 3).plane
    (source.decoration.1 4).plane
    (source.decoration.1 5).plane
    (source.decoration.1 6).plane
    (source.decoration.1 7).plane

/-- Changing only trace order cannot change OUR Cartan restriction. -/
theorem ourCartanOcticRestriction_traceOrder_blind
    (source : LabeledLocalWordSector 8 0) (trace : Equiv.Perm (Fin 8)) :
    ourCartanOcticRestriction { source with trace := trace } =
      ourCartanOcticRestriction source := by
  rfl

/-- OUR raw labelled map into the ordinary field-relabel orbit carrier. -/
def ourRawLabeledToFieldEightOrbit :
    OurLabeledFieldEightSpace →ₗ[ℚ] FieldEightOrbitSpace :=
  Finsupp.linearCombination ℚ
    (fun source => Finsupp.single (Quotient.mk _ source) 1)

/-- OUR signed two-source input carried by the incoming covariant
commutator. -/
def ourIncomingRawDifference : OurLabeledFieldEightSpace :=
  -Finsupp.single incomingBeforeSource 1 +
    Finsupp.single incomingAfterSource 1

/-- The raw two-source input maps to the literal vector whose ordinary trace
quotient class has already been certified nonzero. -/
theorem ourRawLabeledToFieldEightOrbit_incomingRawDifference :
    ourRawLabeledToFieldEightOrbit ourIncomingRawDifference =
      literalIncomingCommutatorVector := by
  simp [ourRawLabeledToFieldEightOrbit, ourIncomingRawDifference,
    literalIncomingCommutatorVector]

/-- The two endpoints of the incoming commutator have exactly the same
unordered Cartan octic monomial. -/
theorem ourCartanOcticRestriction_incoming_endpoints :
    ourCartanOcticRestriction incomingBeforeSource =
      ourCartanOcticRestriction incomingAfterSource := by
  change ourCartanOcticRestriction
      { incomingBeforeSource with trace := incomingAfterSource.trace } =
    ourCartanOcticRestriction incomingAfterSource
  rw [ourCartanOcticRestriction_traceOrder_blind]
  rfl

/-! ## The actual Wilson eighth-jet coefficient on that restriction -/

/-- OUR linear extension of the actual Cartan Wilson eighth-jet coefficient
to raw labelled eight-field syntax.  This is deliberately not claimed to
descend through the full noncommutative relation quotient. -/
def ourRawCartanWilsonEighthJet (a : ℝ) :
    OurLabeledFieldEightSpace →ₗ[ℚ] ℝ :=
  Finsupp.linearCombination ℚ
    (fun source =>
      actualWilsonOcticJetCoefficient a
        (ourCartanOcticRestriction source))

/-- The actual Cartan Wilson eighth-jet coefficient collapses the explicit
incoming commutator pair. -/
theorem ourRawCartanWilsonEighthJet_incomingRawDifference_zero
    (a : ℝ) :
    ourRawCartanWilsonEighthJet a ourIncomingRawDifference = 0 := by
  unfold ourRawCartanWilsonEighthJet ourIncomingRawDifference
  simp only [map_add, map_neg, Finsupp.linearCombination_single, one_smul]
  rw [ourCartanOcticRestriction_incoming_endpoints]
  ring

/-- The collapse is semantically sharp: the same raw pair has a nonzero
class after the ordinary derivative-free trace relations are imposed. -/
theorem ourCartanWilson_traceQuotient_explicitMismatch (a : ℝ) :
    ourRawCartanWilsonEighthJet a ourIncomingRawDifference = 0 ∧
      literalIncomingCommutatorClass ≠ 0 :=
  ⟨ourRawCartanWilsonEighthJet_incomingRawDifference_zero a,
    literalIncomingCommutatorClass_ne_zero⟩

/-! ## The chart-size obstruction -/

/-- A `17`-coordinate Cartan chart cannot be an injective complete dual chart
for the `98`-dimensional ordinary eight-field trace quotient. -/
theorem no_cartan17Coordinate_fullTraceDual_injective
    (candidate : FieldEightPhysicalTraceQuotient →ₗ[ℚ] (Fin 17 → ℚ)) :
    ¬ Function.Injective candidate := by
  intro hinjective
  have hle := LinearMap.finrank_le_finrank_of_injective hinjective
  rw [physicalTraceQuotient_finrank, Module.finrank_fin_fun] at hle
  omega

#print axioms ourRawLabeledToFieldEightOrbit_incomingRawDifference
#print axioms ourRawCartanWilsonEighthJet_incomingRawDifference_zero
#print axioms ourCartanWilson_traceQuotient_explicitMismatch
#print axioms no_cartan17Coordinate_fullTraceDual_injective

end HypercubicDimension16WilsonCartanJointMismatch
end YangMills
end QuantumTheory
end Mettapedia
