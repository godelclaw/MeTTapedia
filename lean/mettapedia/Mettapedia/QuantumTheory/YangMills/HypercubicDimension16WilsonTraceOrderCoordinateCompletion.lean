import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderRepair
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoordinates

/-!
# OUR finite trace-order coordinate completion

The actual Cartan Wilson eighth-jet cannot be a faithful coordinate on the
ordinary eight-field trace quotient: it loses the certified incoming
trace-order class.  The existing exact trace quotient, however, already has
`98` checked coefficient duals with reconstruction.  This module turns those
duals into one explicit coordinate packet and composes that packet with OUR
forced seven-field compensator on the local coupled commutator quotient.

Thus the local repair has a finite, rational, reconstructing trace-order
coordinate layer.  It annihilates the full coupled commutator row and
retains the isolated eight-field trace-order signal with its exact two-pivot
packet.  This is not an analytic construction of a full noncommutative
Wilson functional, a descent proof through the complete relation submodule,
or a conditioning bound for the added seven-field compensator.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16WilsonTraceOrderCoordinateCompletion

open scoped BigOperators

open HypercubicDimension16WilsonTraceOrderRepair
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledColumn
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceEvaluationReynolds
open HypercubicDimension16PhysicalTracePublicConditioning
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceCoordinates
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator

/-- OUR complete `98`-coordinate packet on the ordinary derivative-free
eight-field trace quotient. -/
def ourPhysicalTraceCoordinatePacket :
    FieldEightPhysicalTraceQuotient →ₗ[ℚ] (Fin 98 → ℚ) where
  toFun := fun value row => physicalTraceCoefficientDual row value
  map_add' := by
    intro left right
    funext row
    exact map_add (physicalTraceCoefficientDual row) left right
  map_smul' := by
    intro scalar value
    funext row
    exact map_smul (physicalTraceCoefficientDual row) scalar value

/-- OUR synthesis map from an exact trace-coordinate packet back to its
ordinary trace-quotient class. -/
def ourPhysicalTraceCoordinateSynthesis :
    (Fin 98 → ℚ) →ₗ[ℚ] FieldEightPhysicalTraceQuotient where
  toFun := fun coordinates => ∑ row : Fin 98,
    coordinates row • physicalTraceFreeClass row
  map_add' := by
    intro left right
    simp_rw [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro scalar coordinates
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro row _
    change (scalar * coordinates row) • physicalTraceFreeClass row =
      scalar • (coordinates row • physicalTraceFreeClass row)
    rw [smul_smul]

/-- Synthesis after OUR packet is exactly the identity on the complete
ordinary trace quotient. -/
theorem ourPhysicalTraceCoordinateSynthesis_comp_packet :
    ourPhysicalTraceCoordinateSynthesis.comp ourPhysicalTraceCoordinatePacket =
      LinearMap.id := by
  apply LinearMap.ext
  intro value
  change (∑ row : Fin 98,
    physicalTraceCoefficientDual row value • physicalTraceFreeClass row) = value
  exact physicalTraceFreeBasis_reconstruction value

/-- OUR full trace-coordinate packet is injective: it retains every ordinary
trace-quotient class, not merely the incoming witness. -/
theorem ourPhysicalTraceCoordinatePacket_injective :
    Function.Injective ourPhysicalTraceCoordinatePacket := by
  intro left right hequal
  have hrecover (value : FieldEightPhysicalTraceQuotient) :
      ourPhysicalTraceCoordinateSynthesis
          (ourPhysicalTraceCoordinatePacket value) = value := by
    have h := congrArg (fun coordinate :
        FieldEightPhysicalTraceQuotient →ₗ[ℚ] FieldEightPhysicalTraceQuotient =>
        coordinate value) ourPhysicalTraceCoordinateSynthesis_comp_packet
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using h
  calc
    left = ourPhysicalTraceCoordinateSynthesis
        (ourPhysicalTraceCoordinatePacket left) := (hrecover left).symm
    _ = ourPhysicalTraceCoordinateSynthesis
        (ourPhysicalTraceCoordinatePacket right) := congrArg
          ourPhysicalTraceCoordinateSynthesis hequal
    _ = right := hrecover right

/-- OUR packet of the certified incoming trace-order class is its exact
two-pivot standard trace coordinate vector. -/
theorem ourPhysicalTraceCoordinatePacket_literalIncoming :
    ourPhysicalTraceCoordinatePacket literalIncomingCommutatorClass =
      literalIncomingCoordinate := by
  funext row
  exact physicalTraceCoefficientDual_literalIncoming row

/-- The full trace-coordinate packet detects the certified incoming class. -/
theorem ourPhysicalTraceCoordinatePacket_literalIncoming_ne_zero :
    ourPhysicalTraceCoordinatePacket literalIncomingCommutatorClass ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero (⟨6, by decide⟩ : Fin 98)
  rw [ourPhysicalTraceCoordinatePacket_literalIncoming] at hvalue
  norm_num [literalIncomingCoordinate] at hvalue

/-- OUR explicit trace-order packet on the local seven/eight-field coupled
commutator quotient. -/
def ourCoupledTraceOrderCoordinatePacket :
    CoupledIncomingQuotient →ₗ[ℚ] (Fin 98 → ℚ) :=
  ourPhysicalTraceCoordinatePacket.comp
    ourTraceOrderAwareLocalQuotientCoordinate

/-- OUR completed packet annihilates the full projected physical
covariant-commutator row for either relation policy. -/
theorem ourCoupledTraceOrderCoordinatePacket_physicalCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourCoupledTraceOrderCoordinatePacket
      (coupledIncomingQuotientMap
        (exactFieldSevenEightProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)))) = 0 := by
  unfold ourCoupledTraceOrderCoordinatePacket
  rw [LinearMap.comp_apply,
    ourTraceOrderAwareLocalQuotientCoordinate_physicalCommutator_zero]
  exact map_zero _

/-- On the isolated eight-field component, OUR completed packet retains the
negative of the certified incoming two-pivot trace vector. -/
theorem ourCoupledTraceOrderCoordinatePacket_eightComponent :
    ourCoupledTraceOrderCoordinatePacket
      (coupledIncomingQuotientMap
        (0, coupledIncomingCommutatorVector.2)) =
      -literalIncomingCoordinate := by
  funext row
  unfold ourCoupledTraceOrderCoordinatePacket
  change physicalTraceCoefficientDual row
      (ourTraceOrderAwareLocalQuotientCoordinate
        (coupledIncomingQuotientMap (0, coupledIncomingCommutatorVector.2))) =
      -literalIncomingCoordinate row
  rw [ourTraceOrderAwareLocalQuotientCoordinate_detects_eightComponent,
    map_neg,
    physicalTraceCoefficientDual_literalIncoming]

/-- The completed local packet still detects the isolated eight-field
trace-order component. -/
theorem ourCoupledTraceOrderCoordinatePacket_eightComponent_ne_zero :
    ourCoupledTraceOrderCoordinatePacket
      (coupledIncomingQuotientMap
        (0, coupledIncomingCommutatorVector.2)) ≠ 0 := by
  intro hzero
  have hvalue := congrFun hzero (⟨6, by decide⟩ : Fin 98)
  rw [ourCoupledTraceOrderCoordinatePacket_eightComponent] at hvalue
  norm_num [literalIncomingCoordinate] at hvalue

#print axioms ourPhysicalTraceCoordinateSynthesis_comp_packet
#print axioms ourPhysicalTraceCoordinatePacket_injective
#print axioms ourPhysicalTraceCoordinatePacket_literalIncoming
#print axioms ourPhysicalTraceCoordinatePacket_literalIncoming_ne_zero
#print axioms ourCoupledTraceOrderCoordinatePacket_physicalCommutator_zero
#print axioms ourCoupledTraceOrderCoordinatePacket_eightComponent
#print axioms ourCoupledTraceOrderCoordinatePacket_eightComponent_ne_zero

end HypercubicDimension16WilsonTraceOrderCoordinateCompletion
end YangMills
end QuantumTheory
end Mettapedia
