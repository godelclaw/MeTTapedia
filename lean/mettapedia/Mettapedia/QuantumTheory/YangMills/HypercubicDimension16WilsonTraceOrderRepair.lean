import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoupledDual
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonCartanJointMismatch

/-!
# OUR trace-order-aware local Wilson-coordinate repair

The exact Cartan Wilson eighth jet is a valid calculation on its Cartan
chart, but the preceding mismatch theorem proves that the chart cannot be a
complete noncommutative coordinate system. This file identifies the first
piece of extra data that a repair must carry.

The concrete covariant-commutator row couples a seven-field derivative term
to an eight-field, trace-order-sensitive term. A coordinate that uses only
the canonical eight-field trace map cannot descend through that row. More
strongly, every descended correction has a forced value on its seven-field
component. The existing explicit seven-field compensator realizes that
value, so it gives a local quotient coordinate which both kills the full
physical commutator and still detects its isolated eight-field trace piece.

For clarity, the final data package keeps the actual Cartan Wilson coefficient
packet and the rational trace-order coordinate in distinct components. It is
a local finite repair interface, not a claim that a full noncommutative
Wilson-functional-to-cochain analytic jet has been constructed.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderRepair

open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCoupledColumn
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicWilsonSymanzikRestoration

/-- OUR two-band carrier on which the concrete cross-sector commutator lives. -/
abbrev OurCoupledCarrier := FieldSevenOrbitSpace × FieldEightOrbitSpace

/-- OUR coordinate that remembers only the eight-field trace quotient. -/
def ourFieldEightTraceOnlyCoordinate :
    OurCoupledCarrier →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  exactFieldEightTraceClassMap.comp
    (LinearMap.snd ℚ FieldSevenOrbitSpace FieldEightOrbitSpace)

/-- On the full coupled commutator row, the trace-only coordinate is the
certified nonzero incoming trace class. -/
theorem ourFieldEightTraceOnlyCoordinate_coupledIncomingCommutatorVector :
    ourFieldEightTraceOnlyCoordinate coupledIncomingCommutatorVector =
      literalIncomingCommutatorClass := by
  change exactFieldEightTraceClassMap coupledIncomingCommutatorVector.2 = _
  exact coupledIncomingCommutatorVector_traceClass

/-- The local quotient map kills its defining coupled commutator row. -/
theorem coupledIncomingQuotientMap_coupledIncomingCommutatorVector_zero :
    coupledIncomingQuotientMap coupledIncomingCommutatorVector = 0 := by
  change Submodule.Quotient.mk coupledIncomingCommutatorVector = 0
  exact (Submodule.Quotient.mk_eq_zero coupledIncomingRelationSubmodule).mpr
    (Submodule.subset_span (by simp))

/-- No coordinate obtained from the eight-field trace quotient alone can
descend through the local coupled commutator quotient. -/
theorem no_ourFieldEightTraceOnlyCoordinate_descent :
    ¬ ∃ descended : CoupledIncomingQuotient →ₗ[ℚ]
        FieldEightPhysicalTraceQuotient,
      descended.comp coupledIncomingQuotientMap =
        ourFieldEightTraceOnlyCoordinate := by
  rintro ⟨descended, hdescended⟩
  have hvalue := congrArg
    (fun map : OurCoupledCarrier →ₗ[ℚ] FieldEightPhysicalTraceQuotient =>
      map coupledIncomingCommutatorVector) hdescended
  change descended
      (coupledIncomingQuotientMap coupledIncomingCommutatorVector) =
    ourFieldEightTraceOnlyCoordinate coupledIncomingCommutatorVector at hvalue
  rw [coupledIncomingQuotientMap_coupledIncomingCommutatorVector_zero,
    map_zero,
    ourFieldEightTraceOnlyCoordinate_coupledIncomingCommutatorVector] at hvalue
  exact literalIncomingCommutatorClass_ne_zero hvalue.symm

/-- OUR trace-order correction formed from a proposed seven-field
compensator and the canonical eight-field trace quotient coordinate. -/
def ourTraceOrderCorrectedCoordinate
    (seven : FieldSevenOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient) :
    OurCoupledCarrier →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  (seven.comp (LinearMap.fst ℚ FieldSevenOrbitSpace FieldEightOrbitSpace)) -
    ourFieldEightTraceOnlyCoordinate

/-- A descended trace-order correction is forced to reproduce the literal
trace class on the seven-field component of the coupled commutator row. -/
theorem descended_ourTraceOrderCorrection_forces_sevenValue
    (seven : FieldSevenOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient)
    (descended : CoupledIncomingQuotient →ₗ[ℚ]
      FieldEightPhysicalTraceQuotient)
    (hdescended : descended.comp coupledIncomingQuotientMap =
      ourTraceOrderCorrectedCoordinate seven) :
    seven coupledIncomingCommutatorVector.1 =
      literalIncomingCommutatorClass := by
  have hvalue := congrArg
    (fun map : OurCoupledCarrier →ₗ[ℚ] FieldEightPhysicalTraceQuotient =>
      map coupledIncomingCommutatorVector) hdescended
  change descended
      (coupledIncomingQuotientMap coupledIncomingCommutatorVector) =
    seven coupledIncomingCommutatorVector.1 -
      exactFieldEightTraceClassMap coupledIncomingCommutatorVector.2 at hvalue
  rw [coupledIncomingQuotientMap_coupledIncomingCommutatorVector_zero,
    map_zero,
    coupledIncomingCommutatorVector_traceClass] at hvalue
  exact sub_eq_zero.mp hvalue.symm

/-- Consequently a descended trace-order correction requires a genuinely
nonzero seven-field component. -/
theorem descended_ourTraceOrderCorrection_forces_seven_ne_zero
    (seven : FieldSevenOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient)
    (descended : CoupledIncomingQuotient →ₗ[ℚ]
      FieldEightPhysicalTraceQuotient)
    (hdescended : descended.comp coupledIncomingQuotientMap =
      ourTraceOrderCorrectedCoordinate seven) :
    seven ≠ 0 := by
  intro hzero
  have hvalue := descended_ourTraceOrderCorrection_forces_sevenValue
    seven descended hdescended
  rw [hzero] at hvalue
  exact literalIncomingCommutatorClass_ne_zero hvalue.symm

/-- The explicit local seven-field compensator is exactly OUR forced
trace-order correction. -/
theorem ourTraceOrderCorrectedCoordinate_concrete :
    ourTraceOrderCorrectedCoordinate coupledSevenTraceCompensator =
      coupledIncomingTraceDual := rfl

/-- OUR local trace-order-aware coordinate, descended through the coupled
commutator quotient. -/
def ourTraceOrderAwareLocalQuotientCoordinate :
    CoupledIncomingQuotient →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  coupledIncomingQuotientTraceDual

/-- OUR local coordinate is precisely the forced corrected trace coordinate
after quotienting. -/
theorem ourTraceOrderAwareLocalQuotientCoordinate_comp_quotientMap :
    ourTraceOrderAwareLocalQuotientCoordinate.comp coupledIncomingQuotientMap =
      ourTraceOrderCorrectedCoordinate coupledSevenTraceCompensator := by
  change coupledIncomingQuotientTraceDual.comp coupledIncomingQuotientMap =
    ourTraceOrderCorrectedCoordinate coupledSevenTraceCompensator
  rw [coupledIncomingQuotientTraceDual_comp_quotientMap]
  rfl

/-- For either physical relation policy, OUR local coordinate sends the full
covariant-commutator column to zero after its exact two-band projection. -/
theorem ourTraceOrderAwareLocalQuotientCoordinate_physicalCommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourTraceOrderAwareLocalQuotientCoordinate
      (coupledIncomingQuotientMap
        (exactFieldSevenEightProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)))) = 0 := by
  rw [exactFieldSevenEightProjection_ourCommutator_full]
  rw [coupledIncomingQuotientMap_coupledIncomingCommutatorVector_zero]
  exact map_zero _

/-- The same coordinate still detects the isolated eight-field component of
the coupled row, retaining the trace-order information that the Cartan chart
forgets. -/
theorem ourTraceOrderAwareLocalQuotientCoordinate_detects_eightComponent :
    ourTraceOrderAwareLocalQuotientCoordinate
      (coupledIncomingQuotientMap
        (0, coupledIncomingCommutatorVector.2)) =
      -literalIncomingCommutatorClass := by
  have hcomp := congrArg
    (fun map : OurCoupledCarrier →ₗ[ℚ] FieldEightPhysicalTraceQuotient =>
      map (0, coupledIncomingCommutatorVector.2))
    coupledIncomingQuotientTraceDual_comp_quotientMap
  change ourTraceOrderAwareLocalQuotientCoordinate
      (coupledIncomingQuotientMap
        (0, coupledIncomingCommutatorVector.2)) =
      coupledIncomingTraceDual (0, coupledIncomingCommutatorVector.2) at hcomp
  rw [hcomp]
  change coupledSevenTraceCompensator 0 -
      exactFieldEightTraceClassMap coupledIncomingCommutatorVector.2 = _
  rw [map_zero, zero_sub, coupledIncomingCommutatorVector_traceClass]

/-- The retained eight-field trace-order component is nonzero in OUR local
coupled quotient coordinate. -/
theorem ourTraceOrderAwareLocalQuotientCoordinate_detects_eightComponent_ne_zero :
    ourTraceOrderAwareLocalQuotientCoordinate
      (coupledIncomingQuotientMap
        (0, coupledIncomingCommutatorVector.2)) ≠ 0 := by
  rw [ourTraceOrderAwareLocalQuotientCoordinate_detects_eightComponent]
  exact neg_ne_zero.mpr literalIncomingCommutatorClass_ne_zero

/-- OUR actual Cartan Wilson/Symanzik coefficient packet, retained unchanged
as the analytic component of the local repair interface. -/
def ourActualCartanWilsonCoordinatePacket (a : ℝ) : Fin 17 → ℝ :=
  fun coordinate => actualWilsonDimension16SymanzikCoordinate a coordinate

/-- The Cartan component of OUR package is exactly the certified Wilson
eighth-jet coefficient packet. -/
theorem ourActualCartanWilsonCoordinatePacket_eq
    (a : ℝ) (coordinate : Fin 17) :
    ourActualCartanWilsonCoordinatePacket a coordinate =
      if coordinate = 0 then -(a ^ 12) / 20160 else 0 :=
  actualWilsonDimension16SymanzikCoordinate_eq a coordinate

/-- OUR local repair data: the exact Cartan Wilson packet together with a
trace-order-aware quotient coordinate. The two components are intentionally
kept distinct until an analytic noncommutative Wilson-functional construction
relates them on the complete cochain quotient. -/
structure OurLocalWilsonTraceOrderRepairData (a : ℝ) where
  cartanWilsonPacket : Fin 17 → ℝ
  traceOrderCoordinate : CoupledIncomingQuotient →ₗ[ℚ]
    FieldEightPhysicalTraceQuotient

/-- OUR instantiated local repair data. -/
def ourLocalWilsonTraceOrderRepairData (a : ℝ) :
    OurLocalWilsonTraceOrderRepairData a where
  cartanWilsonPacket := ourActualCartanWilsonCoordinatePacket a
  traceOrderCoordinate := ourTraceOrderAwareLocalQuotientCoordinate

/-- The first component of OUR repair data remains the actual Wilson packet. -/
theorem ourLocalWilsonTraceOrderRepairData_cartanWilsonPacket
    (a : ℝ) (coordinate : Fin 17) :
    (ourLocalWilsonTraceOrderRepairData a).cartanWilsonPacket coordinate =
      if coordinate = 0 then -(a ^ 12) / 20160 else 0 :=
  ourActualCartanWilsonCoordinatePacket_eq a coordinate

/-- The second component of OUR repair data retains the certified nonzero
trace-order signal in the local quotient. -/
theorem ourLocalWilsonTraceOrderRepairData_traceOrderSignal_ne_zero
    (a : ℝ) :
    (ourLocalWilsonTraceOrderRepairData a).traceOrderCoordinate
      (coupledIncomingQuotientMap
        (0, coupledIncomingCommutatorVector.2)) ≠ 0 :=
  ourTraceOrderAwareLocalQuotientCoordinate_detects_eightComponent_ne_zero

#print axioms no_ourFieldEightTraceOnlyCoordinate_descent
#print axioms descended_ourTraceOrderCorrection_forces_sevenValue
#print axioms descended_ourTraceOrderCorrection_forces_seven_ne_zero
#print axioms ourTraceOrderAwareLocalQuotientCoordinate_physicalCommutator_zero
#print axioms ourTraceOrderAwareLocalQuotientCoordinate_detects_eightComponent_ne_zero
#print axioms ourLocalWilsonTraceOrderRepairData_cartanWilsonPacket
#print axioms ourLocalWilsonTraceOrderRepairData_traceOrderSignal_ne_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderRepair
