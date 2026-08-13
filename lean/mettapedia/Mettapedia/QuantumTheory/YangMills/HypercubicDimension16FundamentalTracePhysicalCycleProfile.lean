import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalFamily

/-!
# OUR physical three-cut trace-cycle profile bridge

The complete finite three-cut topology certificate has `210` certified
ordered cut labels.  This module carries that finite family through the
actual `F,D`/IBP physical relation operator and into the coordinate-free
signed-`H(4)` relation semantics already used by the repaired Wilson-lattice
programme.

For every certified physical fundamental-trace row, trace rewiring preserves
the field/derivative decoration.  The signed Reynolds weight consequently
factors into a common derivative weight and the trace-cycle profile gate.
An exact finite replay on the actual physical labels proves that the six
signed gates cancel.  Hence the complete finite physical cochain family is
in the kernel of OUR trace-cycle-profile coordinate under both relation
policies.

This proves only the profile-coordinate component of OUR repaired
correction.  It does not claim annihilation by the separate three-coordinate
part, a complete physical relation census, joint rank or conditioning, or
Wilson-functional analytic coordinates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalCycleProfile

open V14HypercubicFDCensus
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16FundamentalTracePhysicalFamily
open HypercubicDimension16FundamentalTraceCycleProfile
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16CovariantCompressionWall
open HypercubicDimension16WilsonTraceOrderInvariantBianchi

/-- OUR labeled realization of a trace rewiring of the fixed physical
seven-field carrier. -/
def physicalRewireLabeled (rewire : Equiv.Perm (Fin 7)) :
    LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (rewireTraceCarrier ourFieldSevenCommutatorCarrier rewire).2)

/-- OUR ordinary seven-field relabel orbit of a physical trace rewiring. -/
abbrev physicalRewireOrbit (rewire : Equiv.Perm (Fin 7)) :
    FieldSevenOrbitCarrier :=
  Quotient.mk _ (physicalRewireLabeled rewire)

/-- OUR exact full-carrier target of a physical trace rewiring. -/
abbrev physicalRewireExactTarget (rewire : Equiv.Perm (Fin 7)) :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, physicalRewireOrbit rewire⟩

/-- OUR labeled unrewired physical seven-field carrier. -/
abbrev physicalBaseLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourFieldSevenCommutatorCarrier.2)

/-- OUR ordinary seven-field relabel orbit of the unrewired carrier. -/
abbrev physicalBaseOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ physicalBaseLabeled

/-- OUR exact full-carrier target of the unrewired carrier. -/
abbrev physicalBaseExactTarget : ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, physicalBaseOrbit⟩

/-- OUR rational five-cycle gate used by the repaired profile coordinate. -/
def physicalTraceCycleProfileGate (trace : Equiv.Perm (Fin 7)) : ℚ :=
  (if trace.cycleType.count 2 = 1 then (6 / 5 : ℚ) else 0) +
    (if trace.cycleType.count 3 = 1 then (13 / 10 : ℚ) else 0) +
      (if trace.cycleType.count 4 = 1 then (-1 : ℚ) else 0) +
        (if trace.cycleType.count 5 = 1 then (-7 / 10 : ℚ) else 0) +
          (if trace.cycleType.count 6 = 1 then (-3 / 5 : ℚ) else 0)

/-- OUR integer indicator for a single cycle of a specified length. -/
def cycleLengthIndicator
    (cycleLength : ℕ) (cycleType : Multiset ℕ) : Int :=
  if cycleType.count cycleLength = 1 then 1 else 0

/-- OUR denominator-cleared profile gate on a cycle multiset. -/
def traceCycleProfileGateNumerator
    (cycleType : Multiset ℕ) : Int :=
  12 * cycleLengthIndicator 2 cycleType +
    13 * cycleLengthIndicator 3 cycleType -
      10 * cycleLengthIndicator 4 cycleType -
        7 * cycleLengthIndicator 5 cycleType -
          6 * cycleLengthIndicator 6 cycleType

/-- OUR denominator-cleared profile gate on a physical trace permutation. -/
def physicalTraceCycleProfileGateNumerator
    (trace : Equiv.Perm (Fin 7)) : Int :=
  traceCycleProfileGateNumerator trace.cycleType

/-- OUR rational gate is the denominator-cleared integer gate divided by ten. -/
theorem physicalTraceCycleProfileGate_eq_numerator
    (trace : Equiv.Perm (Fin 7)) :
    physicalTraceCycleProfileGate trace =
      (physicalTraceCycleProfileGateNumerator trace : ℚ) / 10 := by
  unfold physicalTraceCycleProfileGate physicalTraceCycleProfileGateNumerator
    traceCycleProfileGateNumerator cycleLengthIndicator
  split_ifs <;> norm_num

/-- The six trace-cycle types in OUR actual physical fundamental-trace row. -/
def physicalFundamentalTraceCycleSignature
    (labels : OurCertifiedThreeCutLabel) : List (Multiset ℕ) :=
  [ physicalBaseLabeled.trace.cycleType
  , (physicalRewireLabeled
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).second)).trace.cycleType
  , (physicalRewireLabeled
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).third)).trace.cycleType
  , (physicalRewireLabeled
      (Equiv.swap (ourFundamentalTraceSiteOf labels).second
        (ourFundamentalTraceSiteOf labels).third)).trace.cycleType
  , (physicalRewireLabeled
      (fundamentalCycleForward (ourFundamentalTraceSiteOf labels))).trace.cycleType
  , (physicalRewireLabeled
      (fundamentalCycleBackward (ourFundamentalTraceSiteOf labels))).trace.cycleType ]

/-- OUR labeled trace-cycle signature is definitionally the actual physical
six-rewire signature used by the existing finite topology certificate. -/
theorem physicalFundamentalTraceCycleSignature_eq_actual
    (labels : OurCertifiedThreeCutLabel) :
    physicalFundamentalTraceCycleSignature labels =
      ourActualFundamentalTraceCycleSignature labels := by
  rfl

/-- OUR denominator-cleared alternating six-rewire profile on an actual
certified physical trace row. -/
def physicalFundamentalTraceProfileNumerator
    (labels : OurCertifiedThreeCutLabel) : Int :=
  physicalTraceCycleProfileGateNumerator physicalBaseLabeled.trace -
        physicalTraceCycleProfileGateNumerator
          (physicalRewireLabeled
            (Equiv.swap (ourFundamentalTraceSiteOf labels).first
              (ourFundamentalTraceSiteOf labels).second)).trace -
          physicalTraceCycleProfileGateNumerator
            (physicalRewireLabeled
              (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                (ourFundamentalTraceSiteOf labels).third)).trace -
            physicalTraceCycleProfileGateNumerator
              (physicalRewireLabeled
                (Equiv.swap (ourFundamentalTraceSiteOf labels).second
                  (ourFundamentalTraceSiteOf labels).third)).trace +
              physicalTraceCycleProfileGateNumerator
                (physicalRewireLabeled
                  (fundamentalCycleForward
                    (ourFundamentalTraceSiteOf labels))).trace +
                physicalTraceCycleProfileGateNumerator
                  (physicalRewireLabeled
                    (fundamentalCycleBackward
                      (ourFundamentalTraceSiteOf labels))).trace

/-- OUR rational alternating six-rewire profile on an actual certified
physical trace row. -/
def physicalFundamentalTraceProfileValue
    (labels : OurCertifiedThreeCutLabel) : ℚ :=
  (physicalFundamentalTraceProfileNumerator labels : ℚ) / 10

/-- Kernel replay: all `210` actual certified physical three-cut rows have
zero denominator-cleared profile. -/
theorem physicalFundamentalTraceProfileNumerator_all_zero :
    ∀ labels : OurCertifiedThreeCutLabel,
      physicalFundamentalTraceProfileNumerator labels = 0 := by
  set_option maxRecDepth 100000 in
    decide +kernel

/-- OUR rational physical profile is exactly the alternating six-gate value. -/
theorem physicalFundamentalTraceProfileValue_eq_signedGates
    (labels : OurCertifiedThreeCutLabel) :
    physicalFundamentalTraceProfileValue labels =
      physicalTraceCycleProfileGate physicalBaseLabeled.trace -
        physicalTraceCycleProfileGate
          (physicalRewireLabeled
            (Equiv.swap (ourFundamentalTraceSiteOf labels).first
              (ourFundamentalTraceSiteOf labels).second)).trace -
          physicalTraceCycleProfileGate
            (physicalRewireLabeled
              (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                (ourFundamentalTraceSiteOf labels).third)).trace -
            physicalTraceCycleProfileGate
              (physicalRewireLabeled
                (Equiv.swap (ourFundamentalTraceSiteOf labels).second
                  (ourFundamentalTraceSiteOf labels).third)).trace +
              physicalTraceCycleProfileGate
                (physicalRewireLabeled
                  (fundamentalCycleForward
                    (ourFundamentalTraceSiteOf labels))).trace +
                physicalTraceCycleProfileGate
                  (physicalRewireLabeled
                    (fundamentalCycleBackward
                      (ourFundamentalTraceSiteOf labels))).trace := by
  unfold physicalFundamentalTraceProfileValue
    physicalFundamentalTraceProfileNumerator
  rw [physicalTraceCycleProfileGate_eq_numerator,
    physicalTraceCycleProfileGate_eq_numerator,
    physicalTraceCycleProfileGate_eq_numerator,
    physicalTraceCycleProfileGate_eq_numerator,
    physicalTraceCycleProfileGate_eq_numerator,
    physicalTraceCycleProfileGate_eq_numerator]
  push_cast
  ring

/-- Consequently OUR rational profile vanishes on every certified physical
three-cut label. -/
theorem physicalFundamentalTraceProfileValue_zero
    (labels : OurCertifiedThreeCutLabel) :
    physicalFundamentalTraceProfileValue labels = 0 := by
  unfold physicalFundamentalTraceProfileValue
  rw [physicalFundamentalTraceProfileNumerator_all_zero labels]
  norm_num

/-- Trace rewiring in OUR realization changes only the trace and leaves the
signed derivative decoration untouched. -/
theorem physicalRewire_profileMultiplicity
    (rewire : Equiv.Perm (Fin 7)) (h : Hypercubic4) :
    ourTraceCycleProfileAxisMultiplicity
      ((physicalRewireLabeled rewire).hypercubicAct h) =
      physicalTraceCycleProfileGate (physicalRewireLabeled rewire).trace *
        (derivativeAxisWordMultiplicity [0, 2]
          (physicalBaseLabeled.hypercubicAct h) : ℚ) := by
  rfl

/-- The signed Reynolds weight of an OUR trace rewire factors through its
trace-cycle profile gate. -/
theorem physicalRewire_profileSignedWeight
    (rewire : Equiv.Perm (Fin 7)) :
    (∑ h : Hypercubic4,
      (physicalRewireLabeled rewire).tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          ((physicalRewireLabeled rewire).hypercubicAct h)) =
      physicalTraceCycleProfileGate (physicalRewireLabeled rewire).trace * 32 := by
  rw [show (∑ h : Hypercubic4,
      (physicalRewireLabeled rewire).tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          ((physicalRewireLabeled rewire).hypercubicAct h)) =
      physicalTraceCycleProfileGate (physicalRewireLabeled rewire).trace *
        (∑ h : Hypercubic4,
          physicalBaseLabeled.tensorSign h *
            (derivativeAxisWordMultiplicity [0, 2]
              (physicalBaseLabeled.hypercubicAct h) : ℚ)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        rw [show (physicalRewireLabeled rewire).tensorSign h =
            physicalBaseLabeled.tensorSign h by rfl,
          physicalRewire_profileMultiplicity rewire h]
        ring,
    source_signedAxisWeight]

/-- The same factorization holds for OUR unrewired base term. -/
theorem physicalBase_profileSignedWeight :
    (∑ h : Hypercubic4,
      physicalBaseLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (physicalBaseLabeled.hypercubicAct h)) =
      physicalTraceCycleProfileGate physicalBaseLabeled.trace * 32 := by
  rw [show (∑ h : Hypercubic4,
      physicalBaseLabeled.tensorSign h *
        ourTraceCycleProfileAxisMultiplicity
          (physicalBaseLabeled.hypercubicAct h)) =
      physicalTraceCycleProfileGate physicalBaseLabeled.trace *
        (∑ h : Hypercubic4,
          physicalBaseLabeled.tensorSign h *
            (derivativeAxisWordMultiplicity [0, 2]
              (physicalBaseLabeled.hypercubicAct h) : ℚ)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        rw [show ourTraceCycleProfileAxisMultiplicity
            (physicalBaseLabeled.hypercubicAct h) =
              physicalTraceCycleProfileGate physicalBaseLabeled.trace *
                (derivativeAxisWordMultiplicity [0, 2]
                  (physicalBaseLabeled.hypercubicAct h) : ℚ) by rfl]
        ring,
    source_signedAxisWeight]

/-- OUR raw trace-cycle coordinate on a Reynolds-averaged rewire. -/
theorem physicalRewire_profileCoordinate
    (rewire : Equiv.Perm (Fin 7)) :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (physicalRewireOrbit rewire) (1 : ℚ))) =
      physicalTraceCycleProfileGate (physicalRewireLabeled rewire).trace / 12 := by
  set_option maxRecDepth 100000 in
    change ourTraceCycleProfileAxisCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single
            (Quotient.mk _ (physicalRewireLabeled rewire) : FieldSevenOrbitCarrier)
            (1 : ℚ))) = _
    rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
      (physicalRewireLabeled rewire)
      (physicalTraceCycleProfileGate (physicalRewireLabeled rewire).trace * 32)
      (physicalRewire_profileSignedWeight rewire)]
    ring

/-- OUR raw trace-cycle coordinate on the Reynolds-averaged base term. -/
theorem physicalBase_profileCoordinate :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single physicalBaseOrbit (1 : ℚ))) =
      physicalTraceCycleProfileGate physicalBaseLabeled.trace / 12 := by
  set_option maxRecDepth 100000 in
    change ourTraceCycleProfileAxisCoordinate
        (sectorFieldOrbitReynolds 7 2
          (Finsupp.single
            (Quotient.mk _ physicalBaseLabeled : FieldSevenOrbitCarrier)
            (1 : ℚ))) = _
    rw [ourTraceCycleProfileAxisCoordinate_reynolds_single
      physicalBaseLabeled
      (physicalTraceCycleProfileGate physicalBaseLabeled.trace * 32)
      physicalBase_profileSignedWeight]
    ring

/-- OUR actual physical fundamental-trace row is the six sparse rewires after
contextual normalization and exact field relabeling. -/
theorem physicalRowFormula
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1) =
      Finsupp.single physicalBaseExactTarget 1 -
        Finsupp.single
          (physicalRewireExactTarget
            (Equiv.swap (ourFundamentalTraceSiteOf labels).first
              (ourFundamentalTraceSiteOf labels).second)) 1 -
          Finsupp.single
            (physicalRewireExactTarget
              (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                (ourFundamentalTraceSiteOf labels).third)) 1 -
            Finsupp.single
              (physicalRewireExactTarget
                (Equiv.swap (ourFundamentalTraceSiteOf labels).second
                  (ourFundamentalTraceSiteOf labels).third)) 1 +
              Finsupp.single
                (physicalRewireExactTarget
                  (fundamentalCycleForward (ourFundamentalTraceSiteOf labels))) 1 +
                Finsupp.single
                  (physicalRewireExactTarget
                    (fundamentalCycleBackward
                      (ourFundamentalTraceSiteOf labels))) 1 := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, ourFundamentalTraceGeneratorAt, physicalRelationRow,
    fundamentalTraceRow, map_sub, map_add]
  rw [normalizeExactContextual_single, normalizeExactContextual_single,
    normalizeExactContextual_single, normalizeExactContextual_single,
    normalizeExactContextual_single, normalizeExactContextual_single]
  simp only [one_smul]
  rw [show normalizeExactFieldRelabel
      (normalizeExactContextualBasis ourFieldSevenCommutatorCarrier) =
      Finsupp.single physicalBaseExactTarget 1 by
        rw [normalizeExactContextualBasis_fieldRelabel]
        change Finsupp.single physicalBaseExactTarget
            (fieldAxisOrientationCoefficient
              (sectorFieldAxisAssignment ourFieldSevenCommutatorCarrier.2)) =
          Finsupp.single physicalBaseExactTarget 1
        congr 1
        decide +kernel,
    show normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap (ourFundamentalTraceSiteOf labels).first
            (ourFundamentalTraceSiteOf labels).second))) =
      Finsupp.single
        (physicalRewireExactTarget
          (Equiv.swap (ourFundamentalTraceSiteOf labels).first
            (ourFundamentalTraceSiteOf labels).second)) 1 by
        rw [normalizeExactContextualBasis_fieldRelabel]
        change Finsupp.single
            (physicalRewireExactTarget
              (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                (ourFundamentalTraceSiteOf labels).second))
            (fieldAxisOrientationCoefficient
              (sectorFieldAxisAssignment
                (rewireTraceCarrier ourFieldSevenCommutatorCarrier
                  (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                    (ourFundamentalTraceSiteOf labels).second)).2)) =
          Finsupp.single
            (physicalRewireExactTarget
              (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                (ourFundamentalTraceSiteOf labels).second)) 1
        congr 1
        change fieldAxisOrientationCoefficient
            (sectorFieldAxisAssignment ourFieldSevenCommutatorCarrier.2) = 1
        decide +kernel,
    show normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap (ourFundamentalTraceSiteOf labels).first
            (ourFundamentalTraceSiteOf labels).third))) =
      Finsupp.single
        (physicalRewireExactTarget
          (Equiv.swap (ourFundamentalTraceSiteOf labels).first
            (ourFundamentalTraceSiteOf labels).third)) 1 by
        rw [normalizeExactContextualBasis_fieldRelabel]
        change Finsupp.single
            (physicalRewireExactTarget
              (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                (ourFundamentalTraceSiteOf labels).third))
            (fieldAxisOrientationCoefficient
              (sectorFieldAxisAssignment
                (rewireTraceCarrier ourFieldSevenCommutatorCarrier
                  (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                    (ourFundamentalTraceSiteOf labels).third)).2)) =
          Finsupp.single
            (physicalRewireExactTarget
              (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                (ourFundamentalTraceSiteOf labels).third)) 1
        congr 1
        change fieldAxisOrientationCoefficient
            (sectorFieldAxisAssignment ourFieldSevenCommutatorCarrier.2) = 1
        decide +kernel,
    show normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap (ourFundamentalTraceSiteOf labels).second
            (ourFundamentalTraceSiteOf labels).third))) =
      Finsupp.single
        (physicalRewireExactTarget
          (Equiv.swap (ourFundamentalTraceSiteOf labels).second
            (ourFundamentalTraceSiteOf labels).third)) 1 by
        rw [normalizeExactContextualBasis_fieldRelabel]
        change Finsupp.single
            (physicalRewireExactTarget
              (Equiv.swap (ourFundamentalTraceSiteOf labels).second
                (ourFundamentalTraceSiteOf labels).third))
            (fieldAxisOrientationCoefficient
              (sectorFieldAxisAssignment
                (rewireTraceCarrier ourFieldSevenCommutatorCarrier
                  (Equiv.swap (ourFundamentalTraceSiteOf labels).second
                    (ourFundamentalTraceSiteOf labels).third)).2)) =
          Finsupp.single
            (physicalRewireExactTarget
              (Equiv.swap (ourFundamentalTraceSiteOf labels).second
                (ourFundamentalTraceSiteOf labels).third)) 1
        congr 1
        change fieldAxisOrientationCoefficient
            (sectorFieldAxisAssignment ourFieldSevenCommutatorCarrier.2) = 1
        decide +kernel,
    show normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (fundamentalCycleForward (ourFundamentalTraceSiteOf labels)))) =
      Finsupp.single
        (physicalRewireExactTarget
          (fundamentalCycleForward (ourFundamentalTraceSiteOf labels))) 1 by
        rw [normalizeExactContextualBasis_fieldRelabel]
        change Finsupp.single
            (physicalRewireExactTarget
              (fundamentalCycleForward (ourFundamentalTraceSiteOf labels)))
            (fieldAxisOrientationCoefficient
              (sectorFieldAxisAssignment
                (rewireTraceCarrier ourFieldSevenCommutatorCarrier
                  (fundamentalCycleForward
                    (ourFundamentalTraceSiteOf labels))).2)) =
          Finsupp.single
            (physicalRewireExactTarget
              (fundamentalCycleForward (ourFundamentalTraceSiteOf labels))) 1
        congr 1
        change fieldAxisOrientationCoefficient
            (sectorFieldAxisAssignment ourFieldSevenCommutatorCarrier.2) = 1
        decide +kernel,
    show normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (fundamentalCycleBackward (ourFundamentalTraceSiteOf labels)))) =
      Finsupp.single
        (physicalRewireExactTarget
          (fundamentalCycleBackward (ourFundamentalTraceSiteOf labels))) 1 by
        rw [normalizeExactContextualBasis_fieldRelabel]
        change Finsupp.single
            (physicalRewireExactTarget
              (fundamentalCycleBackward (ourFundamentalTraceSiteOf labels)))
            (fieldAxisOrientationCoefficient
              (sectorFieldAxisAssignment
                (rewireTraceCarrier ourFieldSevenCommutatorCarrier
                  (fundamentalCycleBackward
                    (ourFundamentalTraceSiteOf labels))).2)) =
          Finsupp.single
            (physicalRewireExactTarget
              (fundamentalCycleBackward (ourFundamentalTraceSiteOf labels))) 1
        congr 1
        change fieldAxisOrientationCoefficient
            (sectorFieldAxisAssignment ourFieldSevenCommutatorCarrier.2) = 1
        decide +kernel]

/-- The seven-field component of OUR physical row retains exactly its six
trace-rewire orbit terms. -/
theorem physicalRowFieldSevenFormula
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)) =
      Finsupp.single physicalBaseOrbit 1 -
        Finsupp.single
          (physicalRewireOrbit
            (Equiv.swap (ourFundamentalTraceSiteOf labels).first
              (ourFundamentalTraceSiteOf labels).second)) 1 -
          Finsupp.single
            (physicalRewireOrbit
              (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                (ourFundamentalTraceSiteOf labels).third)) 1 -
            Finsupp.single
              (physicalRewireOrbit
                (Equiv.swap (ourFundamentalTraceSiteOf labels).second
                  (ourFundamentalTraceSiteOf labels).third)) 1 +
              Finsupp.single
                (physicalRewireOrbit
                  (fundamentalCycleForward (ourFundamentalTraceSiteOf labels))) 1 +
                Finsupp.single
                  (physicalRewireOrbit
                    (fundamentalCycleBackward
                      (ourFundamentalTraceSiteOf labels))) 1 := by
  rw [physicalRowFormula]
  simp only [LinearMap.map_sub, LinearMap.map_add,
    exactFieldSevenProjection_sevenTarget_single]

/-- The raw profile coordinate of an OUR physical row is its finite
trace-topology profile, divided by the Reynolds normalization factor. -/
theorem physicalFundamentalTrace_profileCoordinate
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (exactFieldSevenProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)))) =
      physicalFundamentalTraceProfileValue labels / 12 := by
  rw [physicalRowFieldSevenFormula]
  simp only [LinearMap.map_sub, LinearMap.map_add]
  rw [physicalBase_profileCoordinate,
    physicalRewire_profileCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).second),
    physicalRewire_profileCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).first
        (ourFundamentalTraceSiteOf labels).third),
    physicalRewire_profileCoordinate
      (Equiv.swap (ourFundamentalTraceSiteOf labels).second
        (ourFundamentalTraceSiteOf labels).third),
    physicalRewire_profileCoordinate
      (fundamentalCycleForward (ourFundamentalTraceSiteOf labels)),
    physicalRewire_profileCoordinate
      (fundamentalCycleBackward (ourFundamentalTraceSiteOf labels))]
  calc
    _ = (physicalTraceCycleProfileGate physicalBaseLabeled.trace -
          physicalTraceCycleProfileGate
            (physicalRewireLabeled
              (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                (ourFundamentalTraceSiteOf labels).second)).trace -
            physicalTraceCycleProfileGate
              (physicalRewireLabeled
                (Equiv.swap (ourFundamentalTraceSiteOf labels).first
                  (ourFundamentalTraceSiteOf labels).third)).trace -
              physicalTraceCycleProfileGate
                (physicalRewireLabeled
                  (Equiv.swap (ourFundamentalTraceSiteOf labels).second
                    (ourFundamentalTraceSiteOf labels).third)).trace +
                physicalTraceCycleProfileGate
                  (physicalRewireLabeled
                    (fundamentalCycleForward
                      (ourFundamentalTraceSiteOf labels))).trace +
                  physicalTraceCycleProfileGate
                    (physicalRewireLabeled
                      (fundamentalCycleBackward
                        (ourFundamentalTraceSiteOf labels))).trace) / 12 := by
      ring
    _ = physicalFundamentalTraceProfileValue labels / 12 := by
      rw [← physicalFundamentalTraceProfileValue_eq_signedGates labels]

/-- Thus the raw profile coordinate annihilates every actual certified
physical fundamental-trace row under either policy. -/
theorem physicalFundamentalTrace_profileCoordinate_zero
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (exactFieldSevenProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)))) = 0 := by
  rw [physicalFundamentalTrace_profileCoordinate,
    physicalFundamentalTraceProfileValue_zero]
  norm_num

/-- OUR signed-`H(4)` invariant profile coordinate annihilates every actual
certified physical fundamental-trace row under either policy. -/
theorem ourInvariantTraceCycleProfileCoordinate_physicalFundamentalTrace_zero
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourInvariantTraceCycleProfileCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFundamentalTraceGeneratorAt policy labels) 1)) = 0 := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    physicalFundamentalTrace_profileCoordinate_zero]
  norm_num

/-- The coordinate-free joint semantic image of each basis label is in the
kernel of OUR invariant profile coordinate. -/
theorem ourInvariantTraceCycleProfileCoordinate_fundamentalTraceSingle_zero
    (policy : PhysicalRelationPolicy) (labels : OurCertifiedThreeCutLabel) :
    ourInvariantTraceCycleProfileCoordinate
      ((ourFundamentalTraceToJointRelation policy
        (Finsupp.single labels 1)).1).1 = 0 := by
  rw [ourFundamentalTraceToJointRelation_single_val,
    ourInvariantTraceCycleProfileCoordinate_exactFieldOrbitReynolds,
    ourInvariantTraceCycleProfileCoordinate_physicalFundamentalTrace_zero]

/-- The complete finite physical three-cut cochain family maps into the
kernel of OUR invariant trace-cycle-profile coordinate. -/
theorem ourInvariantTraceCycleProfileCoordinate_fundamentalTrace_zero
    (policy : PhysicalRelationPolicy)
    (cochain : OurFundamentalTraceCochainSpace) :
    ourInvariantTraceCycleProfileCoordinate
      ((ourFundamentalTraceToJointRelation policy cochain).1).1 = 0 := by
  let combined := ourInvariantTraceCycleProfileCoordinate.comp
    (exactFieldOrbitInvariantSubmodule.subtype.comp
      ((jointInvariantRelationSubmodule policy).subtype.comp
        (ourFundamentalTraceToJointRelation policy)))
  set_option maxRecDepth 100000 in
    change combined cochain = 0
    induction cochain using Finsupp.induction_linear with
    | zero => simp [combined]
    | add left right hleft hright => simp [map_add, hleft, hright]
    | single labels coefficient =>
        rw [show Finsupp.single labels coefficient =
            coefficient • Finsupp.single labels 1 by simp]
        simp only [map_smul]
        change coefficient •
          (ourInvariantTraceCycleProfileCoordinate
            ((ourFundamentalTraceToJointRelation policy
              (Finsupp.single labels 1)).1).1) = 0
        rw [ourInvariantTraceCycleProfileCoordinate_fundamentalTraceSingle_zero]
        simp

#print axioms physicalFundamentalTraceProfileNumerator_all_zero
#print axioms physicalFundamentalTraceProfileValue_zero
#print axioms physicalRewire_profileSignedWeight
#print axioms physicalRowFormula
#print axioms physicalFundamentalTrace_profileCoordinate_zero
#print axioms ourInvariantTraceCycleProfileCoordinate_physicalFundamentalTrace_zero
#print axioms ourInvariantTraceCycleProfileCoordinate_fundamentalTrace_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalCycleProfile
