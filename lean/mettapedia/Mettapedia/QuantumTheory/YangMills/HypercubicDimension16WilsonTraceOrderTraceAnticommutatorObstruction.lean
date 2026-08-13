import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair

/-!
# OUR trace-anticommutator test of the finite trace-order repair

The three-coordinate signed-hypercubic correction has been checked on a
concrete commutator, two integration-by-parts rows, Bianchi rows, EOM rows,
and derivative-free eight-field trace rows.  This module tests the next
canonical relation family: the polarized `SU(2)` trace-anticommutator row on
the same seven-field decorated carrier as the commutator calibration.

The three terms have identical field and derivative decorations but distinct
trace wiring.  It is therefore a sharp finite test of whether the current
coordinate packet is trace-sensitive enough to descend through this relation.
The result below is OUR local obstruction certificate; it does not claim a
complete relation census or rule out a further trace-sensitive repair.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction

open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open SU2LatticeFDCensusNoGo
open HypercubicRawFDDimension16Census
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair

/-- OUR adjacent pair in the seven-field commutator carrier's trace cycle. -/
abbrev ourFieldSevenTraceAnticommutatorSite :
    TraceAnticommutatorSite ourFieldSevenCommutatorCarrier where
  left := ⟨0, by decide⟩
  cycleLength_ge_three := by decide

/-- OUR genuine trace-anticommutator generator, available under either
physical relation policy. -/
def ourFieldSevenTraceAnticommutatorGenerator
    (policy : PhysicalRelationPolicy) : PhysicalRelationGenerator policy :=
  .traceAnticommutator ourFieldSevenCommutatorCarrier
    ourFieldSevenTraceAnticommutatorSite

/-- OUR labeled source term of the trace-anticommutator row. -/
abbrev ourTraceAnticommutatorBaseLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourFieldSevenCommutatorCarrier.2)

/-- OUR labeled adjacent-swap term of the trace-anticommutator row. -/
abbrev ourTraceAnticommutatorSwapLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (swapAdjacentTraceCarrier ourFieldSevenTraceAnticommutatorSite).2)

/-- OUR labeled split-trace term of the trace-anticommutator row. -/
abbrev ourTraceAnticommutatorSplitLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (splitAdjacentTraceCarrier ourFieldSevenTraceAnticommutatorSite).2)

/-- The base term is the existing commutator calibration source. -/
theorem ourTraceAnticommutatorBaseLabeled_eq_source :
    ourTraceAnticommutatorBaseLabeled = sourceLabeled := rfl

/- The following finite sums are deliberately stated term by term.  They
certify that the three existing decoration coordinates cannot distinguish the
three trace wirings on this carrier. -/
set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorBase_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorBaseLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ)) = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSwap_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSwapLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ)) = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSplit_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSplitLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ)) = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorBase_oldPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorBaseLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSwap_oldPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSwapLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSplit_oldPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSplitLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorBase_thirdPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorBaseLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSwap_thirdPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSwapLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSplit_thirdPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSplitLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

/-- OUR ordinary relabel orbit of the source term. -/
abbrev ourTraceAnticommutatorBaseOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourTraceAnticommutatorBaseLabeled

/-- OUR ordinary relabel orbit of the adjacent-swap term. -/
abbrev ourTraceAnticommutatorSwapOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourTraceAnticommutatorSwapLabeled

/-- OUR ordinary relabel orbit of the split-trace term. -/
abbrev ourTraceAnticommutatorSplitOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourTraceAnticommutatorSplitLabeled

/-- OUR exact full-carrier target of the source term. -/
abbrev ourTraceAnticommutatorBaseExactTarget :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourTraceAnticommutatorBaseOrbit⟩

/-- OUR exact full-carrier target of the adjacent-swap term. -/
abbrev ourTraceAnticommutatorSwapExactTarget :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourTraceAnticommutatorSwapOrbit⟩

/-- OUR exact full-carrier target of the split-trace term. -/
abbrev ourTraceAnticommutatorSplitExactTarget :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourTraceAnticommutatorSplitOrbit⟩

/-- Exact ordinary-orbit identification of the source term. -/
theorem exactFieldRelabelOrbitOfOriented_ourTraceAnticommutatorBase :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData ourFieldSevenCommutatorCarrier) =
      ourTraceAnticommutatorBaseExactTarget := by
  rfl

/-- Exact ordinary-orbit identification of the adjacent-swap term. -/
theorem exactFieldRelabelOrbitOfOriented_ourTraceAnticommutatorSwap :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData
        (swapAdjacentTraceCarrier ourFieldSevenTraceAnticommutatorSite)) =
      ourTraceAnticommutatorSwapExactTarget := by
  rfl

/-- Exact ordinary-orbit identification of the split-trace term. -/
theorem exactFieldRelabelOrbitOfOriented_ourTraceAnticommutatorSplit :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData
        (splitAdjacentTraceCarrier ourFieldSevenTraceAnticommutatorSite)) =
      ourTraceAnticommutatorSplitExactTarget := by
  rfl

/- The orientations are finite computations.  Trace rewiring leaves their
field/derivative contribution unchanged, but each equality is replayed
directly by the kernel. -/
set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorBase_orientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment ourFieldSevenCommutatorCarrier.2) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSwap_orientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (swapAdjacentTraceCarrier ourFieldSevenTraceAnticommutatorSite).2) =
      1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSplit_orientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (splitAdjacentTraceCarrier ourFieldSevenTraceAnticommutatorSite).2) =
      1 := by
  decide +kernel

/-- Exact normalization of OUR source trace term. -/
theorem ourNormalizeExactContextualBasis_ourTraceAnticommutatorBase :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis ourFieldSevenCommutatorCarrier) =
      Finsupp.single ourTraceAnticommutatorBaseExactTarget 1 := by
  rw [our_normalizeExactContextualBasis_fieldRelabel,
    exactFieldRelabelOrbitOfOriented_ourTraceAnticommutatorBase,
    ourTraceAnticommutatorBase_orientationCoefficient]

/-- Exact normalization of OUR adjacent-swap trace term. -/
theorem ourNormalizeExactContextualBasis_ourTraceAnticommutatorSwap :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (swapAdjacentTraceCarrier ourFieldSevenTraceAnticommutatorSite)) =
      Finsupp.single ourTraceAnticommutatorSwapExactTarget 1 := by
  rw [our_normalizeExactContextualBasis_fieldRelabel,
    exactFieldRelabelOrbitOfOriented_ourTraceAnticommutatorSwap,
    ourTraceAnticommutatorSwap_orientationCoefficient]

/-- Exact normalization of OUR split-trace term. -/
theorem ourNormalizeExactContextualBasis_ourTraceAnticommutatorSplit :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (splitAdjacentTraceCarrier ourFieldSevenTraceAnticommutatorSite)) =
      Finsupp.single ourTraceAnticommutatorSplitExactTarget 1 := by
  rw [our_normalizeExactContextualBasis_fieldRelabel,
    exactFieldRelabelOrbitOfOriented_ourTraceAnticommutatorSplit,
    ourTraceAnticommutatorSplit_orientationCoefficient]

/-- The physical orbit operator sends OUR trace-anticommutator generator to
its exact three-term normalized row. -/
theorem orbitPhysicalRelationOperator_ourTraceAnticommutator
    (policy : PhysicalRelationPolicy) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1) =
      Finsupp.single ourTraceAnticommutatorBaseExactTarget 1 +
        Finsupp.single ourTraceAnticommutatorSwapExactTarget 1 -
          Finsupp.single ourTraceAnticommutatorSplitExactTarget 1 := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, ourFieldSevenTraceAnticommutatorGenerator,
    physicalRelationRow, traceAnticommutatorRow, map_sub, map_add]
  rw [normalizeExactContextual_single, normalizeExactContextual_single,
    normalizeExactContextual_single]
  simp only [one_smul]
  rw [ourNormalizeExactContextualBasis_ourTraceAnticommutatorBase,
    ourNormalizeExactContextualBasis_ourTraceAnticommutatorSwap,
    ourNormalizeExactContextualBasis_ourTraceAnticommutatorSplit]

/-- The seven-field projection of OUR trace-anticommutator row is its three
ordinary trace-wiring orbits. -/
theorem exactFieldSevenProjection_ourTraceAnticommutator
    (policy : PhysicalRelationPolicy) :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      Finsupp.single ourTraceAnticommutatorBaseOrbit 1 +
        Finsupp.single ourTraceAnticommutatorSwapOrbit 1 -
          Finsupp.single ourTraceAnticommutatorSplitOrbit 1 := by
  rw [orbitPhysicalRelationOperator_ourTraceAnticommutator, LinearMap.map_sub,
    LinearMap.map_add,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_sevenTarget_single,
    exactFieldSevenProjection_sevenTarget_single]

/-- The eight-field projection of OUR all-seven-field trace row vanishes. -/
theorem exactFieldEightProjection_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    exactFieldEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  rw [orbitPhysicalRelationOperator_ourTraceAnticommutator, LinearMap.map_sub,
    LinearMap.map_add,
    exactFieldEightProjection_sevenTarget_single,
    exactFieldEightProjection_sevenTarget_single,
    exactFieldEightProjection_sevenTarget_single]
  simp

/-- The first raw coordinate follows the source trace wiring under signed
hypercubic action. -/
theorem derivativeAxisOrbitMultiplicity_ourTraceAnticommutatorBase_action
    (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (ourTraceAnticommutatorBaseOrbit.hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourTraceAnticommutatorBaseOrbit]

/-- The first raw coordinate follows the adjacent-swap trace wiring under
signed hypercubic action. -/
theorem derivativeAxisOrbitMultiplicity_ourTraceAnticommutatorSwap_action
    (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (ourTraceAnticommutatorSwapOrbit.hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourTraceAnticommutatorSwapOrbit]

/-- The first raw coordinate follows the split trace wiring under signed
hypercubic action. -/
theorem derivativeAxisOrbitMultiplicity_ourTraceAnticommutatorSplit_action
    (h : Hypercubic4) :
    derivativeAxisOrbitMultiplicity [0, 2]
      (ourTraceAnticommutatorSplitOrbit.hypercubicAct h) =
      (derivativeAxisWordMultiplicity [0, 2]
        (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ) := by
  simp [derivativeAxisOrbitMultiplicity, ourTraceAnticommutatorSplitOrbit]

/-- The first raw coordinate has Reynolds value `1 / 12` on the source
trace wiring. -/
theorem derivativeAxisCoordinate_reynolds_ourTraceAnticommutatorBase :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ))) = 1 / 12 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ))) =
        ourTraceAnticommutatorBaseLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourTraceAnticommutatorBase_action]
    simp [ourTraceAnticommutatorBaseOrbit]
  simp_rw [hterm]
  rw [ourTraceAnticommutatorBase_signedAxisWeight]
  norm_num

/-- The first raw coordinate has the same Reynolds value on the
adjacent-swap trace wiring. -/
theorem derivativeAxisCoordinate_reynolds_ourTraceAnticommutatorSwap :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ))) = 1 / 12 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ))) =
        ourTraceAnticommutatorSwapLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourTraceAnticommutatorSwap_action]
    simp [ourTraceAnticommutatorSwapOrbit]
  simp_rw [hterm]
  rw [ourTraceAnticommutatorSwap_signedAxisWeight]
  norm_num

/-- The first raw coordinate has the same Reynolds value on the split trace
wiring. -/
theorem derivativeAxisCoordinate_reynolds_ourTraceAnticommutatorSplit :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) = 1 / 12 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) =
        ourTraceAnticommutatorSplitLabeled.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2]
            (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single,
      derivativeAxisOrbitMultiplicity_ourTraceAnticommutatorSplit_action]
    simp [ourTraceAnticommutatorSplitOrbit]
  simp_rw [hterm]
  rw [ourTraceAnticommutatorSplit_signedAxisWeight]
  norm_num

/-- The first invariant coordinate takes OUR trace-anticommutator row to
`1 / 2`: it sees the common decoration but not the trace rewiring. -/
theorem ourInvariantSevenAxisCoordinate_ourTraceAnticommutator
    (policy : PhysicalRelationPolicy) :
    ourInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      1 / 2 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourTraceAnticommutator]
  simp only [LinearMap.map_sub, LinearMap.map_add,
    derivativeAxisCoordinate_reynolds_ourTraceAnticommutatorBase,
    derivativeAxisCoordinate_reynolds_ourTraceAnticommutatorSwap,
    derivativeAxisCoordinate_reynolds_ourTraceAnticommutatorSplit]
  norm_num

/-- The second raw coordinate follows the source trace wiring under signed
hypercubic action. -/
theorem ourIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorBase_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (ourTraceAnticommutatorBaseOrbit.hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity,
    ourTraceAnticommutatorBaseOrbit]

/-- The second raw coordinate follows the adjacent-swap trace wiring under
signed hypercubic action. -/
theorem ourIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorSwap_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (ourTraceAnticommutatorSwapOrbit.hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity,
    ourTraceAnticommutatorSwapOrbit]

/-- The second raw coordinate follows the split trace wiring under signed
hypercubic action. -/
theorem ourIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorSplit_action
    (h : Hypercubic4) :
    ourIBPAxisPlanePairOrbitMultiplicity
      (ourTraceAnticommutatorSplitOrbit.hypercubicAct h) =
      (ourIBPAxisPlanePairMultiplicity
        (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ) := by
  simp [ourIBPAxisPlanePairOrbitMultiplicity,
    ourTraceAnticommutatorSplitOrbit]

/-- The second raw coordinate vanishes after Reynolds averaging the source
trace wiring. -/
theorem ourIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorBase :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ))) =
        ourTraceAnticommutatorBaseLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorBase_action]
    simp [ourTraceAnticommutatorBaseOrbit]
  simp_rw [hterm]
  rw [ourTraceAnticommutatorBase_oldPlanePairSignedWeight]
  norm_num

/-- The second raw coordinate vanishes after Reynolds averaging the
adjacent-swap trace wiring. -/
theorem ourIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorSwap :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ))) =
        ourTraceAnticommutatorSwapLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorSwap_action]
    simp [ourTraceAnticommutatorSwapOrbit]
  simp_rw [hterm]
  rw [ourTraceAnticommutatorSwap_oldPlanePairSignedWeight]
  norm_num

/-- The second raw coordinate vanishes after Reynolds averaging the split
trace wiring. -/
theorem ourIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorSplit :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) =
        ourTraceAnticommutatorSplitLabeled.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity
            (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single,
      ourIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorSplit_action]
    simp [ourTraceAnticommutatorSplitOrbit]
  simp_rw [hterm]
  rw [ourTraceAnticommutatorSplit_oldPlanePairSignedWeight]
  norm_num

/-- The second invariant coordinate vanishes on OUR trace-anticommutator
row. -/
theorem ourInvariantIBPAxisCoordinate_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourTraceAnticommutator]
  simp only [LinearMap.map_sub, LinearMap.map_add,
    ourIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorBase,
    ourIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorSwap,
    ourIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorSplit]
  norm_num

/-- The third raw coordinate follows the source trace wiring under signed
hypercubic action. -/
theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorBase_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourTraceAnticommutatorBaseOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity,
    ourTraceAnticommutatorBaseOrbit]

/-- The third raw coordinate follows the adjacent-swap trace wiring under
signed hypercubic action. -/
theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorSwap_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourTraceAnticommutatorSwapOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity,
    ourTraceAnticommutatorSwapOrbit]

/-- The third raw coordinate follows the split trace wiring under signed
hypercubic action. -/
theorem ourThirdIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorSplit_action
    (h : Hypercubic4) :
    ourThirdIBPAxisPlanePairOrbitMultiplicity
      (ourTraceAnticommutatorSplitOrbit.hypercubicAct h) =
      (ourThirdIBPAxisPlanePairMultiplicity
        (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ) := by
  simp [ourThirdIBPAxisPlanePairOrbitMultiplicity,
    ourTraceAnticommutatorSplitOrbit]

/-- The third raw coordinate vanishes after Reynolds averaging the source
trace wiring. -/
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorBase :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ))) =
        ourTraceAnticommutatorBaseLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorBase_action]
    simp [ourTraceAnticommutatorBaseOrbit]
  simp_rw [hterm]
  rw [ourTraceAnticommutatorBase_thirdPlanePairSignedWeight]
  norm_num

/-- The third raw coordinate vanishes after Reynolds averaging the
adjacent-swap trace wiring. -/
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorSwap :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ))) =
        ourTraceAnticommutatorSwapLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorSwap_action]
    simp [ourTraceAnticommutatorSwapOrbit]
  simp_rw [hterm]
  rw [ourTraceAnticommutatorSwap_thirdPlanePairSignedWeight]
  norm_num

/-- The third raw coordinate vanishes after Reynolds averaging the split
trace wiring. -/
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorSplit :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) = 0 := by
  unfold sectorFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) =
        ourTraceAnticommutatorSplitLabeled.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity
            (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single,
      ourThirdIBPAxisPlanePairOrbitMultiplicity_ourTraceAnticommutatorSplit_action]
    simp [ourTraceAnticommutatorSplitOrbit]
  simp_rw [hterm]
  rw [ourTraceAnticommutatorSplit_thirdPlanePairSignedWeight]
  norm_num

/-- The third invariant coordinate vanishes on OUR trace-anticommutator
row. -/
theorem ourInvariantThirdIBPAxisCoordinate_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourTraceAnticommutator]
  simp only [LinearMap.map_sub, LinearMap.map_add,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorBase,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorSwap,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourTraceAnticommutatorSplit]
  norm_num

/-- The two-coordinate seven-field scalar retains the residual `1 / 2` on
OUR trace-anticommutator row. -/
theorem ourTwoCoordinateInvariantSevenAxisCoordinate_ourTraceAnticommutator
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      1 / 2 := by
  unfold ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_ourTraceAnticommutator,
    ourInvariantIBPAxisCoordinate_ourTraceAnticommutator_zero]
  norm_num

/-- The canonical eight-field trace coordinate vanishes on OUR entirely
seven-field trace-anticommutator row. -/
theorem exactFieldEightTraceProjection_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  change exactFieldEightTraceClassMap
    (exactFieldEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1))) =
      0
  rw [exactFieldEightProjection_ourTraceAnticommutator_zero]
  exact map_zero _

/-- The two-coordinate trace-order correction has the exact residual
`(1 / 2) • literalIncomingCommutatorClass` on OUR trace-anticommutator row. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      (1 / 2 : ℚ) • literalIncomingCommutatorClass := by
  change ourTwoCoordinateInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) -
      exactFieldEightTraceProjection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      (1 / 2 : ℚ) • literalIncomingCommutatorClass
  simp only [ourTwoCoordinateInvariantSevenTraceCompensator,
    LinearMap.smulRight_apply,
    ourTwoCoordinateInvariantSevenAxisCoordinate_ourTraceAnticommutator,
    exactFieldEightTraceProjection_ourTraceAnticommutator_zero, sub_zero]

/-- The full three-coordinate correction has the same exact residual: its
third coordinate is also trace-order blind on this row. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator
    (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      (1 / 2 : ℚ) • literalIncomingCommutatorClass := by
  unfold ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator,
    ourInvariantThirdIBPAxisCoordinate_ourTraceAnticommutator_zero]
  simp

/-- OUR three-coordinate correction is nonzero on the concrete canonical
trace-anticommutator row.  This is a finite obstruction to this particular
coordinate packet, not an obstruction to a further trace-sensitive repair. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) ≠
      0 := by
  rw [ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator]
  exact smul_ne_zero (by norm_num) literalIncomingCommutatorClass_ne_zero

/-- OUR signed-Reynolds invariant member represented by the genuine
trace-anticommutator row. -/
def ourInvariantTraceAnticommutatorRow (policy : PhysicalRelationPolicy) :
    exactFieldOrbitInvariantSubmodule :=
  ⟨exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)),
    exactFieldOrbitReynolds_invariant _⟩

/-- The averaged trace-anticommutator row belongs to the honest
coordinate-free joint invariant relation submodule under either policy. -/
theorem ourInvariantTraceAnticommutatorRow_mem
    (policy : PhysicalRelationPolicy) :
    ourInvariantTraceAnticommutatorRow policy ∈
      jointInvariantRelationSubmodule policy := by
  rw [mem_jointInvariantRelationSubmodule_iff]
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) ∈
      orbitPhysicalRelationSubmodule policy
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (orbitPhysicalRelationSubmodule policy).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply orbitPhysicalRelationSubmodule_signed_invariant policy h
  exact ⟨Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1,
    rfl⟩

/-- The exact residual persists on the actual coordinate-free invariant
relation member, not just on its unaveraged presentation. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator
    (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 =
      (1 / 2 : ℚ) • literalIncomingCommutatorClass := by
  rw [show (ourInvariantTraceAnticommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1))
        by rfl,
    ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator]

/-- The three-coordinate correction is nonzero on an actual member of the
coordinate-free joint relation space. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 ≠ 0 := by
  rw [ourThreeCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator]
  exact smul_ne_zero (by norm_num) literalIncomingCommutatorClass_ne_zero

/-- Consequently, OUR present three-coordinate correction does not
annihilate the complete coordinate-free joint relation submodule. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_not_annihilates_joint
    (policy : PhysicalRelationPolicy) :
    ¬ ∀ value : exactFieldOrbitInvariantSubmodule,
      value ∈ jointInvariantRelationSubmodule policy →
        ourThreeCoordinateInvariantTraceOrderCorrection value.1 = 0 := by
  intro hzero
  exact ourThreeCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_ne_zero
    policy
    (hzero (ourInvariantTraceAnticommutatorRow policy)
      (ourInvariantTraceAnticommutatorRow_mem policy))

#print axioms ourTraceAnticommutatorBase_signedAxisWeight
#print axioms ourTraceAnticommutatorSwap_signedAxisWeight
#print axioms ourTraceAnticommutatorSplit_signedAxisWeight
#print axioms ourTraceAnticommutatorBase_oldPlanePairSignedWeight
#print axioms ourTraceAnticommutatorSwap_oldPlanePairSignedWeight
#print axioms ourTraceAnticommutatorSplit_oldPlanePairSignedWeight
#print axioms ourTraceAnticommutatorBase_thirdPlanePairSignedWeight
#print axioms ourTraceAnticommutatorSwap_thirdPlanePairSignedWeight
#print axioms ourTraceAnticommutatorSplit_thirdPlanePairSignedWeight
#print axioms orbitPhysicalRelationOperator_ourTraceAnticommutator
#print axioms ourInvariantSevenAxisCoordinate_ourTraceAnticommutator
#print axioms ourInvariantIBPAxisCoordinate_ourTraceAnticommutator_zero
#print axioms ourInvariantThirdIBPAxisCoordinate_ourTraceAnticommutator_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_ne_zero
#print axioms ourInvariantTraceAnticommutatorRow_mem
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_ne_zero
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_not_annihilates_joint

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
