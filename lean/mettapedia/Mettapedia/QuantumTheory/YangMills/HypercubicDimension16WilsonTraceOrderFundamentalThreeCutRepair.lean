import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderTraceTopologyRepair

/-!
# OUR coupled trace-cycle repair for a fundamental three-cut row

The preceding four-coordinate trace-order functional repairs one polarized
trace-anticommutator row.  This module next tests the canonical six-term
fundamental `SU(2)` three-cut identity on the same decorated seven-field
carrier.  The six trace wirings have distinct cycle signatures, so this is a
genuine test of whether the earlier two-cycle gate alone has enough topology.

OUR construction adds a second, relabel-invariant trace-cycle character: the
derivative-axis character gated by the presence of a six-cycle.  The exact
finite calculation below determines its interaction with both displayed trace
families.  It is a bounded repair of those explicit rows only; it does not
assert descent through the complete physical relation submodule, a complete
joint rank, or Wilson-functional analytic coordinates.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair

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
open HypercubicDimension16IncomingCommutatorTraceProjection
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantEOM
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderTraceAnticommutatorObstruction
open HypercubicDimension16WilsonTraceOrderTraceTopologyRepair

/-- OUR six-cycle-sensitive axis multiplicity.  It retains the selected
derivative-axis character precisely on trace permutations with one six-cycle.
The cycle count is invariant under uniform field relabeling. -/
def ourSixCycleTraceAxisMultiplicity
    (sector : LabeledLocalWordSector 7 2) : ℕ :=
  if sector.trace.cycleType.count 6 = 1 then
    derivativeAxisWordMultiplicity [0, 2] sector
  else 0

/-- OUR six-cycle gate descends through ordinary field relabeling. -/
theorem ourSixCycleTraceAxisMultiplicity_relabel
    (rename : Equiv.Perm (Fin 7))
    (sector : LabeledLocalWordSector 7 2) :
    ourSixCycleTraceAxisMultiplicity (sector.relabel rename) =
      ourSixCycleTraceAxisMultiplicity sector := by
  unfold ourSixCycleTraceAxisMultiplicity
  rw [ourTraceCycleType_relabel]
  simp [derivativeAxisWordMultiplicity_relabel]

/-- OUR ordinary seven-field orbit scalar induced by the six-cycle gate. -/
def ourSixCycleTraceAxisOrbitMultiplicity : FieldSevenOrbitCarrier → ℚ :=
  Quotient.lift (fun sector =>
    (ourSixCycleTraceAxisMultiplicity sector : ℚ)) (by
      intro left right horbit
      change MulAction.orbitRel (Equiv.Perm (Fin 7))
        (LabeledLocalWordSector 7 2) left right at horbit
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
      rcases horbit with ⟨rename, hrename⟩
      change LabeledLocalWordSector.relabel rename right = left at hrename
      rw [← hrename]
      exact_mod_cast ourSixCycleTraceAxisMultiplicity_relabel rename right)

/-- OUR linear coordinate on the seven-field ordinary-orbit space. -/
def ourSixCycleTraceAxisCoordinate : FieldSevenOrbitSpace →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ ourSixCycleTraceAxisOrbitMultiplicity

@[simp] theorem ourSixCycleTraceAxisCoordinate_single
    (target : FieldSevenOrbitCarrier) (coefficient : ℚ) :
    ourSixCycleTraceAxisCoordinate (Finsupp.single target coefficient) =
      coefficient * ourSixCycleTraceAxisOrbitMultiplicity target := by
  simp [ourSixCycleTraceAxisCoordinate]

/-- OUR six-cycle orbit scalar follows a labeled sector under signed
hypercubic action. -/
theorem ourSixCycleTraceAxisOrbitMultiplicity_action
    (sector : LabeledLocalWordSector 7 2) (h : Hypercubic4) :
    ourSixCycleTraceAxisOrbitMultiplicity
      (FieldRelabelOrbitCarrier.hypercubicAct h (Quotient.mk _ sector)) =
      (ourSixCycleTraceAxisMultiplicity (sector.hypercubicAct h) : ℚ) := by
  simp [ourSixCycleTraceAxisOrbitMultiplicity]

/-- A bounded signed-weight certificate gives the six-cycle Reynolds
coordinate exactly. -/
theorem ourSixCycleTraceAxisCoordinate_reynolds_single
    (sector : LabeledLocalWordSector 7 2) (weight : ℚ)
    (hweight :
      (∑ h : Hypercubic4,
        sector.tensorSign h *
          (ourSixCycleTraceAxisMultiplicity (sector.hypercubicAct h) : ℚ)) =
        weight) :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier) (1 : ℚ))) =
      weight / 384 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourSixCycleTraceAxisCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier)
            (1 : ℚ))) =
        sector.tensorSign h *
          (ourSixCycleTraceAxisMultiplicity (sector.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourSixCycleTraceAxisCoordinate_single,
      ourSixCycleTraceAxisOrbitMultiplicity_action]
    simp
  simp_rw [hterm]
  rw [hweight]
  ring

/-- OUR canonical three distinct trace-cut labels on the seven-field carrier. -/
abbrev ourFieldSevenFundamentalTraceSite :
    FundamentalTraceSite ourFieldSevenCommutatorCarrier where
  label := ⟨![0, 1, 2], by decide⟩

/-- OUR genuine fundamental three-cut generator, available under either
physical relation policy. -/
def ourFieldSevenFundamentalTraceGenerator
    (policy : PhysicalRelationPolicy) : PhysicalRelationGenerator policy :=
  .fundamentalTrace ourFieldSevenCommutatorCarrier
    ourFieldSevenFundamentalTraceSite

/-- OUR labeled source term of the fundamental three-cut row. -/
abbrev ourFundamentalThreeCutBaseLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData ourFieldSevenCommutatorCarrier.2)

/-- OUR labeled `(0,1)` swap term of the fundamental three-cut row. -/
abbrev ourFundamentalThreeCutSwapFirstSecondLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (Equiv.swap ourFieldSevenFundamentalTraceSite.first
          ourFieldSevenFundamentalTraceSite.second)).2)

/-- OUR labeled `(0,2)` swap term of the fundamental three-cut row. -/
abbrev ourFundamentalThreeCutSwapFirstThirdLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (Equiv.swap ourFieldSevenFundamentalTraceSite.first
          ourFieldSevenFundamentalTraceSite.third)).2)

/-- OUR labeled `(1,2)` swap term of the fundamental three-cut row. -/
abbrev ourFundamentalThreeCutSwapSecondThirdLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (Equiv.swap ourFieldSevenFundamentalTraceSite.second
          ourFieldSevenFundamentalTraceSite.third)).2)

/-- OUR labeled forward three-cycle term of the fundamental three-cut row. -/
abbrev ourFundamentalThreeCutForwardLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (fundamentalCycleForward ourFieldSevenFundamentalTraceSite)).2)

/-- OUR labeled backward three-cycle term of the fundamental three-cut row. -/
abbrev ourFundamentalThreeCutBackwardLabeled : LabeledLocalWordSector 7 2 :=
  orientedLocalSectorEquivLabeled 7 2
    (normalizedSectorData
      (rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (fundamentalCycleBackward ourFieldSevenFundamentalTraceSite)).2)

/- The following bounded kernel computations identify the six-cycle character
on the canonical fundamental three-cut row. -/
set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBase_sixCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBaseLabeled.tensorSign h *
        (ourSixCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstSecond_sixCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstSecondLabeled.tensorSign h *
        (ourSixCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutSwapFirstSecondLabeled.hypercubicAct h) : ℚ)) =
      32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstThird_sixCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstThirdLabeled.tensorSign h *
        (ourSixCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutSwapFirstThirdLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapSecondThird_sixCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapSecondThirdLabeled.tensorSign h *
        (ourSixCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutSwapSecondThirdLabeled.hypercubicAct h) : ℚ)) =
      32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutForward_sixCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutForwardLabeled.tensorSign h *
        (ourSixCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutForwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBackward_sixCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBackwardLabeled.tensorSign h *
        (ourSixCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutBackwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

/-- OUR ordinary relabel orbit of the fundamental source term. -/
abbrev ourFundamentalThreeCutBaseOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourFundamentalThreeCutBaseLabeled

/-- OUR ordinary relabel orbit of the first fundamental swap term. -/
abbrev ourFundamentalThreeCutSwapFirstSecondOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourFundamentalThreeCutSwapFirstSecondLabeled

/-- OUR ordinary relabel orbit of the second fundamental swap term. -/
abbrev ourFundamentalThreeCutSwapFirstThirdOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourFundamentalThreeCutSwapFirstThirdLabeled

/-- OUR ordinary relabel orbit of the third fundamental swap term. -/
abbrev ourFundamentalThreeCutSwapSecondThirdOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourFundamentalThreeCutSwapSecondThirdLabeled

/-- OUR ordinary relabel orbit of the forward fundamental cycle term. -/
abbrev ourFundamentalThreeCutForwardOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourFundamentalThreeCutForwardLabeled

/-- OUR ordinary relabel orbit of the backward fundamental cycle term. -/
abbrev ourFundamentalThreeCutBackwardOrbit : FieldSevenOrbitCarrier :=
  Quotient.mk _ ourFundamentalThreeCutBackwardLabeled

/-- OUR exact full-carrier target of the fundamental source term. -/
abbrev ourFundamentalThreeCutBaseExactTarget :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourFundamentalThreeCutBaseOrbit⟩

/-- OUR exact full-carrier target of the first fundamental swap term. -/
abbrev ourFundamentalThreeCutSwapFirstSecondExactTarget :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourFundamentalThreeCutSwapFirstSecondOrbit⟩

/-- OUR exact full-carrier target of the second fundamental swap term. -/
abbrev ourFundamentalThreeCutSwapFirstThirdExactTarget :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourFundamentalThreeCutSwapFirstThirdOrbit⟩

/-- OUR exact full-carrier target of the third fundamental swap term. -/
abbrev ourFundamentalThreeCutSwapSecondThirdExactTarget :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourFundamentalThreeCutSwapSecondThirdOrbit⟩

/-- OUR exact full-carrier target of the forward fundamental cycle term. -/
abbrev ourFundamentalThreeCutForwardExactTarget :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourFundamentalThreeCutForwardOrbit⟩

/-- OUR exact full-carrier target of the backward fundamental cycle term. -/
abbrev ourFundamentalThreeCutBackwardExactTarget :
    ExactFieldRelabelOrbitCarrier :=
  ⟨ourSevenFieldCount, ourFundamentalThreeCutBackwardOrbit⟩

theorem exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutBase :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData ourFieldSevenCommutatorCarrier) =
      ourFundamentalThreeCutBaseExactTarget := by
  rfl

theorem exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutSwapFirstSecond :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap ourFieldSevenFundamentalTraceSite.first
            ourFieldSevenFundamentalTraceSite.second))) =
      ourFundamentalThreeCutSwapFirstSecondExactTarget := by
  rfl

theorem exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutSwapFirstThird :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap ourFieldSevenFundamentalTraceSite.first
            ourFieldSevenFundamentalTraceSite.third))) =
      ourFundamentalThreeCutSwapFirstThirdExactTarget := by
  rfl

theorem exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutSwapSecondThird :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap ourFieldSevenFundamentalTraceSite.second
            ourFieldSevenFundamentalTraceSite.third))) =
      ourFundamentalThreeCutSwapSecondThirdExactTarget := by
  rfl

theorem exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutForward :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (fundamentalCycleForward ourFieldSevenFundamentalTraceSite))) =
      ourFundamentalThreeCutForwardExactTarget := by
  rfl

theorem exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutBackward :
    exactFieldRelabelOrbitOfOriented
      (exactNormalizedSectorData
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (fundamentalCycleBackward ourFieldSevenFundamentalTraceSite))) =
      ourFundamentalThreeCutBackwardExactTarget := by
  rfl

/- The orientations of these six finite representatives are independently
replayed by the kernel. -/
set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBase_orientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment ourFieldSevenCommutatorCarrier.2) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstSecond_orientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap ourFieldSevenFundamentalTraceSite.first
            ourFieldSevenFundamentalTraceSite.second)).2) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstThird_orientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap ourFieldSevenFundamentalTraceSite.first
            ourFieldSevenFundamentalTraceSite.third)).2) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapSecondThird_orientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap ourFieldSevenFundamentalTraceSite.second
            ourFieldSevenFundamentalTraceSite.third)).2) = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutForward_orientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (fundamentalCycleForward ourFieldSevenFundamentalTraceSite)).2) =
      1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBackward_orientationCoefficient :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (fundamentalCycleBackward ourFieldSevenFundamentalTraceSite)).2) =
      1 := by
  decide +kernel

theorem ourNormalizeExactContextualBasis_ourFundamentalThreeCutBase :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis ourFieldSevenCommutatorCarrier) =
      Finsupp.single ourFundamentalThreeCutBaseExactTarget 1 := by
  rw [our_normalizeExactContextualBasis_fieldRelabel,
    exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutBase,
    ourFundamentalThreeCutBase_orientationCoefficient]

theorem ourNormalizeExactContextualBasis_ourFundamentalThreeCutSwapFirstSecond :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap ourFieldSevenFundamentalTraceSite.first
            ourFieldSevenFundamentalTraceSite.second))) =
      Finsupp.single ourFundamentalThreeCutSwapFirstSecondExactTarget 1 := by
  rw [our_normalizeExactContextualBasis_fieldRelabel,
    exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutSwapFirstSecond,
    ourFundamentalThreeCutSwapFirstSecond_orientationCoefficient]

theorem ourNormalizeExactContextualBasis_ourFundamentalThreeCutSwapFirstThird :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap ourFieldSevenFundamentalTraceSite.first
            ourFieldSevenFundamentalTraceSite.third))) =
      Finsupp.single ourFundamentalThreeCutSwapFirstThirdExactTarget 1 := by
  rw [our_normalizeExactContextualBasis_fieldRelabel,
    exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutSwapFirstThird,
    ourFundamentalThreeCutSwapFirstThird_orientationCoefficient]

theorem ourNormalizeExactContextualBasis_ourFundamentalThreeCutSwapSecondThird :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (Equiv.swap ourFieldSevenFundamentalTraceSite.second
            ourFieldSevenFundamentalTraceSite.third))) =
      Finsupp.single ourFundamentalThreeCutSwapSecondThirdExactTarget 1 := by
  rw [our_normalizeExactContextualBasis_fieldRelabel,
    exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutSwapSecondThird,
    ourFundamentalThreeCutSwapSecondThird_orientationCoefficient]

theorem ourNormalizeExactContextualBasis_ourFundamentalThreeCutForward :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (fundamentalCycleForward ourFieldSevenFundamentalTraceSite))) =
      Finsupp.single ourFundamentalThreeCutForwardExactTarget 1 := by
  rw [our_normalizeExactContextualBasis_fieldRelabel,
    exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutForward,
    ourFundamentalThreeCutForward_orientationCoefficient]

theorem ourNormalizeExactContextualBasis_ourFundamentalThreeCutBackward :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier
          (fundamentalCycleBackward ourFieldSevenFundamentalTraceSite))) =
      Finsupp.single ourFundamentalThreeCutBackwardExactTarget 1 := by
  rw [our_normalizeExactContextualBasis_fieldRelabel,
    exactFieldRelabelOrbitOfOriented_ourFundamentalThreeCutBackward,
    ourFundamentalThreeCutBackward_orientationCoefficient]

/-- The physical orbit operator sends OUR fundamental generator to its exact
six-term normalized row. -/
theorem orbitPhysicalRelationOperator_ourFundamentalThreeCut
    (policy : PhysicalRelationPolicy) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1) =
      Finsupp.single ourFundamentalThreeCutBaseExactTarget 1 -
        Finsupp.single ourFundamentalThreeCutSwapFirstSecondExactTarget 1 -
          Finsupp.single ourFundamentalThreeCutSwapFirstThirdExactTarget 1 -
            Finsupp.single ourFundamentalThreeCutSwapSecondThirdExactTarget 1 +
              Finsupp.single ourFundamentalThreeCutForwardExactTarget 1 +
                Finsupp.single ourFundamentalThreeCutBackwardExactTarget 1 := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, ourFieldSevenFundamentalTraceGenerator,
    physicalRelationRow, fundamentalTraceRow, map_sub, map_add]
  rw [normalizeExactContextual_single, normalizeExactContextual_single,
    normalizeExactContextual_single, normalizeExactContextual_single,
    normalizeExactContextual_single, normalizeExactContextual_single]
  simp only [one_smul]
  rw [ourNormalizeExactContextualBasis_ourFundamentalThreeCutBase,
    ourNormalizeExactContextualBasis_ourFundamentalThreeCutSwapFirstSecond,
    ourNormalizeExactContextualBasis_ourFundamentalThreeCutSwapFirstThird,
    ourNormalizeExactContextualBasis_ourFundamentalThreeCutSwapSecondThird,
    ourNormalizeExactContextualBasis_ourFundamentalThreeCutForward,
    ourNormalizeExactContextualBasis_ourFundamentalThreeCutBackward]

/-- The seven-field projection of OUR fundamental row is its six ordinary
trace-wiring orbits. -/
theorem exactFieldSevenProjection_ourFundamentalThreeCut
    (policy : PhysicalRelationPolicy) :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      Finsupp.single ourFundamentalThreeCutBaseOrbit 1 -
        Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit 1 -
          Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit 1 -
            Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit 1 +
              Finsupp.single ourFundamentalThreeCutForwardOrbit 1 +
                Finsupp.single ourFundamentalThreeCutBackwardOrbit 1 := by
  rw [orbitPhysicalRelationOperator_ourFundamentalThreeCut]
  simp only [LinearMap.map_sub, LinearMap.map_add,
    exactFieldSevenProjection_sevenTarget_single]

/-- The eight-field projection of OUR all-seven-field fundamental row is
zero. -/
theorem exactFieldEightProjection_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    exactFieldEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  rw [orbitPhysicalRelationOperator_ourFundamentalThreeCut]
  simp only [LinearMap.map_sub, LinearMap.map_add,
    exactFieldEightProjection_sevenTarget_single]
  simp

/-- OUR scaled six-cycle invariant coordinate.  The scale `12` makes the
fundamental three-cut row take value `-2`. -/
def ourInvariantSixCycleTraceAxisCoordinate :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ :=
  (12 : ℚ) •
    (ourSixCycleTraceAxisCoordinate.comp
      (exactFieldSevenProjection.comp exactFieldOrbitReynolds))

/-- OUR six-cycle scalar coordinate is signed-hypercubic invariant. -/
theorem ourInvariantSixCycleTraceAxisCoordinate_signed_action
    (h : Hypercubic4) (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantSixCycleTraceAxisCoordinate
      (signedExactFieldRelabelOrbitAction h value) =
      ourInvariantSixCycleTraceAxisCoordinate value := by
  unfold ourInvariantSixCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldOrbitReynolds_action]

/-- OUR fifth trace-class contribution, calibrated against the fundamental
three-cut residual. -/
def ourSixCycleTraceInvariantTraceContribution :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ((-1 / 4 : ℚ) • ourInvariantSixCycleTraceAxisCoordinate).smulRight
    literalIncomingCommutatorClass

/-- OUR five-coordinate finite correction.  It retains the four-coordinate
repair and adds the independent six-cycle character. -/
def ourFiveCoordinateInvariantTraceOrderCorrection :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] FieldEightPhysicalTraceQuotient :=
  ourFourCoordinateInvariantTraceOrderCorrection +
    ourSixCycleTraceInvariantTraceContribution

set_option maxRecDepth 100000 in
theorem ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutBase :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit (1 : ℚ))) = 0 := by
  change ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourSixCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutBaseLabeled 0
    ourFundamentalThreeCutBase_sixCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstSecond :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit (1 : ℚ))) =
      1 / 12 := by
  change ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapFirstSecondLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = 1 / 12
  rw [ourSixCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutSwapFirstSecondLabeled 32
    ourFundamentalThreeCutSwapFirstSecond_sixCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstThird :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit (1 : ℚ))) =
      0 := by
  change ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapFirstThirdLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = 0
  rw [ourSixCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutSwapFirstThirdLabeled 0
    ourFundamentalThreeCutSwapFirstThird_sixCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapSecondThird :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit (1 : ℚ))) =
      1 / 12 := by
  change ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapSecondThirdLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = 1 / 12
  rw [ourSixCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutSwapSecondThirdLabeled 32
    ourFundamentalThreeCutSwapSecondThird_sixCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutForward :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutForwardOrbit (1 : ℚ))) = 0 := by
  change ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutForwardLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourSixCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutForwardLabeled 0
    ourFundamentalThreeCutForward_sixCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutBackward :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBackwardOrbit (1 : ℚ))) = 0 := by
  change ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutBackwardLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourSixCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutBackwardLabeled 0
    ourFundamentalThreeCutBackward_sixCycleTraceAxisSignedWeight]
  norm_num

/-- The canonical fundamental three-cut row has six-cycle scalar `-1 / 6`. -/
theorem ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCut :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit (1 : ℚ) -
          Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit (1 : ℚ) -
            Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit (1 : ℚ) -
              Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit (1 : ℚ) +
                Finsupp.single ourFundamentalThreeCutForwardOrbit (1 : ℚ) +
                  Finsupp.single ourFundamentalThreeCutBackwardOrbit (1 : ℚ))) =
      -1 / 6 := by
  simp only [map_sub, map_add,
    ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutBase,
    ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstSecond,
    ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstThird,
    ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapSecondThird,
    ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutForward,
    ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutBackward]
  norm_num

/-- The scaled six-cycle coordinate takes OUR fundamental three-cut row to
`-2`. -/
theorem ourInvariantSixCycleTraceAxisCoordinate_ourFundamentalThreeCut
    (policy : PhysicalRelationPolicy) :
    ourInvariantSixCycleTraceAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      -2 := by
  unfold ourInvariantSixCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourFundamentalThreeCut,
    ourSixCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCut]
  norm_num

/- The existing two-cycle gate has one nonzero term on this six-term row.
These certificates isolate its precise four-coordinate residual. -/
set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBase_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBaseLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstSecond_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstSecondLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutSwapFirstSecondLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstThird_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstThirdLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutSwapFirstThirdLabeled.hypercubicAct h) : ℚ)) =
      32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapSecondThird_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapSecondThirdLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutSwapSecondThirdLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutForward_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutForwardLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutForwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBackward_twoCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBackwardLabeled.tensorSign h *
        (ourTwoCycleTraceAxisMultiplicity
          (ourFundamentalThreeCutBackwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutBase :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTwoCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutBaseLabeled 0
    ourFundamentalThreeCutBase_twoCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstSecond :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit (1 : ℚ))) =
      0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapFirstSecondLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = 0
  rw [ourTwoCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutSwapFirstSecondLabeled 0
    ourFundamentalThreeCutSwapFirstSecond_twoCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstThird :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit (1 : ℚ))) =
      1 / 12 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapFirstThirdLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = 1 / 12
  rw [ourTwoCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutSwapFirstThirdLabeled 32
    ourFundamentalThreeCutSwapFirstThird_twoCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapSecondThird :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit (1 : ℚ))) =
      0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutSwapSecondThirdLabeled :
            FieldSevenOrbitCarrier) (1 : ℚ))) = 0
  rw [ourTwoCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutSwapSecondThirdLabeled 0
    ourFundamentalThreeCutSwapSecondThird_twoCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutForward :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutForwardOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutForwardLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTwoCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutForwardLabeled 0
    ourFundamentalThreeCutForward_twoCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutBackward :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBackwardOrbit (1 : ℚ))) = 0 := by
  change ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourFundamentalThreeCutBackwardLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourTwoCycleTraceAxisCoordinate_reynolds_single
    ourFundamentalThreeCutBackwardLabeled 0
    ourFundamentalThreeCutBackward_twoCycleTraceAxisSignedWeight]
  norm_num

/-- The fundamental row has two-cycle scalar `-1 / 12`. -/
theorem ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCut :
    ourTwoCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit (1 : ℚ) -
          Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit (1 : ℚ) -
            Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit (1 : ℚ) -
              Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit (1 : ℚ) +
                Finsupp.single ourFundamentalThreeCutForwardOrbit (1 : ℚ) +
                  Finsupp.single ourFundamentalThreeCutBackwardOrbit (1 : ℚ))) =
      -1 / 12 := by
  simp only [map_sub, map_add,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutBase,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstSecond,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapFirstThird,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutSwapSecondThird,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutForward,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCutBackward]
  norm_num

theorem ourInvariantTwoCycleTraceAxisCoordinate_ourFundamentalThreeCut
    (policy : PhysicalRelationPolicy) :
    ourInvariantTwoCycleTraceAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      -1 := by
  unfold ourInvariantTwoCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourFundamentalThreeCut,
    ourTwoCycleTraceAxisCoordinate_reynolds_ourFundamentalThreeCut]
  norm_num

/-- A bounded signed-weight certificate gives the original derivative-axis
coordinate on a displayed seven-field trace wiring. -/
theorem ourDerivativeAxisCoordinate_reynolds_single
    (sector : LabeledLocalWordSector 7 2) (weight : ℚ)
    (hweight :
      (∑ h : Hypercubic4,
        sector.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2] (sector.hypercubicAct h) : ℚ)) =
        weight) :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier) (1 : ℚ))) =
      weight / 384 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourDerivativeAxisCoordinate [0, 2]
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier)
            (1 : ℚ))) =
        sector.tensorSign h *
          (derivativeAxisWordMultiplicity [0, 2] (sector.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourDerivativeAxisCoordinate_single]
    simp [derivativeAxisOrbitMultiplicity]
  simp_rw [hterm]
  rw [hweight]
  ring

/-- A bounded signed-weight certificate gives the original plane/axis
coordinate on a displayed seven-field trace wiring. -/
theorem ourIBPAxisPlanePairCoordinate_reynolds_single
    (sector : LabeledLocalWordSector 7 2) (weight : ℚ)
    (hweight :
      (∑ h : Hypercubic4,
        sector.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity (sector.hypercubicAct h) : ℚ)) =
        weight) :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier) (1 : ℚ))) =
      weight / 384 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier)
            (1 : ℚ))) =
        sector.tensorSign h *
          (ourIBPAxisPlanePairMultiplicity (sector.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourIBPAxisPlanePairCoordinate_single]
    simp [ourIBPAxisPlanePairOrbitMultiplicity]
  simp_rw [hterm]
  rw [hweight]
  ring

/-- A bounded signed-weight certificate gives the third plane/axis coordinate
on a displayed seven-field trace wiring. -/
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_single
    (sector : LabeledLocalWordSector 7 2) (weight : ℚ)
    (hweight :
      (∑ h : Hypercubic4,
        sector.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity (sector.hypercubicAct h) : ℚ)) =
        weight) :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier) (1 : ℚ))) =
      weight / 384 := by
  unfold sectorFieldOrbitReynolds
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  have hterm (h : Hypercubic4) :
      ourThirdIBPAxisPlanePairCoordinate
        (signedSectorFieldOrbitAction h 7 2
          (Finsupp.single (Quotient.mk _ sector : FieldSevenOrbitCarrier)
            (1 : ℚ))) =
        sector.tensorSign h *
          (ourThirdIBPAxisPlanePairMultiplicity (sector.hypercubicAct h) : ℚ) := by
    rw [signedSectorFieldOrbitAction_single,
      ourThirdIBPAxisPlanePairCoordinate_single]
    simp [ourThirdIBPAxisPlanePairOrbitMultiplicity]
  simp_rw [hterm]
  rw [hweight]
  ring

/- The three pre-existing decoration coordinates are trace-order blind on
this row: their finite signed weights are respectively constant, zero, and
zero across its six trace wirings. -/
set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBase_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBaseLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourFundamentalThreeCutBaseLabeled.hypercubicAct h) : ℚ)) = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstSecond_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstSecondLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourFundamentalThreeCutSwapFirstSecondLabeled.hypercubicAct h) : ℚ)) =
      32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstThird_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstThirdLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourFundamentalThreeCutSwapFirstThirdLabeled.hypercubicAct h) : ℚ)) =
      32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapSecondThird_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapSecondThirdLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourFundamentalThreeCutSwapSecondThirdLabeled.hypercubicAct h) : ℚ)) =
      32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutForward_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutForwardLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourFundamentalThreeCutForwardLabeled.hypercubicAct h) : ℚ)) = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBackward_signedAxisWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBackwardLabeled.tensorSign h *
        (derivativeAxisWordMultiplicity [0, 2]
          (ourFundamentalThreeCutBackwardLabeled.hypercubicAct h) : ℚ)) = 32 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBase_oldPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBaseLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstSecond_oldPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstSecondLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutSwapFirstSecondLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstThird_oldPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstThirdLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutSwapFirstThirdLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapSecondThird_oldPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapSecondThirdLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutSwapSecondThirdLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutForward_oldPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutForwardLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutForwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBackward_oldPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBackwardLabeled.tensorSign h *
        (ourIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutBackwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBase_thirdPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBaseLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstSecond_thirdPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstSecondLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutSwapFirstSecondLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapFirstThird_thirdPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapFirstThirdLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutSwapFirstThirdLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutSwapSecondThird_thirdPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutSwapSecondThirdLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutSwapSecondThirdLabeled.hypercubicAct h) : ℚ)) =
      0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutForward_thirdPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutForwardLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutForwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourFundamentalThreeCutBackward_thirdPlanePairSignedWeight :
    (∑ h : Hypercubic4,
      ourFundamentalThreeCutBackwardLabeled.tensorSign h *
        (ourThirdIBPAxisPlanePairMultiplicity
          (ourFundamentalThreeCutBackwardLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

/-- The original derivative-axis coordinate annihilates OUR fundamental
three-cut row: all six signed weights agree. -/
theorem ourDerivativeAxisCoordinate_reynolds_ourFundamentalThreeCut :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit (1 : ℚ) -
          Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit (1 : ℚ) -
            Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit (1 : ℚ) -
              Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit (1 : ℚ) +
                Finsupp.single ourFundamentalThreeCutForwardOrbit (1 : ℚ) +
                  Finsupp.single ourFundamentalThreeCutBackwardOrbit (1 : ℚ))) =
      0 := by
  simp only [map_sub, map_add,
    ourDerivativeAxisCoordinate_reynolds_single
      ourFundamentalThreeCutBaseLabeled 32
      ourFundamentalThreeCutBase_signedAxisWeight,
    ourDerivativeAxisCoordinate_reynolds_single
      ourFundamentalThreeCutSwapFirstSecondLabeled 32
      ourFundamentalThreeCutSwapFirstSecond_signedAxisWeight,
    ourDerivativeAxisCoordinate_reynolds_single
      ourFundamentalThreeCutSwapFirstThirdLabeled 32
      ourFundamentalThreeCutSwapFirstThird_signedAxisWeight,
    ourDerivativeAxisCoordinate_reynolds_single
      ourFundamentalThreeCutSwapSecondThirdLabeled 32
      ourFundamentalThreeCutSwapSecondThird_signedAxisWeight,
    ourDerivativeAxisCoordinate_reynolds_single
      ourFundamentalThreeCutForwardLabeled 32
      ourFundamentalThreeCutForward_signedAxisWeight,
    ourDerivativeAxisCoordinate_reynolds_single
      ourFundamentalThreeCutBackwardLabeled 32
      ourFundamentalThreeCutBackward_signedAxisWeight]
  norm_num

/-- The original plane/axis coordinate annihilates OUR fundamental
three-cut row. -/
theorem ourIBPAxisPlanePairCoordinate_reynolds_ourFundamentalThreeCut :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit (1 : ℚ) -
          Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit (1 : ℚ) -
            Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit (1 : ℚ) -
              Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit (1 : ℚ) +
                Finsupp.single ourFundamentalThreeCutForwardOrbit (1 : ℚ) +
                  Finsupp.single ourFundamentalThreeCutBackwardOrbit (1 : ℚ))) =
      0 := by
  simp only [map_sub, map_add,
    ourIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutBaseLabeled 0
      ourFundamentalThreeCutBase_oldPlanePairSignedWeight,
    ourIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutSwapFirstSecondLabeled 0
      ourFundamentalThreeCutSwapFirstSecond_oldPlanePairSignedWeight,
    ourIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutSwapFirstThirdLabeled 0
      ourFundamentalThreeCutSwapFirstThird_oldPlanePairSignedWeight,
    ourIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutSwapSecondThirdLabeled 0
      ourFundamentalThreeCutSwapSecondThird_oldPlanePairSignedWeight,
    ourIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutForwardLabeled 0
      ourFundamentalThreeCutForward_oldPlanePairSignedWeight,
    ourIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutBackwardLabeled 0
      ourFundamentalThreeCutBackward_oldPlanePairSignedWeight]
  norm_num

/-- The third plane/axis coordinate also annihilates OUR fundamental
three-cut row. -/
theorem ourThirdIBPAxisPlanePairCoordinate_reynolds_ourFundamentalThreeCut :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourFundamentalThreeCutBaseOrbit (1 : ℚ) -
          Finsupp.single ourFundamentalThreeCutSwapFirstSecondOrbit (1 : ℚ) -
            Finsupp.single ourFundamentalThreeCutSwapFirstThirdOrbit (1 : ℚ) -
              Finsupp.single ourFundamentalThreeCutSwapSecondThirdOrbit (1 : ℚ) +
                Finsupp.single ourFundamentalThreeCutForwardOrbit (1 : ℚ) +
                  Finsupp.single ourFundamentalThreeCutBackwardOrbit (1 : ℚ))) =
      0 := by
  simp only [map_sub, map_add,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutBaseLabeled 0
      ourFundamentalThreeCutBase_thirdPlanePairSignedWeight,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutSwapFirstSecondLabeled 0
      ourFundamentalThreeCutSwapFirstSecond_thirdPlanePairSignedWeight,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutSwapFirstThirdLabeled 0
      ourFundamentalThreeCutSwapFirstThird_thirdPlanePairSignedWeight,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutSwapSecondThirdLabeled 0
      ourFundamentalThreeCutSwapSecondThird_thirdPlanePairSignedWeight,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutForwardLabeled 0
      ourFundamentalThreeCutForward_thirdPlanePairSignedWeight,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_single
      ourFundamentalThreeCutBackwardLabeled 0
      ourFundamentalThreeCutBackward_thirdPlanePairSignedWeight]
  norm_num

/-- The first invariant coordinate vanishes on OUR fundamental three-cut
row. -/
theorem ourInvariantSevenAxisCoordinate_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourFundamentalThreeCut,
    ourDerivativeAxisCoordinate_reynolds_ourFundamentalThreeCut]
  norm_num

/-- The second invariant coordinate vanishes on OUR fundamental three-cut
row. -/
theorem ourInvariantIBPAxisCoordinate_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourFundamentalThreeCut,
    ourIBPAxisPlanePairCoordinate_reynolds_ourFundamentalThreeCut]
  norm_num

/-- The third invariant coordinate vanishes on OUR fundamental three-cut
row. -/
theorem ourInvariantThirdIBPAxisCoordinate_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourFundamentalThreeCut,
    ourThirdIBPAxisPlanePairCoordinate_reynolds_ourFundamentalThreeCut]
  norm_num

/-- The two-coordinate seven-field scalar already vanishes on OUR
fundamental three-cut row. -/
theorem ourTwoCoordinateInvariantSevenAxisCoordinate_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    ourInvariantSevenAxisCoordinate_ourFundamentalThreeCut_zero,
    ourInvariantIBPAxisCoordinate_ourFundamentalThreeCut_zero]
  norm_num

/-- The canonical eight-field trace coordinate vanishes on OUR all-seven-field
fundamental row. -/
theorem exactFieldEightTraceProjection_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  change exactFieldEightTraceClassMap
    (exactFieldEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1))) =
      0
  rw [exactFieldEightProjection_ourFundamentalThreeCut_zero]
  exact map_zero _

/-- The two-coordinate trace-order correction vanishes on OUR fundamental
three-cut row. -/
theorem ourTwoCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourTwoCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  change ourTwoCoordinateInvariantSevenTraceCompensator
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) -
      exactFieldEightTraceProjection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0
  simp only [ourTwoCoordinateInvariantSevenTraceCompensator,
    LinearMap.smulRight_apply,
    ourTwoCoordinateInvariantSevenAxisCoordinate_ourFundamentalThreeCut_zero,
    exactFieldEightTraceProjection_ourFundamentalThreeCut_zero, sub_zero]
  simp

/-- The three-coordinate correction also vanishes on OUR fundamental
three-cut row. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourTwoCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero,
    ourInvariantThirdIBPAxisCoordinate_ourFundamentalThreeCut_zero]
  simp

/-- The fourth coordinate has the exact new fundamental three-cut residual
`(-1 / 2) • literalIncomingCommutatorClass`. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      (-1 / 2 : ℚ) • literalIncomingCommutatorClass := by
  unfold ourFourCoordinateInvariantTraceOrderCorrection
    ourTwoCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourThreeCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero,
    ourInvariantTwoCycleTraceAxisCoordinate_ourFundamentalThreeCut]
  module

/-- OUR fifth six-cycle contribution cancels the exact fundamental residual. -/
theorem ourFiveCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourFiveCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) =
      0 := by
  unfold ourFiveCoordinateInvariantTraceOrderCorrection
    ourSixCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourFourCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut,
    ourInvariantSixCycleTraceAxisCoordinate_ourFundamentalThreeCut]
  module

/- The six-cycle gate is independently checked to vanish on the preceding
canonical trace-anticommutator row. -/
set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorBase_sixCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorBaseLabeled.tensorSign h *
        (ourSixCycleTraceAxisMultiplicity
          (ourTraceAnticommutatorBaseLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSwap_sixCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSwapLabeled.tensorSign h *
        (ourSixCycleTraceAxisMultiplicity
          (ourTraceAnticommutatorSwapLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourTraceAnticommutatorSplit_sixCycleTraceAxisSignedWeight :
    (∑ h : Hypercubic4,
      ourTraceAnticommutatorSplitLabeled.tensorSign h *
        (ourSixCycleTraceAxisMultiplicity
          (ourTraceAnticommutatorSplitLabeled.hypercubicAct h) : ℚ)) = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ourSixCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorBase :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ))) = 0 := by
  change ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorBaseLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourSixCycleTraceAxisCoordinate_reynolds_single
    ourTraceAnticommutatorBaseLabeled 0
    ourTraceAnticommutatorBase_sixCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourSixCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorSwap :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ))) = 0 := by
  change ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorSwapLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourSixCycleTraceAxisCoordinate_reynolds_single
    ourTraceAnticommutatorSwapLabeled 0
    ourTraceAnticommutatorSwap_sixCycleTraceAxisSignedWeight]
  norm_num

set_option maxRecDepth 100000 in
theorem ourSixCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorSplit :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) = 0 := by
  change ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single
          (Quotient.mk _ ourTraceAnticommutatorSplitLabeled : FieldSevenOrbitCarrier)
          (1 : ℚ))) = 0
  rw [ourSixCycleTraceAxisCoordinate_reynolds_single
    ourTraceAnticommutatorSplitLabeled 0
    ourTraceAnticommutatorSplit_sixCycleTraceAxisSignedWeight]
  norm_num

theorem ourSixCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutator :
    ourSixCycleTraceAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (Finsupp.single ourTraceAnticommutatorBaseOrbit (1 : ℚ) +
          Finsupp.single ourTraceAnticommutatorSwapOrbit (1 : ℚ) -
            Finsupp.single ourTraceAnticommutatorSplitOrbit (1 : ℚ))) = 0 := by
  simp only [map_sub, map_add,
    ourSixCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorBase,
    ourSixCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorSwap,
    ourSixCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutatorSplit]
  norm_num

theorem ourInvariantSixCycleTraceAxisCoordinate_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourInvariantSixCycleTraceAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourInvariantSixCycleTraceAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    exactFieldSevenProjection_ourTraceAnticommutator,
    ourSixCycleTraceAxisCoordinate_reynolds_ourTraceAnticommutator]
  norm_num

/-- The fifth correction retains the prior canonical trace-anticommutator
repair. -/
theorem ourFiveCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourFiveCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) =
      0 := by
  unfold ourFiveCoordinateInvariantTraceOrderCorrection
    ourSixCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply,
    ourFourCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_zero,
    ourInvariantSixCycleTraceAxisCoordinate_ourTraceAnticommutator_zero]
  simp

/-- OUR sixth scalar coordinate is unchanged by exact-field Reynolds
averaging. -/
theorem ourInvariantSixCycleTraceAxisCoordinate_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    ourInvariantSixCycleTraceAxisCoordinate (exactFieldOrbitReynolds value) =
      ourInvariantSixCycleTraceAxisCoordinate value := by
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  simp_rw [ourInvariantSixCycleTraceAxisCoordinate_signed_action]
  rw [Finset.sum_const, Finset.card_univ, Hypercubic4.card_hypercubic4]
  module

/-- OUR five-coordinate correction is unchanged by exact-field Reynolds
averaging. -/
theorem ourFiveCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds
    (value : ExactFieldRelabelOrbitSpace) :
    ourFiveCoordinateInvariantTraceOrderCorrection (exactFieldOrbitReynolds value) =
      ourFiveCoordinateInvariantTraceOrderCorrection value := by
  unfold ourFiveCoordinateInvariantTraceOrderCorrection
    ourSixCycleTraceInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply]
  rw [ourFourCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourInvariantSixCycleTraceAxisCoordinate_exactFieldOrbitReynolds]

/-- OUR signed-Reynolds invariant member represented by the fundamental
three-cut row. -/
def ourInvariantFundamentalThreeCutRow (policy : PhysicalRelationPolicy) :
    exactFieldOrbitInvariantSubmodule :=
  ⟨exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)),
    exactFieldOrbitReynolds_invariant _⟩

/-- The averaged fundamental three-cut row belongs to the honest
coordinate-free joint invariant relation submodule under either policy. -/
theorem ourInvariantFundamentalThreeCutRow_mem
    (policy : PhysicalRelationPolicy) :
    ourInvariantFundamentalThreeCutRow policy ∈
      jointInvariantRelationSubmodule policy := by
  rw [mem_jointInvariantRelationSubmodule_iff]
  change exactFieldOrbitReynolds
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) ∈
      orbitPhysicalRelationSubmodule policy
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply]
  apply (orbitPhysicalRelationSubmodule policy).smul_mem
  apply Submodule.sum_mem
  intro h _
  apply orbitPhysicalRelationSubmodule_signed_invariant policy h
  exact ⟨Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1,
    rfl⟩

/-- The four-coordinate residual persists on the actual averaged fundamental
member of the coordinate-free joint relation space. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 =
      (-1 / 2 : ℚ) • literalIncomingCommutatorClass := by
  rw [show (ourInvariantFundamentalThreeCutRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) by
        rfl,
    ourFourCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourFourCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut]

/-- The four-coordinate residual is nonzero on an actual member of the
coordinate-free joint relation space. -/
theorem ourFourCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut_ne_zero
    (policy : PhysicalRelationPolicy) :
    ourFourCoordinateInvariantTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 ≠ 0 := by
  rw [ourFourCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut]
  exact smul_ne_zero (by norm_num) literalIncomingCommutatorClass_ne_zero

/-- The fifth correction annihilates the actual averaged fundamental
three-cut member. -/
theorem ourFiveCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero
    (policy : PhysicalRelationPolicy) :
    ourFiveCoordinateInvariantTraceOrderCorrection
      (ourInvariantFundamentalThreeCutRow policy).1 = 0 := by
  rw [show (ourInvariantFundamentalThreeCutRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenFundamentalTraceGenerator policy) 1)) by
        rfl,
    ourFiveCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourFiveCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero]

/-- The fifth correction also annihilates the actual averaged prior
trace-anticommutator member. -/
theorem ourFiveCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy) :
    ourFiveCoordinateInvariantTraceOrderCorrection
      (ourInvariantTraceAnticommutatorRow policy).1 = 0 := by
  rw [show (ourInvariantTraceAnticommutatorRow policy).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenTraceAnticommutatorGenerator policy) 1)) by
        rfl,
    ourFiveCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourFiveCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_zero]

#print axioms ourSixCycleTraceAxisMultiplicity_relabel
#print axioms ourFundamentalThreeCutBase_sixCycleTraceAxisSignedWeight
#print axioms ourFundamentalThreeCutSwapFirstSecond_sixCycleTraceAxisSignedWeight
#print axioms ourFundamentalThreeCutSwapFirstThird_sixCycleTraceAxisSignedWeight
#print axioms ourFundamentalThreeCutSwapSecondThird_sixCycleTraceAxisSignedWeight
#print axioms ourFundamentalThreeCutForward_sixCycleTraceAxisSignedWeight
#print axioms ourFundamentalThreeCutBackward_sixCycleTraceAxisSignedWeight
#print axioms orbitPhysicalRelationOperator_ourFundamentalThreeCut
#print axioms ourInvariantTwoCycleTraceAxisCoordinate_ourFundamentalThreeCut
#print axioms ourInvariantSixCycleTraceAxisCoordinate_ourFundamentalThreeCut
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut
#print axioms ourFourCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut_ne_zero
#print axioms ourFiveCoordinateInvariantTraceOrderCorrection_ourFundamentalThreeCut_zero
#print axioms ourFiveCoordinateInvariantTraceOrderCorrection_ourTraceAnticommutator_zero
#print axioms ourInvariantFundamentalThreeCutRow_mem
#print axioms ourFiveCoordinateInvariantTraceOrderCorrection_invariantFundamentalThreeCut_zero
#print axioms ourFiveCoordinateInvariantTraceOrderCorrection_invariantTraceAnticommutator_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
