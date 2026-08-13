import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FundamentalTracePhysicalThreeCoordinate

/-!
# OUR physical adjacent trace-anticommutator family

The fixed physical seven-field carrier used by the repaired Wilson-lattice
calibration has one seven-cycle, hence seven actual adjacent placements of the
polarized `SU(2)` trace-anticommutator relation.  This module realizes that
whole finite family in the `F,D`/IBP relation source, not merely the
previously displayed placement.

For each adjacent placement, the base, adjacent-swap, and split-trace terms
have the same field/derivative decoration.  The three trace-order-blind
coordinates consequently retain the common `1 / 2` incoming trace-class
residual.  A bounded exact replay of the seven trace topologies gives the
common profile value `-1 / 2`; OUR profile contribution cancels that residual.
The resulting finite cochain family is then transported through signed
Reynolds averaging into the coordinate-free joint relation submodule under
both relation policies.

This is an OUR finite-family extension on one specified physical carrier. It
does not assert a census of trace-anticommutator placements on arbitrary
carriers, descent through every physical relation family, joint rank or
conditioning, or Wilson-functional analytic coordinates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceAnticommutatorPhysicalFamily

open V14HypercubicFDCensus
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16IncomingCommutatorTraceCoupledDual
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16FundamentalTracePhysicalFamily
open HypercubicDimension16FundamentalTracePhysicalCycleProfile
open HypercubicDimension16FundamentalTracePhysicalThreeCoordinate
open HypercubicDimension16WilsonTraceOrderFundamentalThreeCutRepair
open HypercubicDimension16WilsonTraceOrderInvariantRepair
open HypercubicDimension16WilsonTraceOrderInvariantBianchi
open HypercubicDimension16WilsonTraceOrderInvariantThreeCoordinateRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16FDIBPCochainJointBridge
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16CovariantCompressionWall
open HypercubicDimension16AntisymmetryQuotient

/-- OUR finite index of all adjacent placements in the fixed physical
seven-cycle. -/
abbrev OurPhysicalTraceAnticommutatorLabel := Fin 7

/-- OUR physical adjacent trace-anticommutator site at one seven-cycle
position. -/
def ourPhysicalTraceAnticommutatorSite
    (left : OurPhysicalTraceAnticommutatorLabel) :
    TraceAnticommutatorSite ourFieldSevenCommutatorCarrier where
  left := left
  cycleLength_ge_three := by
    fin_cases left <;> decide

/-- OUR policy-indexed physical trace-anticommutator generator at one
adjacent placement. -/
def ourPhysicalTraceAnticommutatorGeneratorAt
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    PhysicalRelationGenerator policy :=
  .traceAnticommutator ourFieldSevenCommutatorCarrier
    (ourPhysicalTraceAnticommutatorSite left)

/-- The trace rewiring of OUR adjacent-swap term, written in the uniform
three-cut rewire presentation. -/
def ourPhysicalTraceAnticommutatorSwapRewire
    (left : OurPhysicalTraceAnticommutatorLabel) : Equiv.Perm (Fin 7) :=
  (Equiv.swap (ourPhysicalTraceAnticommutatorSite left).right
    (ourPhysicalTraceAnticommutatorSite left).successor).trans
    (Equiv.swap (ourPhysicalTraceAnticommutatorSite left).left
      (ourPhysicalTraceAnticommutatorSite left).right)

/-- The trace rewiring of OUR split-trace term, written in the uniform
three-cut rewire presentation. -/
def ourPhysicalTraceAnticommutatorSplitRewire
    (left : OurPhysicalTraceAnticommutatorLabel) : Equiv.Perm (Fin 7) :=
  Equiv.swap (ourPhysicalTraceAnticommutatorSite left).left
    (ourPhysicalTraceAnticommutatorSite left).successor

/-- The adjacent-swap carrier is definitionally the corresponding uniform
trace rewire. -/
theorem ourPhysicalTraceAnticommutator_swapCarrier
    (left : OurPhysicalTraceAnticommutatorLabel) :
    swapAdjacentTraceCarrier (ourPhysicalTraceAnticommutatorSite left) =
      rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (ourPhysicalTraceAnticommutatorSwapRewire left) := by
  rfl

/-- The split-trace carrier is definitionally the corresponding uniform trace
rewire. -/
theorem ourPhysicalTraceAnticommutator_splitCarrier
    (left : OurPhysicalTraceAnticommutatorLabel) :
    splitAdjacentTraceCarrier (ourPhysicalTraceAnticommutatorSite left) =
      rewireTraceCarrier ourFieldSevenCommutatorCarrier
        (ourPhysicalTraceAnticommutatorSplitRewire left) := by
  rfl

/-- Exact normalization of OUR unrewired physical seven-field source. -/
theorem ourPhysicalTraceAnticommutator_normalizeBase :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis ourFieldSevenCommutatorCarrier) =
      Finsupp.single physicalBaseExactTarget 1 := by
  rw [normalizeExactContextualBasis_fieldRelabel]
  change Finsupp.single physicalBaseExactTarget
      (fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment ourFieldSevenCommutatorCarrier.2)) =
    Finsupp.single physicalBaseExactTarget 1
  congr 1
  decide +kernel

/-- Exact normalization of any trace rewire of OUR physical seven-field
source.  Trace rewiring leaves its field-axis orientation unchanged. -/
theorem ourPhysicalTraceAnticommutator_normalizeRewire
    (rewire : Equiv.Perm (Fin 7)) :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (rewireTraceCarrier ourFieldSevenCommutatorCarrier rewire)) =
      Finsupp.single (physicalRewireExactTarget rewire) 1 := by
  rw [normalizeExactContextualBasis_fieldRelabel]
  change Finsupp.single (physicalRewireExactTarget rewire)
      (fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment ourFieldSevenCommutatorCarrier.2)) =
    Finsupp.single (physicalRewireExactTarget rewire) 1
  congr 1
  decide +kernel

/-- The actual physical relation operator sends each adjacent placement to
its exact normalized three-term trace row. -/
theorem ourPhysicalTraceAnticommutator_rowFormula
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1) =
      Finsupp.single physicalBaseExactTarget 1 +
        Finsupp.single
          (physicalRewireExactTarget
            (ourPhysicalTraceAnticommutatorSwapRewire left)) 1 -
          Finsupp.single
            (physicalRewireExactTarget
              (ourPhysicalTraceAnticommutatorSplitRewire left)) 1 := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, ourPhysicalTraceAnticommutatorGeneratorAt,
    physicalRelationRow, traceAnticommutatorRow, map_sub, map_add]
  rw [normalizeExactContextual_single, normalizeExactContextual_single,
    normalizeExactContextual_single]
  simp only [one_smul]
  rw [ourPhysicalTraceAnticommutator_normalizeBase,
    ourPhysicalTraceAnticommutator_swapCarrier,
    ourPhysicalTraceAnticommutator_splitCarrier,
    ourPhysicalTraceAnticommutator_normalizeRewire,
    ourPhysicalTraceAnticommutator_normalizeRewire]

/-- The seven-field component of each physical adjacent placement retains its
three trace-rewire orbit terms. -/
theorem ourPhysicalTraceAnticommutator_fieldSevenFormula
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    exactFieldSevenProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)) =
      Finsupp.single physicalBaseOrbit 1 +
        Finsupp.single
          (physicalRewireOrbit
            (ourPhysicalTraceAnticommutatorSwapRewire left)) 1 -
          Finsupp.single
            (physicalRewireOrbit
              (ourPhysicalTraceAnticommutatorSplitRewire left)) 1 := by
  rw [ourPhysicalTraceAnticommutator_rowFormula]
  simp only [LinearMap.map_sub, LinearMap.map_add,
    exactFieldSevenProjection_sevenTarget_single]

/-- The trace-blind derivative-axis coordinate of each physical adjacent row
is the common source weight divided by the Reynolds group order. -/
theorem ourPhysicalTraceAnticommutator_derivativeAxisCoordinate
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourDerivativeAxisCoordinate [0, 2]
      (sectorFieldOrbitReynolds 7 2
        (exactFieldSevenProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single
              (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)))) =
      physicalBaseDerivativeAxisSignedWeight / 384 := by
  rw [ourPhysicalTraceAnticommutator_fieldSevenFormula]
  simp only [LinearMap.map_sub, LinearMap.map_add]
  rw [physicalBase_derivativeAxisCoordinate,
    physicalRewire_derivativeAxisCoordinate,
    physicalRewire_derivativeAxisCoordinate,
    physicalRewire_derivativeAxisSignedWeight,
    physicalRewire_derivativeAxisSignedWeight]
  ring

/-- The common physical source derivative-axis weight is the existing exact
finite value `32`. -/
theorem physicalBaseDerivativeAxisSignedWeight_eq_32 :
    physicalBaseDerivativeAxisSignedWeight = 32 := by
  exact source_signedAxisWeight

/-- The common physical source original plane-pair weight is zero. -/
theorem physicalBaseIBPAxisPlanePairSignedWeight_eq_zero :
    physicalBaseIBPAxisPlanePairSignedWeight = 0 := by
  exact source_ourIBPAxisPlanePairSignedWeight

/-- The common physical source third plane-pair weight is zero. -/
theorem physicalBaseThirdIBPAxisPlanePairSignedWeight_eq_zero :
    physicalBaseThirdIBPAxisPlanePairSignedWeight = 0 := by
  exact source_ourThirdIBPAxisPlanePairSignedWeight

/-- The trace-blind original plane-pair coordinate of each physical adjacent
row is its common source weight divided by the Reynolds group order. -/
theorem ourPhysicalTraceAnticommutator_IBPAxisPlanePairCoordinate
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (exactFieldSevenProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single
              (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)))) =
      physicalBaseIBPAxisPlanePairSignedWeight / 384 := by
  rw [ourPhysicalTraceAnticommutator_fieldSevenFormula]
  simp only [LinearMap.map_sub, LinearMap.map_add]
  rw [physicalBase_IBPAxisPlanePairCoordinate,
    physicalRewire_IBPAxisPlanePairCoordinate,
    physicalRewire_IBPAxisPlanePairCoordinate,
    physicalRewire_IBPAxisPlanePairSignedWeight,
    physicalRewire_IBPAxisPlanePairSignedWeight]
  ring

/-- The trace-blind third plane-pair coordinate of each physical adjacent row
is its common source weight divided by the Reynolds group order. -/
theorem ourPhysicalTraceAnticommutator_thirdIBPAxisPlanePairCoordinate
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourThirdIBPAxisPlanePairCoordinate
      (sectorFieldOrbitReynolds 7 2
        (exactFieldSevenProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single
              (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)))) =
      physicalBaseThirdIBPAxisPlanePairSignedWeight / 384 := by
  rw [ourPhysicalTraceAnticommutator_fieldSevenFormula]
  simp only [LinearMap.map_sub, LinearMap.map_add]
  rw [physicalBase_thirdIBPAxisPlanePairCoordinate,
    physicalRewire_thirdIBPAxisPlanePairCoordinate,
    physicalRewire_thirdIBPAxisPlanePairCoordinate,
    physicalRewire_thirdIBPAxisPlanePairSignedWeight,
    physicalRewire_thirdIBPAxisPlanePairSignedWeight]
  ring

/-- OUR alternating trace-cycle-profile gate on one physical adjacent
trace-anticommutator row. -/
def ourPhysicalTraceAnticommutatorProfileValue
    (left : OurPhysicalTraceAnticommutatorLabel) : ℚ :=
  physicalTraceCycleProfileGate physicalBaseLabeled.trace +
    physicalTraceCycleProfileGate
      (physicalRewireLabeled
        (ourPhysicalTraceAnticommutatorSwapRewire left)).trace -
      physicalTraceCycleProfileGate
        (physicalRewireLabeled
          (ourPhysicalTraceAnticommutatorSplitRewire left)).trace

/-- The profile-axis coordinate of each physical adjacent row is its
alternating topology gate divided by the Reynolds normalization. -/
theorem ourPhysicalTraceAnticommutator_profileCoordinate
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourTraceCycleProfileAxisCoordinate
      (sectorFieldOrbitReynolds 7 2
        (exactFieldSevenProjection
          (orbitPhysicalRelationOperator policy
            (Finsupp.single
              (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)))) =
      ourPhysicalTraceAnticommutatorProfileValue left / 12 := by
  rw [ourPhysicalTraceAnticommutator_fieldSevenFormula]
  simp only [LinearMap.map_sub, LinearMap.map_add]
  rw [physicalBase_profileCoordinate,
    physicalRewire_profileCoordinate,
    physicalRewire_profileCoordinate]
  unfold ourPhysicalTraceAnticommutatorProfileValue
  ring

set_option maxRecDepth 100000 in
/-- A kernel-reduced finite replay over all seven adjacent placements gives
the common negative-half profile value. -/
theorem ourPhysicalTraceAnticommutatorProfileValue_eq_neg_half
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourPhysicalTraceAnticommutatorProfileValue left = -1 / 2 := by
  fin_cases left <;> decide +kernel

/-- The first invariant coordinate has the common residual `1 / 2` on every
physical adjacent placement. -/
theorem ourInvariantSevenAxisCoordinate_physicalTraceAnticommutator
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourInvariantSevenAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)) =
      1 / 2 := by
  unfold ourInvariantSevenAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    ourPhysicalTraceAnticommutator_derivativeAxisCoordinate,
    physicalBaseDerivativeAxisSignedWeight_eq_32]
  norm_num

/-- The second invariant coordinate vanishes on every physical adjacent
placement. -/
theorem ourInvariantIBPAxisCoordinate_physicalTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourInvariantIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)) = 0 := by
  unfold ourInvariantIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    ourPhysicalTraceAnticommutator_IBPAxisPlanePairCoordinate,
    physicalBaseIBPAxisPlanePairSignedWeight_eq_zero]
  norm_num

/-- The third invariant coordinate vanishes on every physical adjacent
placement. -/
theorem ourInvariantThirdIBPAxisCoordinate_physicalTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourInvariantThirdIBPAxisCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)) = 0 := by
  unfold ourInvariantThirdIBPAxisCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    ourPhysicalTraceAnticommutator_thirdIBPAxisPlanePairCoordinate,
    physicalBaseThirdIBPAxisPlanePairSignedWeight_eq_zero]
  norm_num

/-- The eight-field trace projection vanishes on every entirely seven-field
physical adjacent row. -/
theorem exactFieldEightTraceProjection_physicalTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)) = 0 := by
  change exactFieldEightTraceClassMap
    (exactFieldEightProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1))) = 0
  rw [ourPhysicalTraceAnticommutator_rowFormula]
  simp only [LinearMap.map_sub, LinearMap.map_add,
    exactFieldEightProjection_sevenTarget_single]
  simp

/-- The separate three-coordinate correction retains the common
`1 / 2` incoming trace-class residual on every physical adjacent placement. -/
theorem ourThreeCoordinateInvariantTraceOrderCorrection_physicalTraceAnticommutator
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourThreeCoordinateInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)) =
      (1 / 2 : ℚ) • literalIncomingCommutatorClass := by
  unfold ourThreeCoordinateInvariantTraceOrderCorrection
    ourThirdInvariantTraceContribution
    ourTwoCoordinateInvariantTraceOrderCorrection
    ourTwoCoordinateInvariantSevenTraceCompensator
    ourTwoCoordinateInvariantSevenAxisCoordinate
  simp only [LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply]
  rw [ourInvariantSevenAxisCoordinate_physicalTraceAnticommutator,
    ourInvariantIBPAxisCoordinate_physicalTraceAnticommutator_zero,
    exactFieldEightTraceProjection_physicalTraceAnticommutator_zero,
    ourInvariantThirdIBPAxisCoordinate_physicalTraceAnticommutator_zero]
  simp

/-- The invariant profile coordinate has value `-1 / 2` on every physical
adjacent placement. -/
theorem ourInvariantTraceCycleProfileCoordinate_physicalTraceAnticommutator
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourInvariantTraceCycleProfileCoordinate
      (orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)) =
      -1 / 2 := by
  unfold ourInvariantTraceCycleProfileCoordinate
  simp only [LinearMap.smul_apply, LinearMap.comp_apply]
  rw [exactFieldSevenProjection_exactFieldOrbitReynolds,
    ourPhysicalTraceAnticommutator_profileCoordinate,
    ourPhysicalTraceAnticommutatorProfileValue_eq_neg_half]
  norm_num

/-- The full current cycle-profile correction cancels on every actual
physical adjacent trace-anticommutator row. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutator_row_zero
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)) = 0 := by
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [ourThreeCoordinateInvariantTraceOrderCorrection_physicalTraceAnticommutator,
    ourInvariantTraceCycleProfileCoordinate_physicalTraceAnticommutator]
  module

/-- OUR free finite cochain module on all seven physical adjacent
trace-anticommutator placements. -/
abbrev OurPhysicalTraceAnticommutatorCochainSpace :=
  OurPhysicalTraceAnticommutatorLabel →₀ ℚ

/-- The finite adjacent-placement cochains embed in the actual physical
`F,D`/IBP source. -/
def ourPhysicalTraceAnticommutatorCochainEmbedding
    (policy : PhysicalRelationPolicy) :
    OurPhysicalTraceAnticommutatorCochainSpace →ₗ[ℚ]
      OurFDIBPCochainSpace policy :=
  Finsupp.lmapDomain ℚ ℚ
    (ourPhysicalTraceAnticommutatorGeneratorAt policy)

/-- Distinct adjacent labels give distinct actual physical generators. -/
theorem ourPhysicalTraceAnticommutatorGeneratorAt_injective
    (policy : PhysicalRelationPolicy) :
    Function.Injective (ourPhysicalTraceAnticommutatorGeneratorAt policy) := by
  intro left right h
  have hsite : ourPhysicalTraceAnticommutatorSite left =
      ourPhysicalTraceAnticommutatorSite right := by
    injection h
  exact congrArg TraceAnticommutatorSite.left hsite

/-- OUR finite cochain embedding preserves all seven physical source
coordinates. -/
theorem ourPhysicalTraceAnticommutatorCochainEmbedding_injective
    (policy : PhysicalRelationPolicy) :
    Function.Injective (ourPhysicalTraceAnticommutatorCochainEmbedding policy) := by
  intro first second h
  change Finsupp.mapDomain (ourPhysicalTraceAnticommutatorGeneratorAt policy)
      first = Finsupp.mapDomain
        (ourPhysicalTraceAnticommutatorGeneratorAt policy) second at h
  exact Finsupp.mapDomain_injective
    (ourPhysicalTraceAnticommutatorGeneratorAt_injective policy) h

/-- OUR finite physical adjacent trace family transported into the honest
coordinate-free joint relation submodule. -/
def ourPhysicalTraceAnticommutatorToJointRelation
    (policy : PhysicalRelationPolicy) :
    OurPhysicalTraceAnticommutatorCochainSpace →ₗ[ℚ]
      jointInvariantRelationSubmodule policy :=
  (ourFDIBPCochainToJointRelation policy).comp
    (ourPhysicalTraceAnticommutatorCochainEmbedding policy)

@[simp] theorem ourPhysicalTraceAnticommutatorCochainEmbedding_single
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) (coefficient : ℚ) :
    ourPhysicalTraceAnticommutatorCochainEmbedding policy
      (Finsupp.single left coefficient) =
      Finsupp.single
        (ourPhysicalTraceAnticommutatorGeneratorAt policy left) coefficient := by
  simp [ourPhysicalTraceAnticommutatorCochainEmbedding]

/-- On a basis label, OUR finite family map is exactly the signed-Reynolds
average of its actual physical trace row. -/
theorem ourPhysicalTraceAnticommutatorToJointRelation_single_val
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ((ourPhysicalTraceAnticommutatorToJointRelation policy
      (Finsupp.single left 1)).1).1 =
      exactFieldOrbitReynolds
        (orbitPhysicalRelationOperator policy
          (Finsupp.single
            (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)) := by
  change ((ourFDIBPCochainToJointRelation policy
    (ourPhysicalTraceAnticommutatorCochainEmbedding policy
      (Finsupp.single left 1))).1).1 = _
  rw [ourPhysicalTraceAnticommutatorCochainEmbedding_single]
  exact ourFDIBPCochainToJointRelation_val policy
    (Finsupp.single
      (ourPhysicalTraceAnticommutatorGeneratorAt policy left) 1)

/-- The full current correction vanishes on each signed-Reynolds averaged
basis row of OUR physical adjacent trace family. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutatorSingle_zero
    (policy : PhysicalRelationPolicy)
    (left : OurPhysicalTraceAnticommutatorLabel) :
    ourCycleProfileInvariantTraceOrderCorrection
      ((ourPhysicalTraceAnticommutatorToJointRelation policy
        (Finsupp.single left 1)).1).1 = 0 := by
  rw [ourPhysicalTraceAnticommutatorToJointRelation_single_val]
  unfold ourCycleProfileInvariantTraceOrderCorrection
    ourTraceCycleProfileInvariantTraceContribution
  simp only [LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [ourThreeCoordinateInvariantTraceOrderCorrection_exactFieldOrbitReynolds,
    ourInvariantTraceCycleProfileCoordinate_exactFieldOrbitReynolds,
    ourThreeCoordinateInvariantTraceOrderCorrection_physicalTraceAnticommutator,
    ourInvariantTraceCycleProfileCoordinate_physicalTraceAnticommutator]
  module

/-- The complete finite physical adjacent trace-anticommutator cochain family
maps into the kernel of OUR full current cycle-profile correction. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutator_zero
    (policy : PhysicalRelationPolicy)
    (cochain : OurPhysicalTraceAnticommutatorCochainSpace) :
    ourCycleProfileInvariantTraceOrderCorrection
      ((ourPhysicalTraceAnticommutatorToJointRelation policy cochain).1).1 = 0 := by
  let combined := ourCycleProfileInvariantTraceOrderCorrection.comp
    (exactFieldOrbitInvariantSubmodule.subtype.comp
      ((jointInvariantRelationSubmodule policy).subtype.comp
        (ourPhysicalTraceAnticommutatorToJointRelation policy)))
  set_option maxRecDepth 100000 in
    change combined cochain = 0
    induction cochain using Finsupp.induction_linear with
    | zero => simp [combined]
    | add left right hleft hright => simp [map_add, hleft, hright]
    | single left coefficient =>
        rw [show Finsupp.single left coefficient =
            coefficient • Finsupp.single left 1 by simp]
        simp only [map_smul]
        change coefficient •
          (ourCycleProfileInvariantTraceOrderCorrection
            ((ourPhysicalTraceAnticommutatorToJointRelation policy
              (Finsupp.single left 1)).1).1) = 0
        rw [ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutatorSingle_zero]
        simp

#print axioms ourPhysicalTraceAnticommutator_rowFormula
#print axioms ourPhysicalTraceAnticommutatorProfileValue_eq_neg_half
#print axioms ourThreeCoordinateInvariantTraceOrderCorrection_physicalTraceAnticommutator
#print axioms ourInvariantTraceCycleProfileCoordinate_physicalTraceAnticommutator
#print axioms ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutator_row_zero
#print axioms ourPhysicalTraceAnticommutatorGeneratorAt_injective
#print axioms ourPhysicalTraceAnticommutatorCochainEmbedding_injective
#print axioms ourPhysicalTraceAnticommutatorToJointRelation_single_val
#print axioms ourCycleProfileInvariantTraceOrderCorrection_physicalTraceAnticommutatorSingle_zero

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceAnticommutatorPhysicalFamily
