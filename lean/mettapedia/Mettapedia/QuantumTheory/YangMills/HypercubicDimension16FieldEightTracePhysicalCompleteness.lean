import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16WilsonTraceOrderCycleProfileBandReduction
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalLift

/-!
# OUR arbitrary-carrier boundary for derivative-free field-eight traces

At canonical dimension sixteen, a source with eight field strengths has no
derivatives.  This module identifies every actual physical relation column in
that source band with OUR existing derivative-free field-eight trace schemas.
The transport first replaces the proof-carrying `Fin 9` representative of
eight by the literal index `8`; this makes the dependent trace rewires
definitionally visible to the kernel.

The result is a source-band statement only.  It does not assert a complete
relation census, a quotient dimension, or joint conditioning for the full
invariant quotient.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalCompleteness

open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16IBPTraceRelations
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16FieldEightTracePhysicalLift
open HypercubicDimension16WilsonTraceOrderCycleProfileRepair
open HypercubicDimension16WilsonTraceOrderCycleProfileBandReduction
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceProjection

private abbrev ourLiteralEightCarrier
    (sector : DerivativeAlphaReducedSector 8 0) : RelationCarrier :=
  ⟨(8 : Fin 9), sector⟩

private theorem ourLiteralEightNormalizeBasis
    (target : OrientedLocalSector 8 0) :
    normalizeExactFieldRelabelBasis
      (⟨(8 : Fin 9), target⟩ : ExactOrientedLocalCarrier) =
      fieldEightExactEmbed
        (fieldEightOrbitSingle
          ((orientedLocalSectorEquivLabeled 8 0) target)) := by
  change Finsupp.single
      (exactFieldRelabelOrbitOfOriented
        (⟨(8 : Fin 9), target⟩ : ExactOrientedLocalCarrier)) 1 =
    fieldEightExactEmbed
      (Finsupp.single
        (Quotient.mk _ ((orientedLocalSectorEquivLabeled 8 0) target)) 1)
  rw [fieldEightExactEmbed_single]
  rfl

private theorem ourLiteralEightNormalize
    (sector : DerivativeAlphaReducedSector 8 0) :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis (ourLiteralEightCarrier sector)) =
      fieldAxisOrientationCoefficient (sectorFieldAxisAssignment sector) •
        fieldEightExactEmbed
          (fieldEightOrbitSingle
            ((orientedLocalSectorEquivLabeled 8 0)
              (normalizedSectorData sector))) := by
  change normalizeExactFieldRelabel
      (normalizeExactContextualBasis (⟨(8 : Fin 9), sector⟩ : RelationCarrier)) = _
  rw [show normalizeExactContextualBasis
      (⟨(8 : Fin 9), sector⟩ : RelationCarrier) =
      fieldAxisOrientationCoefficient (sectorFieldAxisAssignment sector) •
        Finsupp.single
          (⟨(8 : Fin 9), normalizedSectorData sector⟩ :
            ExactOrientedLocalCarrier) 1 by rfl,
    LinearMap.map_smul,
    normalizeExactFieldRelabel_single]
  simp only [one_smul]
  exact congrArg
    (fun output : ExactFieldRelabelOrbitSpace =>
      fieldAxisOrientationCoefficient (sectorFieldAxisAssignment sector) • output)
    (ourLiteralEightNormalizeBasis (normalizedSectorData sector))

private theorem ourLiteralEightNormalize_setTraceOrder
    (sector : DerivativeAlphaReducedSector 8 0)
    (traceOrder : Equiv.Perm (Fin 8)) :
    normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (setTraceOrder (ourLiteralEightCarrier sector) traceOrder)) =
      fieldAxisOrientationCoefficient
        (sectorFieldAxisAssignment
          (setTraceOrder (ourLiteralEightCarrier sector) traceOrder).2) •
        fieldEightExactEmbed
          (fieldEightOrbitSingle
            ((orientedLocalSectorEquivLabeled 8 0)
              (normalizedSectorData
                (setTraceOrder (ourLiteralEightCarrier sector) traceOrder).2))) := by
  change normalizeExactFieldRelabel
      (normalizeExactContextualBasis
        (ourLiteralEightCarrier
          (setTraceOrder (ourLiteralEightCarrier sector) traceOrder).2)) = _
  exact ourLiteralEightNormalize
    (setTraceOrder (ourLiteralEightCarrier sector) traceOrder).2

private theorem ourLiteralEightFieldAxis_setTraceOrder
    (sector : DerivativeAlphaReducedSector 8 0)
    (traceOrder : Equiv.Perm (Fin 8)) :
    fieldAxisOrientationCoefficient
      (sectorFieldAxisAssignment
        (setTraceOrder (ourLiteralEightCarrier sector) traceOrder).2) =
      fieldAxisOrientationCoefficient (sectorFieldAxisAssignment sector) := by
  rfl

private theorem ourLiteralEightLabeled_setTraceOrder
    (sector : DerivativeAlphaReducedSector 8 0)
    (traceOrder : Equiv.Perm (Fin 8)) :
    (orientedLocalSectorEquivLabeled 8 0)
      (normalizedSectorData
        (setTraceOrder (ourLiteralEightCarrier sector) traceOrder).2) =
      setFieldEightTraceOrder
        ((orientedLocalSectorEquivLabeled 8 0) (normalizedSectorData sector))
        traceOrder := by
  rfl

private def ourLiteralEightAnticommutatorSite
    (sector : DerivativeAlphaReducedSector 8 0)
    (site : TraceAnticommutatorSite (ourLiteralEightCarrier sector)) :
    FieldEightAnticommutatorSite where
  sector := (orientedLocalSectorEquivLabeled 8 0) (normalizedSectorData sector)
  left := site.left
  cycleLength_ge_three := site.cycleLength_ge_three

private theorem ourLiteralEightOrbitAnticommutator
    (policy : PhysicalRelationPolicy)
    (sector : DerivativeAlphaReducedSector 8 0)
    (site : TraceAnticommutatorSite (ourLiteralEightCarrier sector)) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (.traceAnticommutator (ourLiteralEightCarrier sector) site) 1) =
      fieldAxisOrientationCoefficient (sectorFieldAxisAssignment sector) •
        fieldEightExactEmbed
          (fieldEightPhysicalTraceRow
            (.anticommutator (ourLiteralEightAnticommutatorSite sector site))) := by
  change TraceAnticommutatorSite
    (⟨(8 : Fin 9), sector⟩ : RelationCarrier) at site
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, physicalRelationRow, traceAnticommutatorRow,
    LinearMap.map_sub, LinearMap.map_add,
    normalizeExactContextual_single]
  change normalizeExactFieldRelabel
      (normalizeExactContextualBasis (ourLiteralEightCarrier sector)) +
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (setTraceOrder (ourLiteralEightCarrier sector)
            (swapAdjacentTraceOrder site))) -
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (setTraceOrder (ourLiteralEightCarrier sector)
            (splitAdjacentTraceOrder site))) = _
  rw [ourLiteralEightNormalize sector,
    ourLiteralEightNormalize_setTraceOrder
      sector (swapAdjacentTraceOrder site),
    ourLiteralEightNormalize_setTraceOrder
      sector (splitAdjacentTraceOrder site)]
  rw [ourLiteralEightFieldAxis_setTraceOrder
      sector (swapAdjacentTraceOrder site),
    ourLiteralEightFieldAxis_setTraceOrder
      sector (splitAdjacentTraceOrder site),
    ourLiteralEightLabeled_setTraceOrder
      sector (swapAdjacentTraceOrder site),
    ourLiteralEightLabeled_setTraceOrder
      sector (splitAdjacentTraceOrder site)]
  simp only [ourLiteralEightAnticommutatorSite, fieldEightPhysicalTraceRow]
  simp [orientedLocalSectorEquivLabeled, normalizedSectorData,
    TraceAnticommutatorSite.right, TraceAnticommutatorSite.successor,
    fieldEightSwapAdjacentTraceOrder, fieldEightSplitAdjacentTraceOrder,
    swapAdjacentTraceOrder, splitAdjacentTraceOrder,
    smul_add, smul_sub]
  rfl

private def ourLiteralEightFundamentalSite
    (sector : DerivativeAlphaReducedSector 8 0)
    (site : FundamentalTraceSite (ourLiteralEightCarrier sector)) :
    FieldEightFundamentalSite where
  sector := (orientedLocalSectorEquivLabeled 8 0) (normalizedSectorData sector)
  label := site.label

private theorem ourLiteralEightOrbitFundamental
    (policy : PhysicalRelationPolicy)
    (sector : DerivativeAlphaReducedSector 8 0)
    (site : FundamentalTraceSite (ourLiteralEightCarrier sector)) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (.fundamentalTrace (ourLiteralEightCarrier sector) site) 1) =
      fieldAxisOrientationCoefficient (sectorFieldAxisAssignment sector) •
        fieldEightExactEmbed
          (fieldEightPhysicalTraceRow
            (.fundamental (ourLiteralEightFundamentalSite sector site))) := by
  change FundamentalTraceSite
    (⟨(8 : Fin 9), sector⟩ : RelationCarrier) at site
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, physicalRelationRow, fundamentalTraceRow,
    LinearMap.map_sub, LinearMap.map_add,
    normalizeExactContextual_single]
  change normalizeExactFieldRelabel
      (normalizeExactContextualBasis (ourLiteralEightCarrier sector)) -
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (rewireTraceCarrier (ourLiteralEightCarrier sector)
            (Equiv.swap site.first site.second))) -
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (rewireTraceCarrier (ourLiteralEightCarrier sector)
            (Equiv.swap site.first site.third))) -
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (rewireTraceCarrier (ourLiteralEightCarrier sector)
            (Equiv.swap site.second site.third))) +
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (rewireTraceCarrier (ourLiteralEightCarrier sector)
            (fundamentalCycleForward site))) +
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (rewireTraceCarrier (ourLiteralEightCarrier sector)
            (fundamentalCycleBackward site))) = _
  rw [ourLiteralEightNormalize sector]
  change fieldAxisOrientationCoefficient (sectorFieldAxisAssignment sector) •
        fieldEightExactEmbed
          (fieldEightOrbitSingle
            ((orientedLocalSectorEquivLabeled 8 0)
              (normalizedSectorData sector))) -
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (ourLiteralEightCarrier
            (rewireTraceCarrier (ourLiteralEightCarrier sector)
              (Equiv.swap site.first site.second)).2)) -
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (ourLiteralEightCarrier
            (rewireTraceCarrier (ourLiteralEightCarrier sector)
              (Equiv.swap site.first site.third)).2)) -
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (ourLiteralEightCarrier
            (rewireTraceCarrier (ourLiteralEightCarrier sector)
              (Equiv.swap site.second site.third)).2)) +
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (ourLiteralEightCarrier
            (rewireTraceCarrier (ourLiteralEightCarrier sector)
              (fundamentalCycleForward site)).2)) +
      normalizeExactFieldRelabel
        (normalizeExactContextualBasis
          (ourLiteralEightCarrier
            (rewireTraceCarrier (ourLiteralEightCarrier sector)
              (fundamentalCycleBackward site)).2)) = _
  rw [ourLiteralEightNormalize
      (rewireTraceCarrier (ourLiteralEightCarrier sector)
        (Equiv.swap site.first site.second)).2,
    ourLiteralEightNormalize
      (rewireTraceCarrier (ourLiteralEightCarrier sector)
        (Equiv.swap site.first site.third)).2,
    ourLiteralEightNormalize
      (rewireTraceCarrier (ourLiteralEightCarrier sector)
        (Equiv.swap site.second site.third)).2,
    ourLiteralEightNormalize
      (rewireTraceCarrier (ourLiteralEightCarrier sector)
        (fundamentalCycleForward site)).2,
    ourLiteralEightNormalize
      (rewireTraceCarrier (ourLiteralEightCarrier sector)
        (fundamentalCycleBackward site)).2]
  simp only [ourLiteralEightFundamentalSite, fieldEightPhysicalTraceRow]
  simp [orientedLocalSectorEquivLabeled, normalizedSectorData,
    FundamentalTraceSite.first, FundamentalTraceSite.second,
    FundamentalTraceSite.third, fundamentalCycleForward,
    fundamentalCycleBackward, fieldEightFundamentalCycleForward,
    fieldEightFundamentalCycleBackward, rewireTraceCarrier, setTraceOrder,
    smul_add, smul_sub]
  rfl

/-- The shared proof-carrying field index used by OUR construction is the
literal eight index.  This equality transports dependent carrier data without
identifying distinct physical sectors. -/
theorem ourEightFieldCount_eq_literal : ourEightFieldCount = (8 : Fin 9) := by
  apply Fin.ext
  simp [ourEightFieldCount]

private def ourLiteralEightTracelessSite
    (sector : DerivativeAlphaReducedSector 8 0)
    (field : Fin 8)
    (singleton : IsSingletonTrace (ourLiteralEightCarrier sector) field) :
    FieldEightTracelessSite where
  sector := (orientedLocalSectorEquivLabeled 8 0) (normalizedSectorData sector)
  field := field
  singleton := singleton

private theorem ourLiteralEightOrbitTraceless
    (policy : PhysicalRelationPolicy)
    (sector : DerivativeAlphaReducedSector 8 0)
    (field : Fin 8)
    (singleton : IsSingletonTrace (ourLiteralEightCarrier sector) field) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (.traceless (ourLiteralEightCarrier sector) field singleton) 1) =
      fieldAxisOrientationCoefficient (sectorFieldAxisAssignment sector) •
        fieldEightExactEmbed
          (fieldEightPhysicalTraceRow
            (.traceless (ourLiteralEightTracelessSite sector field singleton))) := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, physicalRelationRow, tracelessLetterRow]
  rw [normalizeExactContextual_single]
  simp only [one_smul]
  rw [ourLiteralEightNormalize]
  simp only [ourLiteralEightTracelessSite, fieldEightPhysicalTraceRow]

/-- OUR field-eight traceless trace site obtained from an arbitrary actual
physical carrier. -/
def ourFieldEightTracelessSiteOfPhysical
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (singleton : IsSingletonTrace carrier field)
    (hfield : carrier.1 = ourEightFieldCount) :
    FieldEightTracelessSite := by
  rcases carrier with ⟨fieldCount, sector⟩
  cases hfield
  cases ourEightFieldCount_eq_literal
  exact ourLiteralEightTracelessSite sector field singleton

/-- OUR field-eight polarized trace-anticommutator site obtained from an
arbitrary actual physical carrier. -/
def ourFieldEightAnticommutatorSiteOfPhysical
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier)
    (hfield : carrier.1 = ourEightFieldCount) :
    FieldEightAnticommutatorSite := by
  rcases carrier with ⟨fieldCount, sector⟩
  cases hfield
  cases ourEightFieldCount_eq_literal
  exact ourLiteralEightAnticommutatorSite sector site

/-- OUR field-eight fundamental three-cut trace site obtained from an
arbitrary actual physical carrier. -/
def ourFieldEightFundamentalSiteOfPhysical
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier)
    (hfield : carrier.1 = ourEightFieldCount) :
    FieldEightFundamentalSite := by
  rcases carrier with ⟨fieldCount, sector⟩
  cases hfield
  cases ourEightFieldCount_eq_literal
  exact ourLiteralEightFundamentalSite sector site

/-- Every actual eight-field traceless row has the derivative-free
field-eight trace image, with its explicit orientation coefficient. -/
theorem orbitPhysicalRelationOperator_fieldEightTraceless
    (policy : PhysicalRelationPolicy)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (singleton : IsSingletonTrace carrier field)
    (hfield : carrier.1 = ourEightFieldCount) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (.traceless carrier field singleton) 1) =
      fieldAxisOrientationCoefficient (sectorFieldAxisAssignment carrier.2) •
        fieldEightExactEmbed
          (fieldEightPhysicalTraceRow
            (.traceless
              (ourFieldEightTracelessSiteOfPhysical carrier field singleton hfield))) := by
  rcases carrier with ⟨fieldCount, sector⟩
  cases hfield
  cases ourEightFieldCount_eq_literal
  exact ourLiteralEightOrbitTraceless policy sector field singleton

/-- Every actual eight-field polarized trace-anticommutator row has the
derivative-free field-eight trace image, with its explicit orientation
coefficient. -/
theorem orbitPhysicalRelationOperator_fieldEightAnticommutator
    (policy : PhysicalRelationPolicy)
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier)
    (hfield : carrier.1 = ourEightFieldCount) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (.traceAnticommutator carrier site) 1) =
      fieldAxisOrientationCoefficient (sectorFieldAxisAssignment carrier.2) •
        fieldEightExactEmbed
          (fieldEightPhysicalTraceRow
            (.anticommutator
              (ourFieldEightAnticommutatorSiteOfPhysical site hfield))) := by
  rcases carrier with ⟨fieldCount, sector⟩
  cases hfield
  cases ourEightFieldCount_eq_literal
  exact ourLiteralEightOrbitAnticommutator policy sector site

/-- Every actual eight-field fundamental three-cut row has the
derivative-free field-eight trace image, with its explicit orientation
coefficient. -/
theorem orbitPhysicalRelationOperator_fieldEightFundamental
    (policy : PhysicalRelationPolicy)
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier)
    (hfield : carrier.1 = ourEightFieldCount) :
    orbitPhysicalRelationOperator policy
      (Finsupp.single (.fundamentalTrace carrier site) 1) =
      fieldAxisOrientationCoefficient (sectorFieldAxisAssignment carrier.2) •
        fieldEightExactEmbed
          (fieldEightPhysicalTraceRow
            (.fundamental
              (ourFieldEightFundamentalSiteOfPhysical site hfield))) := by
  rcases carrier with ⟨fieldCount, sector⟩
  cases hfield
  cases ourEightFieldCount_eq_literal
  exact ourLiteralEightOrbitFundamental policy sector site

/-- OUR full profile correction annihilates every actual eight-field
traceless row. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_fieldEightTraceless_zero
    (policy : PhysicalRelationPolicy)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (singleton : IsSingletonTrace carrier field)
    (hfield : carrier.1 = ourEightFieldCount) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (.traceless carrier field singleton) 1)) = 0 := by
  rw [orbitPhysicalRelationOperator_fieldEightTraceless
    policy carrier field singleton hfield, LinearMap.map_smul]
  have hbase : ourCycleProfileInvariantTraceOrderCorrection
      (fieldEightExactEmbed
        (fieldEightPhysicalTraceRow
          (.traceless
            (ourFieldEightTracelessSiteOfPhysical carrier field singleton hfield)))) = 0 := by
    rw [← ourOrbitPhysicalRelationOperator_lift]
    exact ourCycleProfileInvariantTraceOrderCorrection_liftedTraceGenerator_zero
      policy (.traceless
        (ourFieldEightTracelessSiteOfPhysical carrier field singleton hfield))
  rw [hbase]
  simp

/-- OUR full profile correction annihilates every actual eight-field
trace-anticommutator row. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_fieldEightAnticommutator_zero
    (policy : PhysicalRelationPolicy)
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier)
    (hfield : carrier.1 = ourEightFieldCount) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (.traceAnticommutator carrier site) 1)) = 0 := by
  rw [orbitPhysicalRelationOperator_fieldEightAnticommutator
    policy site hfield, LinearMap.map_smul]
  have hbase : ourCycleProfileInvariantTraceOrderCorrection
      (fieldEightExactEmbed
        (fieldEightPhysicalTraceRow
          (.anticommutator
            (ourFieldEightAnticommutatorSiteOfPhysical site hfield)))) = 0 := by
    rw [← ourOrbitPhysicalRelationOperator_lift]
    exact ourCycleProfileInvariantTraceOrderCorrection_liftedTraceGenerator_zero
      policy (.anticommutator
        (ourFieldEightAnticommutatorSiteOfPhysical site hfield))
  rw [hbase]
  simp

/-- OUR full profile correction annihilates every actual eight-field
fundamental three-cut row. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_fieldEightFundamental_zero
    (policy : PhysicalRelationPolicy)
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier)
    (hfield : carrier.1 = ourEightFieldCount) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (.fundamentalTrace carrier site) 1)) = 0 := by
  rw [orbitPhysicalRelationOperator_fieldEightFundamental
    policy site hfield, LinearMap.map_smul]
  have hbase : ourCycleProfileInvariantTraceOrderCorrection
      (fieldEightExactEmbed
        (fieldEightPhysicalTraceRow
          (.fundamental
            (ourFieldEightFundamentalSiteOfPhysical site hfield)))) = 0 := by
    rw [← ourOrbitPhysicalRelationOperator_lift]
    exact ourCycleProfileInvariantTraceOrderCorrection_liftedTraceGenerator_zero
      policy (.fundamental
        (ourFieldEightFundamentalSiteOfPhysical site hfield))
  rw [hbase]
  simp

private theorem ourFieldEight_derivativeCount_zero
    (carrier : RelationCarrier) (hfield : carrier.1 = ourEightFieldCount) :
    dimension16DerivativeCount carrier.1 = 0 := by
  have hvalue : carrier.1.1 = ourEightFieldCount.1 :=
    congrArg Fin.val hfield
  simp [dimension16DerivativeCount, ourEightFieldCount, hvalue]

private theorem ourCycleProfileInvariantTraceOrderCorrection_scalar_of_unit_zero
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hunit : ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator 1)) = 0) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 := by
  rw [show Finsupp.single generator coefficient =
      coefficient • Finsupp.single generator 1 by simp]
  simp only [LinearMap.map_smul, hunit, smul_zero]

/-- OUR full profile correction annihilates every physical relation column
whose source carrier has exactly eight field strengths.  The derivative-bearing
families have no such sites; the remaining trace families are identified above
with the complete derivative-free field-eight trace schemas. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_eight
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hsource : physicalRelationGeneratorSourceFieldCount generator =
      ourEightFieldCount) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 := by
  apply ourCycleProfileInvariantTraceOrderCorrection_scalar_of_unit_zero
    policy generator coefficient
  cases generator with
  | antisymmetry carrier slot =>
      exact ourCycleProfileInvariantTraceOrderCorrection_antisymmetry_zero
        policy carrier slot 1
  | bianchi carrier field position innermost =>
      have hfield : carrier.1 = ourEightFieldCount := by
        simpa [physicalRelationGeneratorSourceFieldCount,
          physicalRelationGeneratorSourceCarrier] using hsource
      have hzero := ourFieldEight_derivativeCount_zero carrier hfield
      rw [hzero] at position
      exact Fin.elim0 position
  | eom enabled carrier field position innermost =>
      have hfield : carrier.1 = ourEightFieldCount := by
        simpa [physicalRelationGeneratorSourceFieldCount,
          physicalRelationGeneratorSourceCarrier] using hsource
      have hzero := ourFieldEight_derivativeCount_zero carrier hfield
      rw [hzero] at position
      exact Fin.elim0 position
  | integrationByParts carrier position outermost =>
      have hfield : carrier.1 = ourEightFieldCount := by
        simpa [physicalRelationGeneratorSourceFieldCount,
          physicalRelationGeneratorSourceCarrier] using hsource
      have hzero := ourFieldEight_derivativeCount_zero carrier hfield
      rw [hzero] at position
      exact Fin.elim0 position
  | traceless carrier field singleton =>
      have hfield : carrier.1 = ourEightFieldCount := by
        simpa [physicalRelationGeneratorSourceFieldCount,
          physicalRelationGeneratorSourceCarrier] using hsource
      exact ourCycleProfileInvariantTraceOrderCorrection_fieldEightTraceless_zero
        policy carrier field singleton hfield
  | covariantCommutator carrier site =>
      have hfield : carrier.1 = ourEightFieldCount := by
        simpa [physicalRelationGeneratorSourceFieldCount,
          physicalRelationGeneratorSourceCarrier] using hsource
      have hvalue : carrier.1.1 = 8 := by
        simpa [ourEightFieldCount] using congrArg Fin.val hfield
      have hlt : carrier.1.1 < 8 := site.fieldCount_lt_eight
      omega
  | traceAnticommutator carrier site =>
      have hfield : carrier.1 = ourEightFieldCount := by
        simpa [physicalRelationGeneratorSourceFieldCount,
          physicalRelationGeneratorSourceCarrier] using hsource
      exact ourCycleProfileInvariantTraceOrderCorrection_fieldEightAnticommutator_zero
        policy site hfield
  | fundamentalTrace carrier site =>
      have hfield : carrier.1 = ourEightFieldCount := by
        simpa [physicalRelationGeneratorSourceFieldCount,
          physicalRelationGeneratorSourceCarrier] using hsource
      exact ourCycleProfileInvariantTraceOrderCorrection_fieldEightFundamental_zero
        policy site hfield

/-- Apart from the six- and seven-field source bands, every physical
relation column is already annihilated by OUR profile correction.  This is a
finite source-index reduction, not a claim that either remaining band has
been classified. -/
theorem ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_not_six_or_seven
    (policy : PhysicalRelationPolicy)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hsix : physicalRelationGeneratorSourceFieldCount generator ≠ (6 : Fin 9))
    (hseven : physicalRelationGeneratorSourceFieldCount generator ≠ ourSevenFieldCount) :
    ourCycleProfileInvariantTraceOrderCorrection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient)) = 0 := by
  generalize hsource : physicalRelationGeneratorSourceFieldCount generator = source
  fin_cases source
  · apply ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_lt_six
      policy generator coefficient
    simp [hsource]
  · apply ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_lt_six
      policy generator coefficient
    simp [hsource]
  · apply ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_lt_six
      policy generator coefficient
    simp [hsource]
  · apply ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_lt_six
      policy generator coefficient
    simp [hsource]
  · apply ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_lt_six
      policy generator coefficient
    simp [hsource]
  · apply ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_lt_six
      policy generator coefficient
    simp [hsource]
  · exact False.elim (hsix (by simp [hsource]))
  · exact False.elim (hseven (by simp [hsource, ourSevenFieldCount]))
  · apply ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_eight
      policy generator coefficient
    simp [hsource, ourEightFieldCount]

#print axioms ourEightFieldCount_eq_literal
#print axioms ourFieldEightTracelessSiteOfPhysical
#print axioms ourFieldEightAnticommutatorSiteOfPhysical
#print axioms ourFieldEightFundamentalSiteOfPhysical
#print axioms orbitPhysicalRelationOperator_fieldEightTraceless
#print axioms orbitPhysicalRelationOperator_fieldEightAnticommutator
#print axioms orbitPhysicalRelationOperator_fieldEightFundamental
#print axioms ourCycleProfileInvariantTraceOrderCorrection_fieldEightTraceless_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_fieldEightAnticommutator_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_fieldEightFundamental_zero
#print axioms ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_eq_eight
#print axioms ourCycleProfileInvariantTraceOrderCorrection_physicalRelation_zero_of_source_not_six_or_seven

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalCompleteness
