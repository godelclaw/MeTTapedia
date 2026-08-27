import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceInvariantWitness

/-!
# OUR physical lift of derivative-free field-eight trace rows

The derivative-free eight-field trace census is written on its own labeled
orbit carrier, while the coordinate-free joint quotient takes the invariant
part of the full physical relation range.  This module constructs OUR
canonical full-carrier representatives of the three derivative-free trace
schemas and proves that the actual physical operator sends each one to the
corresponding embedded eight-field orbit row.

Thus the finite field-eight trace certificates can be transferred only after
their rows have been identified with genuine physical generators.  This module
does not assert a complete joint relation rank, a quotient dimension, or a
conditioning bound.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalLift

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceProjection
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceInvariantWitness
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16IBPTraceRelations

/-- OUR canonical full relation carrier for a derivative-free labeled
eight-field sector. -/
def ourFieldEightTraceRelationCarrier (sector : LabeledLocalWordSector 8 0) :
    RelationCarrier :=
  canonicalExactContextualCarrier
    ⟨ourEightFieldCount,
      (orientedLocalSectorEquivLabeled 8 0).symm sector⟩

/-- OUR exact oriented target underlying the canonical field-eight relation
carrier. -/
def ourFieldEightTraceOrientedTarget (sector : LabeledLocalWordSector 8 0) :
    ExactOrientedLocalCarrier :=
  ⟨ourEightFieldCount,
    (orientedLocalSectorEquivLabeled 8 0).symm sector⟩

/-- OUR canonical carrier normalizes to its stated exact oriented target. -/
theorem ourNormalizeFieldEightTraceRelationCarrier
    (sector : LabeledLocalWordSector 8 0) :
    normalizeExactContextualBasis (ourFieldEightTraceRelationCarrier sector) =
      Finsupp.single (ourFieldEightTraceOrientedTarget sector) 1 := by
  change normalizeExactContextualBasis
      (canonicalExactContextualCarrier (ourFieldEightTraceOrientedTarget sector)) = _
  rw [normalizeExactContextualBasis_eq_fiberEmbed]
  change exactTargetFiberEmbed ourEightFieldCount
      (normalizeContextualBasis
        (canonicalContextualSector
          ((orientedLocalSectorEquivLabeled 8 0).symm sector))) = _
  rw [normalizeContextualBasis_canonical, exactTargetFiberEmbed_single]
  simp [exactTargetFiberEmbedBasis, ourFieldEightTraceOrientedTarget]

/-- OUR exact oriented target has the expected eight-field relabel orbit. -/
theorem ourExactFieldRelabelOrbitOfFieldEightTraceTarget
    (sector : LabeledLocalWordSector 8 0) :
    exactFieldRelabelOrbitOfOriented (ourFieldEightTraceOrientedTarget sector) =
      fieldEightExactCarrier (Quotient.mk _ sector) := by
  change (⟨(8 : Fin 9),
      Quotient.mk _
        ((orientedLocalSectorEquivLabeled 8 0)
          ((orientedLocalSectorEquivLabeled 8 0).symm sector))⟩ :
        ExactFieldRelabelOrbitCarrier) =
    ⟨(8 : Fin 9), Quotient.mk _ sector⟩
  congr 1
  exact congrArg (fun value : LabeledLocalWordSector 8 0 => Quotient.mk _ value)
    ((orientedLocalSectorEquivLabeled 8 0).apply_symm_apply sector)

/-- OUR field-relabel normalization of the canonical field-eight target is
the embedded field-eight orbit basis row. -/
theorem ourNormalizeExactFieldRelabelFieldEightTraceTarget
    (sector : LabeledLocalWordSector 8 0) :
    normalizeExactFieldRelabel
      (Finsupp.single (ourFieldEightTraceOrientedTarget sector) 1) =
      fieldEightExactEmbed (fieldEightOrbitSingle sector) := by
  rw [normalizeExactFieldRelabel_single]
  simp only [one_smul, normalizeExactFieldRelabelBasis,
    ourExactFieldRelabelOrbitOfFieldEightTraceTarget,
    fieldEightOrbitSingle, fieldEightExactEmbed_single]

/-- OUR basis-level form of the field-relabel normalization bridge. -/
theorem ourNormalizeExactFieldRelabelBasisFieldEightTraceTarget
    (sector : LabeledLocalWordSector 8 0) :
    normalizeExactFieldRelabelBasis (ourFieldEightTraceOrientedTarget sector) =
      fieldEightExactEmbed (fieldEightOrbitSingle sector) := by
  change Finsupp.single
      (exactFieldRelabelOrbitOfOriented (ourFieldEightTraceOrientedTarget sector)) 1 =
    fieldEightExactEmbed (Finsupp.single (Quotient.mk _ sector) 1)
  rw [ourExactFieldRelabelOrbitOfFieldEightTraceTarget,
    fieldEightExactEmbed_single]

/-- OUR canonical carrier commutes with literal replacement of its trace
permutation. -/
theorem ourSetTraceOrderFieldEightTraceRelationCarrier
    (sector : LabeledLocalWordSector 8 0)
    (traceOrder : Equiv.Perm (Fin 8)) :
    setTraceOrder (ourFieldEightTraceRelationCarrier sector) traceOrder =
      ourFieldEightTraceRelationCarrier
        (setFieldEightTraceOrder sector traceOrder) := by
  rfl

@[simp] theorem ourFieldEightTraceRelationCarrier_traceOrder
    (sector : LabeledLocalWordSector 8 0) :
    (ourFieldEightTraceRelationCarrier sector).2.trace.traceOrder = sector.trace := by
  rfl

/-- OUR lift of a derivative-free field-eight trace schema to an actual
physical relation generator. -/
def ourLiftFieldEightTraceGenerator
    (policy : PhysicalRelationPolicy) :
    FieldEightTraceGenerator → PhysicalRelationGenerator policy
  | .traceless site =>
      .traceless (ourFieldEightTraceRelationCarrier site.sector) site.field (by
        change site.sector.trace site.field = site.field
        exact site.singleton)
  | .anticommutator site =>
      .traceAnticommutator (ourFieldEightTraceRelationCarrier site.sector)
        { left := site.left
          cycleLength_ge_three := by
            change site.sector.trace (site.sector.trace site.left) ≠ site.left
            exact site.cycleLength_ge_three }
  | .fundamental site =>
      .fundamentalTrace (ourFieldEightTraceRelationCarrier site.sector)
        { label := site.label }

/-- OUR lifted traceless generator has exactly its intended eight-field
physical orbit row. -/
theorem ourOrbitPhysicalRelationOperator_lift_traceless
    (policy : PhysicalRelationPolicy) (site : FieldEightTracelessSite) :
    orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourLiftFieldEightTraceGenerator policy (.traceless site)) 1) =
      fieldEightExactEmbed
        (fieldEightPhysicalTraceRow (.traceless site)) := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp only [one_smul, physicalRelationRow,
    ourLiftFieldEightTraceGenerator, tracelessLetterRow,
    normalizeExactContextual_single, ourNormalizeFieldEightTraceRelationCarrier,
    normalizeExactFieldRelabel_single, one_smul,
    normalizeExactFieldRelabelBasis,
    ourExactFieldRelabelOrbitOfFieldEightTraceTarget,
    fieldEightPhysicalTraceRow, fieldEightOrbitSingle,
    fieldEightExactEmbed_single]

/-- OUR lifted fundamental trace generator has exactly its intended
eight-field physical orbit row. -/
theorem ourOrbitPhysicalRelationOperator_lift_fundamental
    (policy : PhysicalRelationPolicy) (site : FieldEightFundamentalSite) :
    orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourLiftFieldEightTraceGenerator policy (.fundamental site)) 1) =
      fieldEightExactEmbed
        (fieldEightPhysicalTraceRow (.fundamental site)) := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp [physicalRelationRow, ourLiftFieldEightTraceGenerator,
    fundamentalTraceRow, rewireTraceCarrier,
    ourFieldEightTraceRelationCarrier_traceOrder,
    ourSetTraceOrderFieldEightTraceRelationCarrier,
    normalizeExactContextual_single, ourNormalizeFieldEightTraceRelationCarrier,
    LinearMap.map_add, LinearMap.map_sub,
    ourNormalizeExactFieldRelabelBasisFieldEightTraceTarget,
    fieldEightPhysicalTraceRow,
    FundamentalTraceSite.first, FundamentalTraceSite.second,
    FundamentalTraceSite.third, fundamentalCycleForward,
    fundamentalCycleBackward, fieldEightFundamentalCycleForward,
    fieldEightFundamentalCycleBackward]
  rfl

/-- OUR lifted trace-anticommutator generator has exactly its intended
eight-field physical orbit row. -/
theorem ourOrbitPhysicalRelationOperator_lift_anticommutator
    (policy : PhysicalRelationPolicy) (site : FieldEightAnticommutatorSite) :
    orbitPhysicalRelationOperator policy
        (Finsupp.single
          (ourLiftFieldEightTraceGenerator policy (.anticommutator site)) 1) =
      fieldEightExactEmbed
        (fieldEightPhysicalTraceRow (.anticommutator site)) := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  simp [physicalRelationRow, ourLiftFieldEightTraceGenerator,
    traceAnticommutatorRow, swapAdjacentTraceCarrier,
    splitAdjacentTraceCarrier, swapAdjacentTraceOrder,
    splitAdjacentTraceOrder,
    ourFieldEightTraceRelationCarrier_traceOrder,
    ourSetTraceOrderFieldEightTraceRelationCarrier,
    normalizeExactContextual_single, ourNormalizeFieldEightTraceRelationCarrier,
    LinearMap.map_add, LinearMap.map_sub,
    ourNormalizeExactFieldRelabelBasisFieldEightTraceTarget,
    fieldEightPhysicalTraceRow, TraceAnticommutatorSite.right,
    TraceAnticommutatorSite.successor, fieldEightSwapAdjacentTraceOrder,
    fieldEightSplitAdjacentTraceOrder]
  rfl

/-- Every OUR lifted derivative-free eight-field trace generator has exactly
its intended image under the full physical orbit operator. -/
theorem ourOrbitPhysicalRelationOperator_lift
    (policy : PhysicalRelationPolicy) (generator : FieldEightTraceGenerator) :
    orbitPhysicalRelationOperator policy
        (Finsupp.single (ourLiftFieldEightTraceGenerator policy generator) 1) =
      fieldEightExactEmbed (fieldEightPhysicalTraceRow generator) := by
  cases generator with
  | traceless site =>
      exact ourOrbitPhysicalRelationOperator_lift_traceless policy site
  | anticommutator site =>
      exact ourOrbitPhysicalRelationOperator_lift_anticommutator policy site
  | fundamental site =>
      exact ourOrbitPhysicalRelationOperator_lift_fundamental policy site

#print axioms ourNormalizeFieldEightTraceRelationCarrier
#print axioms ourSetTraceOrderFieldEightTraceRelationCarrier
#print axioms ourOrbitPhysicalRelationOperator_lift_traceless
#print axioms ourOrbitPhysicalRelationOperator_lift_fundamental
#print axioms ourOrbitPhysicalRelationOperator_lift_anticommutator
#print axioms ourOrbitPhysicalRelationOperator_lift

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16FieldEightTracePhysicalLift
