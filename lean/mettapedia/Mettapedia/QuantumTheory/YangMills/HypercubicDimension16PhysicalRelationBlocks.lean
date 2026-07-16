import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalOrbitOperator

/-!
# Sector blocks of the dimension-sixteen physical relation operator

The source field count of every standard relation generator is explicit.
All rows preserve that count except the covariant-derivative commutator, whose
inserted curvature term lies in the successor field sector.  This gives the
block upper-bidiagonal incidence needed by sparse rank certificates.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalRelationBlocks

open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16DifferentialRelations
open HypercubicDimension16IBPTraceRelations
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator

def physicalRelationGeneratorSourceCarrier
    {policy : PhysicalRelationPolicy} :
    PhysicalRelationGenerator policy → RelationCarrier
  | .antisymmetry carrier _ => carrier
  | .bianchi carrier _ _ _ => carrier
  | .eom _ carrier _ _ _ => carrier
  | .integrationByParts carrier _ _ => carrier
  | .traceless carrier _ _ => carrier
  | .covariantCommutator carrier _ => carrier
  | .traceAnticommutator carrier _ => carrier
  | .fundamentalTrace carrier _ => carrier

def physicalRelationGeneratorSourceFieldCount
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy) : Fin 9 :=
  (physicalRelationGeneratorSourceCarrier generator).1

def InSourceOrSuccessorFieldSector
    (source target : Fin 9) : Prop :=
  target = source ∨ target.1 = source.1 + 1

instance inSourceOrSuccessorFieldSectorDecidable (source : Fin 9) :
    DecidablePred (InSourceOrSuccessorFieldSector source) := by
  intro target
  unfold InSourceOrSuccessorFieldSector
  infer_instance

private theorem relationCarrier_ne_target_of_same_field
    (source candidate target : RelationCarrier)
    (houtside : target.1 ≠ source.1)
    (hsame : candidate.1 = source.1) :
    candidate ≠ target := by
  intro heq
  apply houtside
  calc
    target.1 = candidate.1 := congrArg (fun value : RelationCarrier => value.1) heq.symm
    _ = source.1 := hsame

private theorem relationCarrier_ne_target_of_successor_field
    (source candidate target : RelationCarrier)
    (houtside : target.1.1 ≠ source.1.1 + 1)
    (hsuccessor : candidate.1.1 = source.1.1 + 1) :
    candidate ≠ target := by
  intro heq
  apply houtside
  calc
    target.1.1 = candidate.1.1 :=
      congrArg (fun value : RelationCarrier => value.1.1) heq.symm
    _ = source.1.1 + 1 := hsuccessor

theorem physicalRelationRow_apply_eq_zero_of_outside_field_band
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy)
    (target : RelationCarrier)
    (outside : ¬ InSourceOrSuccessorFieldSector
      (physicalRelationGeneratorSourceFieldCount generator) target.1) :
    physicalRelationRow generator target = 0 := by
  cases generator with
  | antisymmetry carrier slot =>
      have hout : target.1 ≠ carrier.1 := fun heq => outside (Or.inl heq)
      have hcarrier : carrier ≠ target :=
        relationCarrier_ne_target_of_same_field carrier carrier target hout rfl
      have hswap : swapExactFieldAxes carrier slot ≠ target :=
        relationCarrier_ne_target_of_same_field carrier
          (swapExactFieldAxes carrier slot) target hout rfl
      simp [physicalRelationRow, fieldAntisymmetryRow, hcarrier, hswap]
  | bianchi carrier field position innermost =>
      have hout : target.1 ≠ carrier.1 := fun heq => outside (Or.inl heq)
      have hcarrier : carrier ≠ target :=
        relationCarrier_ne_target_of_same_field carrier carrier target hout rfl
      have hone : bianchiRotateOne carrier field position ≠ target :=
        relationCarrier_ne_target_of_same_field carrier
          (bianchiRotateOne carrier field position) target hout rfl
      have htwo : bianchiRotateTwo carrier field position ≠ target :=
        relationCarrier_ne_target_of_same_field carrier
          (bianchiRotateTwo carrier field position) target hout rfl
      simp [physicalRelationRow, bianchiRow, hcarrier, hone, htwo]
  | eom enabled carrier field position innermost =>
      have hout : target.1 ≠ carrier.1 := fun heq => outside (Or.inl heq)
      have hterm : ∀ axis, eomTerm carrier field position axis ≠ target :=
        fun axis => relationCarrier_ne_target_of_same_field carrier
          (eomTerm carrier field position axis) target hout rfl
      simp [physicalRelationRow, eomRow, hterm]
  | integrationByParts carrier position outermost =>
      have hout : target.1 ≠ carrier.1 := fun heq => outside (Or.inl heq)
      have hterm : ∀ owner, setDerivativeOwner carrier position owner ≠ target :=
        fun owner => relationCarrier_ne_target_of_same_field carrier
          (setDerivativeOwner carrier position owner) target hout rfl
      simp [physicalRelationRow, integrationByPartsRow, hterm]
  | traceless carrier field singleton =>
      have hout : target.1 ≠ carrier.1 := fun heq => outside (Or.inl heq)
      have hcarrier : carrier ≠ target :=
        relationCarrier_ne_target_of_same_field carrier carrier target hout rfl
      simp [physicalRelationRow, tracelessLetterRow, hcarrier]
  | covariantCommutator carrier site =>
      have hout : target.1 ≠ carrier.1 := fun heq => outside (Or.inl heq)
      have houtSuccessor : target.1.1 ≠ carrier.1.1 + 1 :=
        fun heq => outside (Or.inr heq)
      have hcarrier : carrier ≠ target :=
        relationCarrier_ne_target_of_same_field carrier carrier target hout rfl
      have hswap :
          swapExactDerivativePositions carrier site.outer site.inner ≠ target :=
        relationCarrier_ne_target_of_same_field carrier
          (swapExactDerivativePositions carrier site.outer site.inner)
          target hout rfl
      have hbefore :
          insertCurvatureCarrier site CurvatureInsertionSide.before ≠ target :=
        relationCarrier_ne_target_of_successor_field carrier
          (insertCurvatureCarrier site CurvatureInsertionSide.before)
          target houtSuccessor rfl
      have hafter :
          insertCurvatureCarrier site CurvatureInsertionSide.after ≠ target :=
        relationCarrier_ne_target_of_successor_field carrier
          (insertCurvatureCarrier site CurvatureInsertionSide.after)
          target houtSuccessor rfl
      simp [physicalRelationRow, covariantCommutatorRow,
        hcarrier, hswap, hbefore, hafter]
  | traceAnticommutator carrier site =>
      have hout : target.1 ≠ carrier.1 := fun heq => outside (Or.inl heq)
      have hcarrier : carrier ≠ target :=
        relationCarrier_ne_target_of_same_field carrier carrier target hout rfl
      have hswap : swapAdjacentTraceCarrier site ≠ target :=
        relationCarrier_ne_target_of_same_field carrier
          (swapAdjacentTraceCarrier site) target hout rfl
      have hsplit : splitAdjacentTraceCarrier site ≠ target :=
        relationCarrier_ne_target_of_same_field carrier
          (splitAdjacentTraceCarrier site) target hout rfl
      simp [physicalRelationRow, traceAnticommutatorRow,
        hcarrier, hswap, hsplit]
  | fundamentalTrace carrier site =>
      have hout : target.1 ≠ carrier.1 := fun heq => outside (Or.inl heq)
      have hcarrier : carrier ≠ target :=
        relationCarrier_ne_target_of_same_field carrier carrier target hout rfl
      have hrewire : ∀ rewire : Equiv.Perm (Fin carrier.1.1),
          rewireTraceCarrier carrier rewire ≠ target :=
        fun rewire => relationCarrier_ne_target_of_same_field carrier
          (rewireTraceCarrier carrier rewire) target hout rfl
      simp [physicalRelationRow, fundamentalTraceRow, hcarrier, hrewire]

/-! ## Exact field-sector filters -/

def relationFieldFilter (predicate : Fin 9 → Prop)
    [DecidablePred predicate] : RelationSpace →ₗ[ℚ] RelationSpace where
  toFun value := value.filter (fun target => predicate target.1)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

def orientedFieldFilter (predicate : Fin 9 → Prop)
    [DecidablePred predicate] :
    ExactOrientedLocalSpace →ₗ[ℚ] ExactOrientedLocalSpace where
  toFun value := value.filter (fun target => predicate target.1)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

def orbitFieldFilter (predicate : Fin 9 → Prop)
    [DecidablePred predicate] :
    ExactFieldRelabelOrbitSpace →ₗ[ℚ] ExactFieldRelabelOrbitSpace where
  toFun value := value.filter (fun target => predicate target.1)
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

theorem normalizeExactContextual_fieldFilter
    (predicate : Fin 9 → Prop) [DecidablePred predicate]
    (value : RelationSpace) :
    normalizeExactContextual (relationFieldFilter predicate value) =
      orientedFieldFilter predicate (normalizeExactContextual value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add left right hleft hright =>
      simp [map_add, hleft, hright]
  | single carrier coefficient =>
      by_cases membership : predicate carrier.1
      · simp [relationFieldFilter, orientedFieldFilter,
          Finsupp.filter_single_of_pos, membership,
          normalizeExactContextualBasis, exactNormalizedSectorData]
      · simp [relationFieldFilter, orientedFieldFilter,
          Finsupp.filter_single_of_neg, membership,
          normalizeExactContextualBasis, exactNormalizedSectorData]

theorem normalizeExactFieldRelabel_fieldFilter
    (predicate : Fin 9 → Prop) [DecidablePred predicate]
    (value : ExactOrientedLocalSpace) :
    normalizeExactFieldRelabel (orientedFieldFilter predicate value) =
      orbitFieldFilter predicate (normalizeExactFieldRelabel value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add left right hleft hright =>
      simp [map_add, hleft, hright]
  | single target coefficient =>
      by_cases membership : predicate target.1
      · simp [orientedFieldFilter, orbitFieldFilter,
          Finsupp.filter_single_of_pos, membership,
          normalizeExactFieldRelabelBasis,
          exactFieldRelabelOrbitOfOriented]
      · simp [orientedFieldFilter, orbitFieldFilter,
          Finsupp.filter_single_of_neg, membership,
          normalizeExactFieldRelabelBasis,
          exactFieldRelabelOrbitOfOriented]

theorem relationFieldFilter_physicalRelationRow
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy) :
    relationFieldFilter
        (InSourceOrSuccessorFieldSector
          (physicalRelationGeneratorSourceFieldCount generator))
        (physicalRelationRow generator) =
      physicalRelationRow generator := by
  classical
  apply Finsupp.ext
  intro target
  by_cases membership : InSourceOrSuccessorFieldSector
      (physicalRelationGeneratorSourceFieldCount generator) target.1
  · change (if InSourceOrSuccessorFieldSector
        (physicalRelationGeneratorSourceFieldCount generator) target.1
      then physicalRelationRow generator target else 0) = _
    rw [if_pos membership]
  · change (if InSourceOrSuccessorFieldSector
        (physicalRelationGeneratorSourceFieldCount generator) target.1
      then physicalRelationRow generator target else 0) = _
    rw [if_neg membership,
      physicalRelationRow_apply_eq_zero_of_outside_field_band
        generator target membership]

/-- Each column of the physical operator on the genuine field-label orbit
carrier lies in its source field sector plus, only when applicable, the
successor field sector. -/
theorem orbitPhysicalRelationOperator_single_field_band
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy)
    (coefficient : ℚ) :
    orbitFieldFilter
        (InSourceOrSuccessorFieldSector
          (physicalRelationGeneratorSourceFieldCount generator))
        (orbitPhysicalRelationOperator policy
          (Finsupp.single generator coefficient)) =
      orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient) := by
  classical
  simp only [orbitPhysicalRelationOperator,
    normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_single]
  rw [← normalizeExactFieldRelabel_fieldFilter,
    ← normalizeExactContextual_fieldFilter,
    LinearMap.map_smul,
    relationFieldFilter_physicalRelationRow]

theorem orbitPhysicalRelationOperator_single_apply_eq_zero_of_outside_field_band
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy)
    (coefficient : ℚ)
    (target : ExactFieldRelabelOrbitCarrier)
    (outside : ¬ InSourceOrSuccessorFieldSector
      (physicalRelationGeneratorSourceFieldCount generator) target.1) :
    orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient) target = 0 := by
  classical
  have hfiltered := orbitPhysicalRelationOperator_single_field_band
    generator coefficient
  rw [← hfiltered]
  change (if InSourceOrSuccessorFieldSector
      (physicalRelationGeneratorSourceFieldCount generator) target.1
    then _ else 0) = 0
  rw [if_neg outside]

end HypercubicDimension16PhysicalRelationBlocks
end YangMills
end QuantumTheory
end Mettapedia
