import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizCommutator
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16JointPhysicalQuotient

/-!
# OUR Leibniz-corrected physical relation operator

The operator of `HypercubicDimension16PhysicalRelationOperator` uses the
commutator row of `HypercubicDimension16CovariantCommutator`, which is a
field identity only when the commutator's field has no derivatives outside
the pair.  This module assembles the same generator families with the
Leibniz-correct row of `HypercubicDimension16LeibnizCommutator` in place of
that row, on the same generator space and with the same signed hypercubic
action.  It then carries the corrected operator through the exact contextual
quotient and the field-label orbit quotient, and defines the corrected joint
invariant relation submodule and its coordinate-free scalar quotient.

The two operators agree on every generator that is not a commutator site with
outer derivatives on its field.  The earlier operator and its submodules are
unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16LeibnizRelationOperator

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicRawFDCharacterCensus
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16DifferentialRelations
open HypercubicDimension16IBPTraceRelations
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16LeibnizCommutator

/-! ## Rows and operator -/

/-- OUR row of each standard generator, with the Leibniz-correct commutator
row. -/
def leibnizPhysicalRelationRow {policy : PhysicalRelationPolicy} :
    PhysicalRelationGenerator policy → RelationSpace
  | .antisymmetry carrier slot =>
      fieldAntisymmetryRow carrier slot
  | .bianchi carrier field position _ =>
      bianchiRow carrier field position
  | .eom _ carrier field position _ =>
      eomRow carrier field position
  | .integrationByParts carrier position _ =>
      integrationByPartsRow carrier position
  | .traceless carrier field _ =>
      tracelessLetterRow carrier field
  | .covariantCommutator _ site =>
      leibnizCommutatorRow site
  | .traceAnticommutator _ site =>
      traceAnticommutatorRow site
  | .fundamentalTrace _ site =>
      fundamentalTraceRow site

@[simp] theorem leibnizPhysicalRelationRow_covariantCommutator
    {policy : PhysicalRelationPolicy} (carrier : RelationCarrier)
    (site : CovariantCommutatorSite carrier) :
    leibnizPhysicalRelationRow
        (PhysicalRelationGenerator.covariantCommutator (policy := policy)
          carrier site) =
      leibnizCommutatorRow site :=
  rfl

/-- The two row maps agree except on commutator sites whose field carries
outer derivatives. -/
theorem leibnizPhysicalRelationRow_eq_physicalRelationRow
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy)
    (hsound : ∀ (carrier : RelationCarrier)
      (site : CovariantCommutatorSite carrier),
      generator = .covariantCommutator carrier site →
        outerSameOwnerPositions site = ∅) :
    leibnizPhysicalRelationRow generator = physicalRelationRow generator := by
  cases generator
  case covariantCommutator carrier site =>
    exact leibnizCommutatorRow_eq_covariantCommutatorRow site
      (hsound carrier site rfl)
  all_goals rfl

theorem leibnizPhysicalRelationRow_equivariant
    {policy : PhysicalRelationPolicy} (h : Hypercubic4)
    (generator : PhysicalRelationGenerator policy) :
    signedRelationAction h (leibnizPhysicalRelationRow generator) =
      physicalRelationGeneratorSign h generator •
        leibnizPhysicalRelationRow (generator.act h) := by
  cases generator with
  | antisymmetry carrier slot =>
      exact fieldAntisymmetryRow_equivariant h carrier slot
  | bianchi carrier field position innermost =>
      exact bianchiRow_equivariant h carrier field position innermost
  | eom enabled carrier field position innermost =>
      exact eomRow_equivariant h carrier field position innermost
  | integrationByParts carrier position outermost =>
      exact integrationByPartsRow_equivariant h carrier position outermost
  | traceless carrier field singleton =>
      exact tracelessLetterRow_equivariant h carrier field singleton
  | covariantCommutator carrier site =>
      exact leibnizCommutatorRow_equivariant h site
  | traceAnticommutator carrier site =>
      exact traceAnticommutatorRow_equivariant h site
  | fundamentalTrace carrier site =>
      exact fundamentalTraceRow_equivariant h site

/-- OUR Leibniz-corrected joint standard-relation operator. -/
def leibnizPhysicalRelationOperator (policy : PhysicalRelationPolicy) :
    PhysicalRelationGeneratorSpace policy →ₗ[ℚ] RelationSpace :=
  Finsupp.linearCombination ℚ leibnizPhysicalRelationRow

@[simp] theorem leibnizPhysicalRelationOperator_single
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ) :
    leibnizPhysicalRelationOperator policy
        (Finsupp.single generator coefficient) =
      coefficient • leibnizPhysicalRelationRow generator := by
  simp [leibnizPhysicalRelationOperator]

theorem leibnizPhysicalRelationOperator_equivariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : PhysicalRelationGeneratorSpace policy) :
    leibnizPhysicalRelationOperator policy
        (signedPhysicalRelationGeneratorAction policy h value) =
      signedRelationAction h (leibnizPhysicalRelationOperator policy value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single generator coefficient =>
      simp [signedPhysicalRelationGeneratorActionBasis,
        leibnizPhysicalRelationRow_equivariant h generator, smul_smul]

def leibnizPhysicalRelationSubmodule (policy : PhysicalRelationPolicy) :
    Submodule ℚ RelationSpace :=
  LinearMap.range (leibnizPhysicalRelationOperator policy)

theorem leibnizPhysicalRelationSubmodule_signed_invariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : RelationSpace)
    (membership : value ∈ leibnizPhysicalRelationSubmodule policy) :
    signedRelationAction h value ∈ leibnizPhysicalRelationSubmodule policy := by
  rcases membership with ⟨source, rfl⟩
  exact ⟨signedPhysicalRelationGeneratorAction policy h source,
    leibnizPhysicalRelationOperator_equivariant policy h source⟩

/-! ## Transport through the contextual and field-label quotients -/

def leibnizNormalizedPhysicalRelationOperator
    (policy : PhysicalRelationPolicy) :
    PhysicalRelationGeneratorSpace policy →ₗ[ℚ] ExactOrientedLocalSpace :=
  normalizeExactContextual.comp (leibnizPhysicalRelationOperator policy)

theorem leibnizNormalizedPhysicalRelationOperator_equivariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : PhysicalRelationGeneratorSpace policy) :
    leibnizNormalizedPhysicalRelationOperator policy
        (signedPhysicalRelationGeneratorAction policy h value) =
      signedExactOrientedLocalAction h
        (leibnizNormalizedPhysicalRelationOperator policy value) := by
  rw [leibnizNormalizedPhysicalRelationOperator, LinearMap.comp_apply,
    leibnizPhysicalRelationOperator_equivariant]
  exact normalizeExactContextual_signed_equivariant h
    (leibnizPhysicalRelationOperator policy value)

/-- OUR Leibniz-corrected operator on the genuine field-label orbit carrier. -/
def leibnizOrbitPhysicalRelationOperator
    (policy : PhysicalRelationPolicy) :
    PhysicalRelationGeneratorSpace policy →ₗ[ℚ] ExactFieldRelabelOrbitSpace :=
  normalizeExactFieldRelabel.comp
    (leibnizNormalizedPhysicalRelationOperator policy)

theorem leibnizOrbitPhysicalRelationOperator_equivariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : PhysicalRelationGeneratorSpace policy) :
    leibnizOrbitPhysicalRelationOperator policy
        (signedPhysicalRelationGeneratorAction policy h value) =
      signedExactFieldRelabelOrbitAction h
        (leibnizOrbitPhysicalRelationOperator policy value) := by
  rw [leibnizOrbitPhysicalRelationOperator, LinearMap.comp_apply,
    leibnizNormalizedPhysicalRelationOperator_equivariant]
  exact normalizeExactFieldRelabel_signed_equivariant h
    (leibnizNormalizedPhysicalRelationOperator policy value)

def leibnizOrbitPhysicalRelationSubmodule
    (policy : PhysicalRelationPolicy) :
    Submodule ℚ ExactFieldRelabelOrbitSpace :=
  LinearMap.range (leibnizOrbitPhysicalRelationOperator policy)

theorem leibnizOrbitPhysicalRelationSubmodule_signed_invariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : ExactFieldRelabelOrbitSpace)
    (membership : value ∈ leibnizOrbitPhysicalRelationSubmodule policy) :
    signedExactFieldRelabelOrbitAction h value ∈
      leibnizOrbitPhysicalRelationSubmodule policy := by
  rcases membership with ⟨source, rfl⟩
  exact ⟨signedPhysicalRelationGeneratorAction policy h source,
    leibnizOrbitPhysicalRelationOperator_equivariant policy h source⟩

/-- On a generator whose two rows agree, the two orbit columns agree. -/
theorem leibnizOrbitPhysicalRelationOperator_single_of_row_eq
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ)
    (hrow : leibnizPhysicalRelationRow generator = physicalRelationRow generator) :
    leibnizOrbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient) =
      orbitPhysicalRelationOperator policy
        (Finsupp.single generator coefficient) := by
  simp [leibnizOrbitPhysicalRelationOperator,
    leibnizNormalizedPhysicalRelationOperator, orbitPhysicalRelationOperator,
    normalizedPhysicalRelationOperator, hrow]

/-! ## The corrected joint invariant relation submodule -/

/-- OUR Leibniz-corrected joint relations: the invariant vectors in the full
corrected relation range. -/
def leibnizJointInvariantRelationSubmodule (policy : PhysicalRelationPolicy) :
    Submodule ℚ exactFieldOrbitInvariantSubmodule :=
  (leibnizOrbitPhysicalRelationSubmodule policy).comap
    exactFieldOrbitInvariantSubmodule.subtype

theorem mem_leibnizJointInvariantRelationSubmodule_iff
    (policy : PhysicalRelationPolicy)
    (value : exactFieldOrbitInvariantSubmodule) :
    value ∈ leibnizJointInvariantRelationSubmodule policy ↔
      (value.1 : ExactFieldRelabelOrbitSpace) ∈
        leibnizOrbitPhysicalRelationSubmodule policy := by
  rfl

theorem leibnizPhysicalRelationRow_liftOffShellGenerator
    (generator : PhysicalRelationGenerator .offShell) :
    leibnizPhysicalRelationRow (liftOffShellGenerator generator) =
      leibnizPhysicalRelationRow generator := by
  cases generator with
  | antisymmetry carrier slot => rfl
  | bianchi carrier field position innermost => rfl
  | eom enabled carrier field position innermost => cases enabled
  | integrationByParts carrier position outermost => rfl
  | traceless carrier field singleton => rfl
  | covariantCommutator carrier site => rfl
  | traceAnticommutator carrier site => rfl
  | fundamentalTrace carrier site => rfl

theorem leibnizOrbitPhysicalRelationOperator_liftOffShell
    (value : PhysicalRelationGeneratorSpace .offShell) :
    leibnizOrbitPhysicalRelationOperator .onShell
        (liftOffShellGeneratorSpace value) =
      leibnizOrbitPhysicalRelationOperator .offShell value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [LinearMap.map_add, hleft, hright]
  | single generator coefficient =>
      simp [liftOffShellGeneratorSpace, leibnizOrbitPhysicalRelationOperator,
        leibnizNormalizedPhysicalRelationOperator,
        leibnizPhysicalRelationOperator_single,
        leibnizPhysicalRelationRow_liftOffShellGenerator]

theorem leibnizOrbitPhysicalRelationSubmodule_offShell_le_onShell :
    leibnizOrbitPhysicalRelationSubmodule .offShell ≤
      leibnizOrbitPhysicalRelationSubmodule .onShell := by
  rintro value ⟨source, rfl⟩
  exact ⟨liftOffShellGeneratorSpace source,
    leibnizOrbitPhysicalRelationOperator_liftOffShell source⟩

theorem leibnizJointInvariantRelationSubmodule_offShell_le_onShell :
    leibnizJointInvariantRelationSubmodule .offShell ≤
      leibnizJointInvariantRelationSubmodule .onShell := by
  intro value membership
  rw [mem_leibnizJointInvariantRelationSubmodule_iff] at membership ⊢
  exact leibnizOrbitPhysicalRelationSubmodule_offShell_le_onShell membership

/-! ## Coordinate-free corrected joint quotient -/

abbrev LeibnizJointScalarPhysicalQuotient (policy : PhysicalRelationPolicy) :=
  exactFieldOrbitInvariantSubmodule ⧸
    leibnizJointInvariantRelationSubmodule policy

theorem leibnizJointScalarPhysicalQuotient_finrank_formula
    (policy : PhysicalRelationPolicy) :
    Module.finrank ℚ (LeibnizJointScalarPhysicalQuotient policy) =
      Module.finrank ℚ exactFieldOrbitInvariantSubmodule -
        Module.finrank ℚ (leibnizJointInvariantRelationSubmodule policy) := by
  rw [Submodule.finrank_quotient]

theorem leibnizJointScalarPhysicalQuotient_onShell_finrank_le_offShell :
    Module.finrank ℚ (LeibnizJointScalarPhysicalQuotient .onShell) ≤
      Module.finrank ℚ (LeibnizJointScalarPhysicalQuotient .offShell) := by
  rw [leibnizJointScalarPhysicalQuotient_finrank_formula,
    leibnizJointScalarPhysicalQuotient_finrank_formula]
  have hrank := Submodule.finrank_mono
    leibnizJointInvariantRelationSubmodule_offShell_le_onShell
  have hoff := Submodule.finrank_le
    (leibnizJointInvariantRelationSubmodule .offShell)
  have hon := Submodule.finrank_le
    (leibnizJointInvariantRelationSubmodule .onShell)
  omega

#print axioms leibnizPhysicalRelationRow_eq_physicalRelationRow
#print axioms leibnizPhysicalRelationRow_equivariant
#print axioms leibnizPhysicalRelationOperator_equivariant
#print axioms leibnizOrbitPhysicalRelationOperator_equivariant
#print axioms leibnizOrbitPhysicalRelationSubmodule_signed_invariant
#print axioms leibnizOrbitPhysicalRelationOperator_single_of_row_eq
#print axioms leibnizJointInvariantRelationSubmodule_offShell_le_onShell
#print axioms leibnizJointScalarPhysicalQuotient_onShell_finrank_le_offShell

end HypercubicDimension16LeibnizRelationOperator
end YangMills
end QuantumTheory
end Mettapedia
